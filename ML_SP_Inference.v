(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, August 2008                                            *
***************************************************************************)

Set Implicit Arguments.

Require Import List Metatheory.

Section Index.
  Variable A : Set.
  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Fixpoint index (i:nat) (x:A) (l : list A) {struct l} : option nat :=
    match l with
    | nil   => None
    | y::l' => if eq_dec x y then Some i else index (S i) x l'
    end.
End Index.

Require Import ML_SP_Definitions ML_SP_Infrastructure.
Require Import ML_SP_Soundness ML_SP_Unify.

Module MkInfer(Cstr:CstrIntf)(Const:CstIntf).

Module Unify := MkUnify(Cstr)(Const).
Import Unify.
Import Sound0.Infra.
Import Defs.
Import Metatheory_Env.Env.

Module Mk2(Delta:DeltaIntf)(Cstr2:Cstr2I).

Module Sound := Sound0.Mk2(Delta).
Import Sound.
Import JudgInfra.
Import Judge.

Module Body := Unify.Mk2(Cstr2).
Import Body.

Definition unify K T1 T2 S :=
  unify (1 + size_pairs S K ((T1,T2)::nil)) ((T1,T2)::nil) K S.

Definition fvs S K E T :=
  dom S \u fv_in typ_fv S \u dom K \u fv_in kind_fv K \u env_fv E \u typ_fv T.

Definition close_fvk K := close_fvars (length K) K (dom K).

Fixpoint generalize (Bs:list var) (T:typ) {struct T} : typ :=
  match T with
  | typ_bvar n =>
    typ_bvar (length Bs + n)
  | typ_fvar x =>
    match index eq_var_dec 0 x Bs with
    | None   => T
    | Some n => typ_bvar n
    end
  | typ_arrow T1 T2 =>
    typ_arrow (generalize Bs T1) (generalize Bs T2)
  end.

Fixpoint split_env (A:Set) (B:vars) (E:env A) {struct E} : env A * env A :=
  match E with
  | nil => (nil, nil)
  | xk::E' =>
    let (Eb, EB) := split_env B E' in
    if S.mem (fst xk) B then (Eb, xk::EB) else (xk::Eb, EB)
  end.

Definition vars_subst S L :=
  typ_fv_list (List.map (fun x => typ_subst S (typ_fvar x)) (S.elements L)).

Fixpoint typinf (K:kenv) (E:Defs.env) (t:trm) (T:typ) (S:subs) (h:nat)
  {struct h} : option (kenv * subs) :=
  match h with
  | 0 => None
  | S h' =>
  match t with
  | trm_bvar _ => None
  | trm_fvar x =>
    match get x E with
    | None => None
    | Some M =>
      let Vs := proj1_sig (var_freshes (fvs S K E T) (sch_arity M)) in
      unify (K & kinds_open_vars (sch_kinds M) Vs) (M ^ Vs) T S
    end
  | trm_abs t1 =>
    let x := proj1_sig (var_fresh (dom E \u trm_fv t1)) in
    let v1 := proj1_sig (var_fresh (fvs S K E T)) in
    let V2 := typ_fvar (proj1_sig (var_fresh (fvs S K E T \u {{v1}}))) in
    match unify K (typ_arrow (typ_fvar v1) V2) T S with
    | None => None
    | Some (K',S') =>
      typinf K' (E & x ~ Sch (typ_fvar v1) nil) (t1 ^ x) V2 S' h'
    end
  | trm_let t1 t2 =>
    let V := typ_fvar (proj1_sig (var_fresh (fvs S K E T))) in
    match typinf K E t1 V S h' with
    | None => None
    | Some (K0,S') =>
      let K' := Env.map (kind_subst S') K0 in
      let E' := Env.map (sch_subst S') E in
      let ftve := close_fvk K' (env_fv E' \u vars_subst S' (dom K)) in
      let T1 := typ_subst S' V in
      let B := S.diff (close_fvk K' (typ_fv T1)) ftve in
      let (Kb, KB) := split_env B K' in
      let (Bs, Ks) := split KB in
      let x := proj1_sig (var_fresh (dom E \u trm_fv t1 \u trm_fv t2)) in
      typinf Kb
        (E & x~Sch (generalize Bs T1) (List.map (kind_map (generalize Bs)) Ks))
        (t2 ^ x) T S' h'
    end
  | trm_app t1 t2 =>
    let V := typ_fvar (proj1_sig (var_fresh (fvs S K E T))) in
    match typinf K E t1 (typ_arrow V T) S h' with
    | None => None
    | Some (K',S') => typinf K' E t2 V S' h'
    end
  | trm_cst c =>
    let M := Delta.type c in
    let Vs := proj1_sig (var_freshes (fvs S K E T) (sch_arity M)) in
    unify (K & kinds_open_vars (sch_kinds M) Vs) (M ^ Vs) T S
  end
  end.

Fixpoint trm_depth (t : trm) : nat :=
  match t with
  | trm_bvar _ => 0
  | trm_fvar _ => 0
  | trm_abs t1 => S (trm_depth t1)
  | trm_let t1 t2 => S (Max.max (trm_depth t1) (trm_depth t2))
  | trm_app t1 t2 => S (Max.max (trm_depth t1) (trm_depth t2))
  | trm_cst _ => 0
  end.

Lemma env_prop_type_compose : forall S1 S2,
  env_prop type S1 -> env_prop type S2 -> env_prop type (compose S1 S2).
Proof.
  unfold compose.
  intros.
  intro; intros.
  binds_cases H1.
    destruct (binds_map_inv _ _ B) as [T [Eq B']].
    subst.
    apply* typ_subst_type.
  auto*.
Qed.

Section EnvProp.
  Variables (A:Set) (P:A->Prop).

  Lemma env_prop_single : forall x a, P a -> env_prop P (x ~ a).
  Proof.
    intros; intro; intros.
    destruct (binds_single_inv H0). subst*.
  Qed.

  Lemma env_prop_concat : forall l1 l2,
    env_prop P l1 -> env_prop P l2 -> env_prop P (l1 & l2).
  Proof.
    intros; intro; intros.
    binds_cases H1. apply* (H x).
    apply* (H0 x).
  Qed.

End EnvProp.

Hint Resolve env_prop_single env_prop_concat env_prop_type_compose.

Lemma For_all_app : forall (A:Set) (P:A->Prop) l1 l2,
  For_all P l1 -> For_all P l2 -> For_all P (l1++l2).
Proof.
  intros; induction l1. simpl*.
  simpl in *.
  auto*.
Qed.

Lemma unify_rel_all_kind_types :
  forall (P:typ->Prop) k k0 kc (v1:Cstr.valid kc),
  All_kind_types P (Some k) -> All_kind_types P (Some k0) ->
  let krs := kind_rel k ++ kind_rel k0 in
  All_kind_types P (Some (Kind v1 (unify_coherent krs))) /\
  (forall T1 T2,
   In (T1, T2) (snd (unify_kind_rel krs nil (Cstr2.unique kc) nil)) ->
   P T1 /\ P T2).
Proof.
  unfold All_kind_types; intros.
  simpl in *.
  use (For_all_app _ _ _ H H0).
  clear H H0.
  rewrite <- map_app in H1.
  set (kr':=@nil (var*typ)).
  set (pairs':=@nil (typ*typ)).
  assert (For_all P (List.map (fun x : var * typ => snd x) kr')) by simpl*.
  assert (forall T1 T2, In (T1, T2) pairs' -> P T1 /\ P T2) by simpl*.
  gen kr' pairs'.
  induction (kind_rel k ++ kind_rel k0); simpl; intros. auto.
  destruct a.
  simpl in H1.
  destruct (In_dec eq_var_dec v (Cstr2.unique kc)).
    case_eq (get v kr'); intros.
      apply* IHl.
      simpl; intros.
      destruct* H3.
      inversions H3.
      split*.
      clear -H H2.
      induction kr'; simpl in *. discriminate.
      destruct a. destruct (v == v0).
        inversions* H2.
      apply* IHkr'.
    apply* IHl.
    simpl*.
  apply* IHl.
  simpl*.
Qed.

Lemma kenv_ok_remove_env : forall K v,
  kenv_ok K -> kenv_ok (remove_env K v).
Proof.
  intros; split*.
  intro; intros.
  apply (proj2 H x).
  apply* binds_orig_remove_env.
Qed.

Hint Resolve kenv_ok_remove_env.

Lemma All_kind_types_None : forall P, All_kind_types P None.
Proof.
  unfold All_kind_types. simpl*.
Qed.

Hint Resolve All_kind_types_None.

Lemma unify_type : forall K' S' h pairs K S,
  Body.unify h pairs K S = Some (K', S') ->
  is_subst S ->
  env_prop type S ->
  kenv_ok K ->
  (forall T1 T2, In (T1, T2) pairs -> type T1 /\ type T2) ->
  kenv_ok K' /\ env_prop type S'.
Proof.
  induction h; simpl; intros. discriminate.
  destruct pairs. inversions* H.
  destruct p.
  assert (type t /\ type t0). apply* H3.
  destruct H4.
  use (typ_subst_type H1 H4).
  use (typ_subst_type H1 H5).
  case_rewrite (typ_subst S t) R1; try solve [inversion H6];
    case_rewrite (typ_subst S t0) R2; try solve [inversion H7];
      try (unfold unify_nv in H;
           case_rewrite (S.mem v (typ_fv (typ_arrow t1 t2))) R3;
           case_rewrite (get_kind v K) R4; apply* IHh).
    destruct (v == v0). apply* IHh.
    unfold unify_vars in H.
    assert (Hok: forall k, ok (remove_env (remove_env K v) v0 & v0 ~ k)).
      intro; constructor.
      repeat apply* ok_remove_env.
      rewrite* dom_remove_env.
    assert (Horig: forall x a,
      binds x a (remove_env (remove_env K v) v0) -> All_kind_types type a).
      intros; apply (proj2 H2 x a).
      use (binds_orig_remove_env v0 (ok_remove_env v (proj1 H2)) H8).
      apply* binds_orig_remove_env.
    case_rewrite (get_kind v K) R3; case_rewrite (get_kind v0 K) R4;
      try poses Aktc (proj2 H2 _ _ (get_kind_binds _ _ R3));
      try poses Aktc0 (proj2 H2 _ _ (get_kind_binds _ _ R4));
      simpl unify_kinds in H.
          destruct c as [kc kv kr kh].
          destruct c0 as [kc0 kv0 kr0 kh0].
          destruct (Cstr2.valid (Cstr2.lub kc kc0)); try discriminate.
          replace kr with (kind_rel (Kind kv kh)) in H by simpl*.
          replace kr0 with (kind_rel (Kind kv0 kh0)) in H by simpl*.
          destruct*
            (unify_rel_all_kind_types type (Kind kv kh) (Kind kv0 kh0) v1).
          apply* IHh; clear IHh H.
          split*.
          intros.
          destruct* (in_app_or _ _ _ H).
        destruct c as [kc kv kr kh].
        simpl app in H.
        apply* IHh. split*.
      cbv iota beta in H. simpl app in H.
      apply* IHh. split*.
    cbv iota beta in H. simpl app in H.
    apply* IHh. split*.
  apply* IHh; clear IHh H.
  simpl; intros.
  inversions H6.
  inversions H7.
  destruct H. inversions* H.
  destruct H. inversions* H.
  apply* H3.
Qed.

Lemma concat_empty_l : forall (A:Set) (E:env A),
  empty & E = E.
Proof.
  unfold concat, empty. intros; rewrite* <- app_nil_end.
Qed.

Lemma env_incl_map : forall (A:Set) (f:A->A) E1 E2,
  env_incl E1 E2 -> env_incl (map f E1) (map f E2).
Proof.
  intros; intro; intros.
  destruct (binds_map_inv _ _ H0) as [a [HE B]].
  subst.
  apply* binds_map.
Qed.
Lemma split_env_ok : forall (A:Set) (B:vars) (E Eb EB:env A),
  split_env B E = (Eb, EB) -> ok E ->
  ok (Eb & EB) /\ disjoint B (dom Eb) /\ dom EB << B /\
  env_incl E (Eb & EB) /\ env_incl (Eb & EB) E.
Proof.
  induction E; simpl; intros.
    inversions H. simpl. split*. split. intro; auto*.
    split. intros x Hx. elim (in_empty Hx).
    assert (env_incl (A:=A) nil nil) by (intro; tauto).
    auto.
  destruct a.
  case_rewrite (split_env B E) R1.
  simpl in *.
  case_rewrite (S.mem v B) R2.
    inversions H; clear H.
    inversions H0; clear H0.
    destruct* (IHE Eb e0) as [Hok [Dis [Dom [I1 I2]]]]; clear IHE.
    destruct (ok_concat_inv _ _ Hok).
    case_eq (get v (Eb & e0)); intros.
      elim (binds_fresh (I2 _ _ H1) H4).
    poses Hv' (get_none_notin _ H1); clear H1.
    split.
      apply* disjoint_ok.
        apply* (@ok_push _ e0 v a).
      use (ok_disjoint _ _ Hok).
      simpl.
      disjoint_solve.
      destruct* (v0 == v). subst*.
    split*.
    split.
      simpl. intros x Hx. destruct* (S.union_1 Hx).
      rewrite <- (S.singleton_1 H1).
      apply* S.mem_2.
    replace ((v,a) :: E) with (E & v ~ a) by simpl*.
    replace ((v,a) :: e0) with (e0 & v ~ a) by simpl*.
    split; intro; intros; binds_cases H1; auto*.
  inversions H; clear H.
  inversions H0; clear H0.
  destruct* (IHE e EB) as [Hok [Dis [Dom [I1 I2]]]]; clear IHE.
  destruct (ok_concat_inv _ _ Hok).
  case_eq (get v (e & EB)); intros.
    elim (binds_fresh (I2 _ _ H1) H4).
  poses Hv' (get_none_notin _ H1); clear H1.
  split.
    apply* disjoint_ok.
      apply* (@ok_push _ e v a).
    use (ok_disjoint _ _ Hok).
    simpl.
    disjoint_solve; destruct* (v0 == v). subst*.
  split.
    simpl.
    disjoint_solve; destruct* (v0 == v); subst*.
  split*.
  replace ((v,a) :: E) with (E & v ~ a) by simpl*.
  replace ((v,a) :: e) with (e & v ~ a) by simpl*.
  split; intro; intros; binds_cases H1; auto*.
  use (I1 _ _ B0).
  binds_cases H1; auto*.
Qed.

Lemma proper_instance_well_subst : forall S K K' M Us,
  env_prop type S ->
  well_subst K K' S ->
  kenv_ok K' ->
  proper_instance K M Us ->
  proper_instance K' (sch_subst S M) (List.map (typ_subst S) Us).
Proof.
  intros.
  destruct H2 as [HUs [HM HW]].
  split.
    unfold sch_arity; simpl.
    destruct HUs.
    split. repeat rewrite map_length. auto.
    clear -H H3.
    induction H3; simpl*.
  split.
    apply* sch_subst_type.
  pose (Ts := Us).
  assert (Us = Ts) by simpl*. clearbody Ts.
  pattern Us at 2.
  pattern Us at 2 in HW.
  rewrite H2 in *.
  clear H2 HM.
  destruct M as [T Ks]; unfold sch_arity in *; simpl in *.
  destruct HUs.
  gen Ks; induction H3; destruct Ks; simpl; intros; try discriminate. auto.
  split*.
  destruct HW.
  clear IHlist_forall H6.
  rewrite* <- kind_subst_open.
  apply* well_kinded_subst.
Qed.

Lemma All_kind_types_subst : forall k S,
  All_kind_types type k ->
  env_prop type S -> All_kind_types type (kind_subst S k).
Proof.
  intros; unfold kind_subst; apply All_kind_types_map.
  apply* All_kind_types_imp.
Qed.

Lemma kenv_ok_map : forall K S,
  kenv_ok K -> env_prop type S -> kenv_ok (map (kind_subst S) K).
Proof.
  intros.
  split. apply* ok_map0.
  destruct H.
  intro; intros.
  destruct (binds_map_inv _ _ H2) as [b [Hb B]].
  subst.
  apply* All_kind_types_subst.
Qed.

Lemma kenv_ok_subst : forall K' K Ks Ys S,
  env_prop type S ->
  kenv_ok (K & kinds_open_vars Ks Ys) ->
  kenv_ok K' ->
  fresh (dom K') (length Ks) Ys ->
  kenv_ok (K' & map (kind_subst S) (kinds_open_vars Ks Ys)).
Proof.
  introv TS HK HK' Fr.
  apply* kenv_ok_concat.
    destruct (kenv_ok_concat_inv _ _ HK).
    apply* kenv_ok_map.
  rewrite dom_map. rewrite* dom_kinds_open_vars.
  apply disjoint_comm. apply* (fresh_disjoint (length Ks)).
Qed.

Lemma well_subst_extend : forall K S K' Ks Ys,
  env_prop type S ->
  well_subst K K' S ->
  fresh (dom S \u dom K') (length Ks) Ys ->
  well_subst (K & kinds_open_vars Ks Ys)
     (K' & map (kind_subst S) (kinds_open_vars Ks Ys)) S.
Proof.
  introv TS WS Fr.
  intro; intros.
  binds_cases H.
    use (WS _ _ B).
    inversions H. apply wk_any.
    simpl. rewrite <- H1.
    eapply wk_kind.
      apply binds_concat_fresh. apply H3.
      rewrite dom_map.
      unfold kinds_open_vars.
      apply* notin_combine_fresh.
      assert (x \in dom K'). apply* binds_dom.
      auto with sets.
    auto.
  rewrite typ_subst_fresh.
    destruct k as [[kc kv kr kh]|]; try apply wk_any.
    simpl.
    eapply wk_kind.
      apply binds_prepend.
      use (binds_map (kind_subst S) B0). simpl in H; apply H.
    apply entails_refl.
  simpl.
  intro v; destruct* (v == Z).
  subst; left.
  use (binds_dom B0).
  rewrite dom_kinds_open_vars in H; auto.
  destruct* (fresh_disjoint _ _ _ Fr Z).
Qed.

Lemma typing_typ_well_subst : forall gc S K K' E t T,
  env_prop type S ->
  well_subst K K' S ->
  kenv_ok K' ->
  K ; E |gc|= t ~: T -> 
  K'; map (sch_subst S) E |gc|= t ~: (typ_subst S T).
Proof.
  introv TS WS HK' Typ.
  gen K'; induction Typ; intros.
  (* Var *)
  rewrite~ sch_subst_open. apply* typing_var.
  apply* proper_instance_well_subst.
  (* Abs *)
  simpl.
  apply_fresh* (@typing_abs gc) as y.
  replace (Sch (typ_subst S U) nil) with (sch_subst S (Sch U nil)) by auto.
  assert (y \notin L) by auto.
  use (H1 _ H2 _ WS HK').
  (* Let *)
  apply_fresh* (@typing_let gc (sch_subst S M)
    (L1 \u dom S \u fv_in typ_fv S \u sch_fv M \u dom K \u dom K')) as y.
    clear H1 H2. clear L2 T2 t2.
    simpl. intros Ys Fr.
    destruct M as [T Ks]. unfold sch_arity in *; simpl in *.
    rewrite map_length in Fr.
    assert (HK: kenv_ok (K & kinds_open_vars Ks Ys)).
      assert (fresh L1 (length Ks) Ys) by auto*.
      use (H _ H1).
    rewrite* <- sch_subst_open_vars.
    rewrite* <- kinds_subst_open_vars.
    apply* H0; clear H H0.
      apply* well_subst_extend.
    apply* kenv_ok_subst.
  replace (y ~ sch_subst S M) with (map (sch_subst S) (y ~ M)) by simpl*.
  rewrite <- map_concat.
  apply* H2.
  (* App *)
  simpl in IHTyp1; auto*.
  (* Cst *)
  rewrite* sch_subst_open.
  assert (disjoint (dom S) (sch_fv (Delta.type c))).
    intro x. rewrite* Delta.closed.
  rewrite* sch_subst_fresh.
  apply* typing_cst.
  rewrite* <- (sch_subst_fresh _ H2).
  apply* proper_instance_well_subst.
  (* GC *)
  apply* (@typing_gc gc (List.map (kind_subst S) Ks)
                     (L \u dom S \u dom K \u dom K')).
  rewrite map_length; intros.
  rewrite* <- kinds_subst_open_vars.
  apply* (H1 Xs); clear H1.
    apply* well_subst_extend.
  forward~ (H0 Xs); intro Typ.
  apply* (@kenv_ok_subst K' K).
Qed.

Lemma map_compose : forall (A:Set) (f f1 f2:A->A) E,
  (forall a, f1 (f2 a) = f a) ->
  map f1 (map f2 E) = map f E.
Proof.
  intros.
  induction* E.
  simpl. destruct a. simpl. rewrite H. rewrite* IHE.
Qed.

Lemma map_sch_subst_extend : forall S S0 E,
  extends S S0 ->
  map (sch_subst S) (map (sch_subst S0) E) = map (sch_subst S) E.
Proof.
  intros.
  apply map_compose.
  intros.
  destruct a as [T Ks]; unfold sch_subst; simpl.
  rewrite* (H T).
  apply (f_equal (Sch (typ_subst S T))).
  induction Ks; simpl*.
  rewrite IHKs.
  rewrite* (@kind_subst_combine S).
Qed.

Lemma kenv_ok_sch_kinds : forall K M Xs,
  kenv_ok K ->
  scheme M ->
  fresh (dom K) (sch_arity M) Xs ->
  kenv_ok (K & kinds_open_vars (sch_kinds M) Xs).
Proof.
  split.
    apply* disjoint_ok.
      unfold kinds_open_vars, kinds_open. apply* ok_combine_fresh.
    rewrite* dom_kinds_open_vars.
    disjoint_solve.
  apply env_prop_concat. apply (proj2 H).
  unfold kinds_open_vars, kinds_open.
  apply list_forall_env_prop.
  destruct* (H0 Xs).
  clear -H3; induction H3. simpl*.
  simpl; constructor; auto.
  unfold kind_open. unfold typ_open_vars in H3.
  apply* All_kind_types_map.
Qed.

Lemma math_ind : forall Q : nat -> Prop,
  (forall n, (forall m, m < n -> Q m) -> Q n) ->
  forall m, Q m.
Proof.
  intros.
  pose (n:= S m).
  assert (m < n). unfold n; omega.
  clearbody n.
  generalize dependent m.
  induction n; intros.
    elimtype False; omega.
  apply H.
  intros; apply IHn.
  omega.
Qed.

Lemma kind_subst_extend : forall S' S k,
  extends S' S -> kind_subst S' (kind_subst S k) = kind_subst S' k.
Proof.
  intros. apply* kind_subst_combine. 
Qed.

Lemma well_subst_compose : forall S S' K1 K2 K3,
  extends S' S ->
  well_subst K1 K2 S -> well_subst K2 K3 S' -> well_subst K1 K3 S'.
Proof.
  intros.
  intro; intros.
  use (H0 _ _ H2).
  inversions H3; clear H3.
    destruct k; try discriminate. simpl; apply wk_any.
  use (H1 _ _ H7).
  inversions* H3.
    destruct k0; try discriminate.
  fold (typ_subst S' (typ_fvar x)) in H9.
  rewrite H5 in H9.
  fold (typ_subst S (typ_fvar Z)) in H9.
  rewrite H in H9.
  rewrite <- H9.
  rewrite* <- (@kind_subst_extend S' S).
  rewrite <- H4.
  simpl. eapply wk_kind. apply H11.
  eapply entails_trans. apply H12.
  apply* kind_subst_entails.
Qed.

Definition soundness_spec h t K0 E T S0 K S gc :=
  typinf K0 E t T S0 h = Some (K, S) ->
  is_subst S0 -> env_prop type S0 ->
  kenv_ok K0 -> disjoint (dom S0) (dom K0) ->
  ok E -> env_prop scheme E -> type T ->
  extends S S0 /\ env_prop type S /\ is_subst S /\
  kenv_ok K /\ disjoint (dom S) (dom K) /\
  well_subst (map (kind_subst S0) K0) (map (kind_subst S) K) S /\
  map (kind_subst S) K; map (sch_subst S) E | gc |= t ~: typ_subst S T.
          
Lemma soundness_var : forall h v K0 E T S0 K S gc,
  soundness_spec (Datatypes.S h) (trm_fvar v) K0 E T S0 K S gc.
Proof.
  intros until gc; intros HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
  case_rewrite (get v E) R1.
  destruct (var_freshes (fvs S0 K0 E T) (sch_arity s)).
  simpl proj1_sig in HI.
  unfold unify in HI.
  assert (kenv_ok (K0 & kinds_open_vars (sch_kinds s) x)).
    apply* kenv_ok_sch_kinds. apply* (HSE v).
    unfold fvs in f; auto.
  destruct* (unify_kinds_ok _ _ HI HS0).
    unfold fvs in f. rewrite dom_concat. rewrite* dom_kinds_open_vars.
    disjoint_solve.
  poses Hext (typ_subst_extend _ _ _ HS0 HI).
  destruct* (unify_type _ _ HI).
    simpl; intros.
    destruct* H2.
    inversions H2; clear H2.
    split*.
    unfold sch_open_vars.
    refine (proj1 (HSE _ _ R1 x _)). auto.
  intuition.
      destruct* (unify_keep _ _ _ HI).
    intro; intros.
    apply H5.
    rewrite map_concat.
    apply* binds_concat_ok.
    rewrite <- map_concat.
    apply* ok_map0.
  rewrite <- (map_sch_subst_extend E Hext).
  use (unify_types _ _ _ HI HS0).
  rewrite* <- (H1 (sch_open_vars s x) T).
  rewrite* <- (typ_subst_extend _ _ _ HS0 HI).
  unfold fvs in f.
  rewrite* sch_subst_open_vars.
  apply* typing_typ_well_subst.
    apply* kenv_ok_map.
  unfold sch_open_vars, typ_open_vars.
  fold (sch_open (sch_subst S0 s) (typ_fvars x)).
  apply* typing_var.
    apply* kenv_ok_map.
  split.
    unfold sch_arity. simpl. rewrite map_length. fold (sch_arity s).
    rewrite (fresh_length _ _ _ f). apply types_typ_fvars.
  split. apply* sch_subst_type. apply (HSE _ _ R1).
  unfold kinds_open_vars, kinds_open.
  rewrite map_concat.
  rewrite map_combine.
  rewrite map_map.
  rewrite <- (map_ext (fun k => kind_open (kind_subst S0 k) (typ_fvars x))).
    rewrite <- (map_map (kind_subst S0) (fun k => kind_open k (typ_fvars x))).
    destruct s as [Ts Ks]; simpl.
    refine (well_kinded_combine _ _ x nil _).
    rewrite dom_map. rewrite map_length.
    unfold sch_arity, fvs in f; simpl in f; auto.
  intros. rewrite* kind_subst_open_vars.
Qed.

Lemma typing_abs_rename : forall x1 gc K E x2 M t T,
  x1 \notin trm_fv t ->
  x2 \notin dom E \u {{x1}} \u trm_fv t ->
  K; E & x1 ~ M |gc|= t ^ x1 ~: T -> K; E & x2 ~ M |gc|= t ^ x2 ~: T.
Proof.
  intros. replace (E & x2 ~ M) with (E & x2 ~ M & empty) by simpl*.
  replace (t ^ x2) with ([x1~>trm_fvar x2]t^x1).
  apply typing_rename. simpl*.
    assert (x2 \notin trm_fv (t ^ x1)).
      unfold trm_open.
      use (trm_fv_open (trm_fvar x1) t 0). apply (notin_subset H2).
      simpl*.
    simpl*.
  rewrite* trm_subst_open.
  rewrite* trm_subst_fresh.
  simpl. destruct* (x1 == x1).
Qed.

Lemma extends_trans : forall S1 S2 S3,
  extends S1 S2 -> extends S2 S3 -> extends S1 S3.
Proof.
  intros; intro.
  rewrite <- H. rewrite <- (H T).
  rewrite* H0.
Qed.

Lemma soundness_abs : forall h t K0 E T S0 K S gc,
  (forall t K0 E T S0 K S gc, soundness_spec h t K0 E T S0 K S gc) ->
  soundness_spec (Datatypes.S h) (trm_abs t) K0 E T S0 K S gc.
Proof.
  intros until gc; intros IHh  HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T)); simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T \u {{x}})); simpl in HI.
  destruct (var_fresh (dom E \u trm_fv t)); simpl in HI.
  case_rewrite (unify K0 (typ_arrow (typ_fvar x) (typ_fvar x0)) T S0) R1.
  destruct p as [K' S'].
  unfold unify in R1.
  destruct* (unify_keep _ _ _ R1) as [HS' _].
  destruct* (unify_type _ _ R1).
    simpl; intros. destruct* H.
    inversions* H.
  destruct* (unify_kinds_ok _ _ R1). clear H1; destruct H2.
  destruct* (IHh _ _ _ _ _ _ _ gc HI); clear IHh HI.
      apply* ok_cons.
    intro; intros.
    assert (binds x2 a (E & x1 ~ Sch (typ_fvar x) nil)) by apply H3.
    clear H3; binds_cases H4.
      apply* (HSE _ _ B).
    destruct (binds_single_inv B0). subst.
    intro; intros. unfold typ_open_vars. simpl*.
  intuition.
      apply* extends_trans.
      apply* typ_subst_extend.
    apply* well_subst_compose.
  use (unify_types _ _ _ R1 HS0).
  rewrite <- (H3 T).
  rewrite* <- (H9 (typ_arrow (typ_fvar x) (typ_fvar x0)) T).
  rewrite H3.
  simpl.
  simpl map in H10.
  fold (typ_subst S (typ_fvar x0)).
  fold (typ_subst S (typ_fvar x)).
  set (E' := map (sch_subst S) E) in *.
  apply* (@typing_abs gc (dom E' \u {{x1}} \u trm_fv t)).
  intros.
  apply typing_gc_raise.
  apply* (@typing_abs_rename x1).
Qed.

Lemma env_incl_subset_dom : forall (A:Set) (E1 E2:env A),
  env_incl E1 E2 -> dom E1 << dom E2.
Proof.
  intros; intros x Hx.
  case_eq (get x E1); intros.
    use (H _ _ H0).
    apply* binds_dom.
  use (get_none_notin _ H0).
Qed.

Lemma type_generalize : forall Bs Xs T,
  length Bs = length Xs ->
  type T ->
  type (typ_open_vars (generalize Bs T) Xs).
Proof.
  intros.
  unfold typ_open_vars, typ_fvars.
  induction H0; simpl.
    set (n := 0).
    assert (n + length Bs = length Xs) by auto.
    clear H; clearbody n.
    gen n; induction Bs; simpl; intros. auto.
    destruct (X == a). subst.
      simpl.
      clear IHBs.
      gen Xs; induction n; destruct Xs; simpl; intros; try discriminate; auto.
    apply IHBs. omega.
  auto.
Qed.

Lemma scheme_generalize : forall Bs Ks T,
  length Bs = length Ks ->
  type T -> list_forall (All_kind_types type) Ks ->
  scheme (Sch (generalize Bs T) (List.map (kind_map (generalize Bs)) Ks)).
Proof.
  intros.
  intro; simpl; intros.
  rewrite map_length in H2.
  rewrite H2 in H.
  split. apply* type_generalize.
  set (Ks' := Ks). fold Ks' in H1.
  clearbody Ks'.
  induction H1; simpl. auto.
  constructor; auto.
  apply All_kind_types_map.
  apply* All_kind_types_imp; intros.
  apply* type_generalize.
Qed.

Lemma close_fvk_incl : forall L K,
  L << close_fvk K L.
Proof.
  intros L K x Hx.
  unfold close_fvk.
  gen L. generalize (dom K).
  induction (length K); simpl; intros. auto.
  case_eq (S.choose (S.inter v L)); introv R1; auto.
  case_eq (get e K); introv R2; auto.
  apply* IHn. auto with sets.
Qed.

Lemma soundness_let : forall h t1 t2 K0 E T S0 K S gc,
  (forall t K0 E T S0 K S gc, soundness_spec h t K0 E T S0 K S gc) ->
  soundness_spec (Datatypes.S h) (trm_let t1 t2) K0 E T S0 K S gc.
Proof.
  intros until gc; intros IHh  HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T)); simpl in HI.
  case_rewrite (typinf K0 E t1 (typ_fvar x) S0 h) R1. destruct p.
  fold (typ_subst s (typ_fvar x)) in HI.
  set (K' := map (kind_subst s) k) in *.
  case_rewrite (split_env
             (S.diff (close_fvk K' (typ_fv (typ_subst s (typ_fvar x))))
               (close_fvk K'
                 (env_fv (map (sch_subst s) E) \u vars_subst s (dom K0))))
           K') R2.
  case_rewrite (split e0) R3.
  destruct (var_fresh (dom E \u trm_fv t1 \u trm_fv t2)); simpl proj1_sig in HI.
  destruct* (IHh _ _ _ _ _ _ _ gc R1); clear R1.
  destruct H0 as [HTs [Hs [Hk [Disk [WS' Typ']]]]].
  assert (HK':kenv_ok K'). unfold K'; apply* kenv_ok_map.
  destruct* (split_env_ok _ R2) as [Ok [Dise [Se0 [Inc1 Inc2]]]].
  destruct* (IHh _ _ _ _ _ _ _ gc HI); clear IHh HI.
          split. destruct* (ok_concat_inv _ _ Ok).
          intro; intros.
          apply (proj2 HK' x1).
          apply* (Inc2 x1).
        use (env_incl_subset_dom Inc2).
        unfold K' in H0; rewrite dom_map in H0; rewrite dom_concat in H0.
        intro v; destruct* (Disk v).
        use (notin_subset H0 H1).
      apply* ok_cons.
    intro; intros.
    unfold binds in H0; simpl in H0.
    destruct (x1 == x0); subst.
      inversions H0; clear H0.
      fold (typ_subst s (typ_fvar x)).
      use (split_length_l e0).
      rewrite <- (split_length_r e0) in H0.
      rewrite R3 in H0; simpl in H0.
      apply* scheme_generalize.
      use (split_combine e0). rewrite R3 in H1.
      apply* env_prop_list_forall.
        rewrite H1.
        intro; intros.
        apply* (proj2 HK' x1).
      rewrite H1.
      destruct* (ok_concat_inv _ _ Ok).
    apply (HSE _ _ H0).
  intuition.
      apply* extends_trans.
    intro; intros.
    use (WS' _ _ H6).
    inversions H8.
      destruct k0; try discriminate; apply wk_any.
    fold (typ_subst s (typ_fvar Z)) in H10.
    rewrite* <- (kind_subst_combine S S s). rewrite <- H9.
    rewrite <- H0. rewrite <- H10.
    rewrite <- H9 in H8; rewrite <- H10 in H8.
    rewrite <- (map_compose (kind_subst s) (kind_subst s) (kind_subst s))
      in H12.
    destruct (binds_map_inv _ _ H12) as [k2 [Hk2 B]].
    use (Inc1 _ _ B).
    binds_cases H11.
      use (binds_map (kind_subst s) B0).
      use (H5 _ _ H11).
      rewrite Hk2 in H14.
      apply* kind_entails_well_kinded.
      simpl; apply* kind_subst_entails.
    use (S.diff_2 (Se0 _ (binds_dom B1))).
    use (notin_subset (close_fvk_incl _) H11).
    use (binds_dom H6).
    rewrite dom_map in H15.
Lemma vars_subst_in : forall v L S,
  v \in L -> typ_fv (typ_subst S (typ_fvar v)) << vars_subst S L.
Proof.
  intros.
  unfold vars_subst.
  use (S.elements_1 H).
  induction H0; intros x Hx.
    simpl. rewrite <- H0. auto with sets.
  simpl.
  use (IHInA _ Hx). auto with sets.
Qed.
    elim H14.
    apply S.union_3.
    apply* (vars_subst_in s H15).
    rewrite <- H10.
    simpl. auto with sets.
    intro; apply* kind_subst_idem.
  set (M := Sch (generalize l (typ_subst s (typ_fvar x)))
              (List.map (kind_map (generalize l)) l0)) in *.
  apply* (@typing_let gc (sch_subst S M) (dom K)).
    intros.

Theorem soundness : forall h t K0 E T S0 K S gc,
  soundness_spec h t K0 E T S0 K S gc.
Proof.
  induction h; destruct t; intros;
    intros HI HS0 HTS0 HK0 Dis HE HSE HT; try discriminate.
  apply* (soundness_var h).
  apply* (@soundness_abs h).

End Mk2.
End MkInfer.