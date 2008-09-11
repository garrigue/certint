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

  Lemma index_none_notin : forall x l n,
    index n x l = None -> ~In x l.
  Proof.
    induction l; simpl; intros. auto.
    destruct* (eq_dec x a). discriminate.
  Qed.

  Lemma index_ok : forall (B:Set) (f:A->B) (def:B) a l n,
    index 0 a l = Some n ->
    nth n (List.map f l) def = f a.
  Proof.
    intros.
    replace n with (n-0) by omega.
    apply (proj2 (A:= 0 <= n)).
    gen n; generalize 0.
    induction l; simpl; intros. discriminate.
    destruct (eq_dec a a0).
      subst.
      inversions H.
      split*.
      replace (n0 - n0) with 0 by omega.
      auto.
    destruct (IHl _ _ H).
    split. omega.
    case_eq (n0 - n); intros.
      elimtype False; omega.
    replace n2 with (n0 - S n) by omega.
    auto.
  Qed.
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

Definition moregen S0 S :=
  exists S1, forall T, typ_subst S T = typ_subst S1 (typ_subst S0 T).

Lemma extends_moregen : forall S S0,
  extends S S0 -> moregen S0 S.
Proof.
  intros.
  exists* S.
Qed.

Lemma moregen_extends : forall S S0,
  moregen S0 S -> is_subst S0 -> extends S S0.
Proof.
  intros; intro.
  destruct H as [S1 Heq].
  rewrite Heq.
  rewrite* typ_subst_idem.
Qed.

Definition unify K T1 T2 S :=
  unify (1 + size_pairs S K ((T1,T2)::nil)) ((T1,T2)::nil) K S.

Definition fvs S K E T :=
  dom S \u fv_in typ_fv S \u dom K \u fv_in kind_fv K \u env_fv E \u typ_fv T.

(** Variants looking up a kinding environment *)

Fixpoint close_fvars (n:nat)(K:kenv)(VK:vars)(Vs:vars) {struct n} : vars :=
  match n with
  | 0 => Vs
  | S n' =>
    match S.choose (S.inter VK Vs) with
    | None => Vs
    | Some x =>
      let VK' := S.remove x VK in
      let Vs' :=
        match get x K with
        | None => Vs
        | Some k => Vs \u kind_fv k
        end
      in close_fvars n' K VK' Vs'
    end
  end.
    
Definition close_fvk K := close_fvars (length K) K (dom K).

Fixpoint typ_generalize (Bs:list var) (T:typ) {struct T} : typ :=
  match T with
  | typ_bvar n =>
    typ_bvar (length Bs + n)
  | typ_fvar x =>
    match index eq_var_dec 0 x Bs with
    | None   => T
    | Some n => typ_bvar n
    end
  | typ_arrow T1 T2 =>
    typ_arrow (typ_generalize Bs T1) (typ_generalize Bs T2)
  end.

Definition sch_generalize Bs T Ks :=
  Sch (typ_generalize Bs T) (List.map (kind_map (typ_generalize Bs)) Ks).

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
      let (K'', KA) := split_env ftve K' in
      let T1 := typ_subst S' V in
      let B := close_fvk K' (typ_fv T1) in
      let (_, KB) := split_env B K'' in
      let (Bs, Ks) := split KB in
      let x := proj1_sig (var_fresh (dom E \u trm_fv t1 \u trm_fv t2)) in
      typinf KA (E & x ~ sch_generalize Bs T1 Ks) (t2 ^ x) T S' h'
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
  binds_cases H1. auto*.
  destruct (binds_map_inv _ _ B0) as [T [Eq B']].
  subst.
  apply* typ_subst_type.
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
  kenv_ok K' /\ env_prop type S' /\ is_subst S'.
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
  ok (EB & Eb) /\ disjoint B (dom Eb) /\ dom EB << B /\
  env_incl E (EB & Eb) /\ env_incl (EB & Eb) E.
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
    case_eq (get v (e0 & Eb)); intros.
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
    use (I1 _ _ B0). binds_cases H1; auto*.
  inversions H; clear H.
  inversions H0; clear H0.
  destruct* (IHE e EB) as [Hok [Dis [Dom [I1 I2]]]]; clear IHE.
  destruct (ok_concat_inv _ _ Hok).
  case_eq (get v (EB & e)); intros.
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

Definition Gc := (false, GcLet).

Definition soundness_spec h t K0 E T S0 K S :=
  typinf K0 E t T S0 h = Some (K, S) ->
  is_subst S0 -> env_prop type S0 ->
  kenv_ok K0 -> disjoint (dom S0) (dom K0) ->
  ok E -> env_prop scheme E -> type T ->
  extends S S0 /\ env_prop type S /\ is_subst S /\
  kenv_ok K /\ disjoint (dom S) (dom K) /\
  well_subst (map (kind_subst S0) K0) (map (kind_subst S) K) S /\
  map (kind_subst S) K; map (sch_subst S) E |Gc|= t ~: typ_subst S T.
          
Lemma soundness_ind : forall h t K0 E T S0 K S s x,
  scheme s ->
  fresh (fvs S0 K0 E T) (sch_arity s) x ->
  unify (K0 & kinds_open_vars (sch_kinds s) x) (sch_open_vars s x) T S0 =
    Some (K, S) ->
  (kenv_ok (K0 & kinds_open_vars (sch_kinds s) x) ->
   extends S S0 -> kenv_ok K ->
   unifies S ((sch_open_vars s x, T) :: nil) ->
   map (kind_subst S0) (K0 & kinds_open_vars (sch_kinds s) x);
   map (sch_subst S0) E |Gc|= t ~: sch_subst S0 s ^^ typ_fvars x) ->
  soundness_spec h t K0 E T S0 K S.
Proof.
  intros until x; intros Hs f HI Typ _ HS0 HTS0 HK0 Dis HE HSE HT.
  unfold unify in HI.
  assert (kenv_ok (K0 & kinds_open_vars (sch_kinds s) x)).
    apply* kenv_ok_sch_kinds.
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
    destruct* (Hs x).
  intuition.
      destruct* (unify_keep _ _ _ HI).
    intro; intros.
    apply H7.
    rewrite map_concat.
    apply* binds_concat_ok.
    rewrite <- map_concat.
    apply* ok_map0.
  rewrite <- (map_sch_subst_extend E Hext).
  use (unify_types _ _ _ HI HS0).
  rewrite* <- (H8 (sch_open_vars s x) T).
  rewrite* <- Hext.
  unfold fvs in f.
  rewrite* sch_subst_open_vars.
  apply* typing_typ_well_subst.
  apply* kenv_ok_map.
Qed.

Lemma well_kinded_open_vars : forall S K Ks Xs,
  fresh (dom S \u dom K) (length Ks) Xs ->
  env_prop type S ->
  For_all2
     (well_kinded (map (kind_subst S) (K & kinds_open_vars Ks Xs)))
     (kinds_open (List.map (kind_subst S) Ks) (typ_fvars Xs))
     (typ_fvars Xs).
Proof.
  unfold kinds_open_vars, kinds_open; intros.
  rewrite map_concat.
  rewrite map_combine.
  rewrite map_map.
  rewrite <- (map_ext (fun k => kind_open (kind_subst S k) (typ_fvars Xs))).
    rewrite <- (map_map (kind_subst S) (fun k => kind_open k (typ_fvars Xs))).
    refine (well_kinded_combine _ _ Xs nil _).
    rewrite dom_map.
    rewrite* map_length.
  intros. rewrite* kind_subst_open_vars.
Qed.

Lemma soundness_var : forall h v K0 E T S0 K S,
  soundness_spec (Datatypes.S h) (trm_fvar v) K0 E T S0 K S.
Proof.
  intros; intros HI HS0 HTS0 HK0 Dis HE HSE HT.
  poses HI' HI; simpl in HI.
  case_rewrite (get v E) R1.
  destruct (var_freshes (fvs S0 K0 E T) (sch_arity s)).
  unfold fvs in f.
  simpl proj1_sig in HI.
  refine (soundness_ind _ _ _ _ HI _ HI' _ _ _ _ _ _ _); auto.
    apply (HSE _ _ R1).
  intros.
  apply* typing_var.
    apply* kenv_ok_map.
  split.
    unfold sch_arity. simpl. rewrite map_length. fold (sch_arity s).
    rewrite (fresh_length _ _ _ f). apply types_typ_fvars.
  split. apply* sch_subst_type. apply (HSE _ _ R1).
  destruct s as [Ts Ks]; simpl.
  apply* well_kinded_open_vars.
Qed.

Lemma kinds_subst_cst : forall S c,
  List.map (kind_subst S) (sch_kinds (Delta.type c)) = sch_kinds (Delta.type c).
Proof.
  intros.
  assert (forall x, x \notin kind_fv_list (sch_kinds (Delta.type c))).
    intros x Hx.
    assert (x \in sch_fv (Delta.type c)).
      unfold sch_fv.
      auto with sets.
    rewrite Delta.closed in H.
    elim (in_empty H).
  induction (sch_kinds (Delta.type c)). auto.
  simpl in *.
  rewrite* IHl.
    rewrite* kind_subst_fresh.
    intro. use (H x).
  intro; use (H x).
Qed.

Lemma soundness_cst : forall h c K0 E T S0 K S,
  soundness_spec (Datatypes.S h) (trm_cst c) K0 E T S0 K S.
Proof.
  intros; intros HI HS0 HTS0 HK0 Dis HE HSE HT.
  poses HI' HI; simpl in HI.
  destruct (var_freshes (fvs S0 K0 E T) (sch_arity (Delta.type c)));
    simpl in HI.
  refine (soundness_ind _ _ _ _ HI _ HI' _ _ _ _ _ _ _); auto.
    apply Delta.scheme.
  intros.
  rewrite sch_subst_fresh; try (rewrite Delta.closed; intro; auto).
  apply* typing_cst.
    apply* kenv_ok_map.
  split.
    rewrite (fresh_length _ _ _ f). apply types_typ_fvars.
  split. apply Delta.scheme.
  pattern (sch_kinds (Delta.type c)) at 2.
  rewrite <- (kinds_subst_cst S0 c).
  unfold fvs, sch_arity in f.
  apply* well_kinded_open_vars.
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

Lemma soundness_abs : forall h t K0 E T S0 S K,
  (forall t K0 E T S0 K S, soundness_spec h t K0 E T S0 K S) ->
  soundness_spec (Datatypes.S h) (trm_abs t) K0 E T S0 K S.
Proof.
  intros until K; intros IHh  HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
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
  destruct* (IHh _ _ _ _ _ _ _ HI); clear IHh HI.
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
  rewrite* <- (H11 (typ_arrow (typ_fvar x) (typ_fvar x0)) T).
  rewrite H3.
  simpl.
  simpl map in H11.
  fold (typ_subst S (typ_fvar x0)).
  fold (typ_subst S (typ_fvar x)).
  set (E' := map (sch_subst S) E) in *.
  apply* (@typing_abs Gc (dom E' \u {{x1}} \u trm_fv t)).
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

Lemma typ_generalize_reopen : forall Xs T,
  type T -> typ_open (typ_generalize Xs T) (typ_fvars Xs) = T.
Proof.
  induction 1; simpl.
    case_eq (index eq_var_dec 0 X Xs); simpl; intros.
      unfold typ_fvars.
      apply* index_ok.
    auto.
  congruence.
Qed.

Lemma kind_generalize_reopen : forall Xs k,
  All_kind_types type k ->
  kind_open (kind_map (typ_generalize Xs) k) (typ_fvars Xs) = k.
Proof.
  unfold All_kind_types.
  intros; destruct k as [[kc kv kr kh]|]; simpl in *; auto.
  apply kind_pi; simpl*.
  clear kh; induction kr; simpl*.
  destruct a. simpl in *.
  rewrite* typ_generalize_reopen. rewrite* IHkr.
Qed.

Lemma kinds_generalize_reopen : forall Xs Ks,
  list_forall (All_kind_types type) Ks ->
  kinds_open_vars (List.map (kind_map (typ_generalize Xs)) Ks) Xs =
  combine Xs Ks.
Proof.
  unfold kinds_open_vars, kinds_open; intros.
  apply (f_equal (combine (B:=kind) Xs)).
  induction H; simpl. auto.
  rewrite* kind_generalize_reopen.
  congruence.
Qed.

Lemma type_generalize : forall Bs Xs T,
  length Bs = length Xs ->
  type T ->
  type (typ_open_vars (typ_generalize Bs T) Xs).
Proof.
  intros.
  apply* (typ_open_vars_type Bs).
  unfold typ_open_vars.
  rewrite* typ_generalize_reopen.
Qed.

Lemma scheme_generalize : forall Bs Ks T,
  length Bs = length Ks ->
  type T -> list_forall (All_kind_types type) Ks ->
  scheme (sch_generalize Bs T Ks).
Proof.
  intros.
  intro; simpl; intros.
  rewrite map_length in H2.
  rewrite H2 in H.
  split. apply* type_generalize.
  apply* list_forall_map; intros.
  apply All_kind_types_map.
  apply* All_kind_types_imp; intros.
  apply* type_generalize.
Qed.

Lemma close_fvars_subset : forall K n DK L,
  L << close_fvars n K DK L.
Proof.
  induction n; intros; simpl; intros x Hx. auto.
  case_eq (S.choose (S.inter DK L)); introv R1; auto.
  case_eq (get e K); introv R2; apply* IHn; auto with sets.
Qed.

Lemma close_fvk_subset : forall L K, L << close_fvk K L.
Proof.
  intros. unfold close_fvk. apply close_fvars_subset.
Qed.

Require Import Cardinal.

Lemma cardinal_empty : S.cardinal {} = 0.
Proof.
  rewrite S.cardinal_1.
  case_eq (S.elements {}); intros. simpl*.
  assert (In e (e::l)) by auto.
  rewrite <- H in H0.
  assert (e \in {}). auto with sets.
  elim (in_empty H1).
Qed.

Lemma cardinal_env : forall (A:Set) (K:env A),
  ok K -> S.cardinal (dom K) = length K.
Proof.
  induction 1; simpl. apply cardinal_empty.
  rewrite <- (@cardinal_remove x).
    rewrite remove_union.
    assert (S.remove x {{x}} = {}).
      apply eq_ext; intros; split; intros.
        use (S.remove_3 H1).
        elim (S.remove_1 (S.singleton_1 H2) H1).
      elim (in_empty H1).
    rewrite H1. rewrite* remove_notin.
    rewrite* union_empty_l.
  auto with sets.
Qed.

Lemma cardinal_0 : forall L,
  S.cardinal L = 0 -> L = {}.
Proof.
  intros.
  rewrite S.cardinal_1 in H.
  case_rewrite (S.elements L) R1.
  apply eq_ext; intros; split; intro; intros.
    use (S.elements_1 H0).
    rewrite R1 in H1.
    inversion H1.
  elim (in_empty H0).
Qed.

Lemma close_fvk_ok : forall K L x k,
  ok K -> x \in close_fvk K L -> binds x k K -> kind_fv k << close_fvk K L.
Proof.
  intros.
  unfold close_fvk in *.
  use (cardinal_env H).
  use (binds_dom H1).
  revert L H0 H2 H3; generalize (dom K).
  induction (length K); simpl; intros.
    rewrite (cardinal_0 H2) in *. elim (in_empty H3).
  case_rewrite (S.choose (S.inter v L)) R1.
    use (S.choose_1 R1).
    destruct (x == e).
      subst.
      rewrite H1 in *.
      intros x Hx.
      apply close_fvars_subset. auto with sets.
    assert (forall L', x \in close_fvars n K (S.remove e v) L' ->
               kind_fv k << close_fvars n K (S.remove e v) L').
      intros; apply* IHn.
        rewrite <- (@cardinal_remove e) in H2; auto.
        eauto with sets.
      apply* S.remove_2.
    case_rewrite (get e K) R2; intros; auto.
  use (S.choose_2 R1).
  elim (H4 x).
  auto with sets.
Qed.


Lemma split_length : forall (A B:Set) l (l1:list A) (l2:list B),
  split l = (l1, l2) -> length l1 = length l2.
Proof.
  intros.
  use (split_length_l l).
  rewrite <- (split_length_r l) in H0.
  rewrite H in H0; apply H0.
Qed.

Hint Resolve split_length.

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

Lemma sch_arity_subst : forall M S,
  sch_arity (sch_subst S M) = sch_arity M.
Proof.
  destruct M as [T Ks]; unfold sch_arity. simpl.
  intro; rewrite* map_length.
Qed.

Hint Resolve kind_subst_idem.

Lemma disjoint_subset : forall L1 L2 L3,
  L1 << L2 -> disjoint L2 L3 -> disjoint L1 L3.
Proof.
  intros. disjoint_solve. auto.
Qed.

Lemma well_subst_let_inf : forall S0 K0 s k e e0 S K L,
  extends S s -> is_subst s ->
  well_subst (map (kind_subst S0) K0) (map (kind_subst s) k) s ->
  well_subst (map (kind_subst s) e0) (map (kind_subst S) K) S ->
  let K' := map (kind_subst s) k in
  env_incl K' (e0 & e) ->
  disjoint (close_fvk K' (L \u vars_subst s (dom K0))) (dom e) ->
  well_subst (map (kind_subst S0) K0) (map (kind_subst S) K) S.
Proof.
  intros until L; intros Hext Hs WS WS' K' Inc1 Dise; intro; intros.
  use (WS _ _ H).
  inversions H0.
    destruct k0; try discriminate; apply wk_any.
  fold (typ_subst s (typ_fvar Z)) in H2.
  rewrite* <- (kind_subst_combine S S s). rewrite <- H1.
  rewrite <- Hext. rewrite <- H2.
  rewrite <- H1 in H0; rewrite <- H2 in H0.
  rewrite <- (map_compose (kind_subst s) (kind_subst s) (kind_subst s))
    in H4; auto*.
  destruct (binds_map_inv _ _ H4) as [k2 [Hk2 B]].
  use (Inc1 _ _ B).
  binds_cases H3.
    use (binds_map (kind_subst s) B0).
    use (WS' _ _ H3).
    rewrite Hk2 in H6.
    apply* kind_entails_well_kinded.
    simpl; apply* kind_subst_entails.
  use (binds_dom B1).
  destruct* (Dise x).
  use (notin_subset (close_fvk_subset _) H6).
  use (binds_dom H).
  rewrite dom_map in H8.
  elim H7; clear H6 H7.
  apply S.union_3.
  apply* (vars_subst_in s H8).
  rewrite <- H2.
  simpl. auto with sets.
Qed.

Lemma in_ok_binds : forall (A:Set) x (a:A) E,
  In (x,a) E -> ok E -> binds x a E.
Proof.
  intros.
  unfold binds.
  induction H0. elim H.
  simpl.
  simpl in H; destruct H.
    inversions H.
    destruct* (x == x).
  destruct* (x == x0).
  subst.
  elim (binds_fresh (IHok H) H1).
Qed.

Lemma mkset_notin : forall x l, ~In x l -> x \notin mkset l.
Proof.
  induction l; simpl; intros. auto.
  intuition.
  destruct* (S.union_1 H0).
  elim H1; rewrite* (S.singleton_1 H3).
Qed.
Hint Resolve mkset_notin.

Lemma typ_generalize_disjoint : forall Bs T,
  disjoint (typ_fv (typ_generalize Bs T)) (mkset Bs).
Proof.
  induction T; simpl. intro; auto.
    case_eq (index eq_var_dec 0 v Bs); simpl; intros.
      intro; auto.
    use (index_none_notin _ _ _ _ H).
  disjoint_solve.
Qed.

Lemma kinds_generalize_disjoint : forall Bs Ks,
  disjoint (kind_fv_list (List.map (kind_map (typ_generalize Bs)) Ks))
    (mkset Bs).
Proof.
  intros. unfold kind_fv_list.
  induction Ks; simpl. intro; auto.
  apply* disjoint_union.
  unfold kind_fv.
  clear IHKs Ks; destruct a as [[kc kv kr kh]|]; simpl.
    clear kh; induction kr; simpl. intro; auto.
    apply* disjoint_union.
    apply typ_generalize_disjoint.
  intro; auto.
Qed.

Lemma sch_generalize_disjoint : forall Bs T Ks,
  disjoint (sch_fv (sch_generalize Bs T Ks)) (mkset Bs).
Proof.
  intros.
  unfold sch_generalize, sch_fv; simpl.
  apply disjoint_union. apply typ_generalize_disjoint.
  apply kinds_generalize_disjoint.
Qed.

Lemma typing_let_disjoint : forall k EK0 e e0 s,
  let K' := map (kind_subst s) k in
  ok (e0 & e) -> is_subst s ->
  ok K' -> env_incl (e0 & e) K' ->
  disjoint (close_fvk K' EK0) (dom e) ->
  dom e0 << close_fvk K' EK0 ->
  disjoint (dom e) (EK0 \u dom (map (kind_subst s) e0)
                    \u fv_in kind_fv (map (kind_subst s) e0)).
Proof.
  intros until K'; intros Ok Hs HK' Inc2 Dise Se0.
  apply disjoint_comm.
  repeat apply disjoint_union.
  (* env_fv E *)
  apply* disjoint_subset. apply close_fvk_subset.
  (* dom e0 *)
  rewrite dom_map.
  apply* ok_disjoint.
  (* fv_in kind_fv (map (kind_subst s) e0) *)
  refine (disjoint_subset (proj2 (fv_in_subset_inv _ _ _) _) Dise).
  intros.
  destruct (ok_concat_inv _ _ Ok).
  use (in_ok_binds _ _ H (ok_map0 (kind_subst s) H0)).
  apply* close_fvk_ok.
    instantiate (1 := x).
    use (binds_dom H2). rewrite dom_map in H3.
    apply* Se0.
  unfold K'.
  rewrite <- (map_compose _ _ _ k (fun k => kind_subst_idem k Hs)).
  destruct (binds_map_inv _ _ H2) as [b [Hb B]]. subst a.
  apply binds_map.
  apply* Inc2.
Qed.

Lemma typing_let_fresh : forall x l l0 k e e0 e1 e2 s fvE sK0,
  let K' := map (kind_subst s) k in
  let M := sch_generalize l (typ_subst s (typ_fvar x)) l0 in
  split e2 = (l, l0) ->
  ok (e0 & e) -> ok (e2 & e1) -> is_subst s ->
  ok K' -> env_incl (e0 & e) K' -> env_incl (e2 & e1) e ->
  disjoint (close_fvk K' (fvE \u sK0)) (dom e) ->
  dom e0 << close_fvk K' (fvE \u sK0) ->
  fresh
    (fvE \u sch_fv M \u dom (map (kind_subst s) e0) \u
     fv_in kind_fv (map (kind_subst s) e0)) (sch_arity M) l.
Proof.
  intros until M. intros R4 Ok Ok' Hs HK' Inc2 Inc4 Dise Se0.
  unfold sch_arity; simpl length.
  rewrite map_length.
  rewrite <- (split_length _ R4).
  use (split_combine e2). rewrite R4 in H.
  apply* (ok_fresh l l0).
    rewrite H. destruct* (ok_concat_inv _ _ Ok').
  rewrite* <- (dom_combine l l0).
  rewrite H.
  use (env_incl_subset_dom Inc4).
  rewrite dom_concat in H0.
  assert (dom e2 << dom e).
    intros v Hv. apply* (H0 v). auto with sets.
  use (disjoint_subset H1
          (typing_let_disjoint _ _ _ _ Ok Hs HK' Inc2 Dise Se0)).
  assert (disjoint (sch_fv M) (dom e2)).
    unfold M.
    rewrite <- H.
    rewrite* dom_combine.
    apply sch_generalize_disjoint.
  disjoint_solve.
Qed.

Lemma typing_let_fresh_2 : forall l1 l2 s k T fvE sK0 e e0 e1 e2,
  let K' := map (kind_subst s) k in
  let Ks := List.map (kind_map (typ_generalize l1)) l2 in
  let M' := Sch T Ks in
  is_subst s -> kenv_ok K' ->  ok (e0 & e) -> ok (e2 & e1) ->
  env_incl (e0 & e) K' -> env_incl (e2 & e1) e ->
  split e1 = (l1, l2) ->
  disjoint (close_fvk K' (fvE \u sK0)) (dom e) ->
  dom e0 << close_fvk K' (fvE \u sK0) ->
  disjoint (close_fvk K' (typ_fv T)) (dom e1) ->
  dom e2 << close_fvk K' (typ_fv T) ->
  fresh
    (fvE \u sch_fv M' \u dom (map (kind_subst s) e0 & e2) \u
     fv_in kind_fv (map (kind_subst s) e0 & e2)) (sch_arity M') l1.
Proof.
  intros until M'.
  intros Hs HK' Ok Ok' Inc2 Inc4 R5 Dise Se0 Dise1 Se2.
  rewrite dom_concat; rewrite fv_in_concat.
  unfold sch_arity; simpl length.
  unfold Ks; rewrite map_length.
  rewrite <- (split_length _ R5).
  poses He1 (split_combine e1). rewrite R5 in He1.
  apply* (ok_fresh l1 l2).
    rewrite* He1. destruct* (ok_concat_inv _ _ Ok').
  rewrite* <- (dom_combine l1 l2).
  rewrite He1.
  use (env_incl_subset_dom Inc4).
  rewrite dom_concat in H.
  assert (dom e1 << dom e).
    intros v Hv. apply* (H v). auto with sets.
  use (disjoint_subset H0
         (typing_let_disjoint _ _ _ _ Ok Hs (proj1 HK') Inc2 Dise Se0)).
  apply disjoint_comm.
  repeat apply disjoint_union; try solve [disjoint_solve].
  (* sch_fv M' *)
  unfold sch_fv; simpl.
  apply disjoint_union.
    apply* disjoint_subset. apply close_fvk_subset.
  unfold Ks.
  rewrite <- He1. rewrite* dom_combine.
  apply kinds_generalize_disjoint.
  (* e2 *)
  refine (disjoint_subset (proj2 (fv_in_subset_inv _ _ _) _) Dise1).
  intros.
  destruct (ok_concat_inv _ _ Ok').
  use (in_ok_binds _ _ H2 H3).
  apply* close_fvk_ok.
  apply Se2.
  apply* binds_dom.
Qed.

Lemma sch_open_extra : forall Ks Xs T,
  type T -> sch_open_vars (Sch T Ks) Xs = T.
Proof.
  unfold sch_open_vars, typ_open_vars; simpl; intros.
  rewrite* <- typ_open_type.
Qed.

Lemma typing_let_incl : forall s k e e0 e1 e2,
  let ss := map (kind_subst s) in
  is_subst s ->
  ok (e0 & e) -> ok (e2 & e1) ->
  env_incl (ss k) (e0 & e) ->
  env_incl (e0 & e) (ss k) ->
  env_incl e (e2 & e1) ->
  env_incl (e2 & e1) e ->
  env_incl (ss k) (ss e0 & e2 & e1) /\ env_incl (ss e0 & e2 & e1) (ss k).
Proof.
  intros until ss; intros Hs Ok Ok' I1 I2 I3 I4.
  rewrite concat_assoc.
  set (e' := e2 & e1) in *.
  split; intro; intros.
    use (I1 _ _ H).
    binds_cases H0.
      apply binds_concat_fresh.
        destruct (binds_map_inv _ _ H) as [k1 [Hk1 Bk1]].
        subst.
        use (binds_map (kind_subst s) B).
        rewrite kind_subst_idem in H0; auto.
      eapply notin_subset. apply (env_incl_subset_dom I4). auto.
    use (I3 _ _ B0).
  clearbody e'.
  binds_cases H.
    unfold ss.
    rewrite* <- (map_compose (kind_subst s) (kind_subst s) (kind_subst s)).
    apply (env_incl_map (kind_subst s) I2).
    rewrite map_concat.
    apply* binds_concat_fresh.
    rewrite dom_map. eapply notin_subset.
    apply (env_incl_subset_dom I3). auto.
  auto.
Qed.

Lemma soundness_let : forall h t1 t2 K0 E T S0 S K,
  (forall t K0 E T S0 K S, soundness_spec h t K0 E T S0 K S) ->
  soundness_spec (Datatypes.S h) (trm_let t1 t2) K0 E T S0 K S.
Proof.
  intros until K; intros IHh  HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T)); simpl in HI.
  case_rewrite (typinf K0 E t1 (typ_fvar x) S0 h) R1. destruct p.
  fold (typ_subst s (typ_fvar x)) in HI.
  set (K' := map (kind_subst s) k) in *.
  set (T1 := typ_subst s (typ_fvar x)) in *.
  case_rewrite (split_env (close_fvk K'
    (env_fv (map (sch_subst s) E) \u vars_subst s (dom K0))) K') R2.
  case_rewrite (split_env (close_fvk K' (typ_fv T1)) e) R3.
  case_rewrite (split e2) R4.
  destruct (var_fresh (dom E \u trm_fv t1 \u trm_fv t2)); simpl proj1_sig in HI.
  set (M := sch_generalize l T1 l0) in *.
  destruct* (IHh _ _ _ _ _ _ _ R1); clear R1.
  destruct H0 as [HTs [Hs [Hk [Disk [WS' Typ']]]]].
  assert (HT1: type T1) by (unfold T1; auto*).
  assert (HK':kenv_ok K') by (unfold K'; apply* kenv_ok_map).
  destruct* (split_env_ok _ R2) as [Ok [Dise [Se0 [Inc1 Inc2]]]].
  destruct* (split_env_ok _ R3) as [Ok' [Dise' [Se2 [Inc3 Inc4]]]].
    destruct* (ok_concat_inv _ _ Ok).
  poses He2 (split_combine e2). rewrite R4 in He2.
  assert (Oke0: ok e0) by destruct* (ok_concat_inv _ _ Ok).
  assert (Oke2: ok e2) by destruct* (ok_concat_inv _ _ Ok').
  assert (HM: scheme M).
    unfold M.
    apply* scheme_generalize.
    apply* env_prop_list_forall.
      rewrite He2.
      intro; intros.
      apply* (proj2 HK' x1).
    rewrite* He2.
  destruct* (IHh _ _ _ _ _ _ _ HI); clear IHh HI.
          split*.
          intro; destruct* HK'.
        use (env_incl_subset_dom Inc2).
        unfold K' in H0; rewrite dom_map in H0; rewrite dom_concat in H0.
        intro v; destruct* (Disk v).
        use (notin_subset H0 H1).
      apply* ok_cons.
    intro; intros.
    unfold binds in H0; simpl in H0.
    destruct (x1 == x0); subst.
      inversions* H0.
    apply (HSE _ _ H0).
  intuition.
      apply* extends_trans.
    apply* well_subst_let_inf.
  apply* (@typing_let Gc (sch_subst S M)
             (dom S \u dom K \u dom e0 \u mkset l)).
    intros.
    unfold M; simpl.
    rewrite* <- kinds_subst_open_vars.
    rewrite* <- sch_subst_open_vars.
    fold M.
    replace (List.map (kind_map (typ_generalize l)) l0) with (sch_kinds M)
      by simpl*.
    rewrite sch_arity_subst in H6.
    rewrite <- (map_sch_subst_extend E H0).
    apply* typing_typ_well_subst.
        apply (well_subst_extend (sch_kinds M) Xs H2 H5).
        rewrite* dom_map.
      rewrite <- map_concat.
      apply* kenv_ok_map.
      apply* kenv_ok_sch_kinds.
    assert (AryM: sch_arity M = length l).
      unfold sch_arity; simpl.
      rewrite map_length.
      rewrite* (split_length _ R4).
    apply* typing_rename_typ.
        apply* (@typing_let_fresh x l l0 k e e0 e1 e2 s).
      rewrite dom_map.
      rewrite* <- AryM.
    unfold M.
    use (split_combine e2). rewrite R4 in H8.
    assert (list_forall (All_kind_types type) l0).
      apply* env_prop_list_forall.
        rewrite H8. intro; intros. apply* (proj2 HK' x1).
      rewrite* H8.
    unfold sch_open_vars, typ_open_vars. simpl sch_type.
    rewrite* typ_generalize_reopen.
    unfold sch_generalize. simpl sch_kinds.
    rewrite* kinds_generalize_reopen. rewrite H8. clear H9.
    poses He1 (split_combine e1). case_rewrite (split e1) R5.
    pose (Ks := List.map (kind_map (typ_generalize l1)) l2).
    apply* (@typing_gc (true,GcLet) Ks). simpl*.
    poses Typ (typing_gc_raise Typ'). clear Typ'.
    intros.
    pose (M' := Sch T1 Ks).
    rewrite* <- (@sch_open_extra Ks Xs0). fold M'.
    replace Ks with (sch_kinds M') by simpl*.
    apply* typing_rename_typ.
        instantiate (1 := l1).
        unfold M', Ks.
        unfold K' in HK'.
        apply* typing_let_fresh_2.
      unfold Ks in H9. rewrite map_length in H9.
      rewrite* (split_length _ R5).
    assert (list_forall (All_kind_types type) l2).
      apply* env_prop_list_forall.
        rewrite He1. intro; intros. apply* (proj2 HK' x1).
      rewrite* He1. destruct* (ok_concat_inv _ _ Ok').
    simpl sch_kinds.
    unfold Ks; rewrite* kinds_generalize_reopen. rewrite He1; clear H10.
    unfold sch_open_vars, typ_open_vars.
    simpl sch_type. rewrite* <- typ_open_type.
    destruct* (typing_let_incl _ _ _ _ Hs Ok Ok' Inc1 Inc2 Inc3 Inc4).
    unfold T1; apply* typing_kenv_incl.
    split.
      rewrite concat_assoc.
      apply* disjoint_ok.
      rewrite dom_map.
      apply disjoint_comm.
      eapply disjoint_subset. apply (env_incl_subset_dom Inc4).
      apply disjoint_comm. apply* ok_disjoint.
    intro; intros. apply* (proj2 (proj1 (typing_regular Typ)) x1).
  intros.
  instantiate (1 := dom E \u trm_fv t2 \u {{x0}}) in H6.
  apply typing_gc_raise.
  apply* (@typing_abs_rename x0).
  rewrite* dom_map.
Qed.

Lemma soundness_app : forall h t1 t2 K0 E T S0 S K,
  (forall t K0 E T S0 K S, soundness_spec h t K0 E T S0 K S) ->
  soundness_spec (Datatypes.S h) (trm_app t1 t2) K0 E T S0 K S.
Proof.
  intros until K; intros IHh HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T)); simpl in HI.
  case_rewrite (typinf K0 E t1 (typ_arrow (typ_fvar x) T) S0 h) R1.
  destruct p as [K' S'].
  destruct* (IHh _ _ _ _ _ _ _ R1); clear R1.
  destruct* (IHh _ _ _ _ _ _ _ HI); clear IHh HI.
  intuition.
      apply* extends_trans.
    apply* well_subst_compose.
  remember (typ_fvar x) as T1.
  apply* typing_app.
  use (typing_typ_well_subst H0 H10 (kenv_ok_map H6 H0) H12).
  rewrite (map_sch_subst_extend E H1) in H11.
  rewrite H1 in H11.
  apply H11.
Qed.

Theorem typinf_sound : forall h t K0 E T S0 K S,
  soundness_spec h t K0 E T S0 K S.
Proof.
  induction h; destruct t; intros;
    intros HI HS0 HTS0 HK0 Dis HE HSE HT; try discriminate.
  apply* (soundness_var h).
  apply* (@soundness_abs h).
  apply* (@soundness_let h).
  apply* (@soundness_app h).
  apply* (soundness_cst h).
Qed.

Lemma typ_subst_concat_fresh : forall S1 S2 T,
  disjoint (dom S2) (typ_fv T) ->
  typ_subst (S1 & S2) T = typ_subst S1 T.
Proof.
  induction T; simpl; intros. auto.
    case_eq (get v S1); intros.
      rewrite* (binds_concat_fresh S2 H0).
    rewrite* get_notin_dom.
    use (get_none_notin _ H0).
    rewrite dom_concat.
    destruct* (H v).
  rewrite IHT1; try rewrite* IHT2; intro x; destruct* (H x).
Qed.

Lemma typ_subst_combine_fresh : forall S T Xs Us,
  fresh (typ_fv T) (length Us) Xs ->
  typ_subst (S & combine Xs Us) T = typ_subst S T.
Proof.
  intros.
  rewrite* typ_subst_concat_fresh.
  rewrite dom_combine.
    apply* (fresh_disjoint (length Us)).
  symmetry; auto.
Qed.

Lemma diff_union_l : forall L1 L2 L3,
  S.diff (L1 \u L2) L3 = S.diff L1 L3 \u S.diff L2 L3.
Proof.
  intros.
  apply eq_ext; intro; split; intros.
    use (S.diff_1 H); use (S.diff_2 H).
    destruct (S.union_1 H0); auto with sets.
  destruct (S.union_1 H); use (S.diff_1 H0); use (S.diff_2 H0); auto with sets.
Qed.

Lemma typ_fv_subst : forall S T,
  typ_fv (typ_subst S T) << S.diff (typ_fv T) (dom S) \u fv_in typ_fv S.
Proof.
  induction T; simpl; intros x Hx. elim (in_empty Hx).
    case_rewrite (get v S) R1.
      use (fv_in_spec typ_fv R1).
      auto with sets.
    use (get_none_notin _ R1).
    simpl in Hx.
    rewrite (S.singleton_1 Hx) in *.
    auto with sets.
  rewrite diff_union_l.
  destruct (S.union_1 Hx); [use (IHT1 _ H) | use (IHT2 _ H)];
    destruct (S.union_1 H0); auto with sets.
Qed.
    
Lemma kind_fv_subst : forall S k,
  kind_fv (kind_subst S k) << S.diff (kind_fv k) (dom S) \u fv_in typ_fv S.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|].
    unfold kind_fv; simpl.
    clear kh; induction kr; simpl; intros x Hx. elim (in_empty Hx).
    rewrite diff_union_l.
    destruct (S.union_1 Hx).
      use (typ_fv_subst _ _ H).
      destruct (S.union_1 H0); auto with sets.
    destruct (S.union_1 (IHkr _ H)); auto with sets.
  simpl; intros x Hx. elim (in_empty Hx).
Qed.

Lemma kind_subst_combine_fv : forall S L S1 S2 k,
  (forall T, typ_fv T << L -> typ_subst S1 (typ_subst S2 T) = typ_subst S T) ->
  kind_fv k << L -> kind_subst S1 (kind_subst S2 k) = kind_subst S k.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|].
    simpl; apply* kind_pi; simpl.
    unfold kind_fv in H0; simpl in H0.
    clear kv kh.
    induction kr. auto.
    simpl in *.
    rewrite IHkr; try rewrite* H; intros x Hx; apply H0; auto with sets.
  auto.
Qed.

Lemma extends_concat : forall S0 S L n Xs Us,
  dom S0 \u fv_in typ_fv S0 << L ->
  extends S S0 ->
  fresh L n Xs ->
  (forall T, typ_fv T << L ->
    typ_subst (S & combine Xs Us) T = typ_subst S T) ->
  extends (S & combine Xs Us) S0.
Proof.
  introv HL Hext Fr Hsub; intro; intros.
  induction T. simpl*.
    case_eq (get v S0); intros.
      rewrite Hsub. rewrite Hsub.
          rewrite Hext. reflexivity.
        simpl. intros x Hx. rewrite <- (S.singleton_1 Hx).
        use (binds_dom H). auto with sets.
      simpl; rewrite H; intros x Hx.
      use (fv_in_spec typ_fv H Hx).
      auto with sets.
    simpl; rewrite* H.
  simpl. congruence.
Qed.

Lemma unifies_open : forall S n Us L Xs M0 T,
  env_prop type S ->
  types n Us ->
  fresh L n Xs ->
  (forall T, typ_fv T << L ->
    typ_subst (S & combine Xs Us) T = typ_subst S T) ->
  sch_fv M0 \u typ_fv T << L ->
  sch_open (sch_subst S M0) Us = typ_subst S T ->
  typ_subst (S & combine Xs Us) (sch_open_vars M0 Xs) =
  typ_subst (S & combine Xs Us) T.
Proof.
  intros until T; intros HTS HUs Fr Hsub HM0 HU.
  rewrite (Hsub T).
    rewrite <- HU.
    unfold sch_open_vars, sch_open.
    rewrite <- typ_subst_intro0.
          reflexivity.
        rewrite <- (fresh_length _ _ _ Fr).
        apply* fresh_sub.
        unfold sch_fv in HM0.
        intros y Hy; auto with sets.
      rewrite* <- (fresh_length _ _ _ Fr).
    auto.
  intros y Hy; auto with sets.
Qed.

Lemma kind_subst_intro0 : forall S Xs Us k, 
  fresh (kind_fv k) (length Xs) Xs -> 
  types (length Xs) Us ->
  env_prop type S ->
  kind_open (kind_subst S k) Us =
  kind_subst (S & combine Xs Us) (kind_open k (typ_fvars Xs)).
Proof.
  destruct k as [[kc kv kr kh]|]; unfold kind_fv; simpl*; intros.
  apply kind_pi; simpl*.
  clear kh; induction kr. auto.
  destruct a; simpl in *.
  fold (typ_open_vars t Xs).
  rewrite* <- typ_subst_intro0.
  rewrite* IHkr.
Qed.

Lemma fv_in_sch : forall Xs M,
  fv_in kind_fv (combine Xs (sch_kinds M)) << sch_fv M.
Proof.
  intros.
  destruct M as [T Ks]. unfold sch_fv; simpl.
  intros x Hx; apply S.union_3.
  gen Ks; induction Xs; intros; try elim (in_empty Hx). 
  destruct Ks; simpl in *. auto.
  destruct (S.union_1 Hx); auto with sets.
Qed.

Lemma well_subst_concat : forall K M0 Us S S0 K0 E T Xs x,
  env_prop type S ->
  dom S << fvs S0 K0 E T ->
  proper_instance K (sch_subst S M0) Us ->
  well_subst (map (kind_subst S0) K0) K S ->
  binds x M0 E ->
  fresh (fvs S0 K0 E T) (sch_arity M0) Xs ->
  sch_arity M0 = length Us ->
  (forall t, typ_fv t << fvs S0 K0 E T ->
    typ_subst (S & combine Xs Us) t = typ_subst S t) ->
  extends (S & combine Xs Us) S0 ->
  well_subst (map (kind_subst S0) (K0 & kinds_open_vars (sch_kinds M0) Xs))
    K (S & combine Xs Us).
Proof.
  intros until x; intros HTS HS [HUs [HM HWk]] WS B Fr AryM Hsub Hext'.
  intro; intros.
  destruct (binds_map_inv _ _ H) as [k1 [Hk1 Bk1]]; clear H.
  binds_cases Bk1.
    use (WS _ _ (binds_map (kind_subst S0) B0)).
    subst.
    rewrite Hsub.
      rewrite (@kind_subst_combine_fv (compose S S0) (fvs S0 K0 E T)).
          rewrite kind_subst_compose; apply H.
        intros; rewrite typ_subst_compose. rewrite* Hsub.
        intros y Hy. use (typ_fv_subst _ _ Hy).
        destruct (S.union_1 H1).
          use (S.diff_1 H2); auto with sets.
        unfold fvs; auto 6 with sets.
      intros y Hy.
      unfold fvs.
      use (fv_in_spec kind_fv B0 Hy).
      auto with sets.
    simpl. intros y Hy.
    rewrite <- (S.singleton_1 Hy).
    use (binds_dom B0). unfold fvs; auto with sets.
  subst k.
  rewrite (kind_subst_combine _ _ _ k1 Hext').
  simpl.
  case_eq (get Z (combine Xs Us)); intros.
    rewrite (binds_prepend S H).
    unfold kinds_open_vars, kinds_open in B1.
    rewrite <- map_combine in B1.
    destruct (binds_map_inv _ _ B1) as [k [Hk Bk]].
    subst k1.
    rewrite <- kind_subst_intro0.
    subst.
    destruct M0 as [T1 Ks]. simpl in *.
    unfold kinds_open in HWk. rewrite map_map in HWk.
    use (binds_map (fun k => kind_open (kind_subst S k) Us) Bk).
    simpl in H0; rewrite map_combine in H0.
    use (For_all2_get _ _ _ _ HWk H0 H).
    use (fv_in_spec sch_fv B).
    use (fv_in_spec kind_fv Bk).
    use (fv_in_sch Xs M0).
    rewrite <- (fresh_length _ _ _ Fr).
    apply* fresh_sub.
    unfold fvs; intros y Hy; auto 6 with sets.
    subst. rewrite sch_arity_subst in HUs.
    rewrite* <- (fresh_length _ _ _ Fr).
    apply HTS.
  unfold kinds_open_vars, kinds_open in B1.
  elim (get_none_notin _ H).
  use (binds_dom B1).
  rewrite dom_combine. rewrite dom_combine in H0. auto.
  rewrite map_length. unfold sch_arity in Fr; rewrite* (fresh_length _ _ _ Fr).
  rewrite <- AryM. rewrite* (fresh_length _ _ _ Fr).
Qed.


Definition principality S0 K0 S K E t T h :=
  is_subst S0 -> env_prop type S0 ->
  kenv_ok K0 -> disjoint (dom S0) (dom K0) ->
  env_prop type S -> dom S << fvs S0 K0 E T -> extends S S0 ->
  well_subst (map (kind_subst S0) K0) K S ->
  K; map (sch_subst S) E |(false,GcAny)|= t ~: typ_subst S T ->
  trm_depth t < h ->
  exists K', exists S',
    typinf K0 E t T S0 h = Some (K', S') /\
    exists S'',
      dom S'' << S.diff (fvs S' K' E T) (fvs S0 K0 E T) /\
      extends (S & S'') S' /\
      well_subst (map (kind_subst S') K') K (S & S'').

Lemma principal_var : forall h S0 K0 S K E x T,
  principality S0 K0 S K E (trm_fvar x) T (Datatypes.S h).
Proof.
  intros; intros HS0 HTS0 HK0 Dis HTS HS Hext WS Typ Hh.
  inversions Typ; clear Typ; try discriminate.
  simpl.
  destruct (binds_map_inv _ _ H5) as [M0 [HM0 B]].
  rewrite B.
  destruct (var_freshes (fvs S0 K0 E T) (sch_arity M0)) as [Xs Fr]; simpl.
  assert (AryM: sch_arity M0 = length Us).
    destruct H6. subst. rewrite sch_arity_subst in H.
    apply (proj1 H).
  assert (Hsub: forall t, typ_fv t << fvs S0 K0 E T ->
                  typ_subst (S & combine Xs Us) t = typ_subst S t).
    rewrite AryM in Fr.
    intros.
    apply* typ_subst_combine_fresh.
    apply* fresh_sub.
  assert (Ok: ok (K0 & kinds_open_vars (sch_kinds M0) Xs)).
    apply* disjoint_ok. unfold kinds_open_vars. apply* ok_combine_fresh.
    rewrite* dom_kinds_open_vars.
    apply disjoint_comm. unfold fvs in Fr.
    apply* (fresh_disjoint (sch_arity M0)).
  assert (Hext': extends (S & combine Xs Us) S0).
    clear -Fr Hext Hsub.
    apply* extends_concat. unfold fvs; intros x Hx; auto with sets.
  assert (HU: unifies (S & combine Xs Us) ((sch_open_vars M0 Xs, T) :: nil)).
    subst.
    unfold unifies; simpl; intros.
    destruct* H. inversions H; clear H.
    destruct H6. rewrite sch_arity_subst in H.
    apply* unifies_open.
    intros y Hy.
    use (fv_in_spec sch_fv B).
    destruct (S.union_1 Hy); unfold fvs; auto with sets.
  case_eq
    (unify (K0 & kinds_open_vars (sch_kinds M0) Xs) (sch_open_vars M0 Xs) T S0);
    unfold unify; intros.
    destruct p as [K' S']. esplit; esplit. split*.
    unfold fvs in Fr.
    destruct* (unify_mgu0 (K':=K) (S':=S & combine Xs Us) _ H).
      apply* well_subst_concat. subst*.
    destruct* (unify_kinds_ok _ _ H).
      rewrite dom_concat.
      rewrite* dom_kinds_open_vars.
      disjoint_solve.
    exists (combine Xs Us).
    intuition.
    rewrite dom_combine.
      intros y Hy.
      apply S.diff_3.
        assert (y \in dom K' \u dom S').
          apply H8.
          rewrite dom_concat.
          rewrite* dom_kinds_open_vars.
          auto with sets.
        unfold fvs; union_solve y.
        auto 6 with sets.
      destruct* (fresh_disjoint _ _ _ Fr y).
    symmetry. rewrite* <- AryM.
  elimtype False.
  refine (unify_complete0 (K:=K) HS0 Ok Hext' HU _ _ H).
    intro; intros.
    rewrite <- (kind_subst_combine _ _ _ k Hext').
    subst.
    refine (well_subst_concat _ HTS HS H6 WS B Fr AryM Hsub Hext' _).
    apply* binds_map.
  omega.
Qed.

Lemma typ_subst_type' : forall S T,
  type (typ_subst S T) -> type T.
Proof.
  induction T; simpl; intros; auto.
  inversions H. auto.
Qed.

Theorem typinf_principal : forall h S0 K0 S K E t T,
  principality S0 K0 S K E t T h.
Proof.
  induction h; intros until T; intros HS0 HTS0 HK0 Dis HTS HS Hext WS Typ Hh;
    try (elimtype False; omega).
  inversions Typ.
  apply* principal_var.
  (* Abs *)
  simpl.
  destruct (var_fresh (fvs S0 K0 E T)) as [x1 Fr1]; simpl.
  destruct (var_fresh (fvs S0 K0 E T \u {{x1}})) as [x2 Fr2]; simpl.
  destruct (var_fresh (dom E \u trm_fv t1)) as [x Frx]; simpl.
  pose (Xs := x1 :: x2 :: nil).
  pose (Us := U :: T0 :: nil).
  assert (Fr: fresh (fvs S0 K0 E T) 2 Xs) by simpl*.
  assert (Hsub: forall t, typ_fv t << fvs S0 K0 E T ->
                  typ_subst (S & combine Xs Us) t = typ_subst S t).
    intros.
    apply* typ_subst_combine_fresh.
    apply* fresh_sub.
  assert (Hext': extends (S & combine Xs Us) S0).
    apply* extends_concat. unfold fvs; intros y Hy; auto with sets.
  case_eq (unify K0 (typ_arrow (typ_fvar x1) (typ_fvar x2)) T S0);
    unfold unify; intros.
    destruct p as [K' S'].
    destruct* (unify_mgu0 _ H1 (K':=K) (S':=S & combine Xs Us)).
        intro; intros.
        simpl in H2; destruct* H2. inversions H2; clear H2.
        rewrite (typ_subst_combine_fresh S T2).
          simpl. destruct* (x1 == x1).
          destruct* (x2 == x1).
            elim Fr2. rewrite e0. auto with sets.
          destruct* (x2 == x2).
        simpl length. unfold fvs in Fr. auto.
      intro; intros.
      destruct (binds_map_inv _ _ H2) as [k1 [Hk1 Bk1]].
      subst k.
      rewrite* (kind_subst_combine_fv (L:=fvs S0 K0 E T) S (S & combine Xs Us)).
        rewrite <- (kind_subst_combine _ _ _ k1 Hext).
        rewrite Hsub. apply* WS.
        simpl; unfold fvs.
        use (binds_dom Bk1).
        intros y Hy. rewrite <- (S.singleton_1 Hy). auto 6 with sets.
      intros. rewrite* Hext'.
      unfold fvs.
      use (fv_in_spec kind_fv Bk1).
      eapply subset_trans; try apply H3.
      intros y Hy; auto with sets.
    destruct* (unify_type _ _ H1).
      simpl; intros.
      destruct* H5. inversions* H5.
      split*. apply* (typ_subst_type' S).
    destruct* (unify_kinds_ok _ _ H1).
    destruct* (IHh S' K' (S & combine Xs Us) K ((x,Sch (typ_fvar x1) nil) :: E)
                  (t1 ^ x) (typ_fvar x2)).
            apply* env_prop_concat.
            unfold Xs, Us.
            intro; unfold binds; simpl; intros.
            rewrite <- H in Typ.
            use (proj44 (typing_regular Typ)).
            inversions H10.
            destruct (x0 == x1). inversion H9. rewrite* <- H12.
            destruct (x0 == x2). inversion H9. rewrite* <- H12.
            discriminate.
          unfold fvs; simpl.
          intros y Hy.
          destruct (S.union_1 Hy); clear Hy.
            unfold env_fv, sch_fv; simpl. auto with sets.
          destruct (S.union_1 H9); clear H9.
            auto with sets.
          use (HS _ H10); clear H10.
          unfold fvs, env_fv in H9.
          unfold env_fv; simpl.
          apply S.union_2.
          union_solve y; auto 6 with sets.
        
End Mk2.
End MkInfer.