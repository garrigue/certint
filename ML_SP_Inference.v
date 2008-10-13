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
Import Sound.
Import Infra.
Import Defs.
Import Metatheory_Env.Env.

Module Mk2(Delta:DeltaIntf)(Cstr2:Cstr2I).

Module Sound := Sound.Mk2(Delta).
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

Definition fvs S K E T Ts :=
  dom S \u fv_in typ_fv S \u dom K \u fv_in kind_fv K \u env_fv E
  \u typ_fv_list (T :: Ts).

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

Fixpoint typinf (K:kenv) (E:Defs.env) (t:trm) (T:typ) (Ts:list typ) (S:subs)
  (h:nat) {struct h} : option (kenv * subs) :=
  match h with
  | 0 => None
  | S h' =>
  match t with
  | trm_bvar _ => None
  | trm_fvar x =>
    match get x E with
    | None => None
    | Some M =>
      let Vs := proj1_sig (var_freshes (fvs S K E T Ts) (sch_arity M)) in
      unify (K & kinds_open_vars (sch_kinds M) Vs) (M ^ Vs) T S
    end
  | trm_abs t1 =>
    let x := proj1_sig (var_fresh (dom E \u trm_fv t1)) in
    let v1 := proj1_sig (var_fresh (fvs S K E T Ts)) in
    let V2 := typ_fvar (proj1_sig (var_fresh (fvs S K E T Ts \u {{v1}}))) in
    match unify K (typ_arrow (typ_fvar v1) V2) T S with
    | None => None
    | Some (K',S') =>
      typinf K' (E & x ~ Sch (typ_fvar v1) nil) (t1 ^ x) V2 (T::Ts) S' h'
    end
  | trm_let t1 t2 =>
    let V := typ_fvar (proj1_sig (var_fresh (fvs S K E T Ts))) in
    match typinf K E t1 V (T::Ts) S h' with
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
      let Bs' := S.elements (S.diff B (ftve \u dom KB)) in
      let Ks' := List.map (fun x:var => @None ckind) Bs' in
      let x := proj1_sig (var_fresh (dom E \u trm_fv t1 \u trm_fv t2)) in
      typinf KA (E & x ~ sch_generalize (Bs++Bs') T1 (Ks++Ks'))
        (t2 ^ x) T Ts S' h'
    end
  | trm_app t1 t2 =>
    let V := typ_fvar (proj1_sig (var_fresh (fvs S K E T Ts))) in
    match typinf K E t1 (typ_arrow V T) Ts S h' with
    | None => None
    | Some (K',S') => typinf K' E t2 V (T::Ts) S' h'
    end
  | trm_cst c =>
    let M := Delta.type c in
    let Vs := proj1_sig (var_freshes (fvs S K E T Ts) (sch_arity M)) in
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
  apply* (fresh_disjoint (length Ks)).
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

Lemma well_subst_extends : forall K K0 S S0,
  extends S S0 ->
  well_subst K0 K S ->
  well_subst (map (kind_subst S0) K0) K S.
Proof.
  intros; intro; intros.
  destruct (binds_map_inv _ _ H1) as [k1 [Hk1 Bk1]].
  subst k.
  rewrite* (kind_subst_combine S).
Qed.

Hint Resolve well_subst_extends.

Definition Gc := (false, GcLet).

Definition soundness_spec h t K0 E T Ts S0 K S :=
  typinf K0 E t T Ts S0 h = Some (K, S) ->
  is_subst S0 -> env_prop type S0 ->
  kenv_ok K0 -> disjoint (dom S0) (dom K0) ->
  ok E -> env_prop scheme E -> type T ->
  extends S S0 /\ env_prop type S /\ is_subst S /\
  kenv_ok K /\ disjoint (dom S) (dom K) /\
  well_subst K0 (map (kind_subst S) K) S /\
  map (kind_subst S) K; map (sch_subst S) E |Gc|= t ~: typ_subst S T.

Lemma soundness_ind : forall h t K0 E T Ts S0 K S s x,
  scheme s ->
  fresh (fvs S0 K0 E T Ts) (sch_arity s) x ->
  unify (K0 & kinds_open_vars (sch_kinds s) x) (sch_open_vars s x) T S0 =
    Some (K, S) ->
  (kenv_ok (K0 & kinds_open_vars (sch_kinds s) x) ->
   extends S S0 -> kenv_ok K ->
   unifies S ((sch_open_vars s x, T) :: nil) ->
   map (kind_subst S0) (K0 & kinds_open_vars (sch_kinds s) x);
   map (sch_subst S0) E |Gc|= t ~: sch_subst S0 s ^^ typ_fvars x) ->
  soundness_spec h t K0 E T Ts S0 K S.
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
    apply H5.
    apply* binds_concat_ok.
  rewrite <- (map_sch_subst_extend E Hext).
  use (unify_types _ _ _ HI HS0).
  rewrite* <- (H7 (sch_open_vars s x) T).
  rewrite* <- Hext.
  unfold fvs in f.
  rewrite* sch_subst_open_vars.
  poses Hkext (fun k => sym_eq (kind_subst_combine _ _ _ k Hext)).
  rewrite (map_map_env _ _ _ K Hkext).
  apply* typing_typ_well_subst.
    rewrite* <- (map_map_env _ _ _ K Hkext).
  repeat apply* kenv_ok_map.
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

Lemma soundness_var : forall h Ts v K0 E T S0 K S,
  soundness_spec (Datatypes.S h) (trm_fvar v) K0 E T Ts S0 K S.
Proof.
  intros; intros HI HS0 HTS0 HK0 Dis HE HSE HT.
  poses HI' HI; simpl in HI.
  case_rewrite (get v E) R1.
  destruct (var_freshes (fvs S0 K0 E T Ts) (sch_arity s));
    simpl proj1_sig in HI.
  unfold fvs in f.
  refine (soundness_ind _ _ _ _ _ HI _ HI' _ _ _ _ _ _ _); auto.
    apply (HSE _ _ R1).
  intros.
  apply* typing_var.
    apply* kenv_ok_map.
  split.
    unfold sch_arity. simpl. rewrite map_length. fold (sch_arity s).
    rewrite (fresh_length _ _ _ f). apply types_typ_fvars.
  split. apply* sch_subst_type. apply (HSE _ _ R1).
  destruct s as [Us Ks]; simpl.
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
      sets_solve.
    rewrite Delta.closed in H.
    elim (in_empty H).
  induction (sch_kinds (Delta.type c)). auto.
  simpl in *.
  rewrite IHl.
    rewrite* kind_subst_fresh.
    intro. use (H x).
  intro; use (H x).
Qed.

Lemma soundness_cst : forall h Ts c K0 E T S0 K S,
  soundness_spec (Datatypes.S h) (trm_cst c) K0 E T Ts S0 K S.
Proof.
  intros; intros HI HS0 HTS0 HK0 Dis HE HSE HT.
  poses HI' HI; simpl in HI.
  destruct (var_freshes (fvs S0 K0 E T Ts) (sch_arity (Delta.type c)));
    simpl in HI.
  refine (soundness_ind _ _ _ _ _ HI _ HI' _ _ _ _ _ _ _); auto.
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

Lemma soundness_abs : forall h Ts t K0 E T S0 S K,
  (forall t K0 E T Ts S0 K S, soundness_spec h t K0 E T Ts S0 K S) ->
  soundness_spec (Datatypes.S h) (trm_abs t) K0 E T Ts S0 K S.
Proof.
  intros until K; intros IHh  HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T Ts)); simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T Ts \u {{x}})); simpl in HI.
  destruct (var_fresh (dom E \u trm_fv t)); simpl in HI.
  case_rewrite (unify K0 (typ_arrow (typ_fvar x) (typ_fvar x0)) T S0) R1.
  destruct p as [K' S'].
  unfold unify in R1.
  destruct* (unify_keep _ _ _ R1) as [HS' _].
  destruct* (unify_type _ _ R1).
    simpl; intros. destruct* H.
    inversions* H.
  destruct* (unify_kinds_ok _ _ R1). clear H1; destruct H2.
  destruct* (IHh _ _ _ _ _ _ _ _ HI); clear IHh HI.
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
  rewrite* <- (H10 (typ_arrow (typ_fvar x) (typ_fvar x0)) T).
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
  case_eq (get e K); introv R2; apply* IHn; sets_solve.
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
      apply eq_ext; intros; split; intro; sets_solve.
      sets_solve. elim Hn. reflexivity.
    rewrite H1. rewrite* remove_notin.
    rewrite* union_empty_l.
  sets_solve.
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
      apply* close_fvars_subset.
    assert (forall L', x \in close_fvars n K (S.remove e v) L' ->
               kind_fv k << close_fvars n K (S.remove e v) L').
      intros; apply* IHn.
      rewrite <- (@cardinal_remove e) in H2; auto.
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

Lemma well_subst_let_inf : forall K0 s k e e0 S K L,
  extends S s -> is_subst s ->
  well_subst K0 (map (kind_subst s) k) s ->
  well_subst e0 (map (kind_subst S) K) S ->
  let K' := map (kind_subst s) k in
  env_incl K' (e0 & e) ->
  disjoint (close_fvk K' (L \u vars_subst s (dom K0))) (dom e) ->
  well_subst K0 (map (kind_subst S) K) S.
Proof.
  intros until L; intros Hext Hs WS WS' K' Inc1 Dise; intro; intros.
  use (WS _ _ H).
  inversions H0.
    destruct k0; try discriminate; apply wk_any.
  fold (typ_subst s (typ_fvar Z)) in H2.
  rewrite* <- (kind_subst_combine S S s). rewrite <- H1.
  rewrite <- Hext. rewrite <- H2.
  rewrite <- H1 in H0; rewrite <- H2 in H0.
  use (Inc1 _ _ H4).
  binds_cases H3.
    use (WS' _ _ B).
    apply* (@kind_entails_well_kinded (kind_subst S (Some k'))).
    simpl; apply* kind_subst_entails.
  use (binds_dom B0).
  destruct* (Dise x).
  use (notin_subset (close_fvk_subset _) H6).
  use (binds_dom H).
  elim H7; clear H6 H7.
  apply S.union_3.
  apply* (vars_subst_in s H8).
  rewrite <- H2.
  simpl*.
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

Lemma typing_let_disjoint : forall EK0 L e e0 K',
  ok (e0 & e) ->
  ok K' -> env_incl (e0 & e) K' ->
  disjoint (close_fvk K' EK0) L ->
  dom e0 << close_fvk K' EK0 ->
  disjoint L (EK0 \u dom e0 \u fv_in kind_fv e0).
Proof.
  intros until K'; intros Ok HK' Inc2 Dise Se0.
  apply disjoint_comm.
  repeat apply disjoint_union.
  (* env_fv E *)
  apply* disjoint_subset. apply close_fvk_subset.
  (* dom e0 *)
  apply* (disjoint_subset (L3:=L) Se0).
  (* fv_in kind_fv (map (kind_subst s) e0) *)
  refine (disjoint_subset (proj2 (fv_in_subset_inv _ _ _) _) Dise).
  intros.
  destruct (ok_concat_inv _ _ Ok).
  use (in_ok_binds _ _ H H0).
  puts (binds_dom H2).
  apply* (@close_fvk_ok K' EK0 x a).
Qed.

Lemma mkset_in : forall x l, x \in mkset l -> In x l.
Proof.
  induction l; simpl; intros. elim (in_empty H).
  destruct* (S.union_1 H).
  rewrite* (S.singleton_1 H0).
Qed.

Lemma mkset_elements : forall L,
  mkset (S.elements L) = L.
Proof.
  intros. apply eq_ext.
  intros; split; intro.
    apply S.elements_2.
    apply (SetoidList.In_InA S.E.eq_refl).
    apply* mkset_in.
  apply in_mkset.
  use (S.elements_1 H).
  induction H0; auto.
Qed.

Lemma elements_fresh : forall L1 L,
  disjoint L1 L ->
  fresh L1 (length (S.elements L)) (S.elements L).
Proof.
  intros.
  puts (S.elements_3 L).
  rewrite <- (mkset_elements L) in H.
  gen L1; induction H0; intros. simpl*.
  simpl in *. split.
    destruct* (H1 a).
  apply IHsort.
  disjoint_solve.
  destruct* (v == a).
  subst.
  right; intro.
  elim (sort_lt_notin H0 H).
  puts (mkset_in _ H1).
  clear -H3.
  induction l; auto.
Qed.

Lemma diff_disjoint : forall L1 L2, disjoint (S.diff L1 L2) L2.
Proof.
  intros. intro y.
  case_eq (S.mem y (S.diff L1 L2)); intros.
    use (S.diff_2 (S.mem_2 H)).
  use (mem_3 H).
Qed.

Definition ok_concat_inv1 A (E1 E2:env A) H := proj1 (ok_concat_inv E1 E2 H).
Definition ok_concat_inv2 A (E1 E2:env A) H := proj2 (ok_concat_inv E1 E2 H).
Hint Immediate ok_concat_inv1 ok_concat_inv2.

Lemma typing_let_fresh : forall T1 l l0 K' e e0 e1 e2 fvT1 fvE sK0,
  let ftve := close_fvk K' (fvE \u sK0) in
  let Bs := S.elements (S.diff fvT1 (ftve \u dom e2)) in
  let l0' := List.map (fun _:var => @None ckind) Bs in
  let M := sch_generalize (@app var l Bs) T1 (@app kind l0 l0') in
  split e2 = (l, l0) ->
  ok (e0 & e) -> ok (e2 & e1) ->
  ok K' -> env_incl (e0 & e) K' -> env_incl (e2 & e1) e ->
  disjoint ftve (dom e) ->
  dom e0 << ftve ->
  fresh (fvE \u sch_fv M \u dom e0 \u fv_in kind_fv e0) (sch_arity M) (l++Bs).
Proof.
  intros until M. intros R4 Ok Ok' HK' Inc2 Inc4 Dise Se0.
  unfold sch_arity; simpl length.
  rewrite map_length. rewrite app_length.
  rewrite <- (split_length _ R4).
  use (split_combine e2). rewrite R4 in H.
  apply fresh_app.
  apply* (ok_fresh l l0).
    rewrite* H.
  rewrite* <- (dom_combine l l0).
  rewrite H.
  use (env_incl_subset_dom Inc4).
  rewrite dom_concat in H0.
  assert (dom e2 << dom e).
    intros v Hv. apply* (H0 v).
  use (disjoint_subset H1
          (typing_let_disjoint _ _ _ Ok HK' Inc2 Dise Se0)).
  assert (disjoint (sch_fv M) (dom e2)).
    unfold M.
    rewrite <- H.
    rewrite* dom_combine.
    use(sch_generalize_disjoint (l++Bs) T1 (l0 ++ l0')).
    rewrite mkset_app in H3.
    disjoint_solve.
  disjoint_solve.
  unfold l0'.
  rewrite map_length.
  unfold Bs.
  apply elements_fresh.
  rewrite <- H.
  rewrite* dom_combine.
  puts (diff_disjoint fvT1 (ftve \u mkset l)).
  set (l' := S.diff fvT1 (ftve \u mkset l)) in *.
  assert (disjoint ftve l') by disjoint_solve.
  puts (typing_let_disjoint _ _ _ Ok HK' Inc2 H1 Se0).
  clear H1.
  assert (disjoint (sch_fv M) l').
    unfold M.
    use(sch_generalize_disjoint (l++Bs) T1 (l0 ++ l0')).
    rewrite mkset_app in H1.
    rewrite <- (mkset_elements l').
    unfold l'.
    rewrite <- (dom_combine l l0).
    rewrite H. fold Bs. disjoint_solve.
    apply* split_length.
  disjoint_solve.
Qed.

Lemma typing_let_fresh_2 : forall l1 l2 K' T fvE sK0 e e0 e1 e2,
  let Ks := List.map (kind_map (typ_generalize l1)) l2 in
  let M' := Sch T Ks in
  kenv_ok K' ->  ok (e0 & e) -> ok (e2 & e1) ->
  env_incl (e0 & e) K' -> env_incl (e2 & e1) e ->
  split e1 = (l1, l2) ->
  disjoint (close_fvk K' (fvE \u sK0)) (dom e) ->
  dom e0 << close_fvk K' (fvE \u sK0) ->
  disjoint (close_fvk K' (typ_fv T)) (dom e1) ->
  dom e2 << close_fvk K' (typ_fv T) ->
  fresh (fvE \u sch_fv M' \u dom (e0 & e2) \u fv_in kind_fv (e0 & e2))
    (sch_arity M') l1.
Proof.
  intros until M'.
  intros HK' Ok Ok' Inc2 Inc4 R5 Dise Se0 Dise1 Se2.
  rewrite dom_concat; rewrite fv_in_concat.
  unfold sch_arity; simpl length.
  unfold Ks; rewrite map_length.
  rewrite <- (split_length _ R5).
  poses He1 (split_combine e1). rewrite R5 in He1.
  apply* (ok_fresh l1 l2).
    rewrite* He1.
  rewrite* <- (dom_combine l1 l2).
  rewrite He1.
  use (env_incl_subset_dom Inc4).
  rewrite dom_concat in H.
  assert (dom e1 << dom e).
    intros v Hv. apply* (H v).
  use (disjoint_subset H0
         (typing_let_disjoint _ _ _ Ok (proj1 HK') Inc2 Dise Se0)).
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
  assert (ok e2) by auto*.
  use (in_ok_binds _ _ H2 H3).
  apply* (@close_fvk_ok K' (typ_fv T) x).
  apply Se2.
  apply* binds_dom.
Qed.

Lemma sch_open_extra : forall Ks Xs T,
  type T -> sch_open_vars (Sch T Ks) Xs = T.
Proof.
  unfold sch_open_vars, typ_open_vars; simpl; intros.
  rewrite* <- typ_open_type.
Qed.

Lemma typing_let_incl : forall K' e e0 e1 e2 : kenv,
  ok (e0 & e) -> ok (e2 & e1) ->
  env_incl K' (e0 & e) ->
  env_incl (e0 & e) K' ->
  env_incl e (e2 & e1) ->
  env_incl (e2 & e1) e ->
  env_incl K' (e0 & e2 & e1) /\ env_incl (e0 & e2 & e1) K'.
Proof.
  intros until e2; intros Ok Ok' I1 I2 I3 I4.
  rewrite concat_assoc.
  set (e' := e2 & e1) in *.
  split; intro; intros.
    use (I1 _ _ H).
    binds_cases H0.
      apply* binds_concat_fresh.
      eapply notin_subset. apply (env_incl_subset_dom I4). auto.
    use (I3 _ _ B0).
  clearbody e'.
  binds_cases H.
    apply I2.
    apply* binds_concat_ok.
  auto.
Qed.

Lemma typing_let_kenv_ok : forall K' T1 ftve e2 l l0 e0 e e1,
  let Bs := S.elements (S.diff (close_fvk K' (typ_fv T1)) (ftve \u dom e2)) in
  let l0' := List.map (fun _ : var => None) Bs in
  split e2 = (l, l0) ->
  kenv_ok K' -> ok (e0 & e) -> ok (e2 & e1) ->
  dom e0 << ftve -> env_incl (e0 & e) K' -> env_incl (e2 & e1) e ->
  combine l l0 = e2 ->
  kenv_ok (e0 & combine Bs l0' & combine l l0).
Proof.
  intros until l0'; intros R4 HK' Ok Ok' Se0 Inc2 Inc4 He2.
  rewrite concat_assoc.
  puts (diff_disjoint (close_fvk K' (typ_fv T1)) (ftve \u dom e2)).
  puts (elements_fresh (disjoint_comm H)).
  apply kenv_ok_concat.
      split*. intro; intros. apply (proj2 HK' x). apply* Inc2.
    split.
      apply disjoint_ok.
          eapply ok_combine_fresh.
          unfold Bs. apply H0.
        rewrite* He2.
      rewrite* dom_combine. rewrite* dom_combine.
        unfold Bs; rewrite mkset_elements.
        rewrite* <- (dom_combine l l0). rewrite He2.
        disjoint_solve.
      unfold l0'; rewrite* map_length.
    apply env_prop_concat.
      apply list_forall_env_prop.
      unfold l0'; clear; induction Bs; simpl*.
    rewrite He2. intro; intros. apply (proj2 HK' x). apply* Inc2.
  rewrite dom_concat. rewrite He2.
  apply disjoint_comm; apply disjoint_union.
    rewrite dom_combine.
      apply disjoint_comm.
      apply (disjoint_subset (L3:=mkset Bs) Se0).
      unfold Bs; rewrite mkset_elements.
      disjoint_solve.
    unfold l0'; rewrite* map_length.
  puts (ok_disjoint _ _ Ok).
  refine (disjoint_subset _ (disjoint_comm H1)).
  apply env_incl_subset_dom.
  intro; intros. apply* Inc4.
Qed.

Lemma soundness_let : forall h Ts t1 t2 K0 E T S0 S K,
  (forall t K0 E T Ts S0 K S, soundness_spec h t K0 E T Ts S0 K S) ->
  soundness_spec (Datatypes.S h) (trm_let t1 t2) K0 E T Ts S0 K S.
Proof.
  intros until K; intros IHh  HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T Ts)); simpl in HI.
  case_rewrite (typinf K0 E t1 (typ_fvar x) (T::Ts) S0 h) R1. destruct p.
  fold (typ_subst s (typ_fvar x)) in HI.
  set (K' := map (kind_subst s) k) in *.
  set (T1 := typ_subst s (typ_fvar x)) in *.
  set (ftve :=
    close_fvk K' (env_fv (map (sch_subst s) E) \u vars_subst s (dom K0))) in *.
  case_rewrite (split_env ftve K') R2.
  case_rewrite (split_env (close_fvk K' (typ_fv T1)) e) R3.
  case_rewrite (split e2) R4.
  destruct (var_fresh (dom E \u trm_fv t1 \u trm_fv t2)); simpl proj1_sig in HI.
  set (Bs := S.elements (S.diff (close_fvk K' (typ_fv T1)) (ftve \u dom e2)))
    in *.
  set (l0' := List.map (fun _:var => @None ckind) Bs) in *.
  set (M := sch_generalize (l++Bs) T1 (l0++l0')) in *.
  destruct* (IHh _ _ _ _ _ _ _ _ R1); clear R1.
  destruct H0 as [HTs [Hs [Hk [Disk [WS' Typ']]]]].
  assert (HT1: type T1) by (unfold T1; auto*).
  assert (HK':kenv_ok K') by (unfold K'; apply* kenv_ok_map).
  destruct* (split_env_ok _ R2) as [Ok [Dise [Se0 [Inc1 Inc2]]]].
  destruct* (split_env_ok _ R3) as [Ok' [Dise' [Se2 [Inc3 Inc4]]]].
  poses He2 (split_combine e2). rewrite R4 in He2.
  assert (Hkt: list_forall (All_kind_types type) (l0 ++ l0')).
    apply list_forall_app.
      apply* env_prop_list_forall.
        rewrite He2. intro; intros. apply* (proj2 HK' x1).
      rewrite* He2.
    unfold l0'. clear; induction Bs; simpl*.
  assert (HM: scheme M).
    unfold M, l0'.
    apply* scheme_generalize.
    do 2 rewrite app_length. rewrite map_length. rewrite* (split_length _ R4).
  destruct* (IHh _ _ _ _ _ _ _ _ HI); clear IHh HI.
          split*.
          intro; destruct* HK'.
        use (env_incl_subset_dom Inc2).
        unfold K' in H0; rewrite dom_map in H0; rewrite dom_concat in H0.
        intro v; destruct* (Disk v).
      apply* ok_cons.
    intro; intros.
    unfold binds in H0; simpl in H0.
    destruct (x1 == x0); try subst x0.
      inversion* H0.
    apply (HSE _ _ H0).
  intuition.
      apply* extends_trans.
    unfold ftve in *.
    apply* well_subst_let_inf.
  apply* (@typing_let Gc (sch_subst S M)
             (dom S \u dom K \u dom e0 \u mkset l \u mkset Bs)).
    intros.
    unfold M; simpl.
    rewrite* <- kinds_subst_open_vars.
    rewrite* <- sch_subst_open_vars.
    fold M.
    replace (List.map (kind_map (typ_generalize (l ++ Bs))) (l0  ++ l0'))
      with (sch_kinds M) by simpl*.
    rewrite sch_arity_subst in H6.
    rewrite <- (map_sch_subst_extend E H0).
    apply* typing_typ_well_subst.
        apply (well_subst_extend (sch_kinds M) Xs H2 H5).
        rewrite* dom_map.
      rewrite <- map_concat.
      apply* kenv_ok_map.
      apply* kenv_ok_sch_kinds.
    assert (AryM: sch_arity M = length (l ++ Bs)).
      unfold sch_arity; simpl. unfold l0'.
      autorewrite with list.
      rewrite* (split_length _ R4).
    apply* typing_rename_typ.
        apply* (@typing_let_fresh T1 l l0 K' e e0 e1 e2
          (close_fvk K' (typ_fv T1))
          (env_fv (map (sch_subst s) E)) (vars_subst s (dom K0))).
      fold ftve. fold Bs. rewrite <- AryM. rewrite* mkset_app.
    fold ftve. fold Bs.
    unfold M.
    unfold sch_open_vars, typ_open_vars. simpl sch_type.
    rewrite* typ_generalize_reopen.
    unfold sch_generalize. simpl sch_kinds.
    rewrite* kinds_generalize_reopen.
    rewrite* combine_app.
    fold (@combine var kind Bs l0' & combine l l0).
    rewrite <- concat_assoc.
    puts (typing_let_kenv_ok T1 _ _ R4 HK' Ok Ok' Se0 Inc2 Inc4 He2).
    apply* typing_weaken_kinds; clear H8.
    rewrite He2.
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
        unfold ftve in *.
        apply* (@typing_let_fresh_2 l1 l2 K').
      unfold Ks in H8. rewrite map_length in H8.
      rewrite* (split_length _ R5).
    assert (list_forall (All_kind_types type) l2).
      apply* env_prop_list_forall.
        rewrite He1. intro; intros. apply* (proj2 HK' x1).
      rewrite* He1.
    simpl sch_kinds.
    unfold Ks; rewrite* kinds_generalize_reopen. rewrite He1; clear H9.
    unfold sch_open_vars, typ_open_vars.
    simpl sch_type. rewrite* <- typ_open_type.
    destruct* (typing_let_incl _ _ _ Ok Ok' Inc1 Inc2 Inc3 Inc4).
    unfold T1; apply* typing_kenv_incl.
    split.
      rewrite concat_assoc.
      apply* disjoint_ok.
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

Lemma soundness_app : forall h Ts t1 t2 K0 E T S0 S K,
  (forall t K0 E T Ts S0 K S, soundness_spec h t K0 E T Ts S0 K S) ->
  soundness_spec (Datatypes.S h) (trm_app t1 t2) K0 E T Ts S0 K S.
Proof.
  intros until K; intros IHh HI HS0 HTS0 HK0 Dis HE HSE HT; simpl in HI.
  destruct (var_fresh (fvs S0 K0 E T Ts)); simpl in HI.
  case_rewrite (typinf K0 E t1 (typ_arrow (typ_fvar x) T) Ts S0 h) R1.
  destruct p as [K' S'].
  destruct* (IHh _ _ _ _ _ _ _ _ R1); clear R1.
  destruct* (IHh _ _ _ _ _ _ _ _ HI); clear IHh HI.
  intuition.
      apply* extends_trans.
    apply* well_subst_compose.
  remember (typ_fvar x) as T1.
  apply* typing_app.
  use (well_subst_extends H1 H10).
  use (typing_typ_well_subst H0 H11 (kenv_ok_map H6 H0) H12).
  rewrite (map_sch_subst_extend E H1) in H14.
  rewrite H1 in H14.
  apply H14.
Qed.

Theorem typinf_sound : forall h t K0 E T Ts S0 K S,
  soundness_spec h t K0 E T Ts S0 K S.
Proof.
  induction h; destruct t; intros;
    intros HI HS0 HTS0 HK0 Dis HE HSE HT; try discriminate.
  apply* (soundness_var h Ts).
  apply* (@soundness_abs h Ts).
  apply* (@soundness_let h Ts).
  apply* (@soundness_app h Ts).
  apply* (soundness_cst h Ts).
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
    apply disjoint_comm.
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

Lemma typ_fv_subst0 : forall S T,
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

Lemma typ_fv_subst : forall S T,
  typ_fv (typ_subst S T) << typ_fv T \u fv_in typ_fv S.
Proof.
  intros; intros y Hy.
  use (typ_fv_subst0 _ _ Hy).
  destruct (S.union_1 H); clear H Hy.
    use (S.diff_1 H0); auto with sets.
  auto with sets.
Qed.

Lemma kind_fv_subst : forall S k,
  kind_fv (kind_subst S k) << kind_fv k \u fv_in typ_fv S.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|].
    unfold kind_fv; simpl.
    clear kh; induction kr; simpl; intros x Hx. elim (in_empty Hx).
    destruct (S.union_1 Hx).
      use (typ_fv_subst _ _ H).
      destruct (S.union_1 H0); auto with sets.
    destruct (S.union_1 (IHkr _ H)); auto with sets.
  simpl; intros x Hx. elim (in_empty Hx).
Qed.

Lemma kind_subst_ext_fv : forall S2 L S1 k,
  (forall T, typ_fv T << L -> typ_subst S1 T = typ_subst S2 T) ->
  kind_fv k << L -> kind_subst S1 k = kind_subst S2 k.
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

Lemma well_subst_concat : forall S0 K0 K S E T Ts Xs Us,
  well_subst (map (kind_subst S0) K0) K S ->
  (forall t, typ_fv t << fvs S0 K0 E T Ts ->
    typ_subst (S & combine Xs Us) t = typ_subst S t) ->
  extends (S & combine Xs Us) S0 ->
  well_subst K0 K (S & combine Xs Us).
Proof.
  introv WS Hsub Hext'.
  intro; intros.
  rewrite <- (kind_subst_combine _ _ _ k Hext').
  use (WS _ _ (binds_map (kind_subst S0) H)).
  rewrite Hsub.
    rewrite* (@kind_subst_ext_fv S (fvs S0 K0 E T Ts)).
    intros y Hy.
    use (kind_fv_subst _ _ Hy).
    unfold fvs.
    destruct (S.union_1 H1).
      use (fv_in_spec kind_fv H H2).
      auto with sets.
    auto 6 with sets.
  simpl. intros y Hy.
  rewrite <- (S.singleton_1 Hy).
  use (binds_dom H). unfold fvs; auto with sets.
Qed.

Lemma well_subst_concat_abs : forall K M0 Us S S0 K0 E T Ts Xs x,
  env_prop type S ->
  dom S << fvs S0 K0 E T Ts ->
  proper_instance K (sch_subst S M0) Us ->
  well_subst (map (kind_subst S0) K0) K S ->
  binds x M0 E ->
  fresh (fvs S0 K0 E T Ts) (sch_arity M0) Xs ->
  sch_arity M0 = length Us ->
  (forall t, typ_fv t << fvs S0 K0 E T Ts ->
    typ_subst (S & combine Xs Us) t = typ_subst S t) ->
  extends (S & combine Xs Us) S0 ->
  well_subst (K0 & kinds_open_vars (sch_kinds M0) Xs) K (S & combine Xs Us).
Proof.
  intros until x; intros HTS HS [HUs [HM HWk]] WS B Fr AryM Hsub Hext'.
  intro; intros.
  binds_cases H.
    apply* (well_subst_concat _ _ WS Hsub Hext').
  simpl.
  case_eq (get Z (combine Xs Us)); intros.
    rewrite (binds_prepend S H).
    unfold kinds_open_vars, kinds_open in B1.
    rewrite <- map_combine in B1.
    destruct (binds_map_inv _ _ B1) as [k1 [Hk1 Bk]].
    subst k.
    rewrite <- kind_subst_intro0.
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

Lemma typ_fv_subst_keep : forall S T,
  typ_fv T << typ_fv (typ_subst S T) \u dom S.
Proof.
  induction T; simpl; intros y Hy. elim (in_empty Hy).
    rewrite <- (S.singleton_1 Hy) in *. clear y Hy.
    case_eq (get v S); intros.
      use (binds_dom H). auto with sets.
    simpl; auto with sets.
  destruct (S.union_1 Hy); [use (IHT1 _ H) | use (IHT2 _ H)];
    destruct (S.union_1 H0); auto with sets.
Qed.

Lemma kind_fv_subst_keep : forall S k,
  kind_fv k << kind_fv (kind_subst S k) \u dom S.
Proof.
  destruct k as [[kc kv kr kh]|]; unfold kind_fv; simpl; intros y Hy.
    clear kh; induction kr. elim (in_empty Hy).
    simpl in *.
    destruct (S.union_1 Hy).
      use (typ_fv_subst_keep S _ H).
      clear -H0; union_solve y.
    use (IHkr H).
    clear -H0; union_solve y.
  elim (in_empty Hy).
Qed.

Lemma fv_in_typ_subst : forall S S0,
  fv_in typ_fv S0 << fv_in typ_fv (map (typ_subst S) S0) \u dom S.
Proof.
  induction S0; simpl; intros y Hy. elim (in_empty Hy).
  destruct a. simpl.
  destruct (S.union_1 Hy); clear Hy.
    destruct (S.union_1 (typ_fv_subst_keep S _ H)); auto with sets.
  destruct (S.union_1 (IHS0 _ H)); auto with sets.
Qed.

Lemma fv_in_remove_env : forall (A:Set) fv v (a:A) E,
  binds v a E ->
  fv_in fv E << fv a \u fv_in fv (remove_env E v).
Proof.
  unfold binds; induction E; simpl; intros. discriminate.
  destruct a0.
  destruct (v == v0).
    inversions H. apply subset_refl.
  simpl.
  intros y Hy.
  union_solve y.
  use (IHE H _ H0).
  union_solve y.
Qed.

Lemma remove_env_idem : forall (A:Set) v (E:env A),
  v # E -> remove_env E v = E.
Proof.
  induction E; simpl; intros. auto.
  destruct a.
  destruct (v == v0).
    elim H; subst; auto with sets.
  rewrite* IHE.
Qed.

Lemma kind_fv_in_remove_env : forall v E,
  fv_in kind_fv E << kind_fv (get_kind v E) \u fv_in kind_fv (remove_env E v).
Proof.
  intros.
  unfold get_kind.
  case_eq (get v E); intros.
    apply* fv_in_remove_env.
  use (get_none_notin _ H).
  rewrite (remove_env_idem _ H0).
  intros y Hy; auto with sets.
Qed.

Lemma fv_in_typ_subst' : forall S S0,
  fv_in typ_fv (map (typ_subst S) S0) <<
  S.diff (fv_in typ_fv S0) (dom S) \u fv_in typ_fv S.
Proof.
  induction S0; intros y Hy; simpl in *; sets_simpl.
  destruct a. simpl in Hy.
  sets_solve.
  use (typ_fv_subst0 _ _ H).
Qed.

Lemma fv_in_compose : forall S S0,
  fv_in typ_fv (compose S S0) <<
  S.diff (fv_in typ_fv S0) (dom S) \u fv_in typ_fv S.
Proof.
  intros. unfold compose.
  rewrite fv_in_concat.
  intros y Hy; sets_solve.
  apply* fv_in_typ_subst'.
Qed.

Lemma unify_keep_fv_nv : forall h pairs K0 S0 K S E T Ts t t0 T1 v,
  unify_nv (Body.unify h pairs) K0 S0 v T1 = Some (K, S) ->
  typ_subst S0 t = T1 -> typ_subst S0 t0 = typ_fvar v ->
  is_subst S0 -> ok K0 ->
  (forall pairs K0 S0,
    Body.unify h pairs K0 S0 = Some (K, S) ->
    is_subst S0 -> ok K0 ->
    fvs S0 K0 E T Ts << fvs S K E T Ts) ->
  fvs S0 K0 E T Ts << fvs S K E T Ts.
Proof.
  intros until v; intros HU R1 R2 HS0 HK0 IHh.
  unfold unify_nv in HU.
  simpl in HU. case_rewrite (S.mem v (typ_fv T1)) R3.
  case_rewrite (get_kind v K0) R4.
  simpl; intros y Hy. apply* (IHh _ _ _ HU).
  unfold compose.
  clear -HK0 Hy R1 R2 R4; unfold fvs in *.
  rewrite dom_concat. rewrite* dom_remove_env.
  rewrite dom_map. rewrite fv_in_concat.
  simpl dom.
  sets_solve.
      destruct (S.union_1 (fv_in_typ_subst (v ~ T1) _ H)); clear H;
      simpl in *; sets_solve.
    destruct (v == y); subst*.
  use (kind_fv_in_remove_env v _ H).
  rewrite R4 in H0.
  replace (kind_fv None) with {} in H0 by reflexivity.
  sets_solve.
Qed.

Lemma kind_entails_fv : forall k1 k2,
  kind_entails k1 k2 -> kind_fv k2 << kind_fv k1.
Proof.
  unfold kind_entails; intros.
  destruct k2.
    destruct* k1.
    unfold kind_fv; simpl.
    destruct H.
    clear H; induction (kind_rel c); simpl; intros y Hy.
      elim (in_empty Hy).
    destruct (S.union_1 Hy).
      apply* (in_typ_fv (snd a)).
      apply* in_map.
    apply* IHl.
  intros y Hy. elim (in_empty Hy).
Qed.

Lemma unify_fv_sub : forall S K p pairs,
  unify_fv S K pairs << unify_fv S K (p::pairs).
Proof.
  unfold unify_fv; simpl.
  introv y Hy.
  sets_solve.
Qed.

Lemma unify_fv_swap : forall S K T1 T2 pairs,
  unify_fv S K ((T1,T2)::pairs) = unify_fv S K ((T2,T1)::pairs).
Proof.
  unfold unify_fv.
  simpl.
  intros.
  rewrite (union_comm (typ_fv T1)). auto.
Qed.

Lemma unify_keep_fvs_vars : forall K0 v v0 k l pairs K S S0 E T Ts h,
  ok K0 -> v <> v0 ->
  unify_kinds (get_kind v K0) (get_kind v0 K0) = Some (k, l) ->
  Body.unify h (l ++ pairs) (remove_env (remove_env K0 v) v0 & v0 ~ k)
         (compose (v ~ typ_fvar v0) S0) = Some (K, S) ->
  is_subst (compose (v ~ typ_fvar v0) S0) ->
  fvs (compose (v ~ typ_fvar v0) S0)
    (remove_env (remove_env K0 v) v0 & v0 ~ k) E T Ts << fvs S K E T Ts ->
  fvs S0 K0 E T Ts << fvs S K E T Ts.
Proof.
  unfold fvs.
  intros until h; intros HK0 n R3 HU HSv HS.
  unfold compose in HS. repeat rewrite dom_concat in HS.
  rewrite dom_map in HS. repeat rewrite fv_in_concat in HS.
  simpl in HS.
  do 2 rewrite dom_remove_env in HS; auto.
  intros y Hy.
  sets_solve.
        apply* HS.
      apply HS.
      destruct* (S.union_1 (fv_in_typ_subst (v ~ typ_fvar v0) _ H)).
      simpl in H0; sets_solve.
    apply HS.
    destruct (v == y). subst*.
    destruct* (v0 == y). subst*.
  poses Hun (unify_types _ _ _ HU HSv).
  destruct (unify_kinds_sound _ _ (S:=S) R3).
    intro; intros. apply* Hun.
  puts (kind_fv_in_remove_env v _ H).
  destruct (S.union_1 H2); clear H H2 Hun.
    destruct* (S.union_1 (kind_fv_subst_keep S _ H3)); clear H1 H3.
    puts (kind_entails_fv _ _ H0 H).
    destruct* (S.union_1 (kind_fv_subst _ _ H1)).
  puts (kind_fv_in_remove_env v0 _ H3).
  destruct* (S.union_1 H); clear H H0 H3 R3.
  unfold get_kind in *.
  case_rewrite (get v0 K0) R3.
    rewrite (binds_remove_env (v:=v) R3) in H2.
      destruct* (S.union_1 (kind_fv_subst_keep S _ H2)); clear H2.
      puts (kind_entails_fv _ _ H1 H).
      use (S.union_1 (kind_fv_subst _ _ H0)).
    auto*.
  rewrite get_notin_dom in H2. elim (in_empty H2).
  rewrite* dom_remove_env.
  intro. elim (get_none_notin _ R3). eauto with sets.
Qed.

Lemma kind_subst_id : forall k, kind_subst id k = k.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|]; simpl*.
  apply* kind_pi.
  simpl; clear kh.
  induction kr; simpl*; rewrite typ_subst_id; rewrite* IHkr.
Qed.

Lemma get_kind_fv_in : forall K v,
  kind_fv (get_kind v K) << fv_in kind_fv K.
Proof.
  unfold get_kind.
  introv y Hy.
  case_rewrite (get v K) R1.
    apply (fv_in_spec _ R1 Hy).
  elim (in_empty Hy).
Qed.

Lemma unify_keep_fv : forall K S E T Ts h pairs K0 S0,
  Body.unify h pairs K0 S0 = Some (K, S) ->
  is_subst S0 -> ok K0 ->
  fvs S0 K0 E T Ts << fvs S K E T Ts.
Proof.
  induction h; introv HU HS0 HK0. discriminate.
  simpl in HU.
  destruct pairs. inversions HU. apply subset_refl.
  destruct p.
  case_rewrite (typ_subst S0 t) R1; case_rewrite (typ_subst S0 t0) R2.
        destruct (n === n0); try discriminate.
        apply* IHh.
       apply* unify_keep_fv_nv.
      apply* unify_keep_fv_nv.
     destruct (v == v0).
       apply* IHh.
     unfold unify_vars in HU.
     case_rewrite (unify_kinds (get_kind v K0) (get_kind v0 K0)) R3.
     destruct p.
     assert (ok (remove_env (remove_env K0 v) v0 & v0 ~ k)).
       apply* ok_push.
       rewrite* dom_remove_env.
     assert (HSv: is_subst (compose (v ~ typ_fvar v0) S0)) by auto*.
     destruct (IHh _ _ _ HU HSv H) as [HS HF]; clear IHh H.
     apply* unify_keep_fvs_vars.
    apply* unify_keep_fv_nv.
   apply* unify_keep_fv_nv.
  apply* IHh.
Qed.

Definition moregen_scheme K M0 M :=
  forall Ys, fresh (dom K) (sch_arity M) Ys -> scheme M ->
    exists Ts,
      proper_instance (K & kinds_open_vars (sch_kinds M) Ys) M0 Ts
      /\ sch_open M0 Ts = sch_open M (typ_fvars Ys).

Definition moregen_env K E0 E :=
  dom E0 = dom E /\
  forall x M, binds x M E ->
    exists M0, binds x M0 E0 /\ moregen_scheme K M0 M.

Lemma kinds_subst_open_combine : forall Xs Us Ks,
  fresh (kind_fv_list Ks) (length Xs) Xs ->
  types (length Xs) Us ->
  List.map (kind_subst (combine Xs Us)) (kinds_open Ks (typ_fvars Xs)) =
  kinds_open Ks Us.
Proof.
  intros.
  set (Ks' := Ks).
  assert (incl Ks' Ks) by auto.
  clearbody Ks'.
  induction Ks'; intros. auto.
  simpl in *.
  rewrite* IHKs'.
  rewrite* <- (@kind_subst_open_combine Xs Us Ks).
Qed.

Lemma moregen_scheme_refl : forall K M, moregen_scheme K M M.
Proof.
  intros; intro; intros.
  esplit; split*.
  split. rewrite (fresh_length _ _ _ H). apply* types_typ_fvars.
  split*.
  unfold kinds_open_vars.
  apply (@well_kinded_combine K (sch_kinds M) Ys nil).
  apply H.
Qed.

Lemma moregen_env_refl : forall K E, moregen_env K E E.
Proof.
  intros; split*; intro; intros.
  esplit; split*.
  apply moregen_scheme_refl.
Qed.

Lemma unify_complete' : forall S0 K0 S K T1 T2,
  is_subst S0 -> ok K0 -> extends S S0 ->
  typ_subst S T1 = typ_subst S T2 ->
  well_subst K0 K S ->
  exists K', exists S',
    unify K0 T1 T2 S0 = Some (K', S') /\ extends S S' /\ well_subst K' K S.
Proof.
  intros.
  assert (unifies S ((T1,T2)::nil)).
    intro; simpl; intros. destruct* H4; inversions* H4.
  case_eq (unify K0 T1 T2 S0); unfold unify; intros.
    destruct p as [K' S']. esplit; esplit; split*.
    apply* (unify_mgu0 _ H5 (K':=K) (S':=S)).
  elimtype False.
  refine (unify_complete0 (K:=K) (S:=S) _ _ _ _ _ _ H5); auto.
Qed.

Lemma unify_idem : forall K S h pairs,
  unifies S pairs ->
  is_subst S ->
  h > size_pairs S K pairs ->
  Body.unify h pairs K S = Some (K, S).
Proof.
  induction h using math_ind; intros.
  destruct h.
    elimtype False; omega.
  destruct pairs.
    simpl*.
  destruct p; simpl.
  assert (typ_subst S t = typ_subst S t0)
    by (unfold unifies in H0; apply* H0).
  use (size_pairs_grows S K (t,t0) pairs).
  assert (unifies S pairs) by (unfold unifies in *; intros; apply* H0).
  case_eq (typ_subst S t); introv R1; rewrite H3 in R1; rewrite R1.
      destruct* (n === n). apply* H. omega.
    destruct* (v == v). apply* H. omega.
  assert (size_pairs S K ((t1, t1) :: (t2, t2) :: pairs) <
          size_pairs S K ((t, t0) :: pairs)).
    unfold size_pairs, all_size, really_all_fv, all_fv.
    simpl.
    rewrite <- (typ_subst_idem t H1).
    rewrite <- (typ_subst_idem t0 H1).
    rewrite H3.
    rewrite R1; simpl.
    apply pow2exp_lt_le.
      omega.
    assert (forall b a c, a \u (b \u c) = b \u (a \u c)).
      intros. rewrite union_assoc. rewrite (union_comm a).
      rewrite* <- union_assoc.
    rewrite (H6 (typ_fv (typ_subst S t2))).
    repeat rewrite union_assoc.
    omega.
  apply* H.
    intro; simpl; intros. destruct H7. inversions* H7.
    destruct H7. inversions* H7.
    apply* (H5 T1).
  omega.
Qed.

Section Unique_Env.
Variable (A:Set).

Fixpoint make_ok (L:vars) (E:env A) {struct E} : env A :=
  match E with
  | nil => nil
  | a :: E' =>
    if S.mem (fst a) L then make_ok L E'
    else a :: make_ok (S.add (fst a) L) E'
  end.

Lemma make_ok_ok : forall E,
  let E' := make_ok {} E in
  env_incl E E' /\ env_incl E' E /\ ok E'.
Proof.
  intros.
  set (L := {}) in E'.
  assert (ok E' /\ disjoint L (dom E') /\
          forall x, x \notin L -> get x E = get x E').
    unfold E'; clear E'.
    gen L; induction E; intros.
      simpl. intuition.
        fold (@empty A). apply ok_empty.
      intro; auto.
    destruct a.
    simpl in *.
    case_eq (S.mem v L); intros; simpl.
      destruct (IHE L).
      intuition.
      destruct* (x == v).
      subst.
      elim H1; apply* S.mem_2.
    destruct (IHE (S.add v L)).
    intuition.
        apply* ok_cons.
        destruct* (H2 v).
        elim H1; auto with sets.
      disjoint_solve.
        left; intro. elim H1; auto with sets.
      destruct* (v == v0).
      subst.
      use (mem_3 H).
    destruct* (x == v).
    apply H3.
    intro; elim H1. apply* S.add_3.
  intuition; intro; intros.
    unfold binds; rewrite* <- (H2 x).
    intro. elim (in_empty H3).
  unfold binds; rewrite* (H2 x).
  intro. elim (in_empty H3).
Qed.
End Unique_Env.

Definition non_self_binding (p:var*typ) :=
  let (x,a) := p in
  match a with
  | typ_fvar y => if x == y then false else true
  | _ => true
  end.

Lemma filter_env_ok : forall (A:Set) f (E:env A),
  ok E -> ok (filter f E).
Proof.
  intros.
  apply (proj2 (A:=dom (filter f E) << dom E)).
  induction H; intros. simpl.
     split. intros y Hy; auto. fold (@empty A); auto.
  simpl.
  case_eq (f (@pair var A x a)); intros.
    split. simpl.
      destruct IHok. intros y Hy; destruct (S.union_1 Hy); auto with sets.
    apply* ok_cons.
  split*.
  destruct IHok. intros y Hy; auto with sets.
Qed.

Lemma binds_filter : forall (A:Set) f x (a:A) E,
  binds x a (filter f E) -> ok E -> binds x a E /\ f (x,a) = true.
Proof.
  intros.
  poses Hin (get_in H).
  destruct (proj1 (filter_In _ _ _) Hin).
  use (in_ok_binds _ _ H1 H0).
Qed.

Lemma typ_subst_eq_ind : forall S1 S2,
  (forall x, typ_subst S1 (typ_fvar x) = typ_subst S2 (typ_fvar x)) ->
  forall T, typ_subst S1 T = typ_subst S2 T.
Proof.
  induction T; auto. simpl; congruence.
Qed.

Definition ext_subst S :=
  forall x,
    x \notin fv_in typ_fv S \/ typ_subst S (typ_fvar x) = typ_fvar x.

Lemma is_subst_dom : forall S x,
  is_subst S ->  ~ binds x (typ_fvar x) S.
Proof.
  intros; intro.
  use (binds_dom H0).
  destruct* (H _ _ H0 x).
  simpl in H2.
  notin_contradiction.
Qed.

Lemma ext_subst_is_subst : forall S,
  ext_subst S ->
  exists S', is_subst S' /\ forall T, typ_subst S T = typ_subst S' T.
Proof.
  unfold ext_subst; intros.
  destruct (make_ok_ok S).
  destruct H1.
  set (S0 := make_ok {} S) in *.
  exists (filter non_self_binding S0).
  assert (is_subst (filter non_self_binding S0)).
    intro; intros.
    destruct* (binds_filter _ H3).
    use (H1 _ _ H4).
    intro y.
    destruct (H y).
      use (fv_in_spec typ_fv H6).
    simpl in H7.
    left.
    case_eq (get y (filter non_self_binding S0)); introv R1.
      destruct* (binds_filter _ R1).
      use (H1 _ _ H8).
      rewrite H10 in H7.
      subst. simpl in H9.
      destruct* (y == y). discriminate.
    apply (get_none_notin _ R1).
  split*.
  apply typ_subst_eq_ind.
  intro; simpl.
  case_eq (get x (filter non_self_binding S0)); introv R1.
    destruct* (binds_filter _ R1).
    rewrite* (H1 _ _ H4).
  destruct (H x).
    case_eq (get x S); introv R2; auto.
    use (get_in (H0 _ _ R2)).
    case_eq (non_self_binding (x,t)); introv R3.
      use (proj2 (filter_In _ _ _) (conj H5 R3)).
      rewrite (in_ok_binds _ _ H6 (filter_env_ok _ H2)) in R1.
      discriminate.
    simpl in R3.
    destruct t; try discriminate.
    destruct (x == v); try discriminate.
    subst*.
  apply H4.
Qed.

Lemma sch_fv_subst : forall S M,
  sch_fv (sch_subst S M) << sch_fv M \u fv_in typ_fv S.
Proof.
  destruct M as [T Ks].
  unfold sch_fv, sch_subst; simpl.
  intros y Hy; sets_solve.
    use (typ_fv_subst S _ H).
  induction Ks; simpl in *. auto.
  sets_solve.
    use (kind_fv_subst S _ H0).
  use (IHKs H0).
Qed.

Lemma in_kind_fv : forall k Ks,
  In k Ks -> kind_fv k << kind_fv_list Ks.
Proof.
  induction Ks; simpl; intros; intros y Hy. elim H.
  destruct H. subst*.
  use (IHKs H _ Hy).
Qed.

Lemma proper_instance_inf : forall K M Us Ys M' Vs M0 S,
  proper_instance K M Us ->
  proper_instance (K & kinds_open_vars (sch_kinds M) Ys) M' Vs ->
  fresh (dom K \u fv_in kind_fv K \u sch_fv M \u sch_fv M0 \u fv_in typ_fv S)
    (sch_arity M) Ys ->
  sch_subst S M0 = M' ->
  proper_instance K M' (List.map (typ_subst (combine Ys Us)) Vs).
Proof.
  intros until S; intros [HUs [_ WUs]] [HVs [HM' WVs]] FrYs HM0.
  split.
    apply* typ_subst_type_list.
    apply list_forall_env_prop.
    apply (proj2 HUs).
  split*.
  assert (HTUs: env_prop type (combine Ys Us)).
    apply list_forall_env_prop.
    apply (proj2 HUs).
  assert (LenYs: length Ys = length Us)
    by (rewrite <- (proj1 HUs); symmetry; auto).
  replace (sch_kinds M')
    with (List.map (kind_subst (combine Ys Us)) (sch_kinds M')).
    rewrite* <- kinds_subst_open.
    apply* For_all2_map.
    intros.
    inversions H. simpl*.
    binds_cases H0.
      rewrite kind_subst_fresh.
        rewrite typ_subst_fresh. apply* wk_kind.
        simpl.
        rewrite* dom_combine.
        rewrite dom_kinds_open_vars in Fr.
          use (binds_dom B).
        apply (fresh_length _ _ _ FrYs).
      rewrite* dom_combine.
      apply disjoint_comm.
      assert (kind_entails (Some k') (Some k)). simpl*.
      use (kind_entails_fv _ _ H0).
      use (fv_in_spec kind_fv B).
      apply* (fresh_disjoint (sch_arity M)).
      apply* fresh_sub.
      apply* subset_trans.
      apply* subset_trans.
      intros y Hy; sets_solve.
    apply* well_kinded_subst.
    apply well_subst_open_vars.
          unfold sch_arity in FrYs. auto.
        unfold sch_fv in FrYs.
        apply* (fresh_resize (sch_arity M)).
      rewrite* <- (fresh_length _ _ _ FrYs).
    intuition.
  rewrite (list_map_ext (sch_kinds M') (kind_subst (combine Ys Us))
               (fun x:kind => x)).
    apply list_map_id.
  intros.
  apply kind_subst_fresh.
  rewrite* dom_combine.
  apply disjoint_comm.
  apply (fresh_disjoint (sch_arity M)).
  rewrite <- HM0 in H.
  unfold sch_subst in H; simpl in H.
  destruct (proj1 (in_map_iff (kind_subst S) _ _) H) as [k1 [Hk1 Bk1]].
  subst x.
  use (kind_fv_subst S k1).
  use (in_kind_fv _ _ Bk1).
  unfold sch_fv in FrYs; simpl in FrYs.
  apply* fresh_sub.
  apply* subset_trans.
  intros y Hy; sets_solve.
Qed.

Lemma sch_open_inf : forall M Us S M0 Vs Ys,
  types (sch_arity M) Us ->
  sch_open (sch_subst S M0) Vs = sch_open M (typ_fvars Ys) ->
  fresh (sch_fv M \u sch_fv M0 \u fv_in typ_fv S) (sch_arity M) Ys ->
  sch_open (sch_subst S M0) (List.map (typ_subst (combine Ys Us)) Vs) =
  sch_open M Us.
Proof.
  introv HUs EVs FrYs.
  assert (HTUs: env_prop type (combine Ys Us)).
    apply list_forall_env_prop.
    apply (proj2 HUs).
  replace (sch_subst S M0) with (sch_subst (combine Ys Us) (sch_subst S M0)).
    rewrite* <- sch_subst_open.
    rewrite EVs.
    rewrite (proj1 HUs) in FrYs.
    rewrite* sch_subst_open.
    rewrite* (fresh_subst _ _ Us FrYs).
    unfold sch_open, sch_subst; simpl.
    rewrite* typ_subst_fresh.
    rewrite dom_combine.
      apply disjoint_comm.
      unfold sch_fv in FrYs.
      apply* (fresh_disjoint (length Us)).
    rewrite* (fresh_length _ _ _ FrYs).
  rewrite* sch_subst_fresh.
  rewrite dom_combine.
    apply disjoint_comm.
    apply (disjoint_subset (@sch_fv_subst S M0) (L3:=mkset Ys)).
    apply* (fresh_disjoint (sch_arity M)).
  rewrite <- (fresh_length _ _ _ FrYs).
  apply (proj1 HUs).
Qed.

Axiom unify_keep_doms : forall h pairs K0 S0 K S,
  Body.unify h pairs K0 S0 = Some (K, S) ->
  dom K0 \u dom S0 << dom K \u dom S.

Lemma unify_fv_dom_var : forall S0 K0 E0 T M0 Xs x,
  typing_fv S0 K0 E0 T << dom K0 ->
  binds x M0 E0 ->
  length (sch_kinds M0) = length Xs ->
  unify_fv S0 (K0 & kinds_open_vars (sch_kinds M0) Xs)
    ((sch_open_vars M0 Xs, T) :: nil) <<
    dom (K0 & kinds_open_vars (sch_kinds M0) Xs).
Proof.
  introv DomK0 B AryM0.
  unfold unify_fv; simpl.
  rewrite fv_in_concat; rewrite dom_concat.
  rewrite* dom_kinds_open_vars.
  intros z Hz.
  sets_solve;
    try solve [apply S.union_2; apply DomK0; unfold typing_fv; auto].
    puts (fv_in_kinds_open_vars _ _ H0).
    sets_solve.
    apply S.union_2; apply DomK0.
    unfold typing_fv, env_fv.
    puts (fv_in_spec sch_fv B).
    use (H _ (S.union_3 _ H1)).
  unfold sch_open_vars, typ_open_vars in H.
  puts (typ_fv_open _ _ H); clear H.
  rewrite typ_fv_typ_fvars in H0.
  sets_solve.
  apply S.union_2; apply DomK0.
  unfold typing_fv, env_fv.
  puts (fv_in_spec sch_fv B).
  use (H0 _ (S.union_2 _ H)).
Qed.

Definition principality S0 K0 E0 S K E t T Ts h :=
  is_subst S0 -> env_prop type S0 ->
  kenv_ok K0 -> disjoint (dom S0) (dom K0) ->
  env_prop scheme E0 -> ok E0 ->
  moregen_env K (map (sch_subst S) E0) E ->
  env_prop type S -> dom S << fvs S0 K0 E0 T Ts ->
  extends S S0 -> well_subst K0 K S ->
  K; E |(false,GcAny)|= t ~: typ_subst S T ->
  trm_depth t < h ->
  exists K', exists S',
    typinf K0 E0 t T Ts S0 h = Some (K', S') /\
    extends S' S0 /\ fvs S0 K0 E0 T Ts << fvs S' K' E0 T Ts /\
    exists S'',
      dom S'' << S.diff (fvs S' K' E0 T Ts) (fvs S0 K0 E0 T Ts) /\
      extends (S & S'') S' /\
      well_subst K' K (S & S'').

Lemma principal_var : forall h Ts S0 K0 E0 S K E x T,
  principality S0 K0 E0 S K E (trm_fvar x) T Ts (Datatypes.S h).
Proof.
  intros; intros HS0 HTS0 HK0 Dis HE0 OkE0 MGE HTS HS Hext WS Typ Hh.
  inversions Typ; clear Typ; try discriminate.
  simpl.
  destruct (proj2 MGE _ _ H5) as [M' [B' MGM]].
  destruct (binds_map_inv _ _ B') as [M0 [HM0 B]].
  rewrite B.
  destruct (var_freshes (fvs S0 K0 E0 T Ts) (sch_arity M0)) as [Xs Fr]; simpl.
  destruct (var_freshes (dom K \u fv_in kind_fv K \u sch_fv M \u sch_fv M0
              \u fv_in typ_fv S) (sch_arity M)) as [Ys FrYs].
  destruct* (MGM Ys) as [Vs [HVs EVs]]. destruct* H6.
  pose (Vs' := List.map (typ_subst (combine Ys Us)) Vs).
  assert (AryM0: sch_arity M0 = length Vs').
    destruct HVs. subst. rewrite sch_arity_subst in H.
    unfold Vs'; rewrite map_length. apply (proj1 H).
  assert (Hsub: forall t, typ_fv t << fvs S0 K0 E0 T Ts ->
                  typ_subst (S & combine Xs Vs') t = typ_subst S t).
    rewrite AryM0 in Fr.
    intros.
    apply* typ_subst_combine_fresh.
    apply* fresh_sub.
  assert (Ok: ok (K0 & kinds_open_vars (sch_kinds M0) Xs)).
    apply* disjoint_ok. unfold kinds_open_vars. apply* ok_combine_fresh.
    rewrite* dom_kinds_open_vars.
     unfold fvs in Fr.
    apply* (fresh_disjoint (sch_arity M0)).
  assert (Hext': extends (S & combine Xs Vs') S0).
    clear -Fr Hext Hsub.
    apply* extends_concat. unfold fvs; intros x Hx; auto with sets.
  assert (PI: proper_instance K M' Vs')
    by (unfold Vs' in *; apply* proper_instance_inf).
  assert (HU: unifies (S & combine Xs Vs') ((sch_open_vars M0 Xs, T) :: nil)).
    subst.
    unfold unifies; simpl; intros.
    destruct* H. inversions H; clear H.
    destruct HVs. rewrite sch_arity_subst in H.
    apply* unifies_open.
        unfold Vs'.
        apply* typ_subst_type_list.
        apply* list_forall_env_prop.
        apply (proj2 (proj1 H6)).
      intros y Hy.
      use (fv_in_spec sch_fv B).
      unfold fvs, env_fv; simpl; sets_solve.
    rewrite <- H0.
    unfold Vs'. apply* (sch_open_inf _ _ _ _ _ (proj1 H6) EVs).
  case_eq
    (unify (K0 & kinds_open_vars (sch_kinds M0) Xs) (sch_open_vars M0 Xs) T S0);
    unfold unify; intros.
    destruct p as [K' S']. esplit; esplit. split*.
    unfold fvs in Fr.
    destruct* (unify_mgu0 (K':=K) (S':=S & combine Xs Vs') _ H).
      intro; intros.
      subst M'.
      apply* (well_subst_concat_abs Xs HTS HS PI (x:=x)).
    destruct* (unify_kinds_ok _ _ H).
      rewrite dom_concat.
      rewrite* dom_kinds_open_vars.
      disjoint_solve.
    split.
      apply (typ_subst_extend _ _ _ HS0 H).
    destruct (unify_keep_fv E0 T Ts _ _ H HS0 Ok).
    split.
      intros y Hy; apply H9; clear -Hy.
      unfold fvs in *.
      rewrite dom_concat; rewrite fv_in_concat.
      sets_solve.
    split.
      intros y Hy.
      assert (unify_fv S' K' nil << dom K').
        apply H10. apply* unify_fv_dom_var.
      unfold typing_fv in Hy; unfold unify_fv in H11.
      destruct* (S.union_1 Hy); clear Hy.
      assert (y # S' -> y \in dom K0 \u dom S0 -> y \in dom K').
        intros Hn Hy.
        assert (y \in dom K' \u dom S').
          refine (unify_keep_doms _ _ _ _ H _).
          rewrite* dom_concat.
        clear H12; sets_solve; auto*.
      unfold typing_fv in DomK0.
      sets_solve.
          apply* H11.
        apply* H13.
        clear -H14 DomK0.
        case_eq (S.mem y (dom S0)); intros.
          use (S.mem_2 H).
        use (mem_3 H); clear H.
        apply S.union_2; apply* DomK0.
      apply* H13.
      clear -H12 DomK0.
      case_eq (S.mem y (dom S0)); intros.
        use (S.mem_2 H).
      use (mem_3 H); clear H.
      apply S.union_2; apply* DomK0.
    exists (combine Xs Vs').
    intuition.
    intros y Hy.
    rewrite dom_combine in Hy.
    apply S.diff_3.
      apply H9.
      unfold fvs.
      rewrite dom_concat.
      rewrite* dom_kinds_open_vars.
    destruct* (fresh_disjoint _ _ _ Fr y).
    rewrite* <- (fresh_length _ _ _ Fr).
  elimtype False.
  refine (unify_complete0 (K:=K) HS0 Ok Hext' HU _ _ H).
    subst; apply* well_subst_concat_abs.
  omega.
Qed.

Lemma typ_subst_type' : forall S T,
  type (typ_subst S T) -> type T.
Proof.
  induction T; simpl; intros; auto.
  inversions H. auto.
Qed.

Lemma fv_subset_abs : forall S K E T Ts X1 X2 x,
  unifies S ((typ_arrow X1 X2, T) :: nil) ->
  fvs S K E T Ts = fvs S K ((x, Sch X1 nil) :: E) X2 (T::Ts).
Proof.
  intros.
  unfold fvs, env_fv; simpl.
  apply eq_ext; intro y; simpl; split; intro Hy.
    union_solve y.
  unfold sch_fv in *.
  union_solve y; try elim (in_empty H1);
    simpl in H1;
    assert (y \in typ_fv (typ_arrow X1 X2)) by (simpl; auto with sets);
    use (typ_fv_subst_keep S _ H0);
    rewrite (H (typ_arrow X1 X2) T) in H2; simpl*;
    destruct (S.union_1 H2); clear H0 H1 H2;
    try (use (typ_fv_subst _ _ H3);
         destruct (S.union_1 H0); clear H3 H0; auto with sets;
         repeat (apply S.union_2; auto 3 with sets));
    repeat apply* S.union_2.
Qed.

Lemma sch_subst_ext_fv : forall S1 S2 M,
  (forall t : typ, typ_fv t << sch_fv M -> typ_subst S1 t = typ_subst S2 t) ->
  sch_subst S1 M = sch_subst S2 M.
Proof.
  intros.
  destruct M as [T Ks].
  unfold sch_subst; simpl.
  rewrite* H.
    rewrite* (list_map_ext Ks (kind_subst S1) (kind_subst S2)).
    intros.
    apply* kind_subst_ext_fv.
    unfold env_fv, sch_fv; simpl.
    intros y Hy.
    assert (y \in kind_fv_list Ks).
      clear -H0 Hy; induction Ks; simpl in *. contradiction.
      destruct H0. subst. auto with sets.
      auto with sets.
    auto with sets.
  unfold env_fv, sch_fv; simpl.
  intros y Hy; auto with sets.
Qed.

Lemma env_subst_ext_fv : forall S1 S2 E,
  (forall t : typ, typ_fv t << env_fv E -> typ_subst S1 t = typ_subst S2 t) ->
  map (sch_subst S1) E = map (sch_subst S2) E.
Proof.
  induction E; simpl; intros. auto.
  destruct a.
  rewrite <- IHE.
    rewrite* (sch_subst_ext_fv S1 S2).
    intros; apply H.
    unfold env_fv; simpl.
    intros y Hy; use (H0 _ Hy); auto with sets.
  intros. apply H.
  intros y Hy.
  unfold env_fv, sch_fv; simpl; auto with sets.
Qed.

Lemma trm_depth_open : forall x t,
  trm_depth (t ^ x) = trm_depth t.
Proof.
  intros; unfold trm_open.
  generalize 0; induction t; intros; simpl*.
  destruct (n0 === n); reflexivity.
Qed.

Lemma unifies_extends : forall S1 S2 l,
  unifies S1 l -> extends S2 S1 -> unifies S2 l.
Proof.
  intros; intro; intros.
  rewrite <- (H0 T1); rewrite <- (H0 T2).
  apply (f_equal (typ_subst S2)).
  apply* H.
Qed.

Lemma type_scheme : forall T,
  type T -> scheme (Sch T nil).
Proof.
  intros; intro; intros.
  destruct Xs; try discriminate.
  unfold typ_open_vars; simpl.
  split*.
  clear -H; induction H; simpl*.
Qed.

Lemma principal_abs : forall h Ts S0 K0 E0 S K E t1 T,
  (forall Ts S0 K0 E0 S K E t T, principality S0 K0 E0 S K E t T Ts h) ->
  principality S0 K0 E0 S K E (trm_abs t1) T Ts (Datatypes.S h).
Proof.
  intros until T.
  intros IHh HS0 HTS0 HK0 Dis HE0 OkE0 MGE HTS HS Hext WS Typ Hh.
  simpl.
  destruct (var_fresh (fvs S0 K0 E0 T Ts)) as [x1 Fr1]; simpl.
  destruct (var_fresh (fvs S0 K0 E0 T Ts \u {{x1}})) as [x2 Fr2]; simpl.
  destruct (var_fresh (dom E0 \u trm_fv t1)) as [x Frx]; simpl.
  inversions Typ; try discriminate.
  pose (Xs := x1 :: x2 :: nil).
  pose (Us := U :: T0 :: nil).
  assert (Fr: fresh (fvs S0 K0 E0 T Ts) 2 Xs) by simpl*.
  assert (Hsub: forall t, typ_fv t << fvs S0 K0 E0 T Ts ->
                  typ_subst (S & combine Xs Us) t = typ_subst S t).
    intros.
    apply* typ_subst_combine_fresh.
    apply* fresh_sub.
  assert (Hext': extends (S & combine Xs Us) S0).
    apply* extends_concat. unfold fvs; intros y Hy; auto with sets.
  assert (HU: unifies (S & combine Xs Us)
                ((typ_arrow (typ_fvar x1) (typ_fvar x2), T) :: nil)).
    intro; intros.
    simpl in H; destruct* H. inversions H; clear H.
    rewrite (typ_subst_combine_fresh S T2).
      simpl. destruct* (x1 == x1).
      destruct* (x2 == x1).
        elim Fr2. rewrite e0. auto with sets.
      destruct* (x2 == x2).
    simpl length. unfold fvs in Fr. auto.
  case_eq (unify K0 (typ_arrow (typ_fvar x1) (typ_fvar x2)) T S0);
    unfold unify; intros.
    destruct p as [K' S'].
    destruct* (unify_mgu0 _ H (K':=K) (S':=S & combine Xs Us)).
      intro; intros.
      rewrite* (kind_subst_ext_fv (L:=fvs S0 K0 E0 T Ts) S (S & combine Xs Us)).
        rewrite Hsub. apply* WS.
        simpl; unfold fvs.
        use (binds_dom H1).
        intros y Hy. rewrite <- (S.singleton_1 Hy). auto 6 with sets.
      intros y Hy.
      unfold fvs.
      use (fv_in_spec kind_fv H1).
      auto with sets.
    destruct* (unify_type _ _ H).
      simpl; intros.
      destruct* H5. inversions* H5.
      split*. apply* (typ_subst_type' S).
    destruct* (unify_kinds_ok _ _ H).
    poses Uk (unify_keep_fv _ _ H (E:=E0) (T:=T) (Ts:=Ts) HS0 (proj1 HK0)).
    poses UT (unify_types _ _ _ H HS0).
    destruct* (IHh (T::Ts) S' K' (E0 & x ~ Sch (typ_fvar x1) nil)
                   (S & combine Xs Us) K (E & x ~ Sch U nil)
                   (t1 ^ x) (typ_fvar x2)).
          apply* env_prop_concat. intro; intros.
          destruct (binds_single_inv H9). subst.
          apply* type_scheme.
         rewrite map_concat.
         rewrite (env_subst_ext_fv (S & combine Xs Us) S).
           split. repeat rewrite dom_concat.
           rewrite (proj1 MGE). simpl*.
           intro; intros.
           binds_cases H9.
             destruct (proj2 MGE _ _ B) as [M' [BM' MGM']].
             exists M'. split*.
           destruct (binds_single_inv B0). subst.
           exists (Sch U nil).
           split.
             apply binds_prepend.
             unfold binds; simpl. destruct* (x0 == x0).
             unfold sch_subst; simpl. destruct* (x1 == x1).
           apply moregen_scheme_refl.
           intros. apply Hsub.
           eapply subset_trans. apply H9.
         intros y Hy; unfold fvs; auto with sets.
        apply* env_prop_concat.
        unfold Xs, Us.
        intro; unfold binds; simpl; intros.
        rewrite <- H0 in Typ.
        use (proj44 (typing_regular Typ)).
        inversions H10.
        destruct (x0 == x1). inversion H9. rewrite* <- H12.
        destruct (x0 == x2). inversion H9. rewrite* <- H12.
        discriminate.
       clear -Uk UT HS.
       rewrite dom_concat.
       intros y Hy.
       destruct (S.union_1 Hy); clear Hy.
         use (Uk _ (HS _ H)).
         clear -H0; unfold fvs, env_fv in *; simpl in *.
         union_solve y.
       unfold Xs, Us in H; simpl in H.
       unfold fvs, env_fv, sch_fv; simpl.
       clear -H; union_solve y.
      simpl typ_subst.
      destruct (x2 == x1). elim Fr2. rewrite e. auto with sets.
      destruct* (x2 == x2). clear n e.
      destruct (var_fresh (L \u trm_fv t1 \u {{x}})) as [x0 Fr0].
      forward~ (H4 x0); intros.
      apply* typing_abs_rename. auto.
      destruct (x == x0). elim Fr0; subst. auto with sets.
      rewrite <- (proj1 MGE). rewrite dom_map. auto.
     simpl in Hh.
     rewrite trm_depth_open. omega.
    destruct H9 as [S2 [TI [Hext2 [HS2 [S3 [HS3 [Hext3 WS3]]]]]]].
    esplit; esplit; split*.
    split.
      apply* extends_trans.
      apply* typ_subst_extend.
    split.
      intros y Hy.
      use (Uk _ Hy); clear Uk.
      rewrite (fv_subset_abs K' E0 Ts x UT) in H9.
      use (HS2 _ H9).
      rewrite* (fv_subset_abs x0 E0 Ts x (unifies_extends UT Hext2)).
    exists (combine Xs Us & S3).
    rewrite <- concat_assoc.
    split*.
    rewrite dom_concat.
    intros y Hy.
    rewrite (fv_subset_abs x0 E0 Ts x (unifies_extends UT Hext2)).
    destruct (S.union_1 Hy); clear Hy.
      apply S.diff_3.
        clear -H9. simpl in H9.
        unfold fvs, env_fv, sch_fv; simpl.
        union_solve y.
      rewrite dom_combine in H9.
        destruct* (fresh_disjoint _ _ _ Fr y).
      simpl*.
    simpl in HS3; rewrite <- (fv_subset_abs K' E0 Ts x UT) in HS3.
    use (HS3 _ H9).
    apply* S.diff_3. use (S.diff_1 H10).
    use (S.diff_2 H10).
  elimtype False.
  refine (unify_complete0 (K:=K) HS0 (proj1 HK0) Hext' HU _ _ H).
    apply* well_subst_concat.
  omega.
Qed.

Lemma fv_in_kind_subst : forall S K,
  fv_in kind_fv (map (kind_subst S) K) << fv_in kind_fv K \u fv_in typ_fv S.
Proof.
  induction K; simpl; intros y Hy. elim (in_empty Hy).
  destruct a. simpl in Hy.
  destruct (S.union_1 Hy); clear Hy.
    destruct (S.union_1 (kind_fv_subst S _ H)); auto with sets.
  destruct (S.union_1 (IHK _ H)); auto with sets.
Qed.

Lemma ok_map_inv : forall (A:Set) (f:A->A) E, ok (map f E) -> ok E.
Proof.
  induction E; intro. auto.
  destruct a. simpl in H. inversions H.
  apply* ok_cons.
Qed.

Lemma combine_For_all2 : forall (A B:Set) (P:A->B->Prop) l1 l2,
  length l1 = length l2 ->
  (forall a b, In (a,b) (combine l1 l2) -> P a b) ->
  For_all2 P l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros; try discriminate; auto*.
Qed.

Lemma list_map_combine_swap : forall (A B C D:Set) (f1:A->C) (f2:B->D) l1 l2,
  List.map (fun p:A*B => (f2 (snd p), f1 (fst p))) (combine l1 l2) =
  combine (List.map f2 l2) (List.map f1 l1).
Proof.
  induction l1; destruct l2; simpl; intros; auto.
  rewrite* IHl1.
Qed.

Lemma well_subst_For_all2: forall K Ks Xs Vs,
  well_subst (K & kinds_open_vars Ks Xs) K (combine Xs Vs) ->
  fresh (kind_fv_list Ks) (length Ks) Xs ->
  types (length Xs) Vs ->
  For_all2 (well_kinded K) (kinds_open Ks Vs) Vs.
Proof.
  introv WS Fr HVs.
  apply combine_For_all2.
    unfold kinds_open. rewrite map_length. rewrite (fresh_length _ _ _ Fr).
    apply (proj1 HVs).
  intros.
  replace (combine (kinds_open Ks Vs) Vs) with
    (List.map (fun p:var*kind =>
      (kind_subst (combine Xs Vs) (snd p),
       typ_subst (combine Xs Vs) (typ_fvar (fst p)))) (kinds_open_vars Ks Xs))
    in H.
    destruct (proj1 (in_map_iff _ _ _) H) as [[x k] [HE HB]].
    simpl in HE; inversions HE; clear HE H.
    apply (WS x).
    apply binds_prepend.
    apply* in_ok_binds.
    unfold kinds_open_vars. apply* ok_combine_fresh.
  unfold kinds_open_vars.
  rewrite (list_map_combine_swap
    (fun x => typ_subst (combine Xs Vs) (typ_fvar x))
    (kind_subst (combine Xs Vs))).
  rewrite <- (map_map typ_fvar (typ_subst (combine Xs Vs))).
  rewrite kinds_subst_open.
    rewrite <- (fresh_length _ _ _ Fr) in HVs.
    rewrite (proj1 HVs) in Fr.
    fold (typ_fvars Xs).
    rewrite (fresh_subst _ _ _ Fr).
    rewrite (list_map_ext Ks (kind_subst (combine Xs Vs)) (fun k => k)).
      rewrite* list_map_id.
    intros.
    use (in_kind_fv _ _ H0).
    rewrite* kind_subst_fresh.
    rewrite dom_combine.
      apply disjoint_comm.
      apply (fresh_disjoint (length Vs)).
      apply* fresh_sub.
    rewrite* (fresh_length _ _ _ Fr).
  apply* list_forall_env_prop.
  apply (proj2 HVs).
Qed.

Lemma sch_open_vars_type : forall M Xs,
  scheme M -> sch_arity M = length Xs -> type (sch_open_vars M Xs).
Proof.
  unfold sch_open_vars, typ_open_vars.
  intros; fold (sch_open M (typ_fvars Xs)).
  apply sch_open_types. auto.
  rewrite H0. apply types_typ_fvars.
Qed.

Theorem typinf_principal : forall h Ts S0 K0 E0 S K E t T,
  principality S0 K0 E0 S K E t T Ts h.
Proof.
  induction h; intros until T;
    intros HS0 HTS0 HK0 Dis HE0 OkE0 MGE HTS HS Hext WS Typ Hh;
    try (elimtype False; omega).
  inversions Typ.
  apply* (@principal_var h Ts S0 K0 E0 S K E).
  apply* (@principal_abs h Ts S0 K0 E0 S K E).


Lemma principal_let : forall h Ts S0 K0 E0 S K E t1 t2 T,
  (forall Ts S0 K0 E0 S K E t T, principality S0 K0 E0 S K E t T Ts h) ->
  principality S0 K0 E0 S K E (trm_let t1 t2) T Ts (Datatypes.S h).
Proof.
  intros until T.
  intros IHh HS0 HTS0 HK0 Dis HE0 OkE0 MGE HTS HS Hext WS Typ Hh.
  simpl.
  destruct (var_fresh (fvs S0 K0 E0 T Ts)) as [x1 Fr1]; simpl.
  destruct (var_fresh (dom E0 \u trm_fv t1 \u trm_fv t2)) as [x Frx]; simpl.
  inversions Typ; try discriminate.
  destruct (var_freshes (L1 \u fvs S0 K0 E0 T Ts \u {{x1}}) (sch_arity M))
    as [Xs Fr].
  forward~ (H3 Xs); clear H3; intros Typ1.
  set (MXs := sch_open_vars M Xs) in *.
  assert (Hcb: x1 ~ MXs = combine (x1::nil) (MXs :: nil)) by simpl*.
  assert (HSx1: dom (S & x1 ~ MXs) << fvs S0 K0 E0 (typ_fvar x1) (T :: Ts)).
    rewrite dom_concat; unfold fvs; simpl.
    intros y Hy; union_solve y.
    use (HS _ H). unfold fvs in H0; simpl in H0; union_solve y.
    elim (in_empty H0).
  assert (Hsub: forall t, typ_fv t << fvs S0 K0 E0 T Ts ->
                  typ_subst (S & x1 ~ MXs) t = typ_subst S t).
    intros.
    apply typ_subst_concat_fresh.
    simpl. intro y; destruct* (y == x1).
  assert (Hext0: extends (S & x1 ~ MXs) S0).
    rewrite Hcb.
    apply* (@extends_concat S0 S (fvs S0 K0 E0 T Ts) 1).
    intros y Hy; unfold fvs; auto with sets.
  destruct* (IHh (T::Ts) S0 K0 E0 (S & x1 ~ MXs)
                (K & kinds_open_vars (sch_kinds M) Xs) E t1 (typ_fvar x1))
    as [K' [S' [HI [Hext' [Hfvs' H'']]]]].
      split. rewrite <- (proj1 MGE). repeat rewrite* dom_map.
      intros. destruct (proj2 MGE _ _ H) as [M1 [BM1 MGM1]].
      exists M1.
      rewrite (env_subst_ext_fv (S & x1 ~ MXs) S).
        split*.
        intro; intros.
        rewrite dom_concat in H0.
        destruct* (MGM1 Ys).
        exists x2.
        split*.
        destruct H2. destruct H2.
        split*. split*.
        destruct H4.
        apply* For_all2_imp.
        intros. apply* well_kinded_weaken.
        rewrite <- dom_concat in H0.
        apply* disjoint_ok.
          unfold kinds_open_vars. apply* ok_combine_fresh.
        rewrite* dom_kinds_open_vars. apply* fresh_disjoint.
      intros. apply Hsub. apply* subset_trans.
      intros y Hy; unfold fvs; auto with sets.
     rewrite Hcb.
     apply* well_subst_concat.
     apply* well_subst_extends.
     intro; intros.
     apply* well_kinded_extend.
     apply* ok_disjoint.
    simpl typ_subst. destruct* (x1 == x1).
   simpl in Hh.
   eapply Lt.le_lt_trans. apply (Max.le_max_l (trm_depth t1) (trm_depth t2)).
   omega.
  rewrite HI.
  case_eq (split_env
              (close_fvk (map (kind_subst S') K')
                 (env_fv (map (sch_subst S') E0) \u vars_subst S' (dom K0)))
              (map (kind_subst S') K')); intros.
  fold (typ_subst S' (typ_fvar x1)).
  case_eq (split_env (close_fvk (map (kind_subst S') K')
                 (typ_fv (typ_subst S' (typ_fvar x1)))) e); intros.
  case_eq (split e2); intros.
  set (M0 := sch_generalize l (typ_subst S' (typ_fvar x1)) l0).
  destruct* (typinf_sound _ _ _ HI).
  destruct* (split_env_ok _ H).
  assert (Oke: kenv_ok (e0 & e)).
    split*. intro; intuition.
    use (proj2 (kenv_ok_map H9 H7)).
  clear H4.
  assert (Oke1: kenv_ok (e2 & e1)).
    destruct (kenv_ok_concat_inv _ _ Oke).
    destruct* (split_env_ok _ H0).
    split*. intro; intuition. apply* (proj2 Oke).
  assert (HM0: scheme M0).
    unfold M0; apply* scheme_generalize.
    destruct (kenv_ok_concat_inv _ _ Oke1).
    use (split_combine e2).
    rewrite H1 in H8.
    rewrite <- H8 in H4; destruct H4.
    apply* env_prop_list_forall.
  destruct* (IHh Ts S' e0 (E0 & x ~ M0) (S & x1 ~ MXs) K (E & x~M) (t2 ^ x) T)
    as [K'' [S'' [HI' [Hext'' [Hfvs'' H''']]]]].
          destruct* (kenv_ok_concat_inv _ _ Oke).
         intuition.
         intro y; destruct (H10 y). auto.
         poses Hs (env_incl_subset_dom H12).
         rewrite dom_map in Hs.
         use (notin_subset Hs H13).
        split. repeat rewrite dom_concat.
        rewrite <- (proj1 MGE). repeat rewrite dom_map.
        rewrite dom_concat; simpl*.
        intros.
        binds_cases H4.
          destruct (proj2 MGE _ _ B) as [M2 [BM2 HM2]].
          exists M2.
          split*.
          apply binds_concat_fresh.
            rewrite (env_subst_ext_fv (S & x1 ~ MXs) S). auto.
            intros; apply Hsub.
            apply* subset_trans. intros y Hy; unfold fvs; auto with sets.
          rewrite dom_map. simpl. auto.
        destruct (binds_single_inv B0); subst.
        exists (sch_subst (S & x1 ~ MXs) M0).
        clear H4 B0 H8.
        split. unfold binds. simpl. destruct* (x0 == x0).
Lemma typ_fv_generalize : forall Xs T,
  typ_fv (typ_generalize Xs T) << typ_fv T.
Proof.
  induction T; simpl; intros y Hy. auto.
    destruct (index eq_var_dec 0 v Xs).
      elim (in_empty Hy).
    apply Hy.
  destruct (S.union_1 Hy); auto with sets.
Qed.
Lemma close_fvk_ok2 : forall K L L',
  ok K -> L' << close_fvk K L -> close_fvk K L' << close_fvk K L.
Proof.
  intros.
  intros y Hy.
  unfold close_fvk in Hy.
  use (cardinal_env H).
  revert L' H0 Hy H1; generalize (dom K).
  induction (length K); simpl; intros. auto.
  case_rewrite (S.choose (S.inter v L')) R1.
    assert (e \in close_fvk K L).
      apply H0.
      apply (S.inter_2 (s:=v)).
      apply* S.choose_1.
    assert (S.cardinal (S.remove e v) = n).
      assert (e \in v) by eauto with sets.
      use (cardinal_remove H3).
      rewrite H1 in H4.
      inversion* H4.
    case_rewrite (get e K) R2.
      use (close_fvk_ok L H H2 R2).
      assert (L' \u kind_fv k << close_fvk K L).
        intros z Hz. destruct (S.union_1 Hz); auto with sets.
      apply* (IHn _ _ H5 Hy).
    apply* (IHn _ _ H0 Hy).
  auto with sets.
Qed.
Lemma moregen_let :
  forall M Xs S' x1 l l0 S0 T Ts (K' K0 K:kenv) E0 E S S'' e e0 e1 e2,
  let MXs := sch_open_vars M Xs in
  let M0 := sch_generalize l (typ_subst S' (typ_fvar x1)) l0 in
  moregen_env K (map (sch_subst S) E0) E ->
  split_env (close_fvk (map (kind_subst S') K')
    (env_fv (map (sch_subst S') E0) \u vars_subst S' (dom K0)))
    (map (kind_subst S') K') = (e, e0) ->
  split_env (close_fvk (map (kind_subst S') K')
    (typ_fv (typ_subst S' (typ_fvar x1)))) e = (e1, e2) ->
  split e2 = (l, l0) ->
  extends (S & x1 ~ MXs & S'') S' ->
  fresh (fvs S0 K0 E0 T Ts \u {{x1}} \u env_fv E \u sch_fv M \u fv_in kind_fv K)
    (sch_arity M) Xs ->
  is_subst S' -> env_prop type S' -> env_prop type S -> env_prop type S'' ->
  kenv_ok (e0 & e) -> kenv_ok (e2 & e1) -> ok K' ->
  well_subst K' (K & kinds_open_vars (sch_kinds M) Xs) (S & x1 ~ MXs & S'') ->
  moregen_scheme K (sch_subst (S & x1 ~ MXs) M0) M.
Proof.
  intros until M0.
  intros MGE R1 R2 R3 Hext Fr HS' HTS' HTS HTS'' Oke0 Oke2 Ok' WS.
  intro; intros.
  assert (type (typ_subst S' (typ_fvar x1))) by auto.
  assert (env_prop type (S & x1 ~ MXs)).
    apply* env_prop_concat.
    intro; intros. destruct (binds_single_inv H2); subst.
    unfold MXs.
    apply* sch_open_vars_type.
  assert (env_prop type (S & x1 ~ MXs & S'')) by apply* env_prop_concat.
  assert (x1 \in sch_fv M0 -> M0 = Sch (typ_fvar x1) nil).
    unfold sch_fv; intro.
    destruct (S.union_1 H4).
      unfold M0 in H5; simpl in H5.
      case_rewrite (get x1 S') R4.
        destruct (HS' _ _ R4 x1).
          elim (binds_fresh R4 H6).
        elim H6. apply* (typ_fv_generalize l).
      unfold M0. simpl. rewrite R4.
      simpl in R2; rewrite R4 in R2; simpl in R2.
      destruct (split_env_ok _ R2).
        destruct* (ok_concat_inv _ _ (proj1 Oke0)).
      assert (x1 # e).
        intro.
        assert (x1 \in dom (e2 & e1)).
          apply (env_incl_subset_dom (proj43 H7) H8).
        rewrite dom_concat in H9; destruct (S.union_1 H9); clear H8 H9.
          destruct* (typ_generalize_disjoint l (typ_fvar x1) x1).
          use (split_combine e2). rewrite R3 in H9.
          rewrite <- (dom_combine l l0) in H8.
            rewrite H9 in H8; auto.
          apply* split_length.
        destruct* ((proj41 H7) x1).
        elim H8.
        apply* close_fvk_subset.
      set (SK' := map (kind_subst S') K') in *.
      set (L0 := env_fv (map (sch_subst S') E0) \u vars_subst S' (dom K0)) in *.
      assert (disjoint (dom e) (close_fvk SK' {{x1}})).
        destruct* (split_env_ok _ R1). unfold SK'; auto.
        case_eq (get x1 SK'); introv R5.
          assert (x1 \in dom (e0 & e)).
            apply (env_incl_subset_dom (proj43 H10) (binds_dom R5)).
          rewrite dom_concat in H11.
          destruct* (S.union_1 H11); clear H11.
          assert ({{x1}} << close_fvk (map (kind_subst S') K') L0).
            intros y Hy.
            rewrite <- (S.singleton_1 Hy).
            apply* (proj42 H10).
          use (close_fvk_ok2 _ (ok_map0 (kind_subst S') Ok') H11).
          intro y. destruct* ((proj41 H10) y).
        unfold close_fvk.
        destruct (length SK'). simpl*.
        simpl.
        case_eq (S.choose (S.inter (dom SK') {{x1}})); introv R6.
          use (S.choose_1 R6).
          use (S.inter_1 H11).
          use (S.inter_2 H11).
          rewrite <- (S.singleton_1 H13) in H12.
          elim (get_none_notin _ R5 H12).
        auto.
      assert (e2 = empty).
        destruct* e2.
        destruct p.
        use (env_incl_subset_dom (proj44 H7)).
        rewrite dom_concat in H11.
        assert (a \in dom e) by auto with sets. 
        destruct* (H9 a).
        elim H13. apply* (proj42 H7).
        elim (in_empty H10).
      use (split_combine e2).
      rewrite R3 in H11.
      rewrite <- H11 in H10.
      rewrite dom_combine 
    

  intros.
  intros y Hy.
  unfold close_fvk in *.
  use (close_fvk_ok _ H0 Hy).
  use close
            apply (binds_dom x1 (kind_subst S').
            apply binds_map. (binds_dom R5)).
            
          
          

        destruct (split_env_ok _ R1).
          apply* ok_map0.
        
      
        Print is_subst.
        use (typ_subst_res_fresh (typ_fvar x1) (T':=T) HS').
  use (typ_generalize_reopen l H1).
  fold M0 in H4.
  use (f_equal (typ_subst (S & x1 ~ MXs & S'')) H4).
  rewrite typ_subst_open in H5; auto.
  exists (List.map (typ_subst (compose (combine Xs (typ_fvars Ys))
            (S & x1 ~ MXs & S''))) (typ_fvars l)).
  rewrite Hext in H5.
  unfold sch_open.
  split.
    split.
      rewrite sch_arity_subst.
      split. rewrite map_length.
        unfold M0.
        unfold sch_generalize, sch_arity.
        simpl.
        rewrite map_length. unfold typ_fvars; rewrite map_length.
        rewrite* (split_length _ R3).
      remember (S & x1 ~ MXs & S'') as S1.
      apply (list_forall_map
        (typ_subst (compose (combine Xs (typ_fvars Ys)) S1)) (PA:=type)).
        intros. rewrite* typ_subst_compose.
        apply* typ_subst_type.
        apply list_forall_env_prop.
        refine (proj2 (types_typ_fvars _)).
      refine (proj2 (types_typ_fvars _)).
    split.
      apply* sch_subst_type.
      unfold M0; apply* scheme_generalize.
      use (split_combine e2). rewrite R3 in H6.
      destruct (kenv_ok_concat_inv _ _ Oke1).
      eapply env_prop_list_forall.
      instantiate (1:=l). rewrite H6.
      apply (proj2 H8).
      rewrite* H6.
      apply* split_length.
    refine (well_subst_For_all2 _ l _ _ _).
      intro; intros.

  simpl typ_subst in H3.
  replace (sch_open M (typ_fvars Ys))
    with (typ_subst (combine Xs (typ_fvars Ys)) MXs).
  assert 

        intro; intros.

        apply (proj2 MGE x0).
       intuition.
       eapply subset_trans. apply HSx1.
       eapply subset_trans. apply Hfvs'.
       intuition.
       

Qed.

End Mk2.
End MkInfer.