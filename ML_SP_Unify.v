(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure Cardinal.
(* Require Import ML_SP_Soundness. *)

Set Implicit Arguments.

Module MkInfer(Cstr:CstrIntf)(Const:CstIntf).

Module Infra := MkInfra(Cstr)(Const).
Import Infra.
Import Defs.

Definition add_binding x (T:typ) S := map (typ_subst (x ~ T)) S & x ~ T.

Fixpoint unify (pairs:list (typ*typ)) (S:Env.env typ) (h:nat) {struct h}
  : option (Env.env typ) :=
  match h with 0 => None
  | S h' =>
    match pairs with
    | nil => Some S
    | (T1,T2) :: pairs' =>
      match typ_subst S T1, typ_subst S T2 with
      | typ_bvar n, typ_bvar m =>
        if n === m then unify pairs' S h' else None
      | typ_fvar x, typ_fvar y =>
        if x == y then unify pairs' S h' else
        unify pairs' (add_binding x (typ_fvar y) S) h'
      | typ_fvar x, T =>
        if S.mem x (typ_fv T) then None else
        unify pairs' (add_binding x T S) h'
      | T, typ_fvar x =>
        if S.mem x (typ_fv T) then None else
        unify pairs' (add_binding x T S) h'
      | typ_arrow T11 T12, typ_arrow T21 T22 =>
        unify ((T11,T21)::(T12,T22)::pairs') S h'
      | _, _ =>
        None
      end
    end
  end.

Lemma mem_3 : forall v L, S.mem v L = false -> v \notin L.
Proof.
  intros. intro.
  rewrite (S.mem_1 H0) in H.
  discriminate.
Qed.

Hint Resolve mem_3.

Lemma notin_disjoint : forall x L, x \notin L -> disjoint {{x}} L.
Proof.
  intros; intro v. destruct (x == v); try subst; auto.
Qed.

Hint Resolve notin_disjoint.

Lemma binds_map_inv : forall (A:Set) (f:A->A) S x y,
  binds x y (map f S) -> exists z, f z = y /\ binds x z S.
Proof.
  unfold binds.
  induction S; simpl; intros. discriminate.
  destruct a.
  simpl in H.
  destruct (x == v).
  inversions H.
    exists* a.
  apply* IHS.
Qed.

Lemma binds_typ_subst : forall x T S,
  binds x T S -> typ_subst S (typ_fvar x) = T.
Proof.
  intros. simpl. rewrite* H.
Qed.

Definition is_subst S := env_prop (fun T => disjoint (dom S) (typ_fv T)) S.

Lemma disjoint_subst : forall x T L T',
  disjoint (L \u {{x}}) (typ_fv T) ->
  disjoint L (typ_fv T') ->
  disjoint (L \u {{x}}) (typ_fv (typ_subst (x ~ T) T')).
Proof.
  induction T'; simpl; intros.
      intro; auto.
    destruct (v == x).
      subst.
      disjoint_solve.
    simpl.
    assert (disjoint {{v}} {{x}}); disjoint_solve.
    destruct* (v0 == v).
    destruct* (v0 == x).
    subst. elim (n e0).
  assert (disjoint L (typ_fv T'1)) by disjoint_solve.
  assert (disjoint L (typ_fv T'2)) by disjoint_solve.
  use (IHT'1 H H1).
  use (IHT'2 H H2).
  disjoint_solve.
Qed.

Lemma add_binding_is_subst : forall S x T,
  is_subst S ->
  disjoint (dom S \u {{x}}) (typ_fv T) ->
  is_subst (add_binding x T S).
Proof.
  intros.
  unfold add_binding.
  intro; intros.
  binds_cases H1.
    destruct (binds_map_inv _ _ B) as [b [F B']].
    subst.
    use (H _ _ B').
    simpl in *.
    apply* disjoint_subst.
  destruct (binds_single_inv B0); subst.
  auto.
Qed.

Ltac case_rewrite t H :=
  case_eq t; introv H; rewrite H in *; try discriminate.

Lemma map_get_None : forall (A:Set) (f:A->A) v S,
  get v S = None -> get v (map f S) = None.
Proof.
  induction S; simpl; intros. auto.
  destruct a.
  simpl.
  destruct (v == v0). discriminate. auto.
Qed.

Lemma typ_subst_add_binding : forall x T' S T,
  x \notin dom S ->
  typ_subst (add_binding x T' S) T =
  typ_subst (x ~ T') (typ_subst S T).
Proof.
  induction T; simpl; intros; auto.
    destruct (v == x).
      subst.
      case_eq (get x S); intros.
        elim (binds_fresh H0 H).
      simpl. destruct* (x == x).
    case_eq (get v S); intros.
      use (binds_map (typ_subst (x ~ T')) H0).
      unfold binds in H1; rewrite* H1.
    rewrite (map_get_None (typ_subst (x ~ T')) _ _ H0).
    simpl.
    destruct* (v == x).
  rewrite* IHT1.
  rewrite* IHT2.
Qed.

Lemma typ_subst_disjoint : forall S T,
  is_subst S -> disjoint (dom S) (typ_fv (typ_subst S T)).
Proof.
  intros; induction T; simpl in *.
      intro; auto.
    case_eq (get v S); intros.
    use (H _ _ H0).
    use (get_none_notin _ H0).
    simpl; intro x; destruct* (x == v).
  disjoint_solve.
Qed.

Lemma binds_add_binding : forall S T0 T1 v x T,
  is_subst S ->
  typ_subst S T0 = typ_fvar v ->
  binds x (typ_subst S T) S ->
  binds x (typ_subst (add_binding v T1 S) T) (add_binding v T1 S).
Proof.
  intros.
  use (typ_subst_disjoint T0 H).
    rewrite H0 in H2. simpl in H2.
  rewrite* typ_subst_add_binding.
  unfold add_binding.
  apply binds_concat_fresh.
    apply* binds_map.
  destruct* (H2 x).
  elim (binds_fresh H1 H3).
Qed.

Lemma unify_keep : forall h pairs S0 S,
  unify pairs S0 h = Some S ->
  is_subst S0 ->
  is_subst S /\
  forall x T, binds x (typ_subst S0 T) S0 -> binds x (typ_subst S T) S.
Proof.
  induction h; simpl; intros. discriminate.
  destruct pairs.
    inversions H.
    auto.
  destruct p.
  case_rewrite (typ_subst S0 t) R1; case_rewrite (typ_subst S0 t0) R2.
        destruct (n === n0).
          apply* (IHh _ _ _ H).
        discriminate.
       simpl in H.
       case_rewrite (S.mem v {}) R3.
       destruct (IHh _ _ _ H); clear IHh.
         apply* add_binding_is_subst.
         simpl. intro; auto.
       split*.
       intros; apply H2; clear H2.
       apply* binds_add_binding.
      simpl in H.
      destruct (S.mem v {}); try discriminate.
      destruct (IHh _ _ _ H); clear IHh.
        apply* add_binding_is_subst.
        simpl. intro; auto.
      split*.
      intros; apply H2.
      apply* binds_add_binding.
     destruct (v == v0).
       destruct* (IHh _ _ _ H).
     destruct (IHh _ _ _ H); clear IHh.
       apply* add_binding_is_subst.
       simpl.
       use (typ_subst_disjoint t0 H0). rewrite R2 in H1. simpl in H1.
       assert (disjoint {{v}} {{v0}}) by auto.
       disjoint_solve.
     split*.
     intros; apply H2.
     apply* binds_add_binding.
    case_rewrite (S.mem v (typ_fv (typ_arrow t1 t2))) R3.
    destruct (IHh _ _ _ H); clear IHh.
      apply* add_binding_is_subst.
      use (typ_subst_disjoint t0 H0). rewrite R2 in H1.
      use (notin_disjoint (mem_3 R3)).
      disjoint_solve.
    split*.
    intros; apply H2; clear H2.
    apply* binds_add_binding.
   case_rewrite (S.mem v (typ_fv (typ_arrow t1 t2))) R3.
   destruct (IHh _ _ _ H); clear IHh.
     apply* add_binding_is_subst.
     use (typ_subst_disjoint t H0). rewrite R1 in H1.
     use (notin_disjoint (mem_3 R3)).
     disjoint_solve.
    split*.
    intros; apply H2; clear H2.
    apply* binds_add_binding.
  destruct* (IHh _ _ _ H); clear IHh.
Qed.

Lemma typ_subst_idem : forall S T,
  is_subst S -> typ_subst S (typ_subst S T) = typ_subst S T.
Proof.
  intros.
  induction T; simpl. auto.
    case_eq (get v S); intros.
      rewrite* typ_subst_fresh.
      apply (H _ _ H0).
    simpl.
    rewrite* H0.
  simpl; congruence.
Qed.

Lemma binds_subst_idem : forall x T S,
  binds x T S -> is_subst S -> binds x (typ_subst S T) S.
Proof.
  intros.
  use (binds_typ_subst H).
  use (f_equal (typ_subst S) H1).
  rewrite typ_subst_idem in H2; auto.
  congruence.
Qed.

Lemma typ_subst_extend : forall pairs S0 h S T,
  is_subst S0 ->
  unify pairs S0 h = Some S ->
  typ_subst S (typ_subst S0 T) = typ_subst S T.
Proof.
  intros.
  destruct* (unify_keep _ _ H0).
  clear H0.
  induction T; intros. simpl*.
    remember (typ_subst S0 (typ_fvar v)) as T'.
    use (f_equal (typ_subst S0) HeqT').
    rewrite typ_subst_idem in H0; auto.
    simpl in H0.
    case_rewrite (get v S0) R.
      subst.
      use (H2 _ _ R).
      rewrite* (binds_typ_subst H0).
    simpl in HeqT'. rewrite R in HeqT'. subst*.
  simpl. congruence.
Qed.

Lemma unify_var : forall S0 T1 T2 v T pairs h pairs' h' S,
  typ_subst S0 T1 = typ_fvar v ->
  typ_subst S0 T2 = T ->
  unify pairs' S0 h' = Some S ->
  unify pairs (add_binding v T S0) h = Some S ->
  is_subst S0 ->
  v \notin typ_fv T ->
  typ_subst S T1 = typ_subst S T2.
Proof.
  intros.
  assert (is_subst (add_binding v T S0)).
    apply* add_binding_is_subst.
    use (typ_subst_disjoint T2 H3).
    rewrite H0 in H5.
    use (notin_disjoint H4).
    disjoint_solve.
  rewrite <- (typ_subst_extend _ _ T1 H3 H1).
  rewrite H.
  rewrite <- (typ_subst_extend _ _ (typ_fvar v) H5 H2).
  rewrite <- (typ_subst_extend _ _ T2 H3 H1).
  apply (f_equal (typ_subst S)).
  simpl. destruct* (v==v).
Qed.

Theorem unify_sound : forall h pairs S0 S,
  unify pairs S0 h = Some S ->
  is_subst S0 ->
  forall T1 T2,
    In (T1,T2) pairs -> typ_subst S T1 = typ_subst S T2.
Proof.
  induction h; intros. discriminate.
  poses H' H.
  simpl in H.
  destruct pairs.
    elim H1.
  simpl in H1; destruct H1.
    subst.
    case_rewrite (typ_subst S0 T1) R1; case_rewrite (typ_subst S0 T2) R2;
      try case_rewrite (S.mem v (typ_fv (typ_bvar n))) R3;
      try case_rewrite (S.mem v (typ_fv (typ_arrow t t0))) R3.
          destruct (n === n0).
            subst.
            rewrite <- (typ_subst_extend _ _ T1 H0 H').
            rewrite <- (typ_subst_extend _ _ T2 H0 H').
            congruence.
          discriminate.
         symmetry.
         apply* (unify_var _ _ _ _ _ _ R2 R1 H' H).
        apply* (unify_var _ _ _ _ _ _ R1 R2 H' H).
       destruct (v == v0).
         subst.
         rewrite <- (typ_subst_extend _ _ T1 H0 H').
         rewrite <- (typ_subst_extend _ _ T2 H0 H').
         congruence.
       apply* (unify_var _ _ _ _ _ _ R1 R2 H' H).
       simpl; auto.
      apply* (unify_var _ _ _ _ _ _ R1 R2 H' H).
     symmetry.
     apply* (unify_var _ _ _ _ _ _ R2 R1 H' H).
    rewrite <- (typ_subst_extend _ _ T1 H0 H').
    rewrite <- (typ_subst_extend _ _ T2 H0 H').
    rewrite R1; rewrite R2.
    simpl.
    rewrite* (IHh _ _ _ H H0 t t1).
    rewrite* (IHh _ _ _ H H0 t0 t2).
  destruct p.
  case_rewrite (typ_subst S0 t) R1; case_rewrite (typ_subst S0 t0) R2;
    try case_rewrite (S.mem v (typ_fv (typ_bvar n))) R3;
    try case_rewrite (S.mem v (typ_fv (typ_arrow t1 t2))) R3;
    try apply* (IHh _ _ _ H);
    try apply* add_binding_is_subst.
        destruct (n === n0). subst. apply* (IHh _ _ _ H).
        discriminate.
       simpl; intro; auto.
      simpl; intro; auto.
     destruct (v == v0).
       subst.
       apply* (IHh _ _ _ H).
     apply* (IHh _ _ _ H).
     apply* add_binding_is_subst.
     use (typ_subst_disjoint t0 H0).
     rewrite R2 in H2.
     assert (v \notin typ_fv (typ_fvar v0)) by simpl*.
     use (notin_disjoint H3).
     disjoint_solve.
   use (typ_subst_disjoint t0 H0).
   rewrite R2 in H2.
   use (notin_disjoint (mem_3 R3)).
   disjoint_solve.
  use (typ_subst_disjoint t H0).
  rewrite R1 in H2.
  use (notin_disjoint (mem_3 R3)).
  disjoint_solve.
Qed.

Lemma typ_subst_prebind : forall v T S T1,
  typ_subst S T = typ_subst S (typ_fvar v) ->
  typ_subst S (typ_subst (v~T) T1) = typ_subst S T1.
Proof.
  induction T1; intros.
      simpl*.
    simpl. destruct (v0 == v).
      subst*.
    reflexivity.
  simpl.
  rewrite* IHT1_1. rewrite* IHT1_2.
Qed.

Lemma typ_subst_res_fresh : forall S T v,
  is_subst S -> typ_subst S T = typ_fvar v -> v # S.
Proof.
  intros.
  use (typ_subst_disjoint T H).
  rewrite H0 in H1.
  simpl in H1. destruct* (H1 v).
Qed.

Definition mgu_spec pairs S0 S S' :=
  is_subst S0 ->
  (forall T1 T2, In (T1,T2) pairs ->
    typ_subst S' (typ_subst S0 T1) = typ_subst S' (typ_subst S0 T2)) ->
  forall T1 T2,
    typ_subst S T1 = typ_subst S T2 ->
    typ_subst S' (typ_subst S0 T1) = typ_subst S' (typ_subst S0 T2).

Lemma unify_mgu_step : forall S0 pairs S S' h t t0 v T,
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  unify pairs (add_binding v T S0) h = Some S ->
  S.mem v (typ_fv T) = false ->
  (forall S0, unify pairs S0 h = Some S -> mgu_spec pairs S0 S S') ->
  mgu_spec ((t,t0)::pairs) S0 S S'.
Proof.
  intros until T.
  intros R1 R2 HU R3 IHh HS0 Heq.
  intros.
  assert (BS': typ_subst S' T = typ_subst S' (typ_fvar v)).
    assert (In (t, t0) ((t,t0)::pairs)) by simpl*.
    use (Heq _ _ H0); clear H0.
    rewrite R1 in H1; rewrite R2 in H1.
    auto.
  assert (Hv: v # S0) by apply* typ_subst_res_fresh.
  assert (typ_subst S' (typ_subst (add_binding v T S0) T1) =
          typ_subst S' (typ_subst (add_binding v T S0) T2)).
    apply* IHh.
      apply* add_binding_is_subst.
      assert (disjoint {{v}} (typ_fv T)).
        intro x; destruct* (x == v); subst.
        right; intro. rewrite (S.mem_1 H0) in R3. discriminate.
      use (typ_subst_disjoint t0 HS0).
      rewrite R2 in H1.
      disjoint_solve.
    intros.
    repeat rewrite* typ_subst_add_binding.
    assert (In (T0, T3) ((t,t0)::pairs)) by simpl*.
      use (Heq _ _ H1); clear H1.
    repeat rewrite* typ_subst_prebind.
  do 2 rewrite typ_subst_add_binding in H0; auto.
  do 2 rewrite typ_subst_prebind in H0; auto.
Qed.

Lemma unify_mgu0 : forall h pairs S0 S S',
  unify pairs S0 h = Some S -> mgu_spec pairs S0 S S'.
Proof.
  induction h; intros; intro; intros. discriminate.
  simpl in H.
  destruct pairs.
    inversions H; clear H.
    rewrite* H2.
  destruct p.
  case_rewrite (typ_subst S0 t) R1; case_rewrite (typ_subst S0 t0) R2;
    try case_rewrite (S.mem v (typ_fv (typ_bvar n))) R3;
    try case_rewrite (S.mem v (typ_fv (typ_arrow t1 t2))) R3.
        destruct* (n === n0). unfold mgu_spec in IHh; auto*.
        discriminate.
       apply* (unify_mgu_step (S':=S') _ R2 R1 H).
       simpl; intros.
       destruct H3.
         inversions H3; symmetry; apply* H1.
       apply* H1.
      apply* (unify_mgu_step (S':=S') _ R1 R2 H).
     destruct (v == v0).
       subst v0.
       unfold mgu_spec in IHh; auto*.
     apply* (unify_mgu_step (S':=S') _ R1 R2 H).
     simpl. case_eq (S.mem v {{v0}}); intro; auto.
     elim n; rewrite* (S.singleton_1 (S.mem_2 H3)).
    apply* (unify_mgu_step (S':=S') _ R1 R2 H).
   apply* (unify_mgu_step (S':=S') _ R2 R1 H).
   simpl; intros.
   destruct H3.
     inversions H3; symmetry; apply* H1.
   apply* H1.
  apply* (IHh _ _ _ S' H).
  simpl; intros.
  assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
  pose (H1 _ _ H4).
  rewrite <- (typ_subst_idem t H0) in e.
  rewrite <- (typ_subst_idem t0 H0) in e.
  rewrite R1 in e; rewrite R2 in e; simpl in e.
  inversions e.
  destruct H3. inversions* H3.
  destruct* H3. inversions* H3.
Qed.

Definition id := Env.empty (A:=typ).

Lemma typ_subst_id : forall T, typ_subst id T = T.
Proof.
  intro.
  apply typ_subst_fresh.
  simpl. intro; auto.
Qed.

Lemma is_subst_id : is_subst id.
Proof.
  unfold id, is_subst. intro; intros. elim (binds_empty H).
Qed.

Theorem unify_mgu : forall h S S' T1 T2,
  unify ((T1,T2)::nil) id h = Some S ->
  typ_subst S' T1 = typ_subst S' T2 ->
  forall T3 T4,
    typ_subst S T3 = typ_subst S T4 ->
    typ_subst S' T3 = typ_subst S' T4.
Proof.
  intros.
  rewrite <- (typ_subst_id T3).
  rewrite <- (typ_subst_id T4).
  apply* (unify_mgu0 _ _ S' H is_subst_id).
  simpl; intros.
  destruct* H2.
  inversions H2.
  repeat rewrite typ_subst_id.
  auto.
Qed.

Section Accum.
  Variables A B : Set.
  Variables (f : A -> B) (op : B->B->B) (unit : B).

  Fixpoint accum (l:list A) {struct l} : B :=
    match l with
    | nil => unit
    | a::rem => op (f a) (accum rem)
    end.
End Accum.

Fixpoint all_types S (pairs:list(typ*typ)) {struct pairs} : list typ :=
  match pairs with
  | nil => nil
  | p::rem =>
      typ_subst S (fst p) :: typ_subst S (snd p) :: all_types S rem
  end.

Definition all_fv S pairs :=
  accum typ_fv S.union {} (all_types S pairs).
Check all_fv.

Fixpoint typ_size (T : typ) : nat :=
  match T with
  | typ_arrow T1 T2 => S (typ_size T1 + typ_size T2)
  | _ => 1
  end.

Definition all_size S pairs :=
  accum typ_size plus 0 (all_types S pairs).

Fixpoint pow2exp (m n:nat) {struct n} :=
  match n with
  | 0 => m
  | S n' => pow2exp (m*m) n'
  end.

Lemma pow2exp_min : forall n m, m <= pow2exp m n.
Proof.
  induction n; intros; simpl. omega.
  use (IHn (m*m)).
  destruct m; simpl in *. auto.
  set (m*S m) in *. omega.
Qed.

Require Import Arith Omega.

Lemma pow2exp_lt_le : forall m n s t,
  s < t -> m <= n -> pow2exp s m < pow2exp t n.
Proof.
  induction m; destruct n; simpl; intros; try omega.
    use (pow2exp_min n (t*t)).
    assert (s < t * t).
      destruct t; try omega.
      simpl. set (t*S t). omega.
    omega.
  apply IHm.
    eapply le_lt_trans; try apply* mult_lt_compat_r.
      apply mult_le_compat_l. omega.
    omega.
  omega.
Qed.

Definition size_pairs S pairs :=
  pow2exp (all_size S pairs) (S.cardinal (all_fv S pairs)).

Lemma size_pairs_grows : forall S p pairs,
  size_pairs S pairs < size_pairs S (p :: pairs).
Proof.
  intros.
  unfold size_pairs.
  unfold all_fv, all_size.
  simpl.
  rewrite union_assoc.
  rewrite cardinal_union.
  apply pow2exp_lt_le.
    destruct (typ_subst S (fst p)); simpl; omega.
  omega.
Qed.

Lemma typ_fv_decr : forall v T S T1,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  typ_fv (typ_subst (add_binding v T S) T1) <<
  S.remove v (typ_fv T \u typ_fv (typ_subst S T1)).
Proof.
  intros.
  rewrite* typ_subst_add_binding.
  induction (typ_subst S T1); simpl in *; intros x Hx.
      elim (in_empty Hx).
    destruct (v0 == v).
      subst.
      apply* S.remove_2.
        intro Hv; rewrite <- Hv in Hx. destruct* (H0 v).
        elim H1; auto with sets.
      auto with sets.
    apply* S.remove_2.
      intro Hv; rewrite <- Hv in Hx.
      revert Hx; simpl*.
    simpl in Hx; auto with sets.
  destruct (S.union_1 Hx); [use (IHt1 _ H1) | use (IHt2 _ H1)];
    apply* remove_subset;
    intros y Hy; destruct (S.union_1 Hy); auto with sets.
Qed.

Lemma all_fv_decr : forall v T S pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  all_fv (add_binding v T S) pairs <<
  S.remove v (all_fv S ((typ_fvar v, T) :: pairs)).
Proof.
  unfold all_fv.
  induction pairs; intros.
    simpl. intros x Hx. elim (in_empty Hx).
  simpl.
  intros x Hx.
  rewrite* get_notin_dom.
  destruct (S.union_1 Hx).
    use (typ_fv_decr _ _ _ H H0 H1).
    apply* remove_subset.
    intros y Hy.
    destruct (S.union_1 Hy).
      rewrite <- (@typ_subst_fresh S T) in H3; auto with sets.
      disjoint_solve.
    auto with sets.
  destruct (S.union_1 H1); clear Hx H1.
    use (typ_fv_decr _ _ _ H H0 H2).
    apply* remove_subset.
    intros y Hy.
    destruct (S.union_1 Hy).
      rewrite <- (@typ_subst_fresh S T) in H3; auto with sets.
      disjoint_solve.
    auto with sets.
  use (IHpairs H H0 _ H2).
  apply* remove_subset.
  simpl.
  rewrite* get_notin_dom.
  intros y Hy.
  clear H1 H2.
  simpl in Hy.
  destruct (S.union_1 Hy). auto with sets.
  destruct (S.union_1 H1); auto with sets.
Qed.

Lemma cardinal_decr : forall v T S pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  S.cardinal (all_fv (add_binding v T S) pairs) <
  S.cardinal (all_fv S ((typ_fvar v, T) :: pairs)).
Proof.
  intros.
  use (all_fv_decr T S pairs H H0).
  use (le_lt_n_Sm _ _ (cardinal_subset H1)).
  rewrite cardinal_remove in H2. auto.
  unfold all_fv.
  simpl. rewrite* get_notin_dom.
  simpl; auto with sets.
Qed.

Lemma typ_subst_decr : forall v T S T1,
  v # S ->
  typ_size (typ_subst (add_binding v T S) T1) <=
  typ_size T * typ_size (typ_subst S T1).
Proof.
  intros.
  rewrite* typ_subst_add_binding.
  induction (typ_subst S T1); simpl. destruct T; simpl; omega.
    destruct (v0 == v). omega.
    destruct T; simpl; omega.
  assert (0 < typ_size T).
    destruct T; simpl; omega.
  destruct (typ_size T). omega.
  simpl in *.
  rewrite mult_comm in *.
  simpl.
  rewrite mult_plus_distr_r.
  omega.
Qed.

Lemma typ_subst_decr_all : forall v T S pairs,
  v # S ->
  all_size (add_binding v T S) pairs <= typ_size T * all_size S pairs.
Proof.
  unfold all_size; induction pairs; intros; simpl. omega.
  repeat rewrite mult_plus_distr_l.
  use (IHpairs H); clear IHpairs.
  use (typ_subst_decr T S (fst a) H).
  use (typ_subst_decr T S (snd a) H).
  omega.
Qed.

Lemma size_pairs_decr : forall v T S pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  size_pairs (add_binding v T S) pairs < size_pairs S ((typ_fvar v,T)::pairs).
Proof.
  intros.
  unfold size_pairs.
  use (cardinal_decr T S pairs H H0).
  set (S.cardinal (all_fv (add_binding v T S) pairs)) in *.
  set (S.cardinal (all_fv S ((typ_fvar v, T) :: pairs))) in *.
  clearbody n n0.
  destruct n0; try omega.
  simpl.
  apply pow2exp_lt_le; try omega.
  use (typ_subst_decr_all T S pairs H).
  assert (typ_size T < all_size S ((typ_fvar v, T) :: pairs)).
    unfold all_size; simpl.
    rewrite* get_notin_dom.
    rewrite (typ_subst_fresh S T); try disjoint_solve.
    simpl; omega.
  assert (all_size S pairs < all_size S ((typ_fvar v, T) :: pairs)).
    unfold all_size; simpl.
    rewrite* get_notin_dom.
    simpl; omega.
  eapply le_lt_trans. apply H2.
  rewrite mult_comm.
  eapply le_lt_trans; try (eapply mult_lt_compat_r; try apply H4).
    apply mult_le_compat_l. omega.
  destruct T; simpl; omega.
Qed.

Lemma size_pairs_comm : forall S T1 T2 pairs,
  size_pairs S ((T1,T2)::pairs) = size_pairs S ((T2,T1)::pairs).
Proof.
  intros; unfold size_pairs, all_size, all_fv; simpl.
  repeat rewrite union_assoc.
  rewrite (@union_comm (typ_fv (typ_subst S T2))).
  repeat rewrite plus_assoc.
  rewrite* (@plus_comm (typ_size (typ_subst S T2))).
Qed.

Lemma size_pairs_decr' : forall S0 t t0 pairs h v,
  is_subst S0 ->
  S.mem v (typ_fv (typ_subst S0 t0)) = false ->
  size_pairs S0 ((t, t0) :: pairs) < S h ->
  typ_subst S0 t = typ_fvar v ->
  size_pairs (add_binding v (typ_subst S0 t0) S0) pairs < h.
Proof.
  intros.
  use (typ_subst_res_fresh _ H H2).
  use (typ_subst_disjoint t0 H).
  eapply lt_le_trans.
    apply* size_pairs_decr.
    assert (disjoint {{v}} (typ_fv (typ_subst S0 t0))).
      intro v0. destruct* (v0 == v).
      subst.
      right; intro.
      rewrite (S.mem_1 H5) in H0. discriminate.
    disjoint_solve.
  replace (size_pairs S0 ((typ_fvar v, typ_subst S0 t0) :: pairs))
    with (size_pairs S0 ((t, t0) :: pairs)).
    omega.
  unfold size_pairs, all_size, all_fv; simpl.
  rewrite* get_notin_dom.
  rewrite H2.
  rewrite* typ_subst_idem.
Qed.

Lemma typ_subst_eq_add : forall S S0 v T T1 T2 pairs,
  (forall T1 T2 : typ,
    In (T1, T2) pairs ->
    typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
  v # S0 ->
  typ_subst S (typ_fvar v) = typ_subst S T ->
  In (T1, T2) pairs -> 
  typ_subst S (typ_subst (add_binding v T S0) T1) =
  typ_subst S (typ_subst (add_binding v T S0) T2).
Proof.
  intros.
  repeat rewrite* typ_subst_add_binding.
  assert (forall T',
            typ_subst S (typ_subst (v ~ T) T') = typ_subst S T').
    clear -H1; induction T'; simpl; try congruence.
    destruct* (v0 == v).
    subst. apply (sym_eq H1).
  repeat rewrite* H3.
Qed.

Lemma typ_subst_no_cycle : forall v S T,
  v \in typ_fv T ->
  1 < typ_size T ->
  typ_size (typ_subst S (typ_fvar v)) < typ_size (typ_subst S T).
Proof.
  induction T; intros. elim (in_empty H).
    simpl in H0. omega.
  simpl in H.
  clear H0.
  assert (forall T, v \in typ_fv T -> T = T1 \/ T = T2 ->
             typ_size (typ_subst S (typ_fvar v)) <
             typ_size (typ_subst S (typ_arrow  T1 T2))).
    intros.
    case_eq (typ_size T); intros. destruct T; discriminate.
    destruct n. destruct T. elim (in_empty H0).
        rewrite (S.singleton_1 H0) in H1.
        destruct H1; subst; simpl; omega.
      destruct T3; simpl in H2; omega.
    assert (typ_size (typ_subst S (typ_fvar v)) < typ_size (typ_subst S T)).
      assert (1 < typ_size T) by omega.
      destruct H1; subst*.
    destruct H1; subst; simpl in *; omega.
  destruct (S.union_1 H); apply* (H0 _ H1).
Qed.

Lemma unify_complete_step : forall pairs S0 S v T h t t0,
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  size_pairs S0 ((t,t0)::pairs) < Datatypes.S h ->
  is_subst S0 ->
  (forall S0, is_subst S0 ->
    size_pairs S0 pairs < h ->
    (forall T1 T2 : typ,
      In (T1, T2) pairs ->
      typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
    exists S' : Env.env typ, unify pairs S0 h = Some S') ->
  (forall T1 T2 : typ,
    In (T1, T2) ((t, t0) :: pairs) ->
    typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
  T <> typ_fvar v ->
  S.mem v (typ_fv T) = false /\
  exists S', unify pairs (add_binding v T S0) h = Some S'.
Proof.
  intros until t0; intros R1 R2 Hsz HS0 IHh Heq HT.
  case_eq (S.mem v (typ_fv T)); intros.
    elimtype False.
    use (S.mem_2 H).
    assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
    use (Heq _ _ H1); clear H1.
    rewrite R1 in H2; rewrite R2 in H2.
    clear -H0 H2 HT.
    destruct T. elim (in_empty H0).
      elim HT; rewrite* (S.singleton_1 H0).
    assert (1 < typ_size (typ_arrow T1 T2)).
      destruct T1; simpl; omega.
    use (typ_subst_no_cycle S _ H0 H).
    rewrite H2 in H1; omega.
  split*.
  rewrite <- R2 in H.
  use (size_pairs_decr' _ _ _ HS0 H Hsz R1).
  rewrite R2 in H0; simpl in H0.
  use (typ_subst_res_fresh _ HS0 R1).
  destruct* (IHh (add_binding v T S0)); clear IHh.
    apply* add_binding_is_subst.
    use (typ_subst_disjoint t0 HS0).
    rewrite R2 in *; simpl in *.
    assert (disjoint {{v}} (typ_fv T)).
      intro x; destruct (x == v); subst; auto.
    disjoint_solve.
  clear HT H H0.
  intros.
  apply* typ_subst_eq_add.
  rewrite <- R1. rewrite <- R2.
  apply* Heq.
Qed.

Lemma unify_complete0 : forall h pairs S0 S,
  is_subst S0 ->
  (forall T1 T2, In (T1, T2) pairs ->
    typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
  size_pairs S0 pairs < h ->
  exists S', unify pairs S0 h = Some S'.
Proof.
  induction h.
    intros; elimtype False; omega.
  destruct pairs; introv HS0 Heq Hsz.
    exists S0; intuition.
  destruct p.
  simpl unify.
  case_eq (typ_subst S0 t); introv R1; case_eq (typ_subst S0 t0); introv R2.
          destruct (n === n0).
           subst.
           destruct* (IHh pairs _ S HS0).
           use (size_pairs_grows S0 (t,t0) pairs). omega.
          assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
          use (Heq _ _ H).
          rewrite R1 in H0; rewrite R2 in H0.
          simpl in H0. inversions* H0.
         rewrite size_pairs_comm in Hsz.
         destruct* (unify_complete_step S R2 R1 Hsz).
           simpl; intros. destruct H; subst.
             inversions H; symmetry; apply* Heq.
           apply* Heq.
          intro; discriminate. 
         rewrite* H.
        assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
        use (Heq _ _ H).
        rewrite R1 in H0; rewrite R2 in H0. discriminate.
       destruct* (unify_complete_step S R1 R2 Hsz).
        intro; discriminate.
       rewrite* H.
      destruct (v == v0).
       subst.
       destruct* (IHh pairs _ S HS0).
       use (size_pairs_grows S0 (t,t0) pairs). omega.
      destruct* (unify_complete_step S R1 R2 Hsz).
      intro; elim n. inversions* H.
     destruct* (unify_complete_step S R1 R2 Hsz).
      intro; discriminate.
     rewrite* H.
    assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
    use (Heq _ _ H); clear H.
    rewrite R1 in H0; rewrite R2 in H0.
    discriminate.
   rewrite size_pairs_comm in Hsz.
   destruct* (unify_complete_step S R2 R1 Hsz).
     simpl; intros. destruct H; subst.
       inversions H; symmetry; apply* Heq.
     apply* Heq.
    intro; discriminate.
   rewrite* H.
  destruct* (IHh ((t1,t3)::(t2,t4)::pairs) S0 S); clear IHh.
    clear Hsz; intros.
    assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
    use (Heq _ _ H0).
    rewrite <- (typ_subst_idem t HS0) in H1.
    rewrite <- (typ_subst_idem t0 HS0) in H1.
    rewrite R1 in H1; rewrite R2 in H1.
    simpl in H1; inversions H1; clear H1.
    simpl in H; destruct H.
      inversions* H.
    simpl in H; destruct H.
      inversions* H.
    apply* Heq.
  assert (size_pairs S0 ((t1, t3) :: (t2, t4) :: pairs) <
          size_pairs S0 ((t, t0) :: pairs)).
    unfold size_pairs, all_size, all_fv.
    simpl.
    rewrite <- (typ_subst_idem t HS0).
    rewrite <- (typ_subst_idem t0 HS0).
    rewrite R1; rewrite R2; simpl.
    apply pow2exp_lt_le.
      omega.
    rewrite (union_assoc (typ_fv (typ_subst S0 t3))).
    rewrite (union_comm (typ_fv (typ_subst S0 t3))).
    repeat rewrite union_assoc.
    omega.
  omega.
Qed.

Theorem unify_complete : forall T1 T2 S,
  typ_subst S T1 = typ_subst S T2 ->
  exists S',
    unify ((T1,T2)::nil) id (1 + size_pairs id ((T1,T2)::nil)) = Some S'.
Proof.
  intros.
  apply* unify_complete0.
    apply is_subst_id.
  intros. rewrite (typ_subst_id T0). rewrite (typ_subst_id T3).
  simpl in H0; destruct* H0.
  inversions* H0.
Qed.

End MkInfer.