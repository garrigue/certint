(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure.
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
        unify ((T11,T21)::(T12,T22)::pairs) S h'
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
    apply* IHh.
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

Fixpoint typ_depth (T : typ) : nat :=
  match T with
  | typ_arrow T1 T2 => S (typ_depth T1 + typ_depth T2)
  | _ => 1
  end.

Require Import Max.

Definition max_depth S pairs :=
  accum typ_depth max 0 (all_types S pairs).

Definition sum_depth S pairs :=
  accum typ_depth plus 0 (all_types S pairs).

Fixpoint exp2 (n:nat) :=
  match n with
  | 0 => 1
  | S n' => exp2 n' + exp2 n'
  end.

Definition size_pairs S pairs :=
  S.cardinal (all_fv S pairs) * exp2 (max_depth S pairs) + sum_depth S pairs.

Definition id := Env.empty (A:=typ).

Require Import Arith Omega.

Lemma wf_lt : well_founded lt.
Proof (Wf_nat.well_founded_ltof _ (fun n:nat => n)).

Definition math_ind := well_founded_ind wf_lt.
Check math_ind.

Require Import SetoidList.

Lemma elements_empty : forall L,
  S.elements L = nil -> L = {}.
Proof.
  intros.
  apply eq_ext.
  intro. split; intro.
    use (S.elements_1 H0).
    rewrite H in H1.
    inversion H1.
  elim (in_empty H0).
Qed.

Lemma empty_elements : S.elements {} = nil.
Proof.
  assert (forall l, S.elements {} = l -> l = nil). 
    intros.
    destruct l. auto.
    assert (e \in {}).
      apply S.elements_2.
      rewrite* H.
    elim (in_empty H0).
  rewrite* <- (H (S.elements {})).
Qed.

Lemma diff_empty_r : forall L, S.diff L {} = L.
  intros.
  apply eq_ext; intro; split; intro.
    apply* S.diff_1.
  apply* S.diff_3.
Qed.

Lemma diff_empty_l : forall L, S.diff {} L = {}.
  intros.
  apply eq_ext; intro; split; intro.
    apply (S.diff_1 H).
  elim (in_empty H).
Qed.

Lemma union_empty_both : forall L1 L2,
  L1 \u L2 = {} -> L1 = {} /\ L2 = {}.
Proof.
  intros; split; apply eq_ext; intro; split; intro;
    try (rewrite <- H; auto with sets); elim (in_empty H0).
Qed.

Lemma sort_lt_notin : forall a l0,
  sort S.E.lt l0 ->
  lelistA S.E.lt a l0 ->
  ~ InA S.E.eq a l0.
Proof.
  intros.
  intro.
  use (proj1 (InfA_alt S.E.eq_refl S.E.eq_sym S.E.lt_trans
        Var_as_OT_Facts.lt_eq Var_as_OT_Facts.eq_lt a H) H0 _ H1).
  elim (S.E.lt_not_eq _ _ H2). reflexivity.
Qed.

Definition sort_lt_nodup :=
  SortA_NoDupA S.E.eq_refl S.E.eq_sym S.E.lt_trans S.E.lt_not_eq
    Var_as_OT_Facts.lt_eq Var_as_OT_Facts.eq_lt.
Check sort_lt_nodup.

Lemma sort_lt_ext : forall l1 l2,
  sort S.E.lt l1 -> sort S.E.lt l2 ->
  (forall a, InA S.E.eq a l1 <-> InA S.E.eq a l2) -> l1 = l2. 
Proof.
  intros.
  gen l2; induction H; intros.
    destruct l2. auto.
    assert (InA S.E.eq t nil).
      apply (proj2 (H1 t)).
      auto.
    inversion H.
  inversions H1.
    assert (InA S.E.eq a nil).
      apply (proj1 (H2 a)).
      auto.
    inversion H3.
  destruct (S.E.compare a a0).
      elim (sort_lt_notin H1 (cons_leA _ _ _ _ l1)).
      apply* (proj1 (H2 a)).
    rewrite <- e in *. clear e a0.
    rewrite* (IHsort l0).
    intros.
    split; intro.
      destruct (a0 == a).
        subst.
        use (cons_sort H H0).
        use (sort_lt_nodup H6).
        inversions H7. contradiction.
      assert (InA S.E.eq a0 (a :: l0)).
        apply* (proj1 (H2 a0)).
      inversions H6.
        elim (n H8).
      auto.
    clear -H1 H2 H5.
    destruct (a0 == a).
      subst.
      use (sort_lt_nodup H1).
      inversions H. contradiction.
    assert (InA S.E.eq a0 (a :: l)).
      apply* (proj2 (H2 a0)).
    inversions H.
      elim (n H3).
    auto.
  elim (sort_lt_notin (cons_sort H H0) (cons_leA _ _ _ _ l1)).
  apply* (proj2 (H2 a0)).
Qed.

Lemma remove_union : forall a L1 L2,
  S.remove a (L1 \u L2) = S.remove a L1 \u S.remove a L2.
Proof.
  intros; apply eq_ext; intro; split; intro.
    destruct (a == a0).
      elim (S.remove_1 e H).
    destruct (S.union_1 (S.remove_3 H)).
      apply S.union_2. apply (S.remove_2 n H0).
    apply S.union_3. apply (S.remove_2 n H0).
  destruct (a == a0).
    destruct (S.union_1 H); elim (S.remove_1 e H0).
  apply* S.remove_2.
  destruct (S.union_1 H); use (S.remove_3 H0).
    apply* S.union_2.
  apply* S.union_3.
Qed.

Lemma nodup_notin_split : forall a l2 l1,
  NoDupA S.E.eq (l1 ++ a :: l2) -> ~InA S.E.eq a l1 /\ ~InA S.E.eq a l2.
Proof.
  induction l1; simpl; intro; inversions H.
    split*. intro. inversion H0.
  destruct (IHl1 H3).
  split*.
  intro. inversions H4.
    elim H2.
    apply (InA_eqA S.E.eq_sym S.E.eq_trans H6 (l:=l1++a::l2)).
    apply (In_InA S.E.eq_refl).
    apply in_or_app. simpl*.
  elim (H0 H6).
Qed.

Lemma diff_remove : forall a L1 L2,
  a \in L2 -> S.diff (S.remove a L1) (S.remove a L2) = S.diff L1 L2.
Proof.
  intros.
  apply eq_ext; intros; split; intro.
    apply S.diff_3.
      apply* S.remove_3.
      apply* S.diff_1.
    destruct (a == a0).
      use (S.diff_1 H0).
      elim (S.remove_1 e H1).
    intro.
    elim (S.diff_2 H0).
    apply* S.remove_2.
  apply S.diff_3.
    apply S.remove_2.
      intro. rewrite H1 in *.
      elim (S.diff_2 H0 H).
    apply* S.diff_1.
  intro; elim (S.diff_2 H0).
  apply* S.remove_3.
Qed.

Lemma sort_split : forall y l2 l1,
  sort S.E.lt (l1 ++ y :: l2) -> sort S.E.lt (l1 ++ l2).
Proof.
  induction l1; simpl; intros.
    inversions* H.
  inversions H.
  constructor.
    apply* IHl1.
  destruct l1; simpl in *.
    inversions H3.
    apply* (InfA_ltA S.E.lt_trans).
    inversions* H.
    inversions* H5.
  inversions* H3.
Qed.

Lemma cardinal_union : forall L1 L2,
  S.cardinal (L1 \u L2) = S.cardinal L2 + S.cardinal (S.diff L1 L2).
Proof.
  intros.
  repeat rewrite S.cardinal_1.
  remember (S.elements (L1 \u L2)) as elts.
  remember (S.elements L2) as elts2.
  remember (S.elements (S.diff L1 L2)) as elts1.
  gen L1 L2 elts1 elts.
  induction elts2; intros.
    use (elements_empty (sym_equal Heqelts2)).
    subst.
    rewrite diff_empty_r.
    rewrite* union_empty_r.
  assert (a \in L2).
    apply S.elements_2.
    rewrite <- Heqelts2. auto.
  assert (InA S.E.eq a elts).
    subst.
    apply S.elements_1.
    auto with sets.
  subst.
  destruct (InA_split H0) as [l1 [y [l2 [Hl1 Hl]]]].
  rewrite Hl.
  rewrite app_length.
  simpl. rewrite <- plus_n_Sm.
  rewrite <- app_length.
  apply (f_equal S).
  use (S.elements_3 L2).
  rewrite <- Heqelts2 in H1.
  apply (IHelts2 (S.remove a L1) (S.remove a L2)).
      apply sort_lt_ext.
        inversion* H1.
       apply S.elements_3.
      intro; split; intro.
        apply S.elements_1.
        apply S.remove_2.
          intro. rewrite H3 in H1.
          use (sort_lt_nodup H1).
          inversions H4.
          contradiction.
        apply S.elements_2.
        rewrite <- Heqelts2.
        auto.
      use (S.elements_2 H2).
      assert (InA S.E.eq a0 (a :: elts2)).
        rewrite Heqelts2.
        apply S.elements_1.
        apply* S.remove_3.
      inversions H4.
        elim (S.remove_1 (sym_equal H6) H3).
      auto.
    apply (f_equal S.elements).
    rewrite* diff_remove.
  apply sort_lt_ext.
      use (S.elements_3 (L1 \u L2)).
      subst.
      rewrite Hl in H2.
      apply* sort_split.
    apply S.elements_3.
  intro; split; intro.
    apply S.elements_1.
    rewrite <- remove_union.
    rewrite <- Hl1 in *; clear Hl1 y.
    use (S.elements_3 (L1 \u L2)).
    destruct (a == a0).
      rewrite Hl in H3.
      use (sort_lt_nodup H3).
      destruct (nodup_notin_split _ _ _ H4).
      subst; destruct* (InA_app H2).
    assert (a0 \in (L1 \u L2)).
      apply S.elements_2.
      rewrite Hl.
      clear -H2.
      induction l1; simpl in *. auto.
      inversions* H2.
    apply* S.remove_2.
  rewrite <- Hl1 in *; clear Hl1 y.
  use (S.elements_2 H2).
  rewrite <- remove_union in H3.
  use (S.remove_3 H3).
  destruct (a == a0).
    elim (S.remove_1 e H3).
  use (S.elements_1 H4).
  rewrite Hl in H5.
  clear -n H5.
  induction l1; simpl in *; inversions* H5.
  elim (n (S.E.eq_sym _ _ H0)).
Qed.

Lemma exp2_le : forall m n, m <= n -> exp2 m <= exp2 n.
Proof.
  induction m; destruct n; intros; try omega.
    clear; induction (S n). auto.
    simpl in *; omega.
  simpl.
  assert (m <= n) by omega.
  use (IHm n H0).
  omega.
Qed.

Lemma size_pairs_grows : forall S p pairs,
  size_pairs S pairs < size_pairs S (p :: pairs).
Proof.
  intros.
  unfold size_pairs.
  unfold all_fv, max_depth, sum_depth.
  simpl.
  rewrite union_assoc.
  rewrite cardinal_union.
  remember (accum typ_depth max 0 (all_types S pairs)) as md.
  assert (exp2 md <= exp2
     (max (typ_depth (typ_subst S (fst p)))
        (max (typ_depth (typ_subst S (snd p))) md))).
    apply exp2_le.
    eapply le_trans; apply le_max_r.
  assert (0 < typ_depth (typ_subst S (fst p))).
    clear; destruct (typ_subst S (fst p)); simpl; omega.
  destruct (typ_depth (typ_subst S (fst p))).
    elimtype False; omega.
  apply plus_le_lt_compat.
    apply mult_le_compat; omega.
  omega.
Qed.

Lemma cardinal_remove : forall a L,
  a \in L ->
  S (S.cardinal (S.remove a L)) = S.cardinal L.
Proof.
  intros.
  repeat rewrite S.cardinal_1.
  remember (S.elements L) as elts.
  use (S.elements_1 H); clear H.
  rewrite <- Heqelts in H0.
  gen L; induction elts; simpl; intros.
    inversion H0.
  inversions H0.
    rewrite <- H1 in *; clear H1.
Lemma elements_tl : forall a elts L,
  S.elements L = a :: elts -> S.elements (S.remove a L) = elts.
Proof.
  intros.
  apply sort_lt_ext.
      apply S.elements_3.
    use (S.elements_3 L).
    rewrite H in H0.
    inversions* H0.
  intro; split; intro.
    use (S.elements_2 H0).
    use (S.remove_3 H1).
    use (S.elements_1 H2).
    rewrite H in H3.
    inversions* H3.
    elim (S.remove_1 (sym_eq H5) H1).
  apply S.elements_1.
  apply S.remove_2.
    intro.
    rewrite H1 in H.
    use (sort_lt_nodup (S.elements_3 L)).
    rewrite H in H2.
    inversions* H2.
  apply S.elements_2.
  rewrite* H.
Qed.
    rewrite* (@elements_tl a elts L).
  use (elements_tl (sym_eq Heqelts)).
  rewrite <- (IHelts H1 _ (sym_eq H)).
Lemma remove_remove : forall L a b,
  S.remove a (S.remove b L) = S.remove b (S.remove a L).
Proof.
  intro.
  assert (forall a b x, x \in S.remove a (S.remove b L) ->
                        x \in S.remove b (S.remove a L)).
    intros.
    use (S.remove_3 H).
    use (S.remove_3 H0).
    apply* S.remove_2.
      intro.
      elim (S.remove_1 H2 H0).
    apply* S.remove_2.
    intro.
    elim (S.remove_1 H2 H).
  intros.
  apply eq_ext; intro; split; intro; auto.
Qed.

Lemma cardinal_decr : forall v T S pairs,
  S.cardinal (all_fv (add_binding v T S) pairs) <
  S.cardinal (all_fv S ((typ_fvar v, T) :: pairs)).
Proof.
  intros.

Lemma size_pairs_decr : forall v T S pairs,
  size_pairs (add_binding v T S) pairs < size_pairs S ((typ_fvar v,T)::pairs).
Proof.
  intros.
  unfold size_pairs.

Lemma unify_complete0 : forall h pairs S0 S,
  is_subst S0 ->
  is_subst S ->
  (forall T1 T2, In (T1, T2) pairs ->
    typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
  size_pairs S0 pairs < h ->
  exists S',
    unify pairs S0 h = Some S' /\
    (forall x y,
      typ_subst S' (typ_fvar x) = typ_subst S' (typ_fvar y) ->
      typ_subst S (typ_subst S0 (typ_fvar x)) =
      typ_subst S (typ_subst S0 (typ_fvar y))).
Proof.
  induction h using math_ind.
  induction pairs; intros.
    exists S0; intuition.
        destruct h. elimtype False; omega.
        simpl. auto.
      elim H4.
    rewrite* H4.
  destruct h. elimtype False; omega.
  destruct a.
  simpl unify.
  clear IHpairs.
  case_eq (typ_subst S0 t); introv R1; case_eq (typ_subst S0 t0); introv R2.
          destruct (n === n0).
           subst.
           assert (h < Datatypes.S h) by omega.
           destruct* (H _ H4 pairs _ _ H0 H1).
           use (size_pairs_grows S0 (t,t0) pairs). omega.
          assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
          use (H2 _ _ H4).
          rewrite R1 in H5; rewrite R2 in H5.
          simpl in H5. inversions H5. auto*.
         case_eq (S.mem v (typ_fv (typ_bvar n))); intros.
          simpl in H4. elim (in_empty (S.mem_2 H4)).
  

Theorem unify_complete : forall T1 T2 S,
  typ_subst S T1 = typ_subst S T2 ->
  is_subst S ->
  exists S',
    unify ((T1,T2)::nil) id (size_pairs id ((T1,T2)::nil)) = Some S' /\
    typ_subst S' T1 = typ_subst S' T2 /\
    forall x y, typ_subst S' (typ_fvar x) = typ_subst S' (typ_fvar y) ->
      typ_subst S (typ_fvar x) = typ_subst S (typ_fvar y).



End MkInfer.