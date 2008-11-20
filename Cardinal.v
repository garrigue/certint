(***************************************************************************
* Cardinality lemmas                                                       *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import List SetoidList Arith Omega Metatheory.
Set Implicit Arguments.

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

Lemma diff_empty_r : forall L, S.diff L {} = L.
  intros.
  apply eq_ext; intro; split; intro.
    apply* S.diff_1.
  apply* S.diff_3.
Qed.

Definition sort_lt_all :=
  InfA_alt S.E.eq_refl S.E.eq_sym S.E.lt_trans
     Var_as_OT_Facts.lt_eq Var_as_OT_Facts.eq_lt.
(* Check sort_lt_all. *)

Lemma sort_lt_notin : forall a l0,
  sort S.E.lt l0 ->
  lelistA S.E.lt a l0 ->
  ~ InA S.E.eq a l0.
Proof.
  intros.
  intro.
  use (proj1 (sort_lt_all a H) H0 _ H1).
  elim (S.E.lt_not_eq _ _ H2). reflexivity.
Qed.

Definition sort_lt_nodup :=
  SortA_NoDupA S.E.eq_refl S.E.eq_sym S.E.lt_trans S.E.lt_not_eq
    Var_as_OT_Facts.lt_eq Var_as_OT_Facts.eq_lt.
(* Check sort_lt_nodup. *)

Lemma sort_lt_ext : forall l1 l2,
  sort S.E.lt l1 -> sort S.E.lt l2 ->
  (forall a, InA S.E.eq a l1 <-> InA S.E.eq a l2) -> l1 = l2. 
Proof.
  intros.
  gen l2; induction H; intros.
      destruct* l2.
    use (proj2 (H1 t) (InA_cons_hd l2 (refl_equal t))).
    inversions H.
  inversions H1.
    use (proj1 (H2 a) (InA_cons_hd l (refl_equal a))).
    inversion H3.
  destruct (S.E.compare a a0).
      elim (sort_lt_notin H1 (cons_leA _ _ _ _ l1)).
      apply* (proj1 (H2 a)).
    rewrite <- e in *. clear e a0.
    rewrite* (IHsort l0).
    intro; split; intro.
      destruct (a0 == a).
        subst.
        elim (sort_lt_notin H H0 H5).
      use (proj1 (H2 a0) (InA_cons_tl a H5)).
      inversions* H6.
    destruct (a0 == a).
      subst.
      elim (sort_lt_notin H3 H4 H5).
    use (proj2 (H2 a0) (InA_cons_tl a H5)).
    inversions* H6.
  elim (sort_lt_notin (cons_sort H H0) (cons_leA _ _ _ _ l1)).
  apply* (proj2 (H2 a0)).
Qed.

Lemma remove_union : forall a L1 L2,
  S.remove a (L1 \u L2) = S.remove a L1 \u S.remove a L2.
Proof.
  intros; apply eq_ext; intro; split; intro.
    destruct (a == a0).
      elim (S.remove_1 e H).
    destruct (S.union_1 (S.remove_3 H)); eauto with sets.
  destruct (a == a0).
    destruct (S.union_1 H); elim (S.remove_1 e H0).
  apply* S.remove_2.
  destruct (S.union_1 H); eauto with sets.
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
    apply S.diff_3. eauto with sets.
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

Lemma sort_tl : forall a l, sort S.E.lt (a::l) -> sort S.E.lt l.
Proof.
  intros. inversions* H.
Qed.

Lemma sort_lelistA : forall a l,
  sort S.E.lt (a::l) -> lelistA S.E.lt a l.
Proof.
  intros. inversions* H.
Qed.

Hint Resolve sort_tl sort_lelistA.

Lemma sort_split : forall y l2 l1,
  sort S.E.lt (l1 ++ y :: l2) -> sort S.E.lt (l1 ++ l2).
Proof.
  induction l1; simpl; intros. eauto.
  constructor. eauto.
  destruct l1; simpl in *.
    inversions H.
    inversions H3.
    apply* (InfA_ltA S.E.lt_trans).
    inversions* H.
  inversions* H3.
Qed.

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

Lemma remove_idem : forall a L,
  S.remove a (S.remove a L) = S.remove a L.
Proof.
  intros; apply eq_ext; intro; split; intro.
    apply* S.remove_3.
  apply* S.remove_2.
  intro. elim (S.remove_1 H0 H).
Qed.

Lemma elements_remove : forall a L,
  S.elements (S.remove a L) = removeA eq_var_dec a (S.elements L).
Proof.
  intros.
  remember (S.elements L) as elts.
  gen L; induction elts; simpl; intros.
    apply sort_lt_ext. apply S.elements_3.
      auto.
    intro; split; intro.
      use (S.elements_1 (S.remove_3 (S.elements_2 H))).
      rewrite <- Heqelts in H0.
      inversion H0.
    inversion H.
  destruct (a == a0).
    subst.
    rewrite <- (IHelts (S.remove a0 L)).
      rewrite* remove_idem.
    apply sym_eq.
    apply* elements_tl.
  rewrite <- (IHelts (S.remove a0 L)); clear IHelts.
    apply sort_lt_ext. apply S.elements_3.
      constructor. apply S.elements_3.
      apply (InA_InfA S.E.eq_refl).
      intros.
      use (S.remove_3 (S.elements_2 H)).
      use (elements_tl (sym_equal Heqelts)).
      use (S.elements_1 H0).
      rewrite H1 in H2.
      use (S.elements_3 L).
      rewrite <- Heqelts in H3.
      inversions H3.
      use (sort_lt_all a0 H6).
    rewrite remove_remove.
    intro; split; intro.
      destruct* (a1 == a0).
      apply InA_cons_tl.
      auto with sets.
    destruct (a0 == a1).
      subst.
      apply S.elements_1.
      apply* S.remove_2.
      apply S.elements_2.
      rewrite* <- Heqelts.
    inversions H. elim n0; auto.
    eauto with sets.
  rewrite* <- (@elements_tl a0 elts L).
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
  use (elements_tl (sym_equal Heqelts2)).
  assert (a \in L2).
    apply S.elements_2.
    rewrite* <- Heqelts2.
  assert (InA S.E.eq a elts).
    subst.
    auto with sets.
  subst.
  destruct (InA_split H1) as [l1 [y [l2 [Hl1 Hl]]]].
  rewrite Hl.
  rewrite app_length.
  simpl. rewrite <- plus_n_Sm.
  rewrite <- app_length.
  apply (f_equal S).
  apply* (IHelts2 (S.remove a L1) (S.remove a L2)); clear IHelts2.
    apply (f_equal S.elements).
    rewrite* diff_remove.
  apply sort_lt_ext.
      use (S.elements_3 (L1 \u L2)).
      rewrite Hl in H.
      apply* sort_split.
    apply S.elements_3.
  intro; split; intro.
    apply S.elements_1.
    rewrite <- remove_union.
    rewrite <- Hl1 in *; clear Hl1 y.
    use (S.elements_3 (L1 \u L2)).
    destruct (a == a0).
      rewrite Hl in H2.
      use (sort_lt_nodup H2).
      destruct (nodup_notin_split _ _ _ H3).
      subst; destruct* (InA_app H).
    apply* S.remove_2.
    apply S.elements_2.
    rewrite Hl.
    clear -H.
    induction l1; simpl in *. auto.
    inversions* H.
  rewrite <- Hl1 in *; clear Hl1 y.
  use (S.elements_2 H).
  rewrite <- remove_union in H2.
  use (S.remove_3 H2).
  use (S.elements_1 H3).
  rewrite Hl in H4.
  clear -H2 H4.
  induction l1; simpl in *; inversions* H4.
  elim (S.remove_1 (sym_equal H0) H2).
Qed.

Lemma cardinal_remove : forall a L,
  a \in L ->
  S (S.cardinal (S.remove a L)) = S.cardinal L.
Proof.
  intros.
  repeat rewrite S.cardinal_1.
  rewrite elements_remove.
  use (sort_lt_nodup (S.elements_3 L)).
  use (S.elements_1 H).
  clear H; induction H1.
    rewrite H.
    simpl.
    destruct* (y == y).
    inversions H0.
    clear -H3; induction l. auto.
    simpl.
    destruct (y==a). elim H3; auto.
    simpl; rewrite* IHl.
  simpl.
  inversions H0.
  destruct* (a==y). 
  subst*.
Qed.

Lemma remove_subset : forall x L1 L2, L1 << L2 ->
  forall y, y \in S.remove x L1 -> y \in S.remove x L2.
Proof.
  intros.
  apply S.remove_2.
    intro Hx; elim (S.remove_1 Hx H0).
  apply H; apply* S.remove_3.
Qed.

Lemma cardinal_subset : forall L1 L2,
  L1 << L2 -> S.cardinal L1 <= S.cardinal L2.
Proof.
  intro.
  repeat rewrite S.cardinal_1.
  remember (S.elements L1) as elts1.
  gen L1; induction elts1; simpl; intros.
    omega.
  use (elements_tl (sym_eq Heqelts1)).
  use (IHelts1 _ (sym_eq H0) (S.remove a L2)).
  use (H1 (remove_subset H)).
  assert (a \in L2).
    apply H.
    apply S.elements_2.
    rewrite* <- Heqelts1.
  rewrite <- (cardinal_remove H3).
  omega.
Qed.
