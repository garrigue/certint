Lemma elements_mkset : forall l,
  sort S.E.lt l -> S.elements (mkset l) = l.
Proof.
  intros.
  puts (S.elements_3 (mkset l)).
  apply* sort_lt_ext.
  intros; split; intro.
    use (mkset_in _ (S.elements_2 H1)).
  apply S.elements_1. apply in_mkset.
  clear -H1; induction H1. rewrite* H. simpl*.
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

Lemma subset_remove_both : forall v L1 L2,
  L1 << L2 -> S.remove v L1 << S.remove v L2.
Proof.
  intros.
  intros y Hy.
  destruct (v == y).
    elim (S.remove_1 e Hy).
  apply* S.remove_2.
  apply H.
  apply* S.remove_3.
Qed.

Lemma binds_subst_dom : forall (A:Set) x (a:A) Xs Ys Ks L,
  fresh L (length Xs) Ys ->
  binds x a (combine Xs Ks) ->
  exists y,
    binds x (typ_fvar y) (combine Xs (typ_fvars Ys)) /\
    binds y a (combine Ys Ks).
Proof.
  induction Xs; destruct Ys; intros; try discriminate.
    contradiction.
  destruct Ks. discriminate.
  unfold binds in *; simpl in *.
  destruct (x == a0).
    esplit; split*. destruct* (v == v).
  destruct* (IHXs Ys Ks (L \u {{v}})) as [y [Bx By]].
  esplit; split*.
  destruct* (y == v).
  subst.
  destruct (fresh_disjoint _ _ _ (proj2 H) v).
    elim H1.
    use (binds_combine _ _ Bx).
    unfold typ_fvars in H2.
    destruct (proj1 (in_map_iff _ _ _) H2).
    destruct H3. inversions H3.
    apply* in_mkset.
  notin_contradiction.
Qed.

(* Preuves pour une autre version de fv_in *)

Lemma fv_in0_subset : forall (A:Set) (fv:A->vars) E L1 L2,
  L2 << L1 -> fv_in0 fv E L1 << fv_in0 fv E L2.
Proof.
  induction E; simpl; intros.
    auto.
  destruct a.
  case_eq (S.mem v L1); introv R1; case_eq (S.mem v L2); introv R2.
     auto.
    assert (L2 \u {{v}} << L1).
      sets_solve. auto with sets.
    use (IHE _ _ H0).
   elim (mem_3 R1).
   apply H; auto with sets.
  assert (L2 \u {{v}} << L1 \u {{v}}) by auto.
  use (IHE _ _ H0).
Qed.

Lemma fv_in_concat : forall (A:Set) (fv:A->vars) E F,
  fv_in fv (E & F) << fv_in fv F \u fv_in fv E.
Proof.
  intros.
  unfold fv_in.
  fold (fv_in fv E).
  generalize {}.
  induction F; simpl; intros.
    unfold fv_in.
    rewrite union_empty_l.
    apply* fv_in0_subset.
  destruct a. destruct* (S.mem v t).
  sets_solve.
  use (IHF _ _ H).
Qed.

