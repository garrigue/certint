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
