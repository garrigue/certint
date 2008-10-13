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

