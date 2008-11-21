Theorem unify_monotone : forall h pairs K1 S1 K1' S1' K0 S0,
  unify h pairs K1 S1 = Some (K1', S1') ->
  extends S1 S0 -> well_subst K0 (map (kind_subst S1) K1) S1 ->
  is_subst S1 -> ok K1 -> disjoint (dom S1) (dom K1) ->
  is_subst S0 -> ok K0 ->
  exists h', exists K0', exists S0',
    unify h' pairs K0 S0 = Some (K0', S0') /\
    extends S1' S0' /\ well_subst K0' (map (kind_subst S1') K1') S1'.
Proof.
  intros until S0; intros HU Hext WS HS1 HK1 Dis1 HS0 HK0.
  poses Hext1 (typ_subst_extend _ _ _ HS1 HU).
  assert (Hext': extends S1' S0) by apply* extends_trans.
  destruct* (unify_kinds_ok _ _ HU) as [HK1' [Dis1' WS1']].
  assert (WS': well_subst K0 (map (kind_subst S1') K1') S1').
    intro; intros.
    use (WS _ _ H).
    rewrite <- Hext1.
    rewrite <- (kind_subst_combine _ _ _ k Hext1).
    inversions H0.  auto.
    destruct (binds_map_inv _ _ H4) as [k1 [Hk1 Bk1]].
    use (WS1' _ _ Bk1).
    simpl. rewrite <- H2.
    rewrite <- (kind_subst_combine _ _ _ k1 Hext1) in H3.
    rewrite Hk1 in H3.
    inversions H3.
    simpl; rewrite <- H7. clear H2 H7.
    eapply wk_kind. apply H9.
    apply* entails_trans. apply* kind_subst_entails.
  exists (1 + size_pairs S0 K0 pairs).
  assert (Hunif: unifies S1' pairs) by apply* (unify_types _ _ _ HU).
  assert (unify (1 + size_pairs S0 K0 pairs) pairs K0 S0 <> None).
    apply* (unify_complete0 (K:=map (kind_subst S1') K1') (S:=S1')).
  case_rewrite (unify (1 + size_pairs S0 K0 pairs) pairs K0 S0) R1;
    try (elim H; reflexivity).
  destruct p as [K0' S0']. clear H.
  esplit; esplit; split*.
  destruct* (unify_mgu0 _ R1 (K':=map (kind_subst S1') K1') (S':=S1')).
Qed.

Lemma fv_in0_strengthen : forall (A:Set) (fv:A->vars) x E L,
  x # E -> fv_in0 fv E (L \u {{x}}) = fv_in0 fv E L.
Proof.
  induction E; intros.
    reflexivity.
  simpl. destruct a; simpl.
  simpl in H.
  case_eq (S.mem v L); introv R1.
    assert (S.mem v (L \u {{x}}) = true) by auto with sets.
    rewrite H0.
    apply* IHE.
  puts (mem_3 R1).
  case_eq (S.mem v (L \u {{x}})); introv R2.
    use (S.mem_2 R2).
    elim H0. sets_solve.
    elim H; auto.
  rewrite <- union_assoc. rewrite (union_comm {{x}}). rewrite union_assoc.
  rewrite* IHE.
Qed.

Lemma concat_empty_l : forall (A:Set) (E:env A),
  empty & E = E.
Proof.
  unfold concat, empty. intros; rewrite* <- app_nil_end.
Qed.

Lemma incl_map : forall (A:Set) (f:A->A) E1 E2,
  incl E1 E2 -> incl (map f E1) (map f E2).
Proof.
  intros; intro; intros.
  destruct a.
  destruct (in_map_inv _ _ _ _ H0) as [b [HE B]].
  subst.
  rewrite <- map_snd_env_map.
  apply (in_map (fun p:var*A => (fst p, f (snd p))) _ _ (H _ B)).
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

Lemma typ_fv_subst_keep : forall S T,
  typ_fv T << typ_fv (typ_subst S T) \u dom S.
Proof.
  induction T; simpl; sets_solve.
  case_eq (get y S); introv R1.
    use (binds_dom R1).
  simpl*.
Qed.

Lemma fv_in_typ_subst : forall S S0,
  fv_in typ_fv S0 << fv_in typ_fv (map (typ_subst S) S0) \u dom S.
Proof.
  induction S0; simpl; intros y Hy. auto.
  destruct a. simpl.
  sets_solve.
  use (typ_fv_subst_keep S t).
Qed.

Lemma kind_fv_subst_keep : forall S k,
  kind_fv k << kind_fv (kind_subst S k) \u dom S.
Proof.
  unfold kind_fv; destruct k as [[kc kv kr kh]|]; simpl*.
  clear kh; induction kr; simpl*.
  use (typ_fv_subst_keep S (snd a)).
Qed.

Lemma fv_in_remove_env : forall (A:Set) fv v (a:A) E,
  binds v a E ->
  fv_in fv E << fv a \u fv_in fv (remove_env E v).
Proof.
  unfold binds; induction E; simpl; intros. discriminate.
  destruct a0.
  destruct (v == v0).
    inversions* H.
  simpl*.
Qed.

Lemma remove_env_idem : forall (A:Set) v (E:env A),
  v # E -> remove_env E v = E.
Proof.
  induction E; simpl; intros. auto.
  destruct a.
  destruct (v == v0).
    elim H; subst*.
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
  rewrite* (remove_env_idem _ H0).
Qed.

Lemma unify_keep_fv : forall K S E h pairs K0 S0,
  Body.unify h pairs K0 S0 = Some (K, S) ->
  is_subst S0 -> ok K0 ->
  fvs S0 K0 E << fvs S K E.
Proof.
  intros until 2.
  apply* (unify_ind (K':=K) (S':=S)
    (fun K0 S0 _ => ok K0 -> fvs S0 K0 E << fvs S K E));
    clear H H0 K0 S0 pairs h.
    intros until K1.
    unfold K1, S1, fvs; clear K1 S1.
    intros _ R1 R2 _ _ _ R4 IH HK0 y Hy.
    apply* IH; clear IH.
    unfold compose.
    rewrite dom_concat. rewrite* dom_remove_env.
    rewrite dom_map. rewrite fv_in_concat.
    simpl dom.
    sets_solve.
        puts (fv_in_typ_subst (v ~ T) _ H0); simpl in *. sets_solve.
      destruct (v == y); subst*.
    use (kind_fv_in_remove_env v _ H0).
    rewrite R4 in H.
    replace (kind_fv None) with {} in H by reflexivity.
    auto.
  intros until K1.
  unfold K1, S1, fvs; clear K1 S1.
  intros R3 HU _ _ _ HSv n IH HK0.
  assert (ok (remove_env (remove_env K0 v) v0 & v0 ~ k)).
    apply* ok_push.
    rewrite* dom_remove_env.
  poses HS (IH H); clear IH H.
  unfold compose in HS. repeat rewrite dom_concat in HS.
  rewrite dom_map in HS. repeat rewrite fv_in_concat in HS.
  simpl in HS. simpl.
  do 2 rewrite dom_remove_env in HS; auto.
  sets_solve.
      apply HS.
      use (fv_in_typ_subst (v ~ typ_fvar v0) _ H0).
      simpl in H; auto.
    apply HS.
    destruct (v == y). subst*.
    destruct* (v0 == y). subst*.
  poses Hun (unify_types _ _ _ HU HSv).
  destruct (unify_kinds_sound _ _ (S:=S) R3).
    intro; intros. apply* Hun.
  puts (kind_fv_in_remove_env v _ H0).
  clear H0 Hun; sets_solve.
    use (kind_fv_subst_keep S _ H0).
    sets_solve.
    use (kind_entails_fv _ _ H H3).
    use (kind_fv_subst _ _ H2).
  puts (kind_fv_in_remove_env v0 _ H0).
  clear H H0 R3; sets_solve.
  unfold get_kind in *.
  case_rewrite (get v0 K0) R3.
    rewrite (binds_remove_env (v:=v) R3) in H.
      use (kind_fv_subst_keep S _ H); clear H.
      sets_solve.
      puts (kind_entails_fv _ _ H1 H).
      use (kind_fv_subst _ _ H0).
    auto*.
  rewrite get_notin_dom in H. elim (in_empty H).
  rewrite* dom_remove_env.
  intro. elim (get_none_notin _ R3). auto.
Qed.

Lemma diff_union_l : forall L1 L2 L3,
  S.diff (L1 \u L2) L3 = S.diff L1 L3 \u S.diff L2 L3.
Proof.
  intros.
  apply eq_ext; intro; split; intros; auto.
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

Lemma fv_subset_abs : forall S K E T Ts X1 X2 x,
  unifies S ((typ_arrow X1 X2, T) :: nil) ->
  fvs S K E T Ts = fvs S K ((x, Sch X1 nil) :: E) X2 (T::Ts).
Proof.
  intros.
  unfold fvs, env_fv; simpl.
  apply eq_ext; intro y; simpl; split*.
  unfold sch_fv.
  simpl.
  intro Hy; sets_solve;
    assert (y \in typ_fv (typ_arrow X1 X2)) by (simpl; auto with sets);
    use (typ_fv_subst_keep S _ H0);
    rewrite (H (typ_arrow X1 X2) T) in H2; simpl*;
    destruct* (S.union_1 H2); clear H0 H1 H2;
    use (typ_fv_subst _ _ H3).
Qed.

Lemma unifies_extends : forall S1 S2 l,
  unifies S1 l -> extends S2 S1 -> unifies S2 l.
Proof.
  intros; intro; intros.
  rewrite <- (H0 T1); rewrite <- (H0 T2).
  apply (f_equal (typ_subst S2)).
  apply* H.
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
  incl E E' /\ incl E' E /\ ok E'.
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
     split*. fold (@empty A); auto.
  simpl.
  case_eq (f (@pair var A x a)); intros.
    split. simpl.
      destruct* IHok.
    apply* ok_cons.
  split*.
Qed.

Lemma binds_filter : forall (A:Set) f x (a:A) E,
  binds x a (filter f E) -> ok E -> binds x a E /\ f (x,a) = true.
Proof.
  intros.
  poses Hin (binds_in H).
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
    use (binds_in (H0 _ _ R2)).
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
