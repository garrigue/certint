(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, August 2008                                            *
***************************************************************************)

Set Implicit Arguments.

Require Import List Arith Metatheory Cardinal.
Require Import ML_SP_Definitions ML_SP_Unify_wf.

Module MkInfer(Cstr:CstrIntf)(Const:CstIntf).

Module Unify := MkUnify(Cstr)(Const).
Import Unify.
Import MyEval.
Import Rename.
Import Sound.
Import Infra.
Import Defs.
Import Metatheory_Env.Env.

Module Mk2(Delta:DeltaIntf).

Module MyEval2 := MyEval.Mk2(Delta).
Import MyEval2.Rename2.
Import Sound2.
Import JudgInfra.
Import Judge.
Import Unify.

(* Free variables in the inference environment *)

Definition fvs S K E :=
  dom S \u fv_in typ_fv S \u dom K \u fv_in kind_fv K \u env_fv E.

(* Prepare for inclusion of free variables *)

Lemma typ_fv_subst0 : forall S T,
  typ_fv (typ_subst S T) << S.diff (typ_fv T) (dom S) \u fv_in typ_fv S.
Proof.
  induction T; simpl; intros x Hx. elim (in_empty Hx).
    case_rewrite R1 (get v S).
      use (fv_in_spec typ_fv _ _ _ (binds_in R1)).
    puts (get_none_notin _ R1).
    simpl in Hx. auto.
  auto.
Qed.

Lemma typ_fv_subst : forall S T,
  typ_fv (typ_subst S T) << typ_fv T \u fv_in typ_fv S.
Proof.
  intros; intros y Hy.
  use (typ_fv_subst0 _ _ Hy).
Qed.

Lemma kind_fv_subst : forall S k,
  kind_fv (kind_subst S k) << S.diff (kind_fv k) (dom S) \u fv_in typ_fv S.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|].
    unfold kind_fv; simpl.
    clear kh; induction kr; simpl; intros x Hx; auto.
    destruct* (S.union_1 Hx).
    use (typ_fv_subst0 _ _ H).
  unfold kind_fv; simpl*.
Qed.

Lemma fv_in_typ_subst : forall S S0,
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
  sets_solve.
  apply* fv_in_typ_subst.
Qed.

Hint Resolve ok_remove_env.

Lemma ok_remove_add_env : forall (A:Set) E v (a:A),
  ok E -> ok (remove_env E v & v ~ a).
Proof.
  intros. apply* ok_push.
  rewrite* dom_remove_env.
Qed.

Hint Resolve ok_remove_add_env.

Lemma kind_subst_id : forall k, kind_subst id k = k.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|]; simpl*.
  apply kind_pi; simpl*.
  clear kh; induction* kr.
  destruct a; simpl. rewrite IHkr. rewrite* typ_subst_id.
Qed.

Lemma fv_in_kind_subst : forall S K,
  fv_in kind_fv (map (kind_subst S) K) <<
    S.diff (fv_in kind_fv K) (dom S) \u fv_in typ_fv S.
Proof.
  induction K; simpl; intros y Hy. auto.
  destruct a. simpl in Hy.
  use (kind_fv_subst S k).
Qed.

Lemma unify_keep_fv : forall K S E T1 T2 K0 S0,
  unify_spec ((T1,T2)::nil) K0 S0 (Some (K, S)) ->
  fvs S K E << fvs S0 K0 E \u typ_fv T1 \u typ_fv T2.
Proof.
  intros.
  rewrite <- union_assoc.
  replace (typ_fv T1 \u typ_fv T2) with (all_fv id ((T1,T2)::nil))
  by (unfold all_fv; simpl; do 2 rewrite typ_subst_id; rewrite* union_empty_r).
  apply* (unify_ind (K':=K) (S':=S)
    (fun K0 S0 pairs => ok K0 -> fvs S K E << fvs S0 K0 E \u all_fv id pairs));
    clear H K0 S0 T1 T2.
       intros until K1.
       subst K1 S1. unfold fvs in *.
       intros _ R1 R2 _ R4 IH _ y Hy.
       forward ~IH as G; clear IH.
       unfold all_fv; simpl. repeat rewrite typ_subst_id.
       fold (all_fv id pairs).
       rewrite dom_remove_env in G by auto.
       puts (G _ Hy); clear G Hy.
       sets_solve.
         unfold compose in H0; rewrite dom_concat, dom_map in H0.
         simpl in H0.
         puts (typ_fv_subst S0 t). rewrite R1 in H. simpl in H.
         use (singleton_subset H).
        puts (fv_in_compose (v ~ T) S0 H0).
        simpl in H.
        puts (typ_fv_subst S0 t0). rewrite R2 in H1. auto.
       use (fv_in_remove_env _ _ K0 H0).
      intros until K1. subst S1 K1.
      unfold fvs.
      intros Uk _ R1 R2 n IH _ y Hy.
      forward~ IH as G; clear IH.
      puts (G _ Hy); clear G Hy.
      unfold all_fv; simpl. repeat rewrite typ_subst_id.
      fold (all_fv id pairs).
      rewrite dom_concat in H.
      do 2 rewrite dom_remove_env in H by auto. simpl in H.
      puts (typ_fv_subst S0 t). rewrite R1 in H0. simpl in H0.
      puts (singleton_subset H0); clear H0.
      puts (typ_fv_subst S0 t0). rewrite R2 in H0. simpl in H0.
      puts (singleton_subset H0); clear H0.
      puts (unify_kinds_fv _ _ id Uk).
      rewrite all_fv_app in H.
      rewrite kind_subst_id in H0.
      puts (get_kind_fv_in id v K0).
      puts (get_kind_fv_in id v0 K0).
      puts (fv_in_kind_subst id K0).
      replace (fv_in typ_fv id) with {} in H5 by (unfold id; simpl*).
      sets_solve.
        unfold compose in H6; rewrite dom_concat, dom_map in H6.
        simpl in H6. auto.
       puts (fv_in_compose _ _ H6). simpl in H. auto.
      puts (fv_in_remove_env _ _ (remove_env K0 v) H).
      use (fv_in_remove_env _ _ K0 H6).
     unfold all_fv; simpl; intros. use (H2 H3).
    unfold all_fv; simpl; intros. use (H2 H3).
   unfold all_fv; simpl; intros.
   repeat rewrite typ_subst_id in *.
   puts (typ_fv_subst S0 t).
   puts (typ_fv_subst S0 t0).
   rewrite H0 in H4; rewrite H1 in H5.
   simpl in *.
   puts (H2 H3).
   clear -H4 H5 H6.
   unfold fvs in *. auto.
  unfold all_fv; simpl; intros.
  use (H H0).
Qed.

(* Dependently typed unification *)

Definition unify_dep T1 T2 K S :
  is_subst S -> ok K ->
  disjoint (dom S) (dom K) ->
  let res :=  unify_spec ((T1,T2)::nil) K S in
  {KS' | res (Some KS') /\ let (K',S') := KS' in
    (ok K' /\ is_subst S' /\ disjoint (dom S') (dom K')) /\
    (forall E, fvs S' K' E << fvs S K E \u typ_fv T1 \u typ_fv T2)}
  +{res None}.
Proof.
  introv HS HK D. intro.
  subst res.
  puts (@unify_spec_sound ((T1,T2)::nil) _ _ HS HK (lt2_wf _)).
  destruct (unify HS HK (lt2_wf (size_pairs2 S K ((T1, T2) :: nil)))).
    left; esplit; split*.
    destruct p.
    split.
    revert H HK D.
    eapply (unify_ind
      (fun K S p => ok K -> disjoint (dom S) (dom K) ->
        ok k /\ is_subst s /\ disjoint (dom s) (dom k))); auto.
      auto*.
    clear; intros.
    apply* H4; clear H0 H4.
    unfold S1, K1.
    unfold compose; simpl.
    rewrite dom_concat, dom_map; simpl.
    do 2 rewrite dom_remove_env by auto.
    use (typ_subst_res_fresh' _ HS H2).
   intros.
   apply* unify_keep_fv.
  right*.
Qed.

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

Section SplitEnv.
Variables (A:Set) (B:vars).

Fixpoint split_env (E:env A) : env A * env A :=
  match E with
  | nil => (nil, nil)
  | xk::E' =>
    let (Eb, EB) := split_env E' in
    if S.mem (fst xk) B then (Eb, xk::EB) else (xk::Eb, EB)
  end.

Lemma split_env_ok : forall E Eb EB,
  split_env E = (Eb, EB) -> ok E ->
  ok (EB & Eb) /\ disjoint B (dom Eb) /\ dom EB << B /\
  incl E (EB & Eb) /\ incl (EB & Eb) E.
Proof.
  intros.
  revert Eb EB H.
  induction H0; intros.
    inversions H. simpl. env_fix; auto.
  simpl in H1.
  case_rewrite R1 (split_env E).
  case_rewrite R2 (S.mem x B).
    inversions H1; clear H1.
    env_fix.
    destruct~ (IHok Eb e0) as [Hok [Dis [Dom [I1 I2]]]]; clear IHok.
    destruct (ok_concat_inv _ _ Hok).
    case_eq (get x (e0 & Eb)); intros.
      assert (binds x a0 E) by auto.
      elim (binds_fresh H4 H).
    poses Hv' (get_none_notin _ H3); clear H3.
    puts (S.mem_2 R2).
    split4*.
    split; intro; simpl; intros.
      destruct H4. apply* in_or_concat.
      destruct* (in_app_or _ _ _ (I1 _ H4)).
    destruct* (in_app_or _ _ _ H4).
    destruct* H5.
  inversions H1; clear H1.
  env_fix.
  destruct* (IHok e EB) as [Hok [Dis [Dom [I1 I2]]]]; clear IHok.
  case_eq (get x (EB & e)); intros.
    assert (binds x a0 E) by auto.
    elim (binds_fresh H2 H).
  use (get_none_notin _ H1).
Qed.
End SplitEnv.

Definition vars_subst S L :=
  typ_fv_list (List.map (fun x => typ_subst S (typ_fvar x)) (S.elements L)).

Definition typinf_generalize K' E' L T1 :=
  let ftve := close_fvk K' (env_fv E') in
  let (K'', KA) := split_env ftve K' in
  let B := close_fvk K' (typ_fv T1) in
  let (_, KB) := split_env B K'' in
  let (Bs, Ks) := split KB in
  let Bs' := S.elements (S.diff B (ftve \u dom KB)) in
  let Ks' := List.map (fun x:var => @None ckind) Bs' in
  let (_, KC) := split_env L K'' in
  (KA & KC, sch_generalize (Bs++Bs') T1 (Ks++Ks')).

Fixpoint kdom (E : kenv) : vars :=
  match E with
  | nil => {}
  | (x, Some _) :: E' => {{x}} \u kdom E'
  | _ :: E' => kdom E'
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

Lemma trm_depth_open : forall x t,
  trm_depth (t ^ x) = trm_depth t.
Proof.
  intros; unfold trm_open.
  generalize 0; induction t; intros; simpl*.
  destruct (n0 === n); reflexivity.
Qed.

Lemma dom_inv_abs : forall t t1 x,
   Acc lt (trm_depth t) ->
   t = trm_abs t1 -> Acc lt (trm_depth (t1 ^ x)).
Proof.
  introv P eq.
  rewrite eq in P.
  rewrite trm_depth_open.
  simpl in P.
  pose (P1 := le_n (S (trm_depth t1))).
  exact (Acc_inv P _ P1).
Defined.

Lemma lt_max_l : forall n1 n2, n1 < (S (Max.max n1 n2)).
Proof.
  intros; puts (Max.le_max_l n1 n2); auto with arith.
Qed.

Lemma lt_max_r : forall n1 n2, n2 < (S (Max.max n1 n2)).
Proof.
  intros; puts (Max.le_max_r n1 n2); auto with arith.
Qed.

Ltac dom_inv_tac :=
  intros t t1 t2 P eq;
  rewrite eq in P;
  simpl in P;
  try rewrite trm_depth_open;
  solve [exact (Acc_inv P _ (lt_max_l (trm_depth t1) (trm_depth t2)))
        |exact (Acc_inv P _ (lt_max_r (trm_depth t1) (trm_depth t2)))].

Lemma dom_inv_app1 : forall t t1 t2,
   Acc lt (trm_depth t) ->
   t = trm_app t1 t2 -> Acc lt (trm_depth t1).
Proof. dom_inv_tac. Defined.

Lemma dom_inv_app2 : forall t t1 t2,
   Acc lt (trm_depth t) ->
   t = trm_app t1 t2 -> Acc lt (trm_depth t2).
Proof. dom_inv_tac. Defined.

Lemma dom_inv_let1 : forall t t1 t2,
   Acc lt (trm_depth t) ->
   t = trm_let t1 t2 -> Acc lt (trm_depth t1).
Proof. dom_inv_tac. Defined.

Lemma dom_inv_let2 : forall x t t1 t2,
   Acc lt (trm_depth t) ->
   t = trm_let t1 t2 -> Acc lt (trm_depth (t2 ^ x)).
Proof. intro; dom_inv_tac. Defined.

Lemma dom_K_L : forall S K E T L,
  fvs S K E \u typ_fv T << L -> dom K << L.
Proof.
  unfold fvs; intros. auto.
Qed.

Lemma disjoint_fvar : forall S K E T L M Vs,
  disjoint (dom S) (dom K) ->
  fvs S K E \u typ_fv T << L ->
  fresh L (sch_arity M) Vs ->
  disjoint (dom S) (dom (K & kinds_open_vars (sch_kinds M) Vs)).
Proof.
  intros.
  rewrite dom_concat.
  rewrite* dom_kinds_open_vars.
  unfold fvs in H0. auto.
Qed.

Lemma subset_abs : forall S K E L S' K' v1 v2 T x,
  fvs S K E \u typ_fv T << L ->
  fvs S' K' E << fvs S K E \u ({{v1}} \u {{v2}}) \u typ_fv T ->
  fvs S' K' (E & x ~ Sch (typ_fvar v1) nil) \u {{v2}} <<
  L \u {{v1}} \u {{v2}}.
Proof.
  intros.
  unfold fvs in *.
  unfold env_fv. rewrite fv_in_concat. fold (env_fv E).
  unfold sch_fv; simpl*.
Qed.

Lemma subset_let1 : forall L0 L1 L2 L,
  L0 \u L1 << L -> L0 \u L2 << L \u L2.
Proof.
  intros; auto.
Qed.

Lemma typ_fv_generalize : forall Xs T,
  typ_fv (typ_generalize Xs T) << typ_fv T.
Proof.
  induction T; simpl; intros y Hy; auto.
  destruct* (index eq_var_dec 0 v Xs).
Qed.

Lemma kinds_fv_generalize : forall Bs Ks,
  kind_fv_list (List.map (kind_map (typ_generalize Bs)) Ks) << kind_fv_list Ks.
Proof.
  intros. unfold kind_fv_list.
  induction Ks; simpl*.
  sets_solve.
  apply S.union_2.
  unfold kind_fv in *.
  clear IHKs Ks; destruct a as [[kc kv kr kh]|]; simpl in *.
    clear kh; induction kr; simpl in *. auto.
    sets_solve.
      use (typ_fv_generalize _ _ H0).
    apply* S.union_3.
  auto.
Qed.

Lemma sch_fv_generalize : forall Bs T Ks,
  sch_fv (sch_generalize Bs T Ks) << sch_fv (Sch T Ks).
Proof.
  intros.
  unfold sch_generalize, sch_fv; simpl.
  sets_solve. use (typ_fv_generalize _ _ H).
  use (kinds_fv_generalize _ _ H).
Qed.

Lemma fv_in_kind_fv_list : forall Xs Ks,
  length Xs = length Ks ->
  fv_in kind_fv (combine Xs Ks) = kind_fv_list Ks.
Proof.
  induction Xs; destruct Ks; simpl; intros; try discriminate.
    auto.
  inversion H.
  rewrite* IHXs.
Qed.

Lemma ok_generalize : forall K0 K1 S' S E T L v L' L0 x,
  ok K0 -> disjoint (dom S') (dom K0) ->
  fvs S K1 E \u typ_fv T << L ->
  fvs S' K0 E \u (L \u {{v}}) << L' ->
  let K := Env.map (kind_subst S') K0 in
  let E' := Env.map (sch_subst S') E in
  let T1 := typ_subst S' (typ_fvar v) in
  let KAM := typinf_generalize K E' L0 T1 in
  ok (fst KAM) /\ disjoint (dom S') (dom (fst KAM)) /\
  fvs S' (fst KAM) (E & x ~ snd KAM) \u typ_fv T << L'.
Proof.
  introv HK0 D' HL HL'; intros.
  unfold KAM; clear KAM.
  unfold typinf_generalize.
  case_eq (split_env (close_fvk K (env_fv E')) K); introv R1.
  case_eq (split_env (close_fvk K (typ_fv T1)) e); introv R2.
  case_eq (split e2); introv R4.
  case_eq (split_env L0 e); introv R3.
  simpl.
  destruct (split_env_ok _ R1 (ok_map0 _ HK0)) as [Okee0 [De [HLe [I1 I2]]]].
  destruct (ok_concat_inv _ _ Okee0) as [Oke0 Oke].
  puts (ok_disjoint _ _ Okee0).
  destruct (split_env_ok _ R3 Oke) as [Oke34 [De2 [HLe2 [I3 I4]]]].
  destruct (ok_concat_inv _ _ Oke34) as [Oke4 Oke3].
  split.
    assert (dom e4 << dom e) by use (incl_subset_dom I4).
    auto.
  assert (incl (e0 & e4) K).
    intro; intros. apply I2.
    destruct (in_app_or _ _ _ H0); apply* in_or_app.
  puts (incl_subset_dom H0).
  split.
    clear -D' H1.
    subst K. rewrite dom_map in H1. auto.
  set (ftve := close_fvk K (env_fv E')).
  set (fvT := close_fvk K (typ_fv T1)).
  set (B := S.elements (S.diff fvT (ftve \u dom e2))).
  unfold fvs, env_fv. simpl.
  puts (@sch_fv_generalize (l++B) T1 (l0 ++ List.map (fun _ : var => None) B)).
  intros y Hy.
  apply HL'; clear HL' L'.
  unfold fvs; simpl.
  destruct (S.union_1 Hy); clear Hy; auto.
  destruct (S.union_1 H3); clear H3.
    unfold K in H1. rewrite dom_map in H1.
    sets_solve.
    puts (incl_fv_in_subset kind_fv H0 H3); clear H3.
    puts (fv_in_kind_subst S' K0 H4); clear H4.
    clear -H3; auto.
  unfold env_fv.
  destruct (S.union_1 H4); clear H4; auto.
  puts (H2 _ H3); clear H2 H3. unfold sch_fv in H4. simpl in H4.
  destruct (S.union_1 H4); clear H4.
    clear -H2. subst T1.
    use (typ_fv_subst S' _ H2).
  puts (split_combine _ R4).
  rewrite <- (fv_in_kind_fv_list (l ++ B)) in H2 by auto.
  rewrite combine_app in H2 by auto.
  rewrite H3 in H2.
  puts fv_in_concat. unfold concat in H4.
  rewrite H4 in H2; clear H4.
  destruct (S.union_1 H2); clear H2.
    assert (incl e2 K).
      intro; intros.
      destruct (split_env_ok _ R2 Oke) as [Oke12 [De1 [HLe1 [I5 I6]]]].
      apply I2.
      apply in_or_app; left*.
    puts (incl_fv_in_subset kind_fv H2 H4); clear H2 H4.
    puts (fv_in_kind_subst S' K0 H5); clear H5.
    clear -H2; auto.
  elimtype False; clear -H4.
  unfold kind_fv in H4.
  induction B; simpl in *. elim (in_empty H4).
  elim IHB. auto.
Qed.

Lemma subset_app1 : forall L0 L1 L L2,
  L0 \u L1 << L -> L0 \u (L2 \u L1) << L \u L2.
Proof.
  intros; auto.
Qed.

Lemma subset_app2 : forall L0 L L1 L',
  L0 \u (L \u L1) << L' -> L0 \u L1 << L'.
Proof.
  intros; auto.
Qed.

Lemma subset_fvar : forall S K E T L L0 x M Vs,
  fresh L (sch_arity M) Vs ->
  binds x M E ->
  fvs S K E \u typ_fv T << L ->
  L0 << fvs S (K & kinds_open_vars (sch_kinds M) Vs) E \u
  typ_fv (sch_open_vars M Vs) \u typ_fv T ->
  L0 \u L << L \u mkset Vs.
Proof.
  unfold fvs; simpl; introv Fr B HL.
  rewrite dom_concat.
  rewrite dom_kinds_open_vars by auto.
  rewrite fv_in_concat.
  puts (fv_in_kinds_open_vars (sch_kinds M) Vs).
  assert (sch_fv M << env_fv E) by apply* fv_in_spec.
  unfold sch_fv in H0; simpl in H0.
  intros; sets_solve.
  unfold sch_open_vars, typ_open_vars in H3; simpl in H3.
  puts (typ_fv_open _ _ H3).
  rewrite typ_fv_typ_fvars in H1.
  auto.
Qed.

Lemma subset_abs2 : forall S' K' E x L v1 v2 L',
  fvs S' K' (E & x ~ Sch (typ_fvar v1) nil) \u (L \u {{v1}} \u {{v2}}) << L' ->
  fvs S' K' E \u L << L'.
Proof.
  unfold fvs, env_fv, sch_fv; simpl; intros. auto.
Qed.

Lemma subset_let2 : forall L0 L v L' S' K' E x M L'',
  L0 \u (L \u {{v}}) << L' ->
  fvs S' K' (E & x ~ M) \u L' << L'' ->
  fvs S' K' E \u L << L''.
Proof.
  unfold fvs, env_fv; simpl; intros; auto.
Qed.

Lemma subset_app3 : forall L0 L L2 L' L1 L'',
  L0 \u (L \u L2) << L' ->
  L1 \u L' << L'' ->
  L1 \u L << L''.
Proof.
  intros; auto.
Qed.

Lemma subset_cst : forall S K E T L L0 c Vs,
  let M := Delta.type c in
  fresh L (sch_arity M) Vs ->
  fvs S K E \u typ_fv T << L ->
  L0 << fvs S (K & kinds_open_vars (sch_kinds M) Vs) E \u
  typ_fv (sch_open_vars M Vs) \u typ_fv T ->
  L0 \u L << L \u mkset Vs.
Proof.
  unfold fvs; simpl; intros until Vs.
  set (M:=Delta.type c). intros Fr HL.
  rewrite dom_concat.
  rewrite dom_kinds_open_vars by auto.
  rewrite fv_in_concat.
  puts (fv_in_kinds_open_vars (sch_kinds M) Vs).
  assert (sch_fv M << {}).
    puts (Delta.closed c). unfold M; rewrite* H0.
  unfold sch_fv in H0; simpl in H0.
  intros; sets_solve.
  unfold sch_open_vars, typ_open_vars in H3; simpl in H3.
  puts (typ_fv_open _ _ H3).
  rewrite typ_fv_typ_fvars in H1.
  auto.
Qed.

Definition get_dep (A:Set) x E : {a:A | binds x a E}+{x # E}.
Proof.
  intros.
  unfold binds; case_eq (get x E); intros.
    left; esplit; reflexivity.
  right. apply* get_none_notin.
Qed.

Definition typinf_res E L (res : kenv * subs * vars) :=
 let (KS',L') := res in let (K',S') := KS' in
 (ok K' /\ is_subst S' /\ disjoint (dom S') (dom K')) /\ fvs S' K' E \u L << L'.

Fixpoint typinf K E t T L S (h:Acc lt (trm_depth t)) (HS:is_subst S) (HK:ok K)
  (D:disjoint (dom S) (dom K)) (HL: fvs S K E \u typ_fv T << L) {struct h} :
  option (sig (typinf_res E L)) :=
  match t as t' return t = t' -> option (sig (typinf_res E L)) with
  | trm_bvar _ => fun eq => None
  | trm_fvar x => fun eq =>
    match get_dep x E with
    | inright _ => None
    | inleft (exist M eq1) =>
      let (Vs, Fr) := var_freshes L (sch_arity M) in
      match unify_dep (M ^ Vs) T HS
        (ok_kinds_open_vars _ _ HK (fresh_sub _ _ Fr (dom_K_L _ HL)))
        (disjoint_fvar _ _ _ D HL Fr) with
      | inleft (exist (K',S') (conj _ (conj HKSD' HL'))) =>
        Some (exist _ (K',S',L \u mkset Vs)
          (conj HKSD' (subset_fvar _ _ Fr eq1 HL (HL' E))))
      | inright _ => None
      end
    end
  | trm_abs t1 => fun eq =>
    let x := proj1_sig (var_fresh (dom E \u trm_fv t1)) in
    let v1 := proj1_sig (var_fresh L) in
    let v2 := proj1_sig (var_fresh (L \u {{v1}})) in
    match unify_dep (typ_arrow (typ_fvar v1) (typ_fvar v2)) T HS HK D with
    | inright _ => None
    | inleft (exist (K',S') (conj _ (conj (conj HK' (conj HS' D')) HL'))) =>
      match @typinf K' (E & x ~ Sch (typ_fvar v1) nil) (t1 ^ x) (typ_fvar v2)
        (L \u {{v1}} \u {{v2}}) S' (dom_inv_abs x h eq) HS' HK' D'
        (subset_abs _ HL (HL' E)) with
      | None => None
      | Some (exist (K',S',L') (conj HKSD' HL')) =>
        Some (exist _ (K',S',L') (conj HKSD' (subset_abs2 HL')))
      end
    end
  | trm_let t1 t2 => fun eq =>
    let v := proj1_sig (var_fresh L) in
    match @typinf K E t1 (typ_fvar v) (L \u {{v}}) S (dom_inv_let1 h eq)
      HS HK D (subset_let1 HL) with
    | Some (exist (K0,S',L') (conj (conj HK0 (conj HS' D')) HL')) =>
      let K' := Env.map (kind_subst S') K0 in
      let E' := Env.map (sch_subst S') E in
      let T1 := typ_subst S' (typ_fvar v) in
      let KAM := typinf_generalize K' E' (vars_subst S' (kdom K)) T1 in
      let x := proj1_sig (var_fresh (dom E \u trm_fv t1 \u trm_fv t2)) in
      match ok_generalize T (vars_subst S' (kdom K)) x HK0 D' HL HL' with
        (conj HKA (conj DKA HL'')) =>
        match @typinf (fst KAM) (E & x ~ snd KAM) (t2 ^ x) T L' S'
          (dom_inv_let2 x h eq) HS' HKA DKA HL'' with
        | None => None
        | Some (exist (K',S',L') (conj HKSD' HL'')) =>
          Some (exist _ (K',S',L') (conj HKSD' (subset_let2 HL' HL'')))
        end
      end
    | None => None
    end
  | trm_app t1 t2 => fun eq =>
    let v := proj1_sig (var_fresh L) in
    match @typinf K E t1 (typ_arrow (typ_fvar v) T) (L \u {{v}}) S
      (dom_inv_app1 h eq) HS HK D (subset_app1 HL) with
    | Some (exist (K',S',L') (conj (conj HK' (conj HS' D')) HL')) =>
      match @typinf K' E t2 (typ_fvar v) L' S' (dom_inv_app2 h eq) HS' HK' D'
        (subset_app2 HL') with
      | None => None
      | Some (exist (K',S',L') (conj HKSD' HL'')) =>
        Some (exist _ (K',S',L') (conj HKSD' (subset_app3 HL' HL'')))
      end
    | None => None
    end
  | trm_cst c => fun eq =>
    let M := Delta.type c in
    let (Vs, Fr) := var_freshes L (sch_arity M) in
    match unify_dep (M ^ Vs) T HS
      (ok_kinds_open_vars _ _ HK (fresh_sub _ _ Fr (dom_K_L _ HL)))
      (disjoint_fvar _ _ _ D HL Fr) with
    | inleft (exist (K',S') (conj _ (conj HKSD' HL'))) =>
      Some (exist _ (K',S',L \u mkset Vs)
        (conj HKSD' (subset_cst _ _ _ Fr HL (HL' E))))
    | inright _ => None
    end
  end (refl_equal t).

Definition typinf0 K E t T L S := @typinf K E t T L S (lt_wf _).

Lemma normalize_typinf : forall K E t T L S h,
  @typinf K E t T L S h = @typinf0 K E t T L S.
Proof.
  intros.
  unfold typinf0; apply f_equal. apply ProofIrrelevance.proof_irrelevance.
Qed.

Lemma subset_typinf' : forall E v,
  fvs id empty E \u typ_fv (typ_fvar v) << env_fv E \u {{v}}.
Proof.
  unfold fvs; simpl.
  intros. auto.
Qed.

Definition typinf' E t :=
  let v  :=  Variables.var_default in
  let min_vars := env_fv E \u {{v}} in
  let V := typ_fvar v in
  match
    @typinf empty E t V min_vars id (lt_wf _) is_subst_id (ok_empty _)
      (@disjoint_empty _) (@subset_typinf' E v)
  with None => None
  | Some (exist (k, s, L) _) =>
    Some (map (kind_subst s) k, typ_subst s V)
  end.

Lemma env_prop_type_compose : forall S1 S2,
  env_prop type S1 -> env_prop type S2 -> env_prop type (compose S1 S2).
Proof.
  unfold compose.
  intros.
  intro; intros.
  destruct* (in_app_or _ _ _ H1).
  destruct (in_map_inv _ _ _ _ H2) as [T [Eq B']].
  subst*.
Qed.

Hint Resolve env_prop_type_compose.

Lemma unify_rel_all_kind_types :
  forall (P:typ->Prop) k k0 kc (v1:Cstr.valid kc),
  All_kind_types P (Some k) -> All_kind_types P (Some k0) ->
  let krs := kind_rel k ++ kind_rel k0 in
  All_kind_types P (Some (Kind v1 (unify_coherent krs))) /\
  (forall T1 T2,
   In (T1, T2) (snd (unify_kind_rel krs nil (Cstr.unique kc) nil)) ->
   P T1 /\ P T2).
Proof.
  unfold All_kind_types; intros.
  simpl in *.
  puts (list_forall_app H H0).
  clear H H0.
  unfold list_snd in H1; rewrite <- map_app in H1.
  set (kr':=@nil (Cstr.attr*typ)).
  set (pairs':=@nil (typ*typ)).
  assert (list_forall P (List.map (@snd _ _) kr')) by simpl*.
  assert (forall T1 T2, In (T1, T2) pairs' -> P T1 /\ P T2) by simpl*.
  gen kr' pairs'.
  induction (kind_rel k ++ kind_rel k0); simpl; intros. auto.
  destruct a.
  inversion_clear H1.
  case_eq (Cstr.unique kc a); introv R.
    case_eq (assoc Cstr.eq_dec a kr'); intros.
      apply* IHl.
      simpl; intros.
      destruct* H4.
      inversions H4.
      split*.
      clear -H H1.
      apply* (list_forall_out H).
      puts (assoc_sound _ _ _ H1).
      apply (in_map (@snd _ _) _ _ H0).
    apply* IHl.
    simpl*.
  apply* IHl.
  simpl*.
Qed.

Lemma unify_kinds_all_kind_types : forall P k1 k2 k l,
  unify_kinds k1 k2 = Some (k, l) ->
  All_kind_types P k1 ->
  All_kind_types P k2 ->
  All_kind_types P k /\
  forall T1 T2, In (T1,T2) l -> P T1 /\ P T2.
Proof.
  intros.
  destruct k1 as [[kc1 kv1 kr1 kh1]|]; destruct k2 as [[kc2 kv2 kr2 kh2]|];
    simpl in *; try solve [inversions H; split*; intros; elim H2].
  destruct (Cstr.valid_dec (Cstr.lub kc1 kc2)); try discriminate.
  inversions H; clear H; simpl.
  apply (unify_rel_all_kind_types v H0 H1).
Qed.  

Lemma incl_remove_env : forall (A:Set) v (K:env A),
  incl (remove_env K v) K.
Proof.
  induction K; simpl; intro; intros. auto.
  destruct a.
  destruct* (v == v0).
Qed.

Lemma kenv_ok_remove_env : forall K v,
  kenv_ok K -> kenv_ok (remove_env K v).
Proof.
  intros; kenv_ok_solve; auto.
  intro; intros.
  apply (H0 x).
  apply* (incl_remove_env v K).
Qed.

Hint Resolve kenv_ok_remove_env.

Lemma unify_type : forall K' S' pairs K S,
  unify_spec pairs K S (Some (K', S')) ->
  env_prop type S ->
  kenv_ok K ->
  (forall T1 T2, In (T1, T2) pairs -> type T1 /\ type T2) ->
  kenv_ok K' /\ env_prop type S' /\ is_subst S'.
Proof.
  intros until S.
  apply (unify_ind (fun K S pairs =>
    env_prop type S -> kenv_ok K ->
    (forall T1 T2, In (T1, T2) pairs -> type T1 /\ type T2) ->
    kenv_ok K' /\ env_prop type S' /\ is_subst S')); clear; auto; intros.
        subst S1 K1.
        apply* H4; clear H4.
        apply* env_prop_type_compose.
        destruct* (H7 t t0).
        puts (typ_subst_type H5 H8). rewrite H1 in H9.
        intro; intros.
        destruct* H10. inversion H10. subst a. auto.
      subst S1 K1.
      destruct* (unify_kinds_all_kind_types (P:=type) H).
          unfold get_kind. case_eq (get v K); introv Bv; auto.
          apply* (proj2 H6 v).
        unfold get_kind. case_eq (get v0 K); introv Bv0; auto.
        apply* (proj2 H6 v0).
      apply~ H4; clear H4.
        apply* kenv_ok_concat.
      intros. destruct* (in_app_or _ _ _ H4).
    apply~ H2; clear H2.
    destruct* (H5 t t0).
    puts (typ_subst_type H3 H2).
    puts (typ_subst_type H3 H6).
    rewrite H0 in H7; rewrite H1 in H8.
    inversions H7; inversions H8.
    simpl. intros.
    destruct H9. inversions* H9.
    destruct H9. inversions* H9.
    apply* H5.
  apply~ H; clear H.
  simpl; intros.
  destruct H. inversions H. destruct* (H2 T2 T1).
  apply* H2.
Qed.

Lemma proper_instance_well_subst : forall S K K' Ks Us,
  env_prop type S ->
  well_subst K K' S ->
  kenv_ok K' ->
  proper_instance K Ks Us ->
  proper_instance K' (List.map (kind_subst S) Ks) (List.map (typ_subst S) Us).
Proof.
  intros.
  destruct H2 as [HUs HW].
  split.
    destruct HUs.
    split*. clear -H H3. induction H3; simpl*.
  remember Us as Ts.
  pattern Ts at 2.
  pattern Ts at 2 in HW.
  rewrite HeqTs in *.
  clear HeqTs.
  destruct HUs.
  gen Ks; induction H3; destruct Ks; simpl; intros; try discriminate. auto.
  inversions HW; clear HW.
  constructor; auto.
  rewrite* <- kind_subst_open.
Qed.

Lemma kenv_ok_map : forall K S,
  kenv_ok K -> env_prop type S -> kenv_ok (map (kind_subst S) K).
Proof.
  intros.
  split*.
  destruct H.
  intro; intros.
  destruct (in_map_inv _ _ _ _ H2) as [b [Hb B]].
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
  apply* kenv_ok_map.
Qed.

Lemma env_ok_map : forall E S,
  env_ok E -> env_prop type S -> env_ok (map (sch_subst S) E).
Proof.
  intros; split*.
  intro; intros.
  destruct (in_map_inv _ _ _ _ H1) as [b [Hb B]].
  subst.
  apply* sch_subst_type.
  apply* (proj2 H x).
Qed.

Hint Resolve kenv_ok_subst env_ok_map.

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
    puts (WS _ _ B).
    inversions H. auto.
    simpl. rewrite <- H1.
    apply* wk_kind.
  rewrite typ_subst_fresh by simpl*.
  destruct* k as [[kc kv kr kh]|].
  simpl.
  apply~ wk_kind.
  use (binds_map (kind_subst S) B0).
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
  destruct M as [T Ks]; simpl in *.
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
    destruct M as [T Ks]; simpl in *.
    rewrite map_length in Fr.
    assert (HK: kenv_ok (K & kinds_open_vars Ks Ys)).
      assert (fresh L1 (length Ks) Ys) by auto*.
      use (H _ H1).
    rewrite* <- sch_subst_open_vars.
    rewrite* <- kinds_subst_open_vars.
    apply* H0; clear H H0.
    apply* well_subst_extend.
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
  destruct (Delta.type c) as [T Ks]; simpl in *.
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
    apply* ok_combine_fresh.
  apply env_prop_concat. apply (proj2 H).
  apply list_forall_env_prop.
  destruct* (H0 Xs).
  clear -H3; induction H3. simpl*.
  simpl; constructor; auto.
  unfold kind_open. unfold typ_open_vars in H3.
  apply* All_kind_types_map.
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
  puts (H0 _ _ H2).
  inversions H3; clear H3.
    destruct~ k; discriminate.
  puts (H1 _ _ H7).
  inversions* H3.
  destruct k0; try discriminate.
  fold (typ_subst S' (typ_fvar x)) in H9.
  fold (typ_subst S (typ_fvar Z)) in H5.
  rewrite H5 in H9.
  rewrite H in H9.
  rewrite <- H9.
  rewrite* <- (@kind_subst_extend S' S).
  rewrite <- H4.
  simpl. apply* wk_kind.
  refine (entails_trans H12 _).
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

Lemma kind_entails_fv : forall k1 k2,
  kind_entails k1 k2 -> kind_fv k2 << kind_fv k1.
Proof.
  unfold kind_entails; intros.
  destruct k2.
    destruct* k1.
    unfold kind_fv; simpl.
    destruct H.
    clear H; induction (kind_rel c); simpl; intros y Hy. auto.
    destruct (S.union_1 Hy).
      apply* (in_typ_fv (snd a)).
      apply* in_map.
    apply* IHl.
  intros y Hy. elim (in_empty Hy).
Qed.

Definition Gc := (false, GcLet).

Definition soundness_spec h t K0 E T L0 S0 HS0 (HK0:kenv_ok K0) D0 HL0 K S L H'
  :=
  trm_depth t < h ->
  @typinf K0 E t T L0 S0 (lt_wf _) HS0 (proj1 HK0) D0 HL0
  = Some (exist _ (K,S,L) H') ->
  env_prop type S0 ->
  env_ok E -> type T ->
  extends S S0 /\ env_prop type S /\ kenv_ok K /\
  well_subst K0 (map (kind_subst S) K) S /\
  (fvs S K E \u L0 << L /\
  map (kind_subst S) K; map (sch_subst S) E |Gc|= t ~: typ_subst S T).

Lemma map_map_env : forall (A:Set) f f1 f2 (E:Env.env A),
  (forall x, f x = f1 (f2 x)) -> map f E = map f1 (map f2 E).
Proof.
  intros; induction E; simpl. auto.
  destruct a; simpl.
  rewrite H.
  rewrite* IHE.
Qed.

Lemma soundness_ind : forall h t K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H' M x,
  scheme M ->
  fresh L0 (sch_arity M) x ->
  unify_spec ((sch_open_vars M x,T)::nil)
    (K0 & kinds_open_vars (sch_kinds M) x) S0 (Some (K, S)) ->
  (kenv_ok (K0 & kinds_open_vars (sch_kinds M) x) ->
   extends S S0 -> kenv_ok K ->
   unifies S ((sch_open_vars M x, T) :: nil) ->
   (fvs S K E \u L0 << L /\
   map (kind_subst S0) (K0 & kinds_open_vars (sch_kinds M) x);
   map (sch_subst S0) E |Gc|= t ~: sch_subst S0 M ^^ typ_fvars x)) ->
  @soundness_spec h t K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H'.
Proof.
  intros until x; intros HM f HI Typ Ht _ HTS0 HE HT.
  poses Fr (fresh_sub _ _ f HL0).
  assert (kenv_ok (K0 & kinds_open_vars (sch_kinds M) x)).
    apply* kenv_ok_sch_kinds.
    unfold fvs in Fr; auto.
  destruct* (unify_kinds_ok HI).
    unfold fvs in Fr. rewrite dom_concat. rewrite* dom_kinds_open_vars.
  poses Hext (typ_subst_extend HI).
  destruct* (unify_type HI).
    simpl; intros.
    destruct* H2.
    inversions H2; clear H2.
    split*.
    unfold sch_open_vars.
    destruct* (HM x).
  poses HU (unify_types HI).
  destruct* Typ.
  intuition.
    intro; intros.
    apply H7.
    apply* binds_concat_ok.
  rewrite <- (map_sch_subst_extend E Hext).
  rewrite* <- (HU (sch_open_vars M x) T).
  rewrite* <- Hext.
  unfold fvs in Fr.
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
  list_forall2
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

Lemma soundness_var : forall h L0 v K0 E T S0 HS0 HK0 D0 HL0 K S L H',
  @soundness_spec h (trm_fvar v) K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H'.
Proof.
  intros; intros Ht HI HTS0 HE HT.
  poses HI' HI; simpl lt_wf in HI.
  lazy [typinf] in HI.
  destruct (get_dep v E) as [[M R1]|]; try discriminate.
  destruct (var_freshes L0 (sch_arity M));
    simpl proj1_sig in HI.
  destruct (unify_dep (sch_open_vars M x) T HS0
           (ok_kinds_open_vars (sch_kinds M) x (proj41 HK0)
              (fresh_sub (sch_arity M) x f (dom_K_L T HL0)))
           (disjoint_fvar T M x D0 HL0 f))
    as [[[K' S'] [HIres [[HK' [HS' D']] SS']]]|]; try discriminate.
  inversions HI; clear HI; rename HIres into HI.
  refine (soundness_ind _ _ _ _ _ _ _ HI _ _ HI' _ _ _); auto.
    apply* (proj2 HE v).
  split.
    sets_solve.
    poses G (SS' _ _ H3); clear H3 SS'.
    unfold fvs in *.
    rewrite dom_concat, fv_in_concat, dom_kinds_open_vars in G by auto.
    unfold sch_open_vars, typ_open_vars in G; simpl in G.
    puts (fv_in_kinds_open_vars (sch_kinds M) x).
    puts (fv_in_spec sch_fv _ _ _ (binds_in R1)).
    fold env_fv in H4.
    unfold sch_fv in H4; simpl in H4.
    puts (typ_fv_open (typ_fvars x) (sch_type M)).
    rewrite typ_fv_typ_fvars in H5.
    clear -HL0 G H3 H4 H5.
    auto.
  apply* typing_var.
    apply* kenv_ok_map.
  split.
    simpl; rewrite map_length.
    rewrite (fresh_length _ _ _ f). apply types_typ_fvars.
  destruct M as [Us Ks]; simpl.
  apply* well_kinded_open_vars.
  unfold fvs in HL0.
  use (fresh_sub _ _ f HL0).
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

Lemma soundness_cst : forall h L0 c K0 E T S0 HS0 HK0 D0 HL0 K S L H',
  @soundness_spec h (trm_cst c) K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H'.
Proof.
  intros; intros Ht HI HTS0 HE HT.
  poses HI' HI; simpl lt_wf in HI.
  lazy [typinf] in HI.
  set (M := Delta.type c) in *.
  destruct (var_freshes L0 (sch_arity M));
    simpl proj1_sig in HI.
  destruct (unify_dep (sch_open_vars M x) T HS0
           (ok_kinds_open_vars (sch_kinds M) x (proj41 HK0)
              (fresh_sub (sch_arity M) x f (dom_K_L T HL0)))
           (disjoint_fvar T M x D0 HL0 f))
    as [[[K' S'] [HIres [[HK' [HS' D']] SS']]]|]; try discriminate.
  inversions HI; clear HI; rename HIres into HI.
  refine (soundness_ind _ _ _ _ _ _ _ HI _ _ HI' _ _ _); auto.
    apply Delta.scheme.
  assert (sch_fv M << {}).
    puts (Delta.closed c). unfold M; rewrite* H.
  rewrite sch_subst_fresh by (unfold M; rewrite* Delta.closed).
  split.
    sets_solve.
    poses G (SS' _ _ H4); clear H4 SS'.
    unfold fvs in *.
    rewrite dom_concat, fv_in_concat, dom_kinds_open_vars in G by auto.
    unfold sch_open_vars, typ_open_vars in G; simpl in G.
    puts (fv_in_kinds_open_vars (sch_kinds M) x).
    unfold sch_fv in H; simpl in H.
    puts (typ_fv_open (typ_fvars x) (sch_type M)).
    rewrite typ_fv_typ_fvars in H5.
    clear -HL0 G H H4 H5.
    auto.
  apply* typing_cst.
    apply* kenv_ok_map.
  split.
    fold M.
    rewrite (fresh_length _ _ _ f). apply types_typ_fvars.
  rewrite <- (kinds_subst_cst S0 c).
  unfold fvs in HL0.
  apply* well_kinded_open_vars.
  clear -f HL0.
  apply* fresh_sub.
Qed.

Lemma soundness_abs : forall h L0 t K0 E T S0 HS0 HK0 D0 HL0 K S L H',
  (forall t K0 E T L0 S0 HS0 HK0 D0 HL0 H',
    @soundness_spec h t K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H') ->
  @soundness_spec (Datatypes.S h) (trm_abs t) K0 E T L0 S0 HS0 HK0 D0
    HL0 K S L H'.
Proof.
  introv IH; intros Ht HI HTS0 HE HT.
  simpl lt_wf in HI; lazy [typinf] in HI; fold typinf in HI.
  destruct (unify_dep
           (typ_arrow (typ_fvar (proj1_sig (var_fresh L0)))
              (typ_fvar
                 (proj1_sig (var_fresh (L0 \u {{proj1_sig (var_fresh L0)}})))))
           T HS0 (proj41 HK0) D0)
    as [[[K' S'] [R1 [[HK' [HS' D']] SS']]]|]; try discriminate.
  rewrite normalize_typinf in HI.
  simpl proj1_sig in *.
  destruct (var_fresh L0); simpl proj1_sig in *.
  destruct (var_fresh (L0 \u {{x}})); simpl proj1_sig in *.
  destruct (var_fresh (dom E \u trm_fv t)); simpl proj1_sig in *.
  destruct (unify_type R1) as [HKK' HTS']; auto.
    simpl; intros. destruct* H.
    inversions* H.
  case_rewrite R2 (typinf0 (t ^ x1) (typ_fvar x0) HS' HK' D'
               (subset_abs (x:=x1) T HL0 (SS' E))).
  destruct s as [[[K'' S''] L''] [[HK'' [HS'' D'']] HL'']].
  inversions HI; clear HI.
  destruct* (unify_kinds_ok R1) as [_ [_ WS']].
  simpl in Ht. rewrite <- (trm_depth_open x1) in Ht.
  poses Ht' (lt_S_n _ _ Ht).
  rewrite (ProofIrrelevance.proof_irrelevance _ HK' (proj1 HKK')) in  R2.
  destruct* (IH _ _ _ _ _ _ _ _ _ _ _ Ht' R2); clear IH R2.
    env_ok_solve.
    intro; intros. unfold typ_open_vars. simpl*.
  intuition.
        apply* extends_trans.
        apply* typ_subst_extend.
      apply* well_subst_compose.
    clear -H5; unfold fvs in *.
    unfold env_fv in H5; simpl in H5; fold env_fv in H5.
    auto.
  puts (unify_types R1).
  rewrite <- (H T).
  rewrite* <- (H6 (typ_arrow (typ_fvar x) (typ_fvar x0)) T).
  rewrite H.
  simpl.
  simpl map in H7.
  fold (typ_subst S (typ_fvar x0)).
  fold (typ_subst S (typ_fvar x)).
  set (E' := map (sch_subst S) E) in *.
  apply* (@typing_abs Gc (dom E' \u {{x1}} \u trm_fv t)).
  intros.
  apply typing_gc_raise.
  apply* (@typing_abs_rename x1).
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

Lemma cardinal_env : forall (A:Set) (K:env A),
  ok K -> S.cardinal (dom K) = length K.
Proof.
  induction 1; simpl. apply cardinal_empty.
  rewrite <- (@cardinal_remove x).
    rewrite remove_union.
    assert (S.remove x {{x}} = {}).
      apply eq_ext; intros; split; intro; sets_solve.
    rewrite H1. rewrite* remove_notin.
    rewrite* union_empty_l.
  sets_solve.
Qed.

Lemma close_fvk_ok : forall K L x k,
  ok K -> x \in close_fvk K L -> binds x k K -> kind_fv k << close_fvk K L.
Proof.
  intros.
  unfold close_fvk in *.
  puts (cardinal_env H).
  puts (binds_dom H1).
  revert L H0 H2 H3; generalize (dom K).
  induction (length K); simpl; intros.
    rewrite (cardinal_0 H2) in *. elim (in_empty H3).
  case_rewrite R1 (S.choose (S.inter v L)).
    puts (S.choose_1 R1).
    destruct (x == e).
      subst.
      rewrite H1 in *.
      intros x Hx.
      apply* close_fvars_subset.
    assert (forall L', x \in close_fvars n K (S.remove e v) L' ->
               kind_fv k << close_fvars n K (S.remove e v) L').
      intros; apply* IHn.
      rewrite <- (@cardinal_remove e) in H2; auto.
    case_rewrite R2 (get e K); intros; auto.
  puts (S.choose_2 R1).
  elim (H4 x).
  auto with sets.
Qed.

Lemma vars_subst_in : forall v L S,
  v \in L -> typ_fv (typ_subst S (typ_fvar v)) << vars_subst S L.
Proof.
  intros.
  unfold vars_subst.
  puts (S.elements_1 H).
  induction H0; intros x Hx.
    simpl. rewrite <- H0. auto with sets.
  simpl.
  puts (IHInA _ Hx). auto with sets.
Qed.

Lemma sch_arity_subst : forall M S,
  sch_arity (sch_subst S M) = sch_arity M.
Proof.
  destruct M as [T Ks]; simpl*.
Qed.

Hint Resolve kind_subst_idem.

Lemma disjoint_subset : forall L1 L2 L3,
  L1 << L2 -> disjoint L2 L3 -> disjoint L1 L3.
Proof.
  intros. disjoint_solve.
Qed.

Lemma close_fvk_incl : forall EK0 e0 K',
  ok K' -> dom e0 << close_fvk K' EK0 -> incl e0 K' ->
  EK0 \u dom e0 \u fv_in kind_fv e0 << close_fvk K' EK0.
Proof.
  introv HK' Se0 Inc2.
  puts (incl_subset_dom Inc2).
  sets_solve.
    apply* close_fvk_subset.
  destruct (fv_in_binds _ _ H0) as [x [a [B B']]].
  puts (Inc2 _ B').
  puts (in_dom _ _ _ B').
  apply* close_fvk_ok.
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
  puts (S.elements_1 H).
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
  simpl in *. split*.
  apply IHsort.
  disjoint_solve.
  elim (sort_lt_notin H0 H).
  puts (mkset_in _ Hy').
  clear -H1.
  induction l; auto.
Qed.

Lemma typing_let_fresh : forall T1 l l0 K' e e0 e1 e2 fvT1 fvE,
  let ftve := close_fvk K' fvE in
  let Bs := S.elements (S.diff fvT1 (ftve \u dom e2)) in
  let l0' := List.map (fun _:var => @None ckind) Bs in
  let M := sch_generalize (@app var l Bs) T1 (@app kind l0 l0') in
  split e2 = (l, l0) ->
  ok (e0 & e) -> ok (e2 & e1) ->
  ok K' -> incl (e0 & e) K' -> incl (e2 & e1) e ->
  disjoint ftve (dom e) ->
  dom e0 << ftve ->
  fresh (fvE \u sch_fv M \u dom e0 \u fv_in kind_fv e0) (sch_arity M) (l++Bs).
Proof.
  intros until M. intros R4 Ok Ok' HK' Inc2 Inc4 Dise Se0.
  poses DM (@sch_generalize_disjoint (l++Bs) T1 (l0 ++ l0')).
  fold M in DM; rewrite mkset_app in DM.
  simpl length. rewrite map_length, app_length.
  rewrite <- (split_length _ R4).
  puts (split_combine _ R4).
  assert (incl e0 K') by (intro; auto*).
  poses SKA (close_fvk_incl HK' Se0 H0); clear H0.
  fold ftve in SKA.
  apply fresh_app.
    apply* (ok_fresh l l0).
      rewrite* H.
    rewrite <- (dom_combine l l0) in * by auto.
    rewrite H in *.
    use (incl_subset_dom Inc4).
  unfold l0'.
  rewrite map_length.
  unfold Bs.
  apply elements_fresh.
  rewrite <- H.
  rewrite* dom_combine.
  puts (@diff_disjoint fvT1 (ftve \u mkset l)).
  set (l' := S.diff fvT1 (ftve \u mkset l)) in *.
  rewrite <- (dom_combine l l0) in * by auto.
  rewrite H in *.
  subst Bs. rewrite mkset_elements in DM.
  puts (incl_subset_dom Inc4).
  subst l'.
  disjoint_solve.
Qed.

Lemma typing_let_fresh_2 : forall l1 l2 K' T fvE e e0 e1 e2,
  let Ks := List.map (kind_map (typ_generalize l1)) l2 in
  let M' := Sch T Ks in
  kenv_ok K' ->  ok (e0 & e) -> ok (e2 & e1) ->
  incl (e0 & e) K' -> incl (e2 & e1) e ->
  split e1 = (l1, l2) ->
  disjoint (close_fvk K' fvE) (dom e) ->
  dom e0 << close_fvk K' fvE ->
  disjoint (close_fvk K' (typ_fv T)) (dom e1) ->
  dom e2 << close_fvk K' (typ_fv T) ->
  fresh (fvE \u sch_fv M' \u dom (e0 & e2) \u fv_in kind_fv (e0 & e2))
    (sch_arity M') l1.
Proof.
  intros until M'.
  intros HK' Ok Ok' Inc2 Inc4 R5 Dise Se0 Dise1 Se2.
  rewrite dom_concat; rewrite fv_in_concat.
  simpl length.
  unfold Ks; rewrite map_length.
  rewrite <- (split_length _ R5).
  poses He1 (split_combine _ R5).
  apply* (ok_fresh l1 l2).
    rewrite* He1.
  rewrite* <- (dom_combine l1 l2).
  rewrite He1.
  puts (incl_subset_dom Inc4).
  rewrite dom_concat in H.
  assert (incl e0 K') by (intro; auto*).
  puts (close_fvk_incl (proj1 HK') Se0 H0).
  puts (@close_fvk_subset (typ_fv T) K').
  repeat apply disjoint_union; simpl; auto; apply disjoint_comm.
  (* Ks *)
  unfold Ks; simpl.
  rewrite <- He1. rewrite* dom_combine.
  apply kinds_generalize_disjoint.
  (* e2 *)
  refine (disjoint_subset _ Dise1).
  intro; intros.
  apply* close_fvk_incl.
  clear -Inc2 Inc4.
  intro; intros.
  apply Inc2.
  apply* in_or_app.
Qed.

Lemma sch_open_extra : forall Ks Xs T,
  type T -> sch_open_vars (Sch T Ks) Xs = T.
Proof.
  unfold sch_open_vars, typ_open_vars; simpl; intros.
  rewrite* <- typ_open_type.
Qed.

Lemma typing_let_incl : forall K' e e0 e1 e2 : kenv,
  ok (e0 & e) -> ok (e2 & e1) ->
  incl K' (e0 & e) ->
  incl (e0 & e) K' ->
  incl e (e2 & e1) ->
  incl (e2 & e1) e ->
  incl K' (e0 & e2 & e1) /\ incl (e0 & e2 & e1) K'.
Proof.
  intros until e2; intros Ok Ok' I1 I2 I3 I4.
  rewrite concat_assoc.
  set (e' := e2 & e1) in *.
  split; intro; intros.
    puts (I1 _ H).
    destruct* (in_app_or _ _ _ H0).
  destruct* (in_app_or _ _ _ H).
Qed.

Lemma typing_let_kenv_ok : forall K' T1 ftve e2 l l0 e0 e e1,
  let Bs := S.elements (S.diff (close_fvk K' (typ_fv T1)) (ftve \u dom e2)) in
  let l0' := List.map (fun _ : var => None) Bs in
  split e2 = (l, l0) ->
  kenv_ok K' -> ok (e0 & e) -> ok (e2 & e1) ->
  dom e0 << ftve -> incl (e0 & e) K' -> incl (e2 & e1) e ->
  combine l l0 = e2 ->
  kenv_ok (e0 & combine Bs l0' & combine l l0).
Proof.
  intros until l0'; intros R4 HK' Ok Ok' Se0 Inc2 Inc4 He2.
  rewrite concat_assoc.
  puts (@diff_disjoint (close_fvk K' (typ_fv T1)) (ftve \u dom e2)).
  puts (elements_fresh (disjoint_comm H)).
  apply kenv_ok_concat.
      split*. intro; intros. apply (proj2 HK' x). apply* Inc2.
    split.
      apply disjoint_ok.
          apply* ok_combine_fresh.
        rewrite* He2.
      rewrite dom_combine. rewrite* dom_combine.
        unfold Bs; rewrite mkset_elements.
        rewrite* <- (dom_combine l l0). rewrite* He2.
      unfold l0'; rewrite* map_length.
    apply env_prop_concat.
      apply list_forall_env_prop.
      unfold l0'; clear; induction Bs; simpl*.
    rewrite He2. intro; intros. apply (proj2 HK' x).
    apply Inc2. apply in_or_concat; left. apply* Inc4.
  rewrite dom_concat. rewrite He2.
  apply disjoint_union.
    fold Bs in H0.
    rewrite* dom_combine.
    unfold l0'; rewrite* map_length.
  use (incl_subset_dom Inc4).
Qed.

Lemma soundness_generalize : forall L K' E' t T1 KA M,
  K'; E' |Gc|= t ~: T1 ->
  typinf_generalize K' E' L T1 = (KA, M) ->
  kenv_ok KA /\ incl KA K' /\ S.inter (dom K') L << dom KA /\ scheme M /\
  sch_fv M << fv_in kind_fv K' \u typ_fv T1 /\
  exists L1, forall Xs,
    fresh L1 (sch_arity M) Xs ->
    KA & kinds_open_vars (sch_kinds M) Xs; E' |(true,GcLet)|= t ~: M ^ Xs.
Proof.
  unfold typinf_generalize.
  introv Typ HI.
  set (ftve := close_fvk K' (env_fv E')) in *.
  case_rewrite R2 (split_env ftve K').
  case_rewrite R3 (split_env (close_fvk K' (typ_fv T1)) e).
  case_rewrite R4 (split e2).
  set (Bs := S.elements (S.diff (close_fvk K' (typ_fv T1)) (ftve \u dom e2)))
    in *.
  set (l0' := List.map (fun _:var => @None ckind) Bs) in *.
  case_rewrite R5 (split_env L e).
  inversion HI; clear HI. subst KA.
  destruct* (split_env_ok _ R2) as [Ok [Dise [Se0 [Inc1 Inc2]]]].
  destruct* (split_env_ok _ R3) as [Ok' [Dise' [Se2 [Inc3 Inc4]]]].
  destruct* (split_env_ok _ R5) as [Ok'' [Dise3 [Se4 [Inc5 Inc6]]]].
  poses He2 (split_combine _ R4).
  assert (HK': kenv_ok K') by auto.
  assert (Hkt: list_forall (All_kind_types type) (l0 ++ l0')).
    apply list_forall_app.
      refine (env_prop_list_forall l _ _ _ _); auto*.
        rewrite He2. intro; intros. apply* (proj2 HK' x).
        apply Inc2. apply* in_or_concat.
      rewrite* He2.
    unfold l0'. clear; induction Bs; simpl*.
  assert (HM: scheme M).
    subst M; unfold l0'.
    apply* scheme_generalize.
  assert (IncKA: incl (e0 & e4) K').
    intros a Ha.
    destruct (in_app_or _ _ _ Ha).
      assert (In a e); auto.
    auto.
  assert (HKA: kenv_ok (e0 & e4)).
    split. apply* disjoint_ok. 
      use (incl_subset_dom Inc6).
    intro; intros.
    apply* (proj2 (proj1 (typing_regular Typ)) x).
  split*. split*.
  split.
    intro; intros.
    puts (incl_subset_dom Inc1).
    use (incl_subset_dom Inc5).
  split. rewrite* H1.
  split.
    intros y Hy. puts (sch_fv_generalize Hy).
    clear Hy; unfold sch_fv, l0' in H; simpl in H.
    rewrite kind_fv_list_app in H.
    clearbody Bs.
    clear -Inc2 Inc4 R4 H.
    rewrite <- (fv_in_kind_fv_list l l0 (split_length _ R4)) in H.
    rewrite (split_combine _ R4) in H.
    puts (incl_fv_in_subset kind_fv Inc2).
    puts (incl_fv_in_subset kind_fv Inc4).
    disjoint_solve.
    clear -H; induction Bs. elim (in_empty H).
    apply IHBs. simpl in H; sets_solve. elim (in_empty H0).
  intros.
  assert (AryM: sch_arity M = length (l ++ Bs)).
    rewrite <- H1.
    unfold l0'. simpl*.
  esplit; intros.
  apply typing_weaken_kinds.
  eapply typing_rename_typ.
      instantiate (1 := l ++ Bs).
      unfold l0', Bs, ftve; apply* typing_let_fresh.
    instantiate (1 := dom (e0 & e4) \u mkset (l++Bs)) in H.
    rewrite dom_concat in H.
    rewrite <- AryM; rewrite* <- H1.
  unfold sch_open_vars, typ_open_vars. simpl sch_type.
  rewrite* typ_generalize_reopen.
  unfold sch_generalize. simpl sch_kinds.
  rewrite* kinds_generalize_reopen.
  rewrite* combine_app.
  fold (@combine var kind Bs l0' & combine l l0).
  rewrite <- concat_assoc.
  puts (typing_let_kenv_ok T1 _ _ R4 HK' Ok Ok' Se0 Inc2 Inc4 He2).
  apply* typing_weaken_kinds; clear H0.
  rewrite He2.
  case_eq (split e1); introv R6.
  poses He1 (split_combine _ R6).
  pose (Ks := List.map (kind_map (typ_generalize l1)) l2).
  apply* (@typing_gc (true,GcLet) Ks). simpl*.
  poses Typ' (typing_gc_raise Typ). clear Typ. simpl in Typ'.
  intros.
  pose (M' := Sch T1 Ks).
  rewrite* <- (@sch_open_extra Ks Xs0). fold M'.
  replace Ks with (sch_kinds M') by simpl*.
  eapply typing_rename_typ.
      instantiate (1 := l1).
      unfold M', Ks.
      unfold ftve in *.
      apply* (@typing_let_fresh_2 l1 l2 K').
    unfold Ks in H0. rewrite map_length in H0.
    rewrite* (split_length _ R6).
  assert (list_forall (All_kind_types type) l2).
    refine (env_prop_list_forall l1 _ _ _ _); auto*.
      rewrite He1. intro; intros. apply (proj2 HK' x).
      apply Inc2. apply* in_or_concat.
    rewrite* He1.
  simpl sch_kinds.
  unfold Ks; rewrite* kinds_generalize_reopen. rewrite He1; clear H2.
  unfold sch_open_vars, typ_open_vars.
  simpl sch_type. rewrite* <- typ_open_type.
  destruct* (typing_let_incl _ _ _ Ok Ok' Inc1 Inc2 Inc3 Inc4).
  apply* typing_kenv_incl.
  split.
    rewrite concat_assoc.
    apply* disjoint_ok.
      use (incl_subset_dom Inc4).
    intro; intros. assert (kenv_ok K') by auto. apply* (proj2 H5).
  apply* kenv_ok_sch_kinds. rewrite* H1.
Qed.

Lemma binds_kdom : forall x k K,
  binds x (Some k) K -> x \in kdom K.
Proof.
  unfold binds; induction K; simpl; intros. discriminate.
  destruct a.
  destruct (x == v). inversions* H.
  puts (IHK H). destruct* o.
Qed.

Lemma well_subst_let_inf: forall K0 s k e S K,
  well_subst K0 (map (kind_subst s) k) s ->
  well_subst e (map (kind_subst S) K) S ->
  S.inter (dom (map (kind_subst s) k)) (vars_subst s (kdom K0)) << dom e ->
  incl e (map (kind_subst s) k) -> ok k ->
  extends S s ->
  well_subst K0 (map (kind_subst S) K) S.
Proof.
  intros until K; intros WS WS' Inc1 Inc2 Hk Hext Z; intros.
  puts (WS _ _ H).
  rewrite <- (kind_subst_extend k0 Hext).
  rewrite <- Hext.
  inversions* H0.
  fold (typ_subst s (typ_fvar Z)) in H2.
  rewrite <- H2.
  case_eq (get x e); intros.
    assert (Some k' = k2) by apply* binds_func.
    subst k2.
    puts (WS' _ _ H3).
    eapply kind_entails_well_kinded; try apply H6.
    simpl*.
  elim (get_none_notin _ H3).
  apply Inc1.
  destruct k0; try discriminate.
  puts (vars_subst_in s (binds_kdom H)).
  rewrite <- H2 in H6. simpl in H6.
  puts (binds_dom H4).
  puts (S.singleton_2 (refl_equal x)).
  auto with sets.
Qed.

Lemma soundness_let : forall h L0 t1 t2 K0 E T S0 HS0 HK0 D0 HL0 K S L H',
  (forall t K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H',
    @soundness_spec h t K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H') ->
  @soundness_spec (Datatypes.S h) (trm_let t1 t2) K0 E T L0 S0 HS0 HK0 D0
    HL0 K S L H'.
Proof.
  introv IH; intros Ht HI HTS0 HE HT.
  simpl lt_wf in HI; lazy [typinf] in HI; fold typinf in HI.
  rewrite normalize_typinf in HI.
  destruct (var_fresh L0); simpl proj1_sig in HI.
  set (TI:=typinf0 t1 (typ_fvar x) HS0 (proj1 HK0) D0 (subset_let1 HL0)).
  simpl typ_fv in *.
  fold TI in HI.
  case_rewrite R1 TI; unfold TI in *; clear TI.
  destruct s as [[[k' S'] L'] [[HK' [HS' D']] HL']].
  revert HI.
  case (ok_generalize T (vars_subst S' (kdom K0))
    (proj1_sig (var_fresh (dom E \u trm_fv t1 \u trm_fv t2))) HK' D'
    HL0 HL').
  intros HKA [DKA HLA] HI.
  rewrite normalize_typinf in HI.
  set (K' := map (kind_subst S') k') in *.
  set (E' := map (sch_subst S') E) in *.
  set (T1 := typ_subst S' (typ_fvar x)) in *.
  destruct (var_fresh (dom E \u trm_fv t1 \u trm_fv t2)); simpl proj1_sig in HI.
  remember (typinf_generalize K' E' (vars_subst S' (kdom K0)) T1) as TG.
  destruct TG as [KA M]. simpl snd in *. simpl fst in *.
  simpl in Ht.
  assert (Ht': trm_depth t1 < h).
    puts (Max.le_max_l (trm_depth t1) (trm_depth t2)). omega.
  unfold typinf0 in R1.
  destruct* (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ht' R1); clear R1.
  destruct H0 as [HTs [Hk' [WS' [HL0' Typ']]]].
  destruct (soundness_generalize _ Typ' (sym_equal HeqTG))
    as [HKA' [Inc2 [Inc1 [HM [Hfv [L2 Typ2]]]]]].
  clear Ht'; assert (Ht': trm_depth t2 < h).
    puts (Max.le_max_r (trm_depth t1) (trm_depth t2)). omega.
  rewrite <- (trm_depth_open x0) in Ht'.
  set (TI:=typinf0 (t2 ^ x0) T HS' HKA DKA HLA).
  simpl proj1_sig in TI. fold TI in HI.
  case_rewrite R2 TI.
  destruct s as [[[K'' S''] L''] [[HK'' [HS'' D'']] HL'']].
  subst TI.
  inversions HI; clear HI.
  rewrite (ProofIrrelevance.proof_irrelevance _ HKA (proj1 HKA')) in R2.
  destruct* (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ht' R2); clear IH R2.
    split*. apply* extends_trans.
  intuition.
      apply* well_subst_let_inf.
    clear -HL'' HL0'.
    unfold fvs in *; simpl in HL''. auto.
  apply* (@typing_let Gc (sch_subst S M) (dom S \u dom K \u L2)).
    intros.
    simpl.
    rewrite* <- kinds_subst_open_vars.
    rewrite* <- sch_subst_open_vars.
    rewrite sch_arity_subst in H5.
    rewrite <- (map_sch_subst_extend E H0).
    apply* typing_typ_well_subst.
      apply (well_subst_extend (sch_kinds M) Xs H2 H3).
      rewrite* dom_map.
    rewrite <- map_concat.
    apply* kenv_ok_map.
    apply* kenv_ok_sch_kinds.
  instantiate (1 := dom E \u trm_fv t2 \u {{x0}}).
  intros.
  apply typing_gc_raise.
  apply* (@typing_abs_rename x0).
Qed.

Lemma soundness_app : forall h L0 t1 t2 K0 E T S0 HS0 HK0 D0 HL0 K S L H',
  (forall t K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H',
    @soundness_spec h t K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H') ->
  @soundness_spec (Datatypes.S h) (trm_app t1 t2) K0 E T L0 S0 HS0 HK0 D0
    HL0 K S L H'.
Proof.
  introv IH; intros Ht HI HTS0 HE HT.
  simpl lt_wf in HI; lazy [typinf] in HI; fold typinf in HI.
  rewrite normalize_typinf in HI.
  destruct (var_fresh L0); simpl proj1_sig in HI.
  case_rewrite R1
   (typinf0 t1 (typ_arrow (typ_fvar x) T) HS0 (proj1 HK0) D0 (subset_app1 HL0)).
  destruct s as [[[K' S'] L'] [[HK' [HS' D']] HL']].
  rewrite normalize_typinf in HI.
  simpl in Ht.
  assert (Ht': trm_depth t1 < h).
    puts (Max.le_max_l (trm_depth t1) (trm_depth t2)). omega.
  destruct* (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ht' R1); clear R1.
  clear Ht'; assert (Ht': trm_depth t2 < h).
    puts (Max.le_max_r (trm_depth t1) (trm_depth t2)). omega.
  case_rewrite R2 (typinf0 t2 (typ_fvar x) HS' HK' D' (subset_app2 HL')).
  destruct s as [[[K'' S''] L''] [[HK'' [HS'' D'']] HL'']].
  inversions HI; clear HI.
  destruct H0 as [HTS' [HKK' [WS' [_ Typ']]]].
  rewrite (ProofIrrelevance.proof_irrelevance _ HK' (proj1 HKK')) in *.
  destruct* (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ht' R2); clear IH R2.
  intuition.
      apply* extends_trans.
    apply* well_subst_compose.
  remember (typ_fvar x) as T1.
  apply* typing_app.
  poses WS (well_subst_extends H0 H3).
  poses Typ (typing_typ_well_subst H2 WS (kenv_ok_map H1 H2) Typ').
  rewrite (map_sch_subst_extend E H0) in Typ.
  rewrite H0 in Typ.
  apply Typ.
Qed.

Lemma typinf_sound : forall h t L0 K0 E T S0 HS0 HK0 D0 HL0 K S L H',
  @soundness_spec h t K0 E T L0 S0 HS0 HK0 D0 HL0 K S L H'.
Proof.
 induction h; intro t; destruct t; intros; intros Ht HI HTS0 HE HT;
      try elim (lt_n_O _ Ht); try discriminate.
  apply* soundness_var.
  apply* soundness_abs.
  apply* soundness_let. 
  apply* soundness_app.
  apply* soundness_cst.
Qed.

Lemma map_sch_subst_fresh : forall S E,
  disjoint (dom S) (env_fv E) -> map (sch_subst S) E = E.
Proof.
  unfold env_fv; induction E; simpl; intros. auto.
  destruct a. 
  rewrite* sch_subst_fresh.
  rewrite* IHE.
Qed.

Corollary typinf_sound' : forall t K E T,
  env_ok E -> env_fv E = {} ->
  typinf' E t = Some (K, T) -> K; E |Gc|= t ~: T.
Proof.
  unfold typinf'.
  introv HE HC HI.
  rewrite normalize_typinf in HI.
  case_rewrite R1 (typinf0 t (typ_fvar var_default) is_subst_id 
           (ok_empty kind) (@disjoint_empty _)
           (@subset_typinf' E var_default)).
  destruct s as [[[K' S'] L'] [[HK' [HS' D']] HL']].
  inversions HI; clear HI.
  assert (kenv_ok empty). split*. intro; intros. elim H.
  rewrite (ProofIrrelevance.proof_irrelevance _ (ok_empty kind) (proj1 H))
    in R1.
  destruct* (typinf_sound _ _ _ _ _ (lt_n_Sn _) R1).
      intro; intros. elim H0.
  rewrite* <- (map_sch_subst_fresh S' E).
  rewrite HC. intro. auto.
Qed.


(** Principality *)

Lemma typ_subst_concat_fresh : forall S1 S2 T,
  disjoint (dom S2) (typ_fv T) ->
  typ_subst (S1 & S2) T = typ_subst S1 T.
Proof.
  induction T; simpl; intros. auto.
    case_eq (get v S1); intros.
      rewrite* (binds_concat_fresh S2 H0).
    rewrite* get_notin_dom.
  rewrite* IHT1; rewrite* IHT2.
Qed.

Lemma typ_subst_combine_fresh : forall S T Xs Us,
  fresh (typ_fv T) (length Us) Xs ->
  typ_subst (S & combine Xs Us) T = typ_subst S T.
Proof.
  intros.
  rewrite* typ_subst_concat_fresh.
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
    rewrite IHkr; try rewrite* H; intros x Hx; apply* H0.
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
        simpl; use (binds_dom H).
      simpl. rewrite H.
      use (fv_in_spec typ_fv _ _ _ (binds_in H)).
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
  rewrite* (Hsub T).
  rewrite <- HU.
  unfold sch_open_vars, sch_open.
  rewrite* <- typ_subst_intro0.
    unfold sch_fv in HM0.
    rewrite <- (fresh_length _ _ _ Fr).
    apply* disjoint_fresh.
  rewrite* <- (fresh_length _ _ _ Fr).
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
  gen Ks; induction Xs; simpl; intros. auto.
  destruct Ks; simpl in *; auto.
  use (IHXs Ks).
Qed.

Lemma well_subst_concat : forall E S0 K0 K S L Xs Us,
  well_subst (map (kind_subst S0) K0) K S ->
  (forall t, typ_fv t << L ->
    typ_subst (S & combine Xs Us) t = typ_subst S t) ->
  extends (S & combine Xs Us) S0 ->
  fvs S0 K0 E << L ->
  well_subst K0 K (S & combine Xs Us).
Proof.
  introv WS Hsub Hext' HL.
  intro; intros.
  rewrite <- (kind_subst_combine _ _ _ k Hext').
  puts (WS _ _ (binds_map (kind_subst S0) H)).
  unfold fvs in HL.
  rewrite Hsub.
    rewrite* (@kind_subst_ext_fv S L).
    intros y Hy.
    puts (kind_fv_subst _ _ Hy).
    use (fv_in_spec kind_fv _ _ _ (binds_in H)).
  simpl.
  use (binds_dom H).
Qed.

Lemma well_subst_concat_abs : forall K M0 Us S S0 K0 E L Xs x,
  env_prop type S ->
  dom S \u fvs S0 K0 E << L ->
  proper_instance K (sch_kinds (sch_subst S M0)) Us ->
  well_subst (map (kind_subst S0) K0) K S ->
  binds x M0 E ->
  fresh L (sch_arity M0) Xs ->
  sch_arity M0 = length Us ->
  (forall t, typ_fv t << L ->
    typ_subst (S & combine Xs Us) t = typ_subst S t) ->
  extends (S & combine Xs Us) S0 ->
  well_subst (K0 & kinds_open_vars (sch_kinds M0) Xs) K (S & combine Xs Us).
Proof.
  intros until x; intros HTS HL [HUs HWk] WS B Fr AryM Hsub Hext'.
  intro; intros.
  binds_cases H.
    refine (well_subst_concat (E:=E) _ _ WS Hsub Hext' _ _); auto.
  simpl.
  case_eq (get Z (combine Xs Us)); intros.
    rewrite (binds_prepend S H).
    unfold kinds_open_vars, kinds_open in B1.
    rewrite <- map_combine in B1.
    destruct (binds_map_inv _ _ B1) as [k1 [Hk1 Bk]].
    subst k.
    rewrite <- kind_subst_intro0; trivial.
        destruct M0 as [T1 Ks]. simpl in *.
        unfold kinds_open in HWk. rewrite map_map in HWk.
        puts (binds_map (fun k => kind_open (kind_subst S k) Us) Bk).
        simpl in H0; rewrite map_combine in H0.
        use (list_forall2_get _ HWk H0 H).
      puts (fv_in_spec sch_fv _ _ _ (binds_in B)).
      puts (fv_in_spec kind_fv _ _ _ (binds_in Bk)).
      puts (fv_in_sch Xs M0).
      rewrite <- (fresh_length _ _ _ Fr).
      apply* fresh_sub.
      unfold fvs, env_fv in HL; intros y Hy; simpl in *; sets_solve.
    rewrite sch_arity_subst in HUs.
    rewrite* <- (fresh_length _ _ _ Fr).
  elim (get_none_notin _ H). auto.
Qed.

Definition moregen_scheme K M0 M :=
  forall Ys, fresh (dom K) (sch_arity M) Ys ->
    exists Ts,
      proper_instance (K & kinds_open_vars (sch_kinds M) Ys) (sch_kinds M0) Ts
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

Lemma sch_fv_subst : forall S M,
  sch_fv (sch_subst S M) << sch_fv M \u fv_in typ_fv S.
Proof.
  destruct M as [T Ks].
  unfold sch_fv, sch_subst; simpl.
  sets_solve.
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
  proper_instance K (sch_kinds M) Us ->
  proper_instance (K & kinds_open_vars (sch_kinds M) Ys) (sch_kinds M') Vs ->
  fresh (dom K \u fv_in kind_fv K \u sch_fv M \u sch_fv M0 \u fv_in typ_fv S)
    (sch_arity M) Ys ->
  sch_subst S M0 = M' ->
  proper_instance K (sch_kinds M') (List.map (typ_subst (combine Ys Us)) Vs).
Proof.
  intros until S; intros [HUs WUs] [HVs WVs] FrYs HM0.
  split.
    apply* typ_subst_type_list.
    apply list_forall_env_prop.
    apply (proj2 HUs).
  assert (HTUs: env_prop type (combine Ys Us)).
    apply list_forall_env_prop.
    apply (proj2 HUs).
  assert (LenYs: length Ys = length Us)
    by (rewrite <- (proj1 HUs); symmetry; auto).
  replace (sch_kinds M')
    with (List.map (kind_subst (combine Ys Us)) (sch_kinds M')).
    rewrite* <- kinds_subst_open.
    apply* list_forall2_map.
    intros.
    inversions H. simpl*.
    binds_cases H0.
      rewrite kind_subst_fresh.
        rewrite* typ_subst_fresh.
      assert (kind_entails (Some k') (Some k)) by simpl*.
      puts (kind_entails_fv _ _ H0).
      use (fv_in_spec kind_fv _ _ _ (binds_in B)).
    apply* well_kinded_subst.
    apply* well_subst_open_vars.
      unfold sch_fv in FrYs.
      apply* (fresh_resize (sch_arity M)).
    rewrite* <- (fresh_length _ _ _ FrYs).
  rewrite (list_map_ext (sch_kinds M') (kind_subst (combine Ys Us))
               (fun x:kind => x)).
    apply list_map_id.
  intros.
  apply kind_subst_fresh.
  rewrite <- HM0 in H.
  unfold sch_subst in H; simpl in H.
  destruct (proj1 (in_map_iff (kind_subst S) _ _) H) as [k1 [Hk1 Bk1]].
  subst x.
  puts (kind_fv_subst S k1).
  unfold sch_fv in FrYs; simpl in FrYs.
  use (in_kind_fv _ _ Bk1).
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
    unfold sch_fv in FrYs.
    rewrite* typ_subst_fresh.
  rewrite* sch_subst_fresh.
  use (@sch_fv_subst S M0).
Qed.

Definition principality S0 K0 E0 HS0 (HK0:kenv_ok K0) D0 S K E t T L HL h :=
  env_prop type S0 -> env_ok E0 ->
  moregen_env K (map (sch_subst S) E0) E ->
  env_prop type S -> dom S << L ->
  extends S S0 -> well_subst K0 K S ->
  K; E |(false,GcAny)|= t ~: typ_subst S T ->
  trm_depth t < h ->
  exists K', exists S', exists L', exists H',
    @typinf0 K0 E0 t T L S0 HS0 (proj1 HK0) D0 HL = Some (exist _ (K',S',L') H')
    /\
    exists S'',
      dom S'' << S.diff L' L /\ env_prop type S'' /\ extends (S & S'') S' /\
      well_subst K' K (S & S'').

Lemma principal_var : forall h L S0 K0 E0 HS0 HK0 D0 S K E x T HL,
  @principality S0 K0 E0 HS0 HK0 D0 S K E (trm_fvar x) T L HL (Datatypes.S h).
Proof.
  intros; intros HTS0 HE0 MGE HTS HSL Hext WS Typ Hh.
  inversions Typ; clear Typ; try discriminate.
  simpl.
  destruct (proj2 MGE _ _ H5) as [M' [B' MGM]].
  destruct (binds_map_inv _ _ B') as [M0 [HM0 B]].
  unfold typinf0; simpl lt_wf.
  lazy [typinf]; fold typinf.
  destruct (get_dep x E0) as [[M1 B1]|G]; [|elim (binds_fresh B G)].
  unfold binds in B; rewrite B1 in B.
  inversions B; clear B; rename B1 into B.
  destruct (var_freshes L (sch_arity M0)) as [Xs Fr]; simpl proj1_sig.
  destruct (var_freshes (dom K \u fv_in kind_fv K \u sch_fv M \u sch_fv M0
              \u fv_in typ_fv S) (sch_arity M)) as [Ys FrYs].
  destruct* (MGM Ys) as [Vs [HVs EVs]]. destruct H6.
  pose (Vs' := List.map (typ_subst (combine Ys Us)) Vs).
  assert (AryM0: sch_arity M0 = length Vs').
    destruct HVs. subst. rewrite sch_arity_subst in H4.
    unfold Vs'; rewrite map_length. apply (proj1 H4).
  assert (Hsub: forall t, typ_fv t << L ->
                  typ_subst (S & combine Xs Vs') t = typ_subst S t).
    rewrite AryM0 in Fr.
    intros.
    apply* typ_subst_combine_fresh.
    apply* fresh_sub.
  assert (Ok: ok (K0 & kinds_open_vars (sch_kinds M0) Xs)).
    unfold fvs in HL.
    apply* ok_kinds_open_vars. apply* fresh_sub.
  assert (Hext': extends (S & combine Xs Vs') S0).
    clear -Fr Hext Hsub HL. unfold fvs in HL.
    apply* extends_concat. auto.
  assert (PI: proper_instance K (sch_kinds (sch_subst S M0)) Vs').
    unfold Vs' in *. apply* proper_instance_inf. split*.
  assert (HU: unifies (S & combine Xs Vs') ((sch_open_vars M0 Xs, T) :: nil)).
    subst.
    unfold unifies; simpl; intros.
    destruct* H4. inversions H4; clear H4.
    destruct HVs. rewrite sch_arity_subst in H4.
    apply* unifies_open.
        unfold Vs'.
        apply* typ_subst_type_list.
        apply* list_forall_env_prop.
        apply (proj2 H).
      intros y Hy.
      puts (fv_in_spec sch_fv _ _ _ (binds_in B)).
      unfold fvs, env_fv in HL; simpl in *; auto.
    rewrite <- H0.
    unfold Vs'. apply* (sch_open_inf _ _ _ _ _ H EVs).
  set (HK0' := ok_kinds_open_vars (sch_kinds M0) Xs (proj41 HK0)
    (fresh_sub (sch_arity M0) Xs Fr (dom_K_L T HL))) in *.
  clearbody HK0'.
  assert (WS': well_subst (K0 & kinds_open_vars (sch_kinds M0) Xs)
                  K (S & combine Xs Vs')).
    intro; intros.
    refine (well_subst_concat_abs Xs HTS _ PI (x:=x) _ _ _ _ _ _ _); auto*.
    clear -HL HSL. auto.
  destruct (unify_dep (sch_open_vars M0 Xs) T HS0 HK0'
               (disjoint_fvar T M0 Xs D0 HL Fr))
    as [[[K' S'] [HU' [[HK' [HS' D']] Hf']]] | HU'];
  destruct* (unify_complete0 HU' Hext' HU WS')
    as [K1 [S1 [HU1 [Hext1 WS1]]]];
  inversions HU1; clear HU1.
  esplit; esplit; esplit; esplit; split*.
  destruct* (unify_kinds_ok HU').
    rewrite dom_concat.
    rewrite dom_kinds_open_vars by auto.
    puts (fresh_sub _ _ Fr HL). clear Fr.
    unfold fvs in H4; disjoint_solve.
  exists (combine Xs Vs').
  intuition.
  apply* list_forall_env_prop.
  unfold Vs'.
  assert (env_prop type (combine Ys Us)).
    apply list_forall_env_prop. apply (proj2 H).
  puts (proj2 (proj1 HVs)).
  clear -H9 H6; induction H9; simpl*.
Qed.

Lemma typ_subst_type' : forall S T,
  type (typ_subst S T) -> type T.
Proof.
  induction T; simpl; intros; auto.
  inversions H. auto.
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
      destruct* H0. subst*.
    auto.
  unfold env_fv, sch_fv; simpl*.
Qed.

Lemma env_subst_ext_fv : forall S1 S2 E,
  (forall t : typ, typ_fv t << env_fv E -> typ_subst S1 t = typ_subst S2 t) ->
  map (sch_subst S1) E = map (sch_subst S2) E.
Proof.
  induction E; simpl; intros. auto.
  destruct a.
  rewrite* <- IHE.
  rewrite* (sch_subst_ext_fv S1 S2).
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

Lemma moregen_mono : forall S0 K0 E0 T L S K E x x1 U S',
  fvs S0 K0 E0 \u typ_fv T << L ->
  moregen_env K (map (sch_subst S) E0) E ->
  (forall t, typ_fv t << L -> typ_subst (S & S') t = typ_subst S t) ->
  binds x1 U S' ->
  moregen_env K (map (sch_subst (S & S')) (E0 & x ~ Sch (typ_fvar x1) nil))
    (E & x ~ Sch U nil).
Proof.
  introv HL MGE Hsub B.
  rewrite map_concat.
  rewrite (env_subst_ext_fv (S & S') S).
    split. repeat rewrite dom_concat.
      rewrite (proj1 MGE). simpl*.
    intro; intros.
    binds_cases H.
      destruct (proj2 MGE _ _ B0) as [M' [BM' MGM']].
      exists M'. split*.
    destruct (binds_single_inv B1). subst.
    exists (Sch U nil).
    split.
      apply binds_prepend.
      unfold sch_subst; simpl. 
      rewrite (binds_prepend _ B).
      auto.
    apply moregen_scheme_refl.
  intros. apply Hsub.
  eapply subset_trans. apply H.
  unfold fvs in HL; auto.
Qed.

Lemma principal_abs : forall h L S0 K0 E0 HS0 HK0 D0 S K E t1 T HL,
  (forall L S0 K0 E0 HS0 HK0 D0 S K E t T HL,
    @principality S0 K0 E0 HS0 HK0 D0 S K E t T L HL h) ->
  @principality S0 K0 E0 HS0 HK0 D0 S K E (trm_abs t1) T L HL (Datatypes.S h).
Proof.
  introv IH; intros HTS0 HE0 MGE HTS HSL Hext WS Typ Hh.
  inversions Typ; try discriminate.
  unfold typinf0; simpl lt_wf.
  lazy [typinf]; fold typinf.
  destruct (var_fresh L) as [x1 Fr1]; simpl proj1_sig.
  destruct (var_fresh (L \u {{x1}})) as [x2 Fr2]; simpl proj1_sig.
  pose (Xs := x1 :: x2 :: nil).
  pose (Us := U :: T0 :: nil).
  assert (Fr: fresh L 2 Xs) by simpl*.
  assert (Hsub: forall t, typ_fv t << L ->
                  typ_subst (S & combine Xs Us) t = typ_subst S t).
    intros.
    apply* typ_subst_combine_fresh.
  assert (Hext': extends (S & combine Xs Us) S0).
    apply* extends_concat. unfold fvs in HL; auto.
  assert (HU: unifies (S & combine Xs Us)
                ((typ_arrow (typ_fvar x1) (typ_fvar x2), T) :: nil)).
    intro; intros.
    simpl in H; destruct* H. inversions H; clear H.
    rewrite (typ_subst_combine_fresh S T2).
      simpl. destruct* (x1 == x1).
      destruct* (x2 == x1).
        elim Fr2. rewrite* e0.
      destruct* (x2 == x2).
    simpl length. clear -HL Fr. unfold fvs in HL.
    refine (fresh_sub _ _ Fr _); auto.
  assert (WS': well_subst K0 K (S & combine Xs Us)).
    apply* well_subst_concat. instantiate (1:=E0); auto.
  destruct (unify_dep (typ_arrow (typ_fvar x1) (typ_fvar x2)) T HS0
               (proj41 HK0) D0) as [[[K' S'] [HU' [[HK' [HS' D']] Hf']]] | HU'];
  destruct* (unify_complete0 HU' Hext' HU WS')
    as [K1 [S1 [HU1 [Hext1 WS1]]]];
  inversions HU1; clear HU1.
  rewrite normalize_typinf.
  destruct (var_fresh (dom E0 \u trm_fv t1)) as [x Frx]; simpl proj1_sig.
  set (HS1 := Hf' E0); clearbody HS1; clear Hf'.
  destruct (unify_type HU') as [HKK' [HTS' _]]; auto.
    simpl; intros.
    destruct H; try contradiction.
    inversions H.
    split; auto. apply* (typ_subst_type' S).
  destruct* (unify_kinds_ok HU') as [_ [_ WS2]].
  poses UT (unify_types HU').
  assert (OkE0': env_ok (E0 & x ~ Sch (typ_fvar x1) nil)).
    split; auto.
    apply* env_prop_concat. intro; intros.
    destruct H; inversions H.
    apply* type_scheme.
  assert (TUs: env_prop type (combine Xs Us)).
    unfold Xs, Us. intro; simpl; intros.
    rewrite <- H0 in Typ.
    puts (proj44 (typing_regular Typ)).
    inversions H1.
    destruct H. inversion H. rewrite* <- H8.
    destruct* H. inversion H. rewrite* <- H8.
  forward~ (@IH (L\u{{x1}}\u{{x2}}) S1 K1 (E0 & x ~ Sch (typ_fvar x1) nil)
                   HS' HKK' D' (S & combine Xs Us) K (E & x ~ Sch U nil)
                   (t1 ^ x) (typ_fvar x2)).
        apply* moregen_mono. unfold Xs, Us. simpl. env_fix. auto.
      simpl typ_subst.
      destruct (x2 == x1). elim Fr2. rewrite* e.
      destruct* (x2 == x2). clear n e.
      destruct (var_fresh (L0 \u trm_fv t1 \u {{x}})) as [x0 Fr0].
      forward~ (H4 x0); intros.
      apply* (@typing_abs_rename x0).
      destruct (x == x0). elim Fr0; subst*.
      rewrite* <- (proj1 MGE).
    simpl in Hh.
    rewrite trm_depth_open. omega.
  intros [K2 [S2 [L' [[[HK2 [HS2 D2]] HL']
             [TI [S3 [HS3 [TS3 [Hext3 WS3]]]]]]]]].
  instantiate (1:=subset_abs T HL HS1) in TI.
  rewrite (ProofIrrelevance.proof_irrelevance _ HK' (proj1 HKK')).
  rewrite TI; clear TI.
  esplit; esplit; esplit; esplit; split*.
  exists (combine Xs Us & S3).
  rewrite <- concat_assoc.
  split*.
  rewrite dom_concat.
  unfold Xs, Us; simpl.
  clear -Fr1 Fr2 HL' HS3.
  sets_solve; apply* S.diff_3.
Qed.

Lemma sch_open_vars_type : forall M Xs,
  scheme M -> sch_arity M = length Xs -> type (sch_open_vars M Xs).
Proof.
  unfold sch_open_vars, typ_open_vars.
  intros; fold (sch_open M (typ_fvars Xs)).
  apply sch_open_types. auto.
  rewrite H0. apply types_typ_fvars.
Qed.

Lemma close_fvk_ok2 : forall K L L',
  ok K -> L' << close_fvk K L -> close_fvk K L' << close_fvk K L.
Proof.
  intros.
  intros y Hy.
  unfold close_fvk in Hy.
  puts (cardinal_env H).
  revert L' H0 Hy H1; generalize (dom K).
  induction (length K); simpl; intros; auto.
  case_rewrite R1 (S.choose (S.inter v L')).
    puts (S.choose_1 R1).
    assert (e \in close_fvk K L) by auto.
    assert (S.cardinal (S.remove e v) = n).
      assert (e \in v) by auto.
      puts (cardinal_remove H4).
      rewrite H1 in H5.
      inversion* H5.
    case_rewrite R2 (get e K).
      puts (close_fvk_ok L H H3 R2).
      assert (L' \u kind_fv k << close_fvk K L) by auto.
      apply* (IHn _ _ H6 Hy).
    apply* (IHn _ _ H0 Hy).
  auto.
Qed.

Lemma close_fvk_inv : forall K L,
  close_fvk K L << fv_in kind_fv K \u L.
Proof.
  unfold close_fvk.
  intro. generalize (dom K).
  induction (length K); simpl; intros. auto.
  destruct* (S.choose (S.inter v L)).
  intro; intros.
  puts (IHn _ _ _ H).
  sets_solve.
  case_rewrite R1 (get e K).
    use (fv_in_spec kind_fv _ _ _ (binds_in R1)).
  auto.
Qed.

Lemma vars_subst_empty : forall S, vars_subst S {} = {}.
Proof.
  intros.
  unfold vars_subst.
  remember (S.elements {}) as l.
  destruct* l.
  assert (SetoidList.InA E.eq e (e::l)) by auto.
  rewrite Heql in H.
  puts (S.elements_2 H). elim (in_empty H0).
Qed.

Lemma vars_subst_incl : forall S l1 l2,
  let s := fun x => typ_subst S (typ_fvar x) in
  incl l1 l2 ->
  typ_fv_list (List.map s l1) << typ_fv_list (List.map s l2).
Proof.
  intros; induction l1; simpl. auto.
  sets_solve.
    assert (In a l2). apply* H.
    clear -H0 H1.
    induction l2; simpl in *. elim H1.
    destruct H1. subst*.
    use (IHl2 H).
  assert (incl l1 l2). intro; intros; apply* H.
  use (IHl1 H1).
Qed.

Lemma vars_subst_union : forall S L1 L2,
  vars_subst S (L1 \u L2) = vars_subst S L1 \u vars_subst S L2.
Proof.
  intros.
  unfold vars_subst.
  set (l:=S.elements (L1 \u L2)) in *.
  set (l1:=S.elements L1) in *.
  set (l2:=S.elements L2) in *.
  assert (incl (l1 ++ l2) l).
    intros x Hx.
    apply InA_In. unfold l; apply S.elements_1.
    destruct (in_app_or _ _ _ Hx); [apply S.union_2|apply S.union_3];
      apply S.elements_2; apply (SetoidList.In_InA E.eq_refl).
      fold l1; auto.
    fold l2; auto.
  assert (incl l (l1 ++ l2)).
    intros x Hx.
    puts (SetoidList.In_InA E.eq_refl Hx).
    apply in_or_app.
    destruct (S.union_1 (S.elements_2 H0));
      [left | right]; apply InA_In; apply* (S.elements_1 H1).
  apply eq_ext; split; intros.
    puts (vars_subst_incl S H0).
    rewrite map_app in H2.
    rewrite fv_list_map in H2. auto.
  puts (vars_subst_incl S H).
  rewrite map_app in H2.
  rewrite fv_list_map in H2. auto.
Qed.

Lemma typ_fv_after_subst : forall S T,
  typ_fv (typ_subst S T) = vars_subst S (typ_fv T).
Proof.
  intros.
  induction T; simpl. rewrite* vars_subst_empty.
    unfold vars_subst. rewrite elements_singleton. simpl.
    rewrite* union_empty_r.
  rewrite vars_subst_union. congruence.
Qed.

Lemma kind_fv_after_subst : forall S k,
  kind_fv (kind_subst S k) = vars_subst S (kind_fv k).
Proof.
  unfold kind_fv.
  intros.
  destruct k as [[kc kv kr kh]|]; simpl.
    clear kh; induction kr; simpl. rewrite* vars_subst_empty.
    rewrite IHkr.
    rewrite vars_subst_union.
    rewrite* typ_fv_after_subst.
  rewrite* vars_subst_empty.
Qed.

Lemma sch_fv_after_subst: forall S M,
  sch_fv (sch_subst S M) = vars_subst S (sch_fv M).
Proof.
  unfold sch_fv; destruct M as [T Ks]; intros.
  simpl sch_type. simpl sch_kinds.
  rewrite vars_subst_union.
  rewrite typ_fv_after_subst.
  apply (f_equal (S.union (vars_subst S (typ_fv T)))).
  induction Ks; simpl. rewrite* vars_subst_empty.
  rewrite kind_fv_after_subst. rewrite vars_subst_union.
  congruence.
Qed.

Lemma close_fvk_subst : forall K K' S x E,
  well_subst K K' S -> ok K' ->
  x \in close_fvk K (env_fv E) ->
  typ_fv (typ_subst S (typ_fvar x)) <<
  close_fvk K' (env_fv (map (sch_subst S) E)).
Proof.
  unfold env_fv.
  introv WS Ok Hx.
  unfold close_fvk in Hx.
  set (L:=fv_in sch_fv E) in Hx.
  assert (forall x, x \in L -> typ_fv (typ_subst S (typ_fvar x)) <<
    close_fvk K' (fv_in sch_fv (map (sch_subst S) E))).
    clear x Hx; subst L; intros x Hx.
    eapply subset_trans; [|apply close_fvk_subset].
    destruct (fv_in_binds _ _ Hx) as [y [a [Ha B]]].
    assert (In (y, sch_subst S a) (map (sch_subst S) E)).
      rewrite <- map_snd_env_map.
      apply (in_map_snd (sch_subst S) _ _ _ B).
    eapply subset_trans; [|apply (fv_in_spec sch_fv _ _ _ H)]; clear H.
    destruct a as [T Ks].
    unfold sch_fv in Ha; simpl in Ha.
    destruct (S.union_1 Ha); clear Ha.
      unfold sch_fv; simpl sch_type.
      rewrite (typ_fv_after_subst S T).
      use (vars_subst_in S H).
    unfold sch_fv; simpl sch_kinds.
    intros z Hz; apply S.union_3.
    clear B; induction Ks. elim (in_empty H).
    simpl in H; simpl. destruct (S.union_1 H); clear H.
      rewrite (kind_fv_after_subst S).
      use (vars_subst_in S H0).
    use (IHKs H0).
  revert L Hx H. generalize (dom K).
  induction (length K); simpl close_fvars; intros. auto.
  case_rewrite R1 (S.choose (S.inter v L)).
    case_rewrite R2 (get e K).
      apply (IHn _ _ Hx); clear IHn Hx; intros.
      destruct* (S.union_1 H0); clear H0.
      puts (S.inter_2 (S.choose_1 R1)).
      puts (H _ H0); clear H H0.
      puts (WS _ _ R2).
      inversions H.
        destruct k; try discriminate. elim (in_empty H1).
      fold (typ_subst S (typ_fvar e)) in H3.
      rewrite <- H3 in H2. simpl in H2.
      puts (H2 x1 (S.singleton_2 (refl_equal _))); clear H2.
      puts (close_fvk_ok _ Ok H4 H5).
      intros y Hy; apply H2.
      apply (kind_entails_fv (Some k') (Some k0)). simpl*.
      rewrite H0. rewrite (kind_fv_after_subst S).
      apply (vars_subst_in S H1 Hy).
    apply* IHn.
  auto*.
Qed.

Lemma typ_fv_open_min : forall Ts T,
  typ_fv T << typ_fv (typ_open T Ts).
Proof.
  induction T; simpl; sets_solve.
Qed.

Lemma kind_fv_open_min : forall Ts k,
  kind_fv k << kind_fv (kind_open k Ts).
Proof.
  unfold kind_fv.
  destruct k as [[kc kv kr kh]|]; simpl*.
  clear kh; induction kr; simpl; sets_solve.
  use (typ_fv_open_min Ts (snd a)).
Qed.

Lemma moregen_scheme_fv : forall K M0 M,
  moregen_scheme K M0 M ->
  sch_fv M0 << sch_fv M \u fv_in kind_fv K.
Proof.
  unfold moregen_scheme.
  intros.
  destruct (var_freshes (dom K \u sch_fv M0) (sch_arity M)) as [Ys Fr].
  destruct* (H Ys) as [Ts [PI SO]]; clear H.
  intros y Hy.
  destruct M0 as [T1 K1]; destruct M as [T2 K2]; simpl in *.
  unfold sch_open in SO; simpl in SO.
  unfold sch_fv in *; simpl in *; sets_solve.
    puts (typ_fv_open (typ_fvars Ys) T2).
    rewrite <- SO in H0.
    puts (typ_fv_open_min Ts T1).
    sets_solve.
    rewrite typ_fv_typ_fvars in H0. auto.
  unfold proper_instance in PI. intuition.
  clear -Fr H H1.
  remember Ts as Us.
  pattern Us at 2 in H1. rewrite HeqUs in H1.
  clear HeqUs; gen Ts; induction K1; intros. elim (in_empty H).
  simpl in *.
  inversions H1; clear H1.
  destruct (S.union_1 H); clear H.
    inversions H3. destruct a; try discriminate. elim (in_empty H0).
    puts (kind_fv_open_min Us a).
    puts (kind_entails_fv (Some k') (Some k)).
    simpl in H6; rewrite H in H6.
    puts (H6 H4); clear H6; sets_solve.
    puts (fv_in_spec kind_fv _ _ _ (binds_in H1) Hin0).
    rewrite fv_in_concat in H2.
    disjoint_solve.
    unfold kinds_open_vars in H1.
    rewrite fv_in_kind_fv_list in H1; auto.
    clear -Hin1 H H1.
    rewrite <- typ_fv_typ_fvars in Hin1.
    induction K2; intros. elim (in_empty H1).
    simpl in *.
    sets_solve.
      use (kind_fv_open _ _ H0).
    use (IHK2 H0).
  apply* IHK1.
Qed.

Lemma moregen_env_fv : forall K E E0,
  moregen_env K E0 E -> ok E0 ->
  env_fv E0 << env_fv E \u fv_in kind_fv K.
Proof.
  introv HME Ok.
  destruct HME.
  intros y Hy.
  destruct (fv_in_binds sch_fv E0 Hy) as [x [a [Hx B]]].
  puts (in_dom _ _ _ B).
  rewrite H in H1.
  destruct (dom_binds _ H1) as [z Hz].
  destruct (H0 _ _ Hz) as [b [Hb HM]].
  puts (binds_func Hb (in_ok_binds _ _ B Ok)). subst b.
  puts (moregen_scheme_fv HM).
  sets_solve.
  unfold env_fv.
  use (fv_in_spec sch_fv _ _ _ (binds_in Hz)).
Qed.

Lemma close_fvk_disjoint : forall K K' L,
  disjoint (L \u fv_in kind_fv K) (dom K') -> ok (K & K') ->
  close_fvk (K & K') L << close_fvk K L.
Proof.
  introv H Ok x Hx.
  unfold close_fvk in Hx.
  set (L' := L) in H, Hx.
  assert (L' << close_fvk K L) by apply close_fvk_subset.
  gen L'; generalize (dom (K&K')); induction (length (K & K')); simpl; intros.
    auto.
  case_rewrite R1 (S.choose (S.inter v L')).
    puts (S.inter_2 (S.choose_1 R1)).
    assert (e # K') by auto.
    case_eq (get e K); introv R2.
      rewrite (binds_concat_fresh _ R2 H2) in Hx.
      refine (IHn _ _ _ Hx _).
        use (fv_in_spec kind_fv _ _ _ (binds_in R2)).
      intros y Hy.
      poses OkK (proj1 (ok_concat_inv _ _ Ok)).
      apply (close_fvk_ok2 _ OkK H0).
      clear H0.
      sets_solve. apply* close_fvk_subset.
      refine (close_fvk_ok _ OkK _ R2 H0). apply* close_fvk_subset.
    rewrite get_notin_dom in Hx; auto*.
  auto.
Qed.

Lemma kindl_generalize_reopen : forall Xs Ks,
  list_forall (All_kind_types type) Ks ->
  kinds_open (List.map (kind_map (typ_generalize Xs)) Ks) (typ_fvars Xs) = Ks.
Proof.
  unfold kinds_open; intros.
  induction H; simpl. auto.
  rewrite* kind_generalize_reopen.
  congruence.
Qed.

Lemma typ_subst_combine_inv : forall x Xs Ys,
  let XYs := combine Xs (typ_fvars Ys) in
  exists y, typ_subst XYs (typ_fvar x) = typ_fvar y
    /\ (x = y /\ x # XYs \/ binds x (typ_fvar y) XYs).
Proof.
  induction Xs; destruct Ys; simpl; try solve [exists* x].
  destruct (x == a). env_fix. subst. exists* v.
  env_fix.
  destruct (IHXs Ys) as [y [Ts Hy]].
  destruct Hy. simpl in Ts; subst. exists* y.
  exists* y.
Qed.

Lemma binds_map_var : forall (A:Set) x y (a:A) Xs Ys As,
  fresh {} (length Xs) Ys ->
  binds x (typ_fvar y) (combine Xs (typ_fvars Ys)) ->
  binds x a (combine Xs As) ->
  binds y a (combine Ys As).
Proof.
  unfold binds. generalize {}.
  induction Xs; destruct Ys; destruct As; simpl; intros; try discriminate.
  destruct (x == a0).
    inversions H0.
    inversions H.
    destruct* (y == y).
  destruct (y == v).
    subst.
    puts (in_combine_r _ _ _ _ (binds_in H0)).
    destruct H.
    clear -H2 H3. elimtype False.
    gen t. generalize (length Xs).
    induction Ys; simpl; intros; destruct* n.
    simpl in H2. destruct H3.
    destruct H2. inversions* H1.
    apply* (IHYs H1 n t).
  apply* (IHXs Ys As).
Qed.

Lemma vars_subst_inv : forall S L x,
  x \in vars_subst S L ->
  exists y, y \in L /\ x \in typ_fv (typ_subst S (typ_fvar y)).
Proof.
  unfold vars_subst.
  intros.
  rewrite <- (mkset_elements L).
  induction (S.elements L). elim (in_empty H).
  set (sS := typ_subst S) in *.
  simpl in *.
  destruct (S.union_1 H); clear H.
    exists* a.
  destruct (IHl H0). exists* x0.
Qed.

Lemma ftve_subst : forall S' K' E0 S K E S1 M Xs y,
  let K1 := map (kind_subst S') K' in
  let E1 := map (sch_subst S') E0 in
  y \in close_fvk K1 (env_fv E1) ->
  moregen_env K (map (sch_subst S) E0) E ->
  env_ok E0 ->
  extends S1 S' ->
  well_subst K' (K & kinds_open_vars (sch_kinds M) Xs) S1 ->
  ok (K & kinds_open_vars (sch_kinds M) Xs) ->
  fresh (env_fv E \u fv_in kind_fv K) (sch_arity M) Xs ->
  (forall t : typ, typ_fv t << env_fv E0 -> typ_subst S1 t = typ_subst S t) ->
  typ_fv (typ_subst S1 (typ_fvar y)) << env_fv E \u fv_in kind_fv K.
Proof.
  intros until E1; intros H MGE OkE0 Hext WS Ok Fr Hsub.
  poses WS1 (well_subst_extends Hext WS). fold K1 in WS1.
  intros x Hx.
  puts (@close_fvk_subst _ _ _ y E1 WS1 Ok H _ Hx).
  clear H Hx.
  unfold E1 in H0. rewrite map_sch_subst_extend in H0; auto.
  rewrite <- (env_subst_ext_fv S) in H0.
    assert (ok (map (sch_subst S) E0)) by auto.
    puts (moregen_env_fv MGE H).
    cut (x \in close_fvk K (env_fv E \u fv_in kind_fv K)); intros.
      use (close_fvk_inv _ _ H2).
    refine (close_fvk_ok2 _ _ (L':=env_fv(map (sch_subst S) E0)) _ _).
        destruct* (ok_concat_inv _ _ Ok).
      intros z Hz. apply* close_fvk_subset.
    refine (close_fvk_disjoint _ (kinds_open_vars (sch_kinds M) Xs) _ _ _);
      auto.
  intros. symmetry. auto.
Qed.

Lemma typinf_generalize_sch_fv : forall K1 E1 T1 e e0 e1 e2 l l0,
  let ftve := close_fvk K1 (env_fv E1) in
  let Bs := S.elements (S.diff (close_fvk K1 (typ_fv T1)) (ftve \u dom e2)) in
  let l0' := List.map (fun _ : var => None) Bs in
  let M0 := sch_generalize (l ++ Bs) T1 (l0 ++ l0') in
  ok K1 ->
  kenv_ok (e0 & e) ->
  split_env ftve K1 = (e, e0) -> 
  split_env (close_fvk K1 (typ_fv T1)) e = (e1, e2) ->
  split e2 = (l, l0) ->
  sch_fv M0 << ftve.
Proof.
  intros until M0. intros Ok1 Oke0 R1 R2 R3.
  unfold M0; intros x Hx.
  destruct (split_env_ok _ R2).
    destruct* (ok_concat_inv _ _ (proj1 Oke0)).
  puts (split_combine _ R3).
  destruct* (in_vars_dec x ftve).
  elimtype False.
  elim (@sch_generalize_disjoint (l++Bs) T1 (l0 ++ l0') x). auto.
  rewrite mkset_app.
  unfold Bs; rewrite mkset_elements.
  rewrite* <- H1.
  destruct* (in_vars_dec x (mkset l)).
  cut (x \in close_fvk K1 (typ_fv T1)). auto*.
  destruct* (split_env_ok _ R1). clear H H2.
  puts (sch_fv_generalize Hx).
  unfold sch_fv in H; simpl in H.
  sets_solve. apply* close_fvk_subset.
  rewrite kind_fv_list_app in H2.
  sets_solve.
    rewrite <- (fv_in_kind_fv_list _ _ (split_length _ R3)) in H.
    rewrite H1 in H.
    destruct (fv_in_binds _ _ H) as [y [b [Hx' Hy]]].
    assert (In (y,b) K1).
      apply (proj44 H3).
      apply in_or_concat; left*.
    refine (close_fvk_ok _ _ _ _ Hx'); trivial.
      apply (proj42 H0). apply (in_dom _ _ _ Hy).
    auto.
  unfold l0' in H.
  elimtype False; clear -H; induction Bs. elim (in_empty H).
  simpl in *. elim IHBs. sets_solve. elim (in_empty H0).
Qed.

Lemma sch_subst_compose : forall S1 S2 M,
  sch_subst (compose S1 S2) M = sch_subst S1 (sch_subst S2 M).
Proof.
  unfold sch_subst; simpl.
  intros.
  rewrite typ_subst_compose.
  apply f_equal.
  induction (sch_kinds M). auto.
  simpl. rewrite IHl. rewrite* kind_subst_compose.
Qed.

Lemma typinf_generalize_well_kinded : forall K1 S1 M Xs Ys l l0 K,
  let XYs := combine Xs (typ_fvars Ys) in
  fresh (sch_fv M \u fv_in kind_fv K) (sch_arity M) Xs ->
  well_subst K1 (K & kinds_open_vars (sch_kinds M) Xs) S1 ->
  fresh (dom K) (sch_arity M) Ys ->
  ok K1 ->
  dom XYs = mkset Xs ->
  env_prop type XYs ->
  incl (combine l l0) K1 ->
  length l = length l0 ->
  list_forall2 (well_kinded (K & kinds_open_vars (sch_kinds M) Ys))
    (List.map (kind_subst (compose XYs S1)) l0)
    (List.map (typ_subst (compose XYs S1)) (List.map typ_fvar l)).
Proof.
  intros until XYs. intros Fr WS HYs Ok1 DXYs HXYs H6 H0.
  gen l0. fold kind.
  induction l; destruct l0; simpl; intros; auto;
    try discriminate.
  inversion H0; clear H0.
  constructor.
    fold (typ_subst (compose XYs S1) (typ_fvar a)).
    rename WS into H.
    assert (well_kinded K1 k (typ_fvar a)) by destruct* k.
    puts (well_kinded_subst H H0).
    rewrite kind_subst_compose.
    rewrite typ_subst_compose.
    inversions H2. apply wk_any.
    simpl.
    rewrite <- H4.
    clear H3 H4 IHl.
    destruct (typ_subst_combine_inv x Xs Ys) as [y [Tsy Hy]].
    fold XYs in Tsy. rewrite Tsy.
    destruct Hy. destruct H3. subst.
      binds_cases H7.
        eapply wk_kind. puts (binds_dom B). apply* binds_concat_fresh.
        assert (kind_subst XYs (Some k') = (Some k')).
          apply kind_subst_fresh.
          rewrite DXYs. 
          use (fv_in_spec kind_fv _ _ _ (binds_in B)).
        simpl in H3. inversion H3.
        apply (kind_subst_entails XYs H8).
      fold XYs in H4; rewrite DXYs in H4.
      puts (binds_dom B0). rewrite dom_kinds_open_vars in H3; auto*.
    binds_cases H7.
      fold XYs in H3.
      puts (binds_dom H3).
      rewrite DXYs in H4.
      rewrite dom_kinds_open_vars in Fr0; auto*.
    puts (binds_map (kind_subst XYs) B0).
    apply* (@wk_kind (ckind_map (typ_subst XYs) k')).
    apply binds_prepend.
    unfold kinds_open_vars in H4.
    rewrite map_combine in H4.
    rewrite kinds_subst_open in H4; auto.
    poses Fr' Fr.
    rewrite (fresh_length _ _ _ HYs) in Fr'.
    replace (length Ys) with (length (typ_fvars Ys)) in Fr' by auto.
    puts (fresh_subst _ _ _ Fr').
    fold XYs in H5; rewrite H5 in H4.
    rewrite kinds_subst_fresh in H4.
      apply* binds_map_var.
    rewrite* <- (fresh_length _ _ _ Fr).
    unfold sch_fv in Fr.
    rewrite* DXYs.
  apply* (IHl l0).
Qed.

Lemma moregen_let :
  forall M Xs S' x1 l l0 S0 T L L' (K' K0 K:kenv) E0 E S S'' e e0 e1 e2 t1,
  let MXs := sch_open_vars M Xs in
  let K1 := map (kind_subst S') K' in
  let E1 := map (sch_subst S') E0 in
  let ftve := close_fvk K1 (env_fv E1) in
  let T1 := typ_subst S' (typ_fvar x1) in
  let Bs := S.elements (S.diff (close_fvk K1 (typ_fv T1)) (ftve \u dom e2)) in
  let l0' := List.map (fun _ : var => None) Bs in
  let M0 := sch_generalize (l++Bs) T1 (l0++l0') in
  moregen_env K (map (sch_subst S) E0) E ->
  env_ok E0 ->
  split_env ftve K1 = (e, e0) ->
  split_env (close_fvk K1 (typ_fv T1)) e = (e1, e2) ->
  split e2 = (l, l0) ->
  dom S \u fvs S0 K0 E0 \u typ_fv T << L ->
  dom S'' << S.diff L' (L \u {{x1}}) -> 
  extends (S & x1 ~ MXs & S'') S' ->
  fresh (L \u {{x1}} \u env_fv E \u sch_fv M \u fv_in kind_fv K)
    (sch_arity M) Xs ->
  x1 \notin L ->
  is_subst S' -> env_prop type S' -> env_prop type S -> env_prop type S'' ->
  kenv_ok (e0 & e) -> kenv_ok (e2 & e1) -> ok K' ->
  well_subst K' (K & kinds_open_vars (sch_kinds M) Xs) (S & x1 ~ MXs & S'') ->
  K & kinds_open_vars (sch_kinds M) Xs; E |(false, GcAny)|= t1 ~: MXs ->
  (forall t, typ_fv t << L ->
    typ_subst (S & x1 ~ MXs) t = typ_subst S t) ->
  (forall S t, typ_fv t << L \u {{x1}} ->
    typ_subst (S & S'') t = typ_subst S t) ->
  moregen_scheme K (sch_subst (S & x1 ~ MXs & S'') M0) M.
Proof.
  intros until M0.
  intros MGE OkE0 R1 R2 R3 HL HS'' Hext Fr Fr1 HS' HTS' HTS HTS''
    Oke0 Oke2 Ok' WS Typ Hsub Hsub'.
  intro; intros.
  assert (type T1) by (unfold T1; auto).
  assert (env_prop type (S & x1 ~ MXs)) by auto.
  assert (env_prop type (S & x1 ~ MXs & S'')) by auto.
  set (S1 := S & x1 ~ MXs & S'') in *.
  pose (XYs := combine Xs (typ_fvars Ys)).
  assert (Ok1: ok K1) by (unfold K1; auto).
  assert (sch_fv M0 << ftve)
    by apply (typinf_generalize_sch_fv _ Ok1 Oke0 R1 R2 R3).
  assert(sch_fv (sch_subst S1 M0) << env_fv E \u fv_in kind_fv K).
    intros x Hx.
    rewrite sch_fv_after_subst in Hx.
    destruct (vars_subst_inv _ _ Hx) as [y [Hy Hx']].
    unfold ftve, K1, E1 in *;
      refine (ftve_subst _ _ _ (H3 _ Hy) MGE _ Hext WS _ _ _ Hx'); auto.
    intros; unfold fvs in HL; unfold S1; rewrite* Hsub'.
  assert (DXYs: dom XYs = mkset Xs).
    unfold XYs. rewrite dom_combine. auto.
    rewrite <- (fresh_length _ _ _ Fr).
    unfold typ_fvars; rewrite map_length.
    auto.
  assert (sch_subst (compose XYs S1) M0 = sch_subst S1 M0).
    rewrite sch_subst_compose.
    apply sch_subst_fresh.
    rewrite* DXYs.
  assert (HXYs: env_prop type XYs).
     apply list_forall_env_prop. apply (proj2 (types_typ_fvars Ys)).
  exists (List.map (typ_subst (compose XYs S1)) (typ_fvars (l ++ Bs))).
  split.
    split.
      rewrite sch_arity_subst.
      unfold M0. simpl.
      split.
        unfold l0'. length_hyps. fold kind; rewrite* <- H7.
      puts (proj2 (types_typ_fvars (l++Bs))).
      clear -H6 H2 HXYs; induction H6; simpl*.
    replace (kinds_open (sch_kinds (sch_subst S1 M0))
        (List.map (typ_subst (compose XYs S1)) (typ_fvars (l ++ Bs))))
       with (List.map (kind_subst (compose XYs S1))
              (kinds_open (sch_kinds M0) (typ_fvars (l ++ Bs)))).
      unfold M0; simpl.
      rewrite kindl_generalize_reopen.
      unfold typ_fvars; repeat rewrite map_app.
      apply list_forall2_app.
        assert (incl e2 K1). intro; intros.
          destruct (split_env_ok _ R1); auto.
          destruct (split_env_ok _ R2); [auto*|].
          apply (proj44 H8).
          apply in_or_concat; left.
          apply (proj44 H10). auto.
        rewrite <- (split_combine _ R3)in H6.
        apply* (@typinf_generalize_well_kinded (map (kind_subst S') K')).
      unfold l0'. clearbody Bs XYs S1. clear.
      induction Bs; simpl. auto.
     constructor; auto.
    apply list_forall_app.
      puts (split_combine _ R3).
      refine (env_prop_list_forall l _ _ _ _); auto*; fold kind; rewrite* H6.
    unfold l0'; clearbody Bs; clear. induction Bs; simpl*.
   rewrite kinds_subst_open.
     clearbody M0; clear -H5. unfold sch_subst in H5; simpl in H5.
     inversion H5. rewrite* H1.
   apply* env_prop_type_compose.
  rewrite <- H5.
  rewrite <- sch_subst_open.
   rewrite typ_subst_compose.
   replace M with (sch_subst XYs M).
    rewrite <- (fresh_subst {} Xs (typ_fvars Ys)). fold XYs.
     rewrite <- sch_subst_open.
      unfold M0; simpl.
      unfold sch_open. simpl.
      rewrite* typ_generalize_reopen.
      unfold S1, T1.
      rewrite Hext.
      unfold S1; rewrite typ_subst_concat_fresh.
        simpl. destruct* (x1 == x1).
      simpl*.
     auto.
    unfold typ_fvars; rewrite map_length.
    rewrite* <- (fresh_length _ _ _ H).
   rewrite* sch_subst_fresh.
   rewrite* DXYs.
  apply* env_prop_type_compose.
Qed.

Lemma fv_in_sch_subst : forall S E,
  env_fv (map (sch_subst S) E) << env_fv E \u fv_in typ_fv S.
Proof.
  induction E; simpl; intros y Hy. auto.
  destruct a. simpl in Hy.
  use (@sch_fv_subst S s).
Qed.

Lemma binds_kdom_inv : forall x K,
  ok K -> x \in kdom K -> exists k, binds x (Some k) K.
Proof.
  induction 1; intros. elim (in_empty H).
  simpl in H1. destruct a.
    destruct (x == x0). subst. exists* c.
    destruct (S.union_1 H1). elim n. rewrite* (S.singleton_1 H2).
    destruct (IHok H2). exists* x1.
  destruct (IHok H1). exists* x1.
Qed.

Lemma kdom_dom : forall K, kdom K << dom K.
  induction K; simpl*. destruct a. destruct* k.
Qed.

Lemma principal_let : forall h L S0 K0 E0 HS0 HK0 D0 S K E t1 t2 T HL,
  (forall L S0 K0 E0 HS0 HK0 D0 S K E t T HL,
    @principality S0 K0 E0 HS0 HK0 D0 S K E t T L HL h) ->
  @principality S0 K0 E0 HS0 HK0 D0 S K E (trm_let t1 t2) T L HL(Datatypes.S h).
Proof.
  introv IH; intros HTS0 HE0 MGE HTS HSL Hext WS Typ Hh.
  inversions Typ; try discriminate.
  unfold typinf0; simpl lt_wf.
  lazy [typinf]; fold typinf.
  rewrite normalize_typinf.
  destruct (var_fresh L) as [x1 Fr1]; simpl proj1_sig.
  destruct (var_freshes (L1 \u L \u {{x1}} \u
    env_fv E \u sch_fv M \u fv_in kind_fv K) (sch_arity M))
    as [Xs Fr].
  forward~ (H3 Xs); clear H3; intros Typ1.
  set (MXs := sch_open_vars M Xs) in *.
  assert (Hcb: x1 ~ MXs = combine (x1::nil) (MXs :: nil)) by simpl*.
  assert (Hsub: forall t, typ_fv t << L ->
                  typ_subst (S & x1 ~ MXs) t = typ_subst S t).
    intros.
    apply typ_subst_concat_fresh.
    simpl. intro y; destruct* (y == x1).
  assert (Hext0: extends (S & x1 ~ MXs) S0).
    rewrite Hcb.
    apply* (@extends_concat S0 S L 1).
    unfold fvs in HL; auto.
  forward~ (IH (L \u {{x1}}) S0 K0 E0 HS0 HK0 D0 (S & x1 ~ MXs)
                (K & kinds_open_vars (sch_kinds M) Xs) E t1 (typ_fvar x1)).
       split. rewrite <- (proj1 MGE). repeat rewrite* dom_map.
       intros. destruct (proj2 MGE _ _ H) as [M1 [BM1 MGM1]].
       exists M1.
       rewrite (env_subst_ext_fv (S & x1 ~ MXs) S).
        split*.
        intro; intros.
        rewrite dom_concat in H0.
        destruct* (MGM1 Ys).
        exists x0.
        split*.
        destruct H1. destruct H1.
        split. auto.
        refine (list_forall2_imp _ H3 _).
        intros. apply* well_kinded_weaken.
        rewrite <- dom_concat in H0.
        apply* ok_kinds_open_vars.
       intros. apply Hsub. unfold fvs in HL; auto.
     rewrite Hcb.
     apply* (@well_subst_concat E0).
     apply* well_subst_extends.
     intro; intros.
     apply* well_kinded_extend.
    simpl typ_subst. destruct* (x1 == x1).
   simpl in Hh.
   eapply Lt.le_lt_trans. apply (Max.le_max_l (trm_depth t1) (trm_depth t2)).
   omega.
  instantiate (1:=subset_let1 HL).
  intros [K' [S' [L' [[[HK1 [HS' D']] HL'] [HI [S'' H'']]]]]].
  rewrite HI.
  destruct* (typinf_sound _ _ _ _ _ (lt_n_Sn _) HI)
    as [_ [HTS' [HK' [WS' [_ Typ']]]]]; clear HI.
  set (K1 := map (kind_subst S') K') in *.
  set (E1 := map (sch_subst S') E0) in *.
  fold (typ_subst S' (typ_fvar x1)).
  set (T1 := typ_subst S' (typ_fvar x1)) in *.
  set (ftve := close_fvk K1 (env_fv E1)) in *.
  rewrite normalize_typinf.
  destruct (var_fresh (dom E0 \u trm_fv t1 \u trm_fv t2)) as [x Frx];
    simpl proj1_sig.
  set (HG := ok_generalize T (vars_subst S' (kdom K0)) x HK1 D' HL HL').
  clearbody HG. lazy zeta in HG.
  revert HG. fold K1; fold E1; fold T1.
  remember (typinf_generalize K1 E1 (vars_subst S' (kdom K0)) T1) as TG.
  revert HeqTG; unfold typinf_generalize.
  fold ftve.
  case_eq (split_env ftve K1); introv R1.
  case_eq (split_env (close_fvk K1 (typ_fv T1)) e); introv R2.
  case_eq (split e2); introv R3.
  case_eq (split_env (vars_subst S' (kdom K0)) e); introv R4.
  set (Bs := S.elements (S.diff (close_fvk K1 (typ_fv T1)) (ftve \u dom e2))).
  set (l0' := List.map (fun _ : var => @None ckind) Bs).
  set (M0 := sch_generalize (l++Bs) T1 (l0++l0')).
  intro TI; subst TG. simpl fst; simpl snd.
  intros [HKG [Dis04 Fvs04]].
  assert (OkK1: kenv_ok K1) by apply* kenv_ok_map.
  destruct* (split_env_ok _ R1).
  assert (Oke: kenv_ok (e0 & e)) by (kenv_ok_solve; intro; intros; apply* H9).
  assert (Oke1: kenv_ok (e2 & e1)).
    destruct* (split_env_ok _ R2).
    kenv_ok_solve; intro; intros; apply* H20.
  assert (HM0: scheme M0).
    unfold M0; apply* scheme_generalize.
        do 2 rewrite app_length. unfold l0'; rewrite map_length.
        rewrite* (split_length _ R3).
      unfold T1; auto*.
    apply list_forall_app.
      rewrite <- (split_combine _ R3) in Oke1.
      refine (env_prop_list_forall l _ _ _ _); auto.
    unfold l0'; clear. induction Bs; simpl*.
  assert (Hsub': forall S t, typ_fv t << L \u {{x1}} ->
                  typ_subst (S & S'') t = typ_subst S t).
    intros; apply* typ_subst_concat_fresh.
  assert (Inc04: incl (e0 & e4) K1).
    intro; intros. apply (proj44 H0).
    destruct (in_concat_or _ _ _ H1); auto.
    destruct (split_env_ok _ R4). destruct* Oke.
    apply* in_or_concat.
  assert (Ok04: kenv_ok (e0 & e4)).
    kenv_ok_solve.
    intro; intros. apply* H2.
  assert (OkE0': env_ok (E0 & x ~ M0)) by auto.
  assert (HT: type T) by apply* (typ_subst_type' S).
  forward~ (IH L' S' (e0&e4) (E0&x~M0) HS' Ok04 Dis04
              (S& x1~MXs &S'') K (E&x~M) (t2 ^ x) T).
       split.
         repeat rewrite dom_concat.
         rewrite <- (proj1 MGE). repeat rewrite dom_map.
         rewrite dom_concat; simpl*.
       intros.
       binds_cases H1.
         destruct (proj2 MGE _ _ B) as [M2 [BM2 HM2]].
         exists M2.
         split*.
         apply binds_concat_fresh.
           rewrite concat_assoc.
           rewrite (env_subst_ext_fv (S & (x1 ~ MXs & S'')) S). auto.
           intros; rewrite <- concat_assoc.
           unfold fvs in HL.
           rewrite* Hsub'.
         rewrite dom_map. simpl. auto.
        destruct (binds_single_inv B0); subst.
        exists (sch_subst (S & x1 ~ MXs & S'') M0).
        clear H1 B0 H3.
        split. unfold binds. simpl. destruct* (x0 == x0).
        unfold M0, l0', Bs, ftve, K1, T1, E1, MXs; apply* moregen_let.
        rewrite <- union_assoc.
        intro; intros. destruct (S.union_1 H1). auto. apply (HL _ H2).
       auto*.
      repeat rewrite dom_concat in *. intuition.
      auto*.
     intro; intros.
     assert (binds Z k K1) by auto*.
     unfold K1 in H2. destruct (binds_map_inv _ _ H2) as [k1 [Hk1 Bk1]].
     subst k.
     puts ((proj44 H'') _ _ Bk1).
     rewrite (kind_subst_extend k1 (proj43 H'')).
     inversions H3. destruct k1; try discriminate. apply wk_any.
     simpl; rewrite <- H6; rewrite <- H4.
     binds_cases H8. auto*.
     env_fix.
     fold (typ_subst (S & x1 ~ MXs & S'') (typ_fvar Z)) in H6.
     puts (binds_dom B0); clear B0.
     rewrite dom_kinds_open_vars in H7; auto.
     binds_cases H1.
     assert (x0 \in typ_fv (typ_subst (S & x1 ~ MXs & S'') (typ_fvar Z))).
       rewrite <- H6. simpl*.
     assert (x0 \in env_fv E \u fv_in kind_fv K).
       assert (Z \in ftve). apply (proj42 H0). apply (binds_dom B).
         refine (ftve_subst _ _ _ H8 MGE _ (proj43 H'') (proj44 H'') _ _ _ H1);
           auto.
         unfold fvs in HL, HSL; clear -HL HSL Hsub Hsub'.
         intros; rewrite* Hsub'.
       elim (fresh_disjoint _ _ Fr H7). auto.
     destruct* (split_env_ok _ R4). destruct* Oke.
     puts ((proj42 H8) _ (binds_dom B0)).
     destruct (vars_subst_inv _ _ H12) as [y [Hy By]].
     destruct (binds_kdom_inv (proj1 HK0) Hy).
     puts (WS' _ _ H13).
     inversion H14. fold (typ_subst S' (typ_fvar y)) in H16.
     rewrite <- H16 in By.
     simpl in By. rewrite (S.singleton_1 By) in H16.
     rewrite H16 in H6.
     rewrite (proj43 H'') in H6.
     unfold fvs in HL, HSL; puts (kdom_dom K0).
     rewrite Hsub' in H6 by simpl*. rewrite Hsub in H6 by simpl*.
     subst. puts (WS _ _ H13).
     rewrite <- H6 in H15.
     inversions H15.
     clear -H7 H23 Typ1 Fr.
     elim (ok_disjoint _ _ (proj1 (proj41 (typing_regular Typ1)))
             (binds_dom H23)).
     auto.
    rewrite Hsub' by auto. rewrite Hsub by auto. simpl gc_raise in H5.
    destruct (var_fresh (L2 \u trm_fv t2 \u {{x}})) as [x0 Fr0].
    forward~ (H5 x0) as Typ2.
    apply* (@typing_abs_rename x0).
    destruct (x == x0). elim Fr0; subst*.
    rewrite* <- (proj1 MGE).
   simpl in Hh.
   rewrite trm_depth_open.
   clear -Hh.
   puts (Max.le_max_r (trm_depth t1) (trm_depth t2)). omega.
  instantiate (1 := Fvs04).
  intros [K'' [S1' [L'' [[[HK2 [HS1' D'']] HL''] [HI' [S''' H''']]]]]].
  rewrite (ProofIrrelevance.proof_irrelevance _ HKG (proj41 Ok04)).
  rewrite HI'; clear HI'.
  esplit; esplit; esplit; esplit; split*.
  exists (x1~MXs & S'' & S''').
  repeat rewrite <- concat_assoc.
  intuition trivial.
    repeat rewrite dom_concat; simpl.
    sets_solve. rewrite <- (S.singleton_1 H10) in *. apply* S.diff_3.
    apply* S.diff_3.
  auto.
Qed.

Lemma principal_app : forall h L S0 K0 E0 HS0 HK0 D0 S K E t1 t2 T HL,
  (forall L S0 K0 E0 HS0 HK0 D0 S K E t T HL,
    @principality S0 K0 E0 HS0 HK0 D0 S K E t T L HL h) ->
  @principality S0 K0 E0 HS0 HK0 D0 S K E (trm_app t1 t2) T L HL(Datatypes.S h).
Proof.
  introv IH; intros HTS0 HE0 MGE HTS HSL Hext WS Typ Hh.
  inversions Typ; try discriminate.
  unfold typinf0; simpl lt_wf.
  lazy [typinf]; fold typinf.
  rewrite normalize_typinf.
  destruct (var_fresh L) as [x1 Fr1]; simpl proj1_sig.
  simpl in H3, H5.
  assert (Hsub: forall t, typ_fv t << L ->
                  typ_subst (S & x1 ~ S1) t = typ_subst S t).
    intros.
    apply typ_subst_concat_fresh.
    simpl. intro y; destruct* (y == x1).
  assert (Hcb: x1 ~ S1 = combine (x1::nil) (S1 :: nil)) by simpl*.
  assert (Hext0: extends (S & x1 ~ S1) S0).
    rewrite Hcb.
    apply* (@extends_concat S0 S L 1).
    unfold fvs in HL; auto.
  forward~ (IH (L \u {{x1}}) S0 K0 E0 HS0 HK0 D0 (S & x1 ~ S1) K E t1
                 (typ_arrow (typ_fvar x1) T)).
       split.
         rewrite <- (proj1 MGE). repeat rewrite dom_map. auto.
       intros.
       destruct (proj2 MGE _ _ H) as [M2 [BM2 HM2]].
       exists M2. split*.
       unfold fvs in HL.
       rewrite* (env_subst_ext_fv (S & x1 ~ S1) S).
     rewrite Hcb; apply* (@well_subst_concat E0). 
    simpl. destruct* (x1 == x1). env_fix. rewrite* Hsub.
   clear -Hh. simpl in *.
   puts (Max.le_max_l (trm_depth t1) (trm_depth t2)). omega.
  instantiate (1:=subset_app1 HL).
  intros [K' [S' [L' [[[HK1 [HS' D']] HL'] [HI [S'' H'']]]]]].
  rewrite HI.
  destruct* (typinf_sound _ _ _ _ _ (lt_n_Sn _) HI)
    as [_ [HTS' [HK' [WS' [_ Typ']]]]]; clear HI.
    constructor; auto. apply* (typ_subst_type' S).
  rewrite normalize_typinf.
  intuition.
  assert (Hsub': forall S t, typ_fv t << L \u {{x1}} ->
                  typ_subst (S & S'') t = typ_subst S t).
    intros; apply* typ_subst_concat_fresh.
  forward~ (IH L' S' K' E0 HS' HK' D' (S & x1 ~ S1 & S'') K E t2 (typ_fvar x1)).
      split. rewrite <- (proj1 MGE). repeat rewrite dom_map. auto.
      intros.
      destruct (proj2 MGE _ _ H2) as [M2 [BM2 HM2]].
      exists M2. split*.
      rewrite* (env_subst_ext_fv (S & x1 ~ S1 & S'') S).
      intros; unfold fvs in HL; rewrite* Hsub'.
     disjoint_solve. apply* HL'.
    rewrite* Hsub'. simpl. destruct* (x1 == x1). simpl*.
   clear -Hh; simpl in *.
   puts (Max.le_max_r (trm_depth t1) (trm_depth t2)). omega.
  instantiate (1 := subset_app2 HL').
  intros [K'' [S1' [L'' [[[HK2 [HS1' D'']] HL''] [HI' [S''' H''']]]]]].
  rewrite (ProofIrrelevance.proof_irrelevance _ HK1 (proj1 HK')).
  rewrite HI'; clear HI'.
  esplit; esplit; esplit; esplit; split*.
  exists (x1 ~ S1 & S'' & S''').
  repeat rewrite <- concat_assoc.
  intuition trivial.
    repeat rewrite dom_concat; simpl*.
    clear -Fr1 HL' HL'' H H2.
    sets_solve; apply* S.diff_3. apply* HL''. apply S.union_3. apply* HL'.
  auto.
Qed.

Lemma principal_cst : forall h L S0 K0 E0 HS0 HK0 D0 S K E c T HL,
  @principality S0 K0 E0 HS0 HK0 D0 S K E (trm_cst c) T L HL (Datatypes.S h).
Proof.
  intros; intros HTS0 HE0 MGE HTS HSL Hext WS Typ Hh.
  inversions Typ; try discriminate.
  unfold typinf0; simpl lt_wf.
  lazy [typinf]; fold typinf.
  set (M := Delta.type c) in *.
  destruct (var_freshes L (sch_arity M)) as [Xs Fr]; simpl proj1_sig.
  assert (Hsub: forall t, typ_fv t << L ->
                  typ_subst (S & combine Xs Us) t = typ_subst S t).
    intros.
    apply* typ_subst_combine_fresh.
    apply* fresh_sub. rewrite* <- (proj1 (proj1 H5)).
  set (Ok:=ok_kinds_open_vars (sch_kinds M) Xs 
           (proj41 HK0) (fresh_sub (sch_arity M) Xs Fr (dom_K_L T HL))).
  set (Fvs := disjoint_fvar T M Xs D0 HL Fr).
  assert (Hext': extends (S & combine Xs Us) S0).
    clear -Fr Hext Hsub HL. unfold fvs in HL.
    apply* extends_concat. auto.
  assert (HU: unifies (S & combine Xs Us) ((sch_open_vars M Xs, T) :: nil)).
    unfold unifies; simpl; intros.
    destruct* H. inversions H; clear H.
    destruct H5.
    apply* unifies_open.
      sets_solve. unfold M in H3. rewrite Delta.closed in H3. auto. auto.
    rewrite* sch_subst_fresh.
    unfold M. rewrite Delta.closed. intro; auto.
  destruct H5 as [TUs Wk].
  assert (WS': well_subst (K0 & kinds_open_vars (sch_kinds M) Xs) K 
                          (S & combine Xs Us)).
    intro; intros.
    binds_cases H.
      refine (well_subst_concat (E:=E0) _ _ (well_subst_extends Hext WS)
                    Hsub Hext' _ _); auto.
    simpl.
    case_eq (get Z (combine Xs Us)); intros.
      rewrite (binds_prepend S H).
      unfold kinds_open_vars, kinds_open in B0.
      rewrite <- map_combine in B0.
      destruct (binds_map_inv _ _ B0) as [k1 [Hk1 Bk]].
      subst k.
      assert (kind_fv k1 = {}).
        puts (fv_in_spec kind_fv _ _ _ (binds_in Bk)). simpl in H2.
        puts (fv_in_sch Xs M).
        apply eq_ext; split; intros; auto.
        sets_solve.
        unfold M in Hin0; rewrite Delta.closed in Hin0; auto.
      rewrite~ <- kind_subst_intro0.
        puts (binds_map (fun k => kind_open k Us) Bk).
        simpl in H3; rewrite map_combine in H3.
        unfold kinds_open in Wk.
        puts (list_forall2_get _ Wk H3 H).
        rewrite* kind_subst_fresh.
        rewrite H2; intro; auto.
        rewrite H2; rewrite* <- (fresh_length _ _ _ Fr).
      rewrite* <- (fresh_length _ _ _ Fr).
    unfold kinds_open_vars, kinds_open in B0.
    elim (get_none_notin _ H). auto.
  destruct (unify_dep (sch_open_vars M Xs) T HS0 Ok Fvs)
    as [[[K' S'] [HU' [[HK' [HS' D']] Hf']]] | HU'];
  destruct* (unify_complete0 (K:=K) HU' Hext' HU WS')
    as [K1 [S1 [HU1 [Hext1 WS1]]]];
  inversions HU1; clear HU1.
  esplit; esplit; esplit; esplit; split*.
  destruct* (unify_kinds_ok HU').
  exists (combine Xs Us).
  intuition trivial.
    clearbody Ok Fvs.
    rewrite* dom_combine.
  apply* list_forall_env_prop. apply (proj2 TUs).
Qed.

Lemma typinf_principal : forall h L S0 K0 E0 HS0 HK0 D0 S K E t T HL,
  @principality S0 K0 E0 HS0 HK0 D0 S K E t T L HL h.
Proof.
  induction h; intros; intros HTS0 HE0 MGE HTS HSL Hext WS Typ Hh;
    try (elimtype False; omega).
  inversions Typ.
  apply* principal_var.
  apply* principal_abs.
  apply* principal_let.
  apply* principal_app.
  apply* principal_cst.
  discriminate.
Qed.

Corollary typinf_principal' : forall K E t T,
  env_fv E = {} ->
  K; E |(false,GcAny)|= t ~: T ->
  exists K', exists T', typinf' E t = Some (K', T') /\
    exists S, well_subst K' K S /\ T = typ_subst S T'.
Proof.
  introv HE Typ.
  assert (HK0: kenv_ok empty). split*. intro; intros. elim H.
  unfold typinf'.
  forward~
    (@typinf_principal (S (trm_depth t)) (env_fv E \u {{var_default}})
      id empty E is_subst_id HK0 (@disjoint_empty _)
      (var_default ~ T) K E t (typ_fvar var_default)
      (@subset_typinf' E var_default));
    try solve [try split*; intro; auto; intros; elim H].
       simpl. rewrite map_sch_subst_fresh. apply moregen_env_refl.
       rewrite HE; intro; auto.
     intro; intros. replace (@empty typ) with id by reflexivity.
     rewrite* typ_subst_id.
    intro; intros. elim (binds_empty H).
   simpl. destruct* (var_default == var_default).
  rewrite normalize_typinf.
  rewrite (ProofIrrelevance.proof_irrelevance _ (proj41 HK0) (ok_empty kind)).
  intros [K' [S' [L' [[[HK1 [HS' D']] HL'] [HI [S'' H'']]]]]].
  rewrite HI.
  esplit; esplit; split*.
  intuition.
  exists (var_default ~ T & S'').
  split.
    apply* well_subst_extends.
  rewrite H0.
  rewrite typ_subst_concat_fresh.
    simpl. destruct* (var_default == var_default).
  simpl.
  intro.
  destruct* (x == var_default).
Qed.

End Mk2.
End MkInfer.
