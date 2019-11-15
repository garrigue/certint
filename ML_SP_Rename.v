(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, August 2008                                            *
***************************************************************************)

Set Implicit Arguments.

Require Import List Metatheory.
Require Import ML_SP_Definitions ML_SP_Soundness.

Module MkRename(Cstr:CstrIntf)(Const:CstIntf).

Module Sound := MkSound(Cstr)(Const).
Import Sound.
Import Infra.
Import Defs.
Import Metatheory_Env.Env.

Module Mk2(Delta:DeltaIntf).

Module Sound2 := Sound.Mk2(Delta).
Import Sound2.
Import JudgInfra.
Import Judge.

(* ********************************************************************** *)
(** Renaming lemmas *)

Lemma trm_fv_open : forall t' t n,
  trm_fv (trm_open_rec n t' t) << trm_fv t \u trm_fv t'.
Proof.
  induction t; intros; intros x Hx; simpl in *; auto*.
  destruct (n0 === n); simpl in *; auto.
  apply* (IHt (S n)).
  puts (IHt1 n); use (IHt2 (S n)).
  puts (IHt1 n); use (IHt2 n).
Qed.

Lemma typing_rename : forall gc K E x y M E' t T,
  K ; E & x ~ M & E' |gc|= t ~: T ->
  y \notin (dom E \u dom E' \u {{x}} \u trm_fv t) ->
  K ; E & y ~ M & E' |gc|= trm_subst x (trm_fvar y) t ~: T.
Proof.
  introv Typ.
  gen_eq (E & x ~ M & E') as E0. gen E'.
  induction Typ; intros; subst; simpl trm_subst.
  (* Var *)
  destruct (x0 == x).
    subst.
    puts (binds_mid _ _ _ _ (proj1 H0)).
    puts (binds_func H1 H3).
    subst; clear H3.
    apply* typing_var.
  apply* typing_var.
  binds_cases H1; auto.
  (* Abs *)
  clear H0.
  apply* (@typing_abs gc (L \u {{y}} \u {{x}})).
  intros.
  forward~ (H1 x0) as Typ; clear H1.
  rewrite concat_assoc in Typ.
  forward~ (Typ _ (refl_equal _)) as Typ'; clear Typ.
    simpl in *; disjoint_solve.
    puts (trm_fv_open _ _ _ H1).
    simpl in H2; auto.
  repeat rewrite <- concat_assoc in Typ'.
  rewrite trm_subst_open in Typ' by auto.
  simpl trm_subst in Typ'.
  destruct* (x0 == x).
  subst. elim H0; auto.
  (* Let *)
  clear H H1.
  simpl in H4.
  apply~ (@typing_let gc M0 L1 (L2 \u {{y}} \u {{x}})).
  clear H0; intros.
  forward~ (H2 x0) as Typ0; clear H2.
  rewrite concat_assoc in Typ0.
  forward (Typ0 _ (refl_equal _)) as Typ; clear Typ0.
    simpl in *. disjoint_solve.
    puts (trm_fv_open _ _ _ H0).
    simpl in H1; auto.
  rewrite <- concat_assoc in Typ.
  rewrite trm_subst_open in Typ by auto.
  simpl trm_subst in Typ.
  destruct* (x0 == x).
  subst. elim H; auto.
  (* App *)
  simpl in H0.
  apply* (@typing_app gc K (E & y ~ M & E') S).
  (* Cst *)
  apply* typing_cst.
  (* GC *)
  apply* typing_gc.
Qed.

Lemma typing_abs_rename : forall x1 gc K E x2 M t T,
  x1 \notin trm_fv t ->
  x2 \notin dom E \u {{x1}} \u trm_fv t ->
  K; E & x1 ~ M |gc|= t ^ x1 ~: T -> K; E & x2 ~ M |gc|= t ^ x2 ~: T.
Proof.
  intros. replace (E & x2 ~ M) with (E & x2 ~ M & empty) by simpl*.
  replace (t ^ x2) with ([x1~>trm_fvar x2]t^x1).
    apply typing_rename. simpl*.
    disjoint_solve.
    puts (trm_fv_open _ _ _ H2).
    simpl in H3; auto.
  rewrite trm_subst_open by auto.
  rewrite trm_subst_fresh  by auto.
  simpl. destruct* (x1 == x1).
Qed.

Lemma binds_rename : forall (Ks:list kind) Xs Ys L Z k,
  length Ks = length Xs ->
  fresh L (length Xs) Ys ->
  binds Z k (combine Xs Ks) ->
  exists Z',
    typ_subst (combine Xs (typ_fvars Ys)) (typ_fvar Z) = typ_fvar Z'
    /\ binds Z' k (combine Ys Ks).
Proof.
  unfold binds.
  induction Ks; destruct Xs; destruct Ys; simpl; intros; try discriminate.
    elim H0.
  destruct (Z==v).
    inversion H1. exists v0. destruct* (v0 == v0).
  inversion H; clear H. destruct H0.
  destruct* (IHKs Xs Ys (L \u {{v0}}) Z k) as [Z' [HT HG]].
  exists Z'.
  simpl in HT.
  split2*.
  destruct* (Z' == v0).
  subst.
  puts (binds_dom HG).
  rewrite dom_combine in H2; auto.
  elim (fresh_disjoint _ _ H0 H2); auto.
Qed.

Lemma in_env_rename : forall (Ks:list kind) Xs Ys L Z k,
  length Ks = length Xs ->
  fresh L (length Ys) Xs ->
  In (Z, k) (combine Xs Ks) ->
  exists Z',
    typ_subst (combine Xs (typ_fvars Ys)) (typ_fvar Z) = typ_fvar Z'
    /\ In (Z', k) (combine Ys Ks).
Proof.
  induction Ks; destruct Xs; destruct Ys; simpl; intros; try contradiction.
  destruct H1.
    inversions H1. exists v0. destruct* (Z == Z).
  inversion H; clear H. destruct H0.
  destruct* (IHKs Xs Ys (L \u {{v}}) Z k) as [Z' [HT HG]].
  exists Z'.
  simpl in HT.
  split2*.
  destruct* (Z == v).
  subst.
  elim (in_fresh _ _ H0 (in_combine_l _ _ _ _ H1)). auto.
Qed.

Lemma kinds_subst_fresh : forall S Ks,
  disjoint (dom S) (kind_fv_list Ks) ->
  List.map (kind_subst S) Ks = Ks.
Proof.
  induction Ks; intros. auto.
  simpl in *.
  rewrite* kind_subst_fresh.
  rewrite* IHKs.
Qed.

Lemma well_subst_rename : forall K Ks Xs Ys,
  let S := combine Xs (typ_fvars Ys) in
  fresh (fv_in kind_fv K) (length Ks) Xs ->
  fresh (mkset Xs) (length Xs) Ys ->
  well_subst
    (K & kinds_open_vars Ks Xs & combine Ys (kinds_open Ks (typ_fvars Xs)))
    (K & map (kind_subst S) (combine Ys (kinds_open Ks (typ_fvars Xs)))) S.
Proof.
  intros; intro; intros.
  destruct k as [[kc kv kr kh]|]; [|auto].
  assert (DS: dom S = mkset Xs) by apply* dom_combine.
  binds_cases H1.
      rewrite typ_subst_fresh.
        rewrite* kind_subst_fresh.
        rewrite DS.
        use (fv_in_spec kind_fv _ _ _ (binds_in B0)).
      rewrite DS; simpl*.
    unfold kinds_open_vars in B1.
    assert (length (kinds_open Ks (typ_fvars Xs)) = length Xs)
      by (unfold kinds_open; auto).
    destruct (binds_rename _ _ _ _ H1 H0 B1) as [Z' [HT HG]].
    unfold S at 3. rewrite HT.
    simpl; apply* wk_kind.
    use (binds_map (kind_subst S) HG).
  rewrite typ_subst_fresh.
    unfold kind_subst. simpl.
    use (binds_map (kind_map (typ_subst S)) B0).
  rewrite* DS.
Qed.

Lemma typing_rename_typ : forall E M K Xs Ys gc t,
  fresh (env_fv E \u sch_fv M \u dom K \u fv_in kind_fv K)
    (sch_arity M) Xs ->
  fresh (dom K \u mkset Xs) (length Xs) Ys ->
  K & kinds_open_vars (sch_kinds M) Xs; E |gc|= t ~: M ^ Xs ->
  K & kinds_open_vars (sch_kinds M) Ys; E |gc|= t ~: M ^ Ys.
Proof.
  intros.
  set (S := combine Xs (typ_fvars Ys)).
  assert (DS: dom S = mkset Xs) by (unfold S; rewrite~ dom_combine).
  assert (TS: env_prop type S).
    unfold S; apply list_forall_env_prop. refine (proj2 (types_typ_fvars _)).
  unfold sch_open_vars, typ_open_vars.
  unfold sch_fv in H.
  rewrite~ (typ_subst_intro Xs (Us:=typ_fvars Ys)).
    fold S.
    replace E with (E & map (sch_subst S) empty) by auto.
    replace (kinds_open_vars (sch_kinds M) Ys) with
      (map(kind_subst S)(combine Ys (kinds_open (sch_kinds M) (typ_fvars Xs)))).
      apply* typing_typ_subst.
          rewrite* DS.
        apply* well_subst_rename.
      apply* typing_weaken_kinds'.
      kenv_ok_solve.
        apply* ok_combine_fresh.
      apply list_forall_env_prop.
      apply* (env_prop_list_forall _ _ H4).
    rewrite map_combine.
    rewrite* kinds_subst_open.
    rewrite kinds_subst_fresh.
      subst S.
      rewrite* (fresh_subst {} Xs (typ_fvars Ys)).
      unfold typ_fvars; rewrite map_length.
      rewrite* <- (fresh_length _ _ _ H0).
    rewrite* DS.
  rewrite* (fresh_length _ _ _ H0).
Qed.

(** Type generalization and reopening *)

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

Lemma typ_generalize_reopen : forall Xs T,
  type T -> typ_open (typ_generalize Xs T) (typ_fvars Xs) = T.
Proof.
  induction 1; simpl.
    case_eq (index eq_var_dec 0 X Xs); simpl; intros.
      unfold typ_fvars.
      destruct (index_ok _ var_default _ _ H).
      rewrite <- (map_length typ_fvar) in H0.
      rewrite <- (f_equal typ_fvar H1).
      rewrite <- (map_nth typ_fvar).
      apply* nth_indep.
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
  inversions H.
  rewrite* typ_generalize_reopen. rewrite* IHkr.
Qed.

Lemma kind_list_generalize_reopen : forall Ks Xs,
  list_forall (All_kind_types type) Ks ->
  kinds_open (List.map (kind_map (typ_generalize Xs)) Ks) (typ_fvars Xs) = Ks.
Proof.
  intros.
  induction H. simpl*.
  simpl. rewrite* kind_generalize_reopen.
  congruence.
Qed.

Lemma kinds_generalize_reopen : forall Xs Ks,
  list_forall (All_kind_types type) Ks ->
  kinds_open_vars (List.map (kind_map (typ_generalize Xs)) Ks) Xs =
  combine Xs Ks.
Proof.
  unfold kinds_open_vars, kinds_open; intros.
  apply (f_equal (combine (B:=kind) Xs)).
  apply (kind_list_generalize_reopen Xs H).
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

Lemma typ_generalize_disjoint : forall Bs T,
  disjoint (typ_fv (typ_generalize Bs T)) (mkset Bs).
Proof.
  induction T; simpl*.
  case_eq (index eq_var_dec 0 v Bs); simpl; intros; auto.
  use (index_none_notin _ _ _ _ H).
Qed.

Lemma kinds_generalize_disjoint : forall Bs Ks,
  disjoint (kind_fv_list (List.map (kind_map (typ_generalize Bs)) Ks))
    (mkset Bs).
Proof.
  intros. unfold kind_fv_list.
  induction Ks; simpl*.
  disjoint_solve.
  revert H; unfold kind_fv.
  clear Hin Ks; destruct a as [[kc kv kr kh]|]; simpl*.
  clear kh; induction kr; simpl*.
  use (typ_generalize_disjoint Bs (snd a)).
Qed.

Lemma sch_generalize_disjoint : forall Bs T Ks,
  disjoint (sch_fv (sch_generalize Bs T Ks)) (mkset Bs).
Proof.
  intros.
  unfold sch_generalize, sch_fv; simpl.
  disjoint_solve. apply (typ_generalize_disjoint _ _ H Hy').
  apply (kinds_generalize_disjoint _ _ H Hy').
Qed.

(** Free variables *)

Lemma typ_fv_open : forall Us T,
  typ_fv (typ_open T Us) << typ_fv T \u typ_fv_list Us.
Proof.
  induction T; simpl*.
  intros x Hx.
  gen n; induction Us; destruct n; simpl; intros; auto.
  use (IHUs n Hx).
Qed.

Lemma kind_fv_open : forall Us k,
  kind_fv (kind_open k Us) << kind_fv k \u typ_fv_list Us.
Proof.
  destruct k as [[kc kv kr kh]|]; unfold kind_fv; simpl*.
  rewrite list_snd_map_snd.
  clear; induction kr; simpl*.
  disjoint_solve.
  use (typ_fv_open _ _ H).
Qed.

Lemma fv_in_kinds_open_vars : forall Ks Xs,
  fv_in kind_fv (kinds_open_vars Ks Xs) << kind_fv_list Ks \u mkset Xs.
Proof.
  unfold kinds_open_vars.
  intros.
  rewrite <- typ_fv_typ_fvars.
  set (Us := typ_fvars Xs); clearbody Us.
  gen Ks; induction Xs; destruct Ks; simpl*.
  sets_solve.
    use (kind_fv_open _ _ H).
  use (IHXs Ks _ H).
Qed.

(** A more general form of kinds weakening *)

Lemma typing_kenv_incl : forall gc K E t T,
  K; E |gc|= t ~: T ->
  forall K',
    incl K K' -> kenv_ok K' -> K'; E |gc|= t ~:T.
Proof.
  induction 1; intros; auto*.
  (* Var *)
  apply* typing_var.
  destruct H2; split2*.
  apply* list_forall2_imp.
  intros.
  inversions* H6.
  (* Let *)
  apply* (@typing_let gc M (L1 \u dom K')).
  intros.
  assert (kenv_ok (K' & kinds_open_vars (sch_kinds M) Xs)) by forward~ (H Xs).
  apply* H0.
  intro; intros.
  destruct* (in_app_or _ _ _ H7).
  (* Cst *)
  apply* typing_cst.
  destruct H1; split; intuition.
  apply* list_forall2_imp.
  intros.
  inversions* H5.
  (* Gc *)
  apply* (@typing_gc gc Ks (L \u dom K')).
  intros.
  assert (kenv_ok (K' & kinds_open_vars Ks Xs)) by forward~ (H0 Xs).
  apply* (H1 Xs).
  intro; intros.
  destruct* (in_app_or _ _ _ H6).
Qed.

(** Miscellanous lemmata *)

Lemma kind_fv_list_app : forall K2 K1,
  kind_fv_list (K1 ++ K2) = kind_fv_list K1 \u kind_fv_list K2.
Proof.
  unfold kind_fv_list; induction K1; simpl. rewrite* union_empty_l.
  rewrite* IHK1. rewrite* union_assoc.
Qed.

(* ********************************************************************** *)
(** Removing Gc through inversion *)

(* An alternative way to get rid of Gc, eliminating it completely.
   This part of the development is not needed for soundness, as we can
   use the canonization lemma in ML_SP_Soundness.v.
   However, many lemmas proved here are actually required for
   the proof of soundness and principality of type inference.
   Originally the proof was about 1350 lines long, which contrasts
   with the mere 100 lines of canonicalization, but some lemmas, like
   renaming, have been moved around.
   This proof demonstrates how difficult it is to remove _all_ uses
   of typing_gc in this approach, and how muddy things become when
   you start needing renaming. *)

(* Idea of the proof: in order to prove that if K; E |= t ~: T using
   typing_gc then we can find K' such that K,K'; E |= t ~: T without it,
   we prove by induction that K,K'; F |= t ~: T for any F "weaker" than E,
   i.e. where any binding (x : Sch U Ks) of E may be replaced by a binding
   (x : Sch U (Ks ++ Ks')). This way, in the Let rule, we can transfer
   the extra kinds of the kinding environment to the type environment of
   the right derivation.
   On paper, the proof is straightforward. Here, we need renaming for both
   terms and types, and to prove a lot of technical properties on the way. *)

Definition env_weaker E F :=
  forall x T Ks,
    binds x (Sch T Ks) E ->
    exists Ks', binds x (Sch T (Ks++Ks')) F.

Lemma typ_open_extra : forall Us Vs T,
  type (typ_open T Us) ->
  typ_open T Us = typ_open T (Us ++ Vs).
Proof.
  induction T; simpl; intros; auto.
    gen Us; induction n; destruct Us; simpl in *; intros; auto ; inversion* H.
  inversions H.
  rewrite* IHT1. rewrite* IHT2.
Qed.

Lemma kind_open_extra : forall Us Vs k,
  All_kind_types type (kind_open k Us) ->
  kind_open k Us = kind_open k (Us ++ Vs).
Proof.
  unfold All_kind_types. 
  destruct k as [[kc kv kr kh]|]; simpl*; intros.
  apply* kind_pi; simpl.
  clear -H; induction kr; simpl in *. auto.
  inversions H; clear H.
  rewrite* (typ_open_extra Us Vs).
  rewrite* IHkr.
Qed.

Lemma env_weaker_ok : forall Us U Ks Ks' k Xs',
  types (length Ks) Us ->
  length Ks' = length Xs' ->
  scheme (Sch U (Ks ++ Ks')) ->
  In k (kinds_open Ks' (Us ++ typ_fvars Xs')) ->
  All_kind_types type k.
Proof.
  intros.
  destruct (var_freshes {} (length Ks)) as [Xs Fr].
  destruct (H1 (Xs ++ Xs')) as [_ HA]; clear H1.
    simpl. repeat rewrite app_length.
    rewrite H0. rewrite* (fresh_length _ _ _ Fr).
  clear H0.
  use (list_forall_app_inv _ _ HA); clear HA.
  induction H0; simpl in *. elim H2.
  destruct H2; subst.
    unfold kind_open.
    clear -H Fr H1.
    apply All_kind_types_map.
    apply* All_kind_types_imp.
    simpl; intros.
    unfold typ_open_vars in H0.
    eapply typ_open_other_type. apply H0.
    unfold typ_fvars. rewrite map_length.
    split.
      repeat rewrite app_length; rewrite map_length.
      rewrite* <- (fresh_length _ _ _ Fr).
    destruct H.
    clear -H2. induction H2; simpl*.
    induction Xs'; simpl*.
  apply* IHlist_forall.
Qed.

Lemma well_kinded_combine : forall K Ks' Xs Us,
  fresh (dom K) (length Ks') Xs ->
  list_forall2 (well_kinded
    (K & combine Xs (List.map (fun k => kind_open k (Us ++ typ_fvars Xs)) Ks')))
   (List.map (fun k => kind_open k (Us ++ typ_fvars Xs)) Ks') (typ_fvars Xs).
Proof.
  intros.
  assert (fresh (dom (empty(A:=kind))) (length Ks') Xs) by auto.
  use (list_forall2_binds _ _ _ H0).
  simpl in H1.
  unfold typ_fvars; apply* list_forall2_map.
  simpl; intros.
  destruct x; try apply wk_any.
  simpl.
  apply* wk_kind.
  apply binds_prepend.
  rewrite <- map_combine.
  apply (binds_map (fun k => kind_open k (Us ++ List.map typ_fvar Xs)) H2).
Qed.

Lemma well_kinded_combine2 : forall K U Ks Us Ks' Xs,
  proper_instance K Ks Us ->
  typ_body U Ks ->
  typ_body U (Ks ++ Ks') ->
  fresh (dom K) (length Ks') Xs ->
  list_forall2
    (well_kinded (K & combine Xs (kinds_open Ks' (Us ++ typ_fvars Xs))))
    (kinds_open (Ks ++ Ks') (Us ++ typ_fvars Xs))
    (Us ++ typ_fvars Xs).
Proof.
  introv PI HS0 HS Fr.
  destruct PI as [HT HW].
  simpl in *.
  unfold kinds_open. rewrite map_app.
  apply list_forall2_app.
    unfold kinds_open in HW.
    (* destruct HS0 as [L' HF]. *)
    destruct (var_freshes {} (length Ks)) as [Xs' Fr'].
    use (proj2 (HS0 Xs' (fresh_length _ _ _ Fr'))).
    clear -HT Fr Fr' HW H.
    remember Us as Vs.
    destruct HT.
    rewrite H0 in Fr'.
    pattern Vs at 1 in HW.
    pattern Vs at -3.
    rewrite HeqVs in *.
    rewrite <- HeqVs in H0.
    clear HeqVs.
    gen Vs; induction Ks; destruct Vs; intros; simpl in *; try discriminate.
      auto.
    inversions HW; inversion H0; inversions H; clear HW H H0.
    constructor; auto.
    clear -Fr Fr' H1 H5 H8.
    destruct a; simpl in *; try apply wk_any.
    destruct t; inversions H5; clear H5.
    eapply wk_kind.
      apply* binds_concat_fresh.
    destruct c as [kc kv kr kh]; simpl in *.
    destruct H4; split2*. clear H.
    intros.
    apply H0; clear H0.
    unfold All_kind_types in H8; simpl in *.
    clear -Fr' H8 H H1.
    induction kr; simpl in *. auto.
    inversion_clear H8; destruct* H.
    clear IHkr; left*; subst.
    rewrite* (typ_open_extra Us (typ_fvars Xs)).
    unfold typ_open_vars in H0.
    apply (typ_open_other_type (typ_fvars Xs')). auto.
    split2*.
  clear -Fr.
  apply* well_kinded_combine.
Qed.

Lemma incl_swap : forall (A:Set) (E E1 E2:Env.env A),
  ok (E & E1 & E2) -> incl (E & E2 & E1) (E & E1 & E2).
Proof.
  intros; intro; intros.
  destruct* (in_app_or _ _ _ H0).
  destruct* (in_app_or _ _ _ H1).
Qed.

Lemma env_weaker_push : forall E F x U Ks Ks',
  env_weaker E F -> x # F ->
  env_weaker (E & x ~ Sch U Ks) (F & x ~ Sch U (Ks++Ks')).
Proof.
  intros; intro; intros.
  binds_cases H1.
    destruct (H _ _ _ B) as [Ks1 HB].
    exists* Ks1.
  inversions H2.
  exists* Ks'.
Qed.

Lemma ok_combine_other : forall (A B:Set) Xs (Us:list A) (Vs:list B),
  ok (combine Xs Us) -> length Us = length Vs -> ok (combine Xs Vs).
Proof.
  induction Xs; simpl; intros. fold (empty(A:=B)). auto.
  destruct Vs; destruct Us; try discriminate.
    fold (empty(A:=B)). auto.
  inversion H0.
  inversions H. apply* (@ok_push B (combine Xs Vs) a b).
  clear -H2 H6.
  gen Us Vs; induction Xs; simpl; intros. auto.
  destruct Us; destruct Vs; try discriminate; auto.
  simpl in *.
  assert (a # combine Xs Vs) by apply* (IHXs Us).
  auto.
Qed.

Lemma ok_fresh : forall (A:Set) Xs (Us:list A) L,
  ok (combine Xs Us) ->
  length Xs = length Us ->
  disjoint (mkset Xs) L ->
  fresh L (length Xs) Xs.
Proof.
  induction Xs; destruct Us; simpl; intros; try discriminate. auto.
  split2*.
  inversions H. 
  apply* (IHXs Us).
Qed.

Lemma typing_remove_gc_var : forall K E x M Us F LK,
  kenv_ok K ->
  env_ok E ->
  binds x M E ->
  proper_instance K (sch_kinds M) Us ->
  env_weaker E F ->
  env_ok F ->
  exists K',
    disjoint (dom K') LK /\
    K & K'; F | (false, GcAny) |= trm_fvar x ~: sch_open M Us.
Proof.
  intros.
  destruct M as [U Ks].
  destruct (H3 x _ _ H1) as [Ks' HB]. destruct* H2.
  destruct (var_freshes (LK \u dom K) (length Ks')) as [Xs Fr].
  exists (combine Xs (kinds_open Ks' (Us ++ typ_fvars Xs))).
  assert (dom (combine Xs (kinds_open Ks' (Us ++ typ_fvars Xs))) = mkset Xs)
    by rewrite* dom_combine.
  split.
    rewrite* H6.
  assert (HS: scheme (Sch U (Ks ++ Ks'))) by apply* (proj2 H4 x).
  assert (HS0: scheme (Sch U Ks)) by apply* env_prop_binds.
  replace (sch_open (Sch U Ks) Us)
    with (sch_open (Sch U (Ks++Ks')) (Us ++ typ_fvars Xs)).
    apply* typing_var.
      destruct H.
      split.
        apply* disjoint_ok. apply* ok_combine_fresh.
      apply* env_prop_concat.
      intro; intros.
      eapply env_weaker_ok.
            apply H2.
          apply (fresh_length _ _ _ Fr).
        apply (proj2 H4 _ _ (binds_in HB)).
      apply (in_combine_r _ _ _ _ H8).
    split.
      destruct H2.
      split2*.
      clear -H7; induction Us; simpl; inversion* H7.
      induction Xs; simpl*.
    simpl; apply* well_kinded_combine2. simpl in *. split2*.
  unfold sch_open. simpl.
  assert (K; E |(false,GcAny)|= trm_fvar x ~: (Sch U Ks) ^^ Us).
    apply* typing_var. split2*.
  assert (type ((Sch U Ks) ^^ Us)) by auto.
  unfold sch_open in H8. simpl in H8.
  rewrite* (typ_open_extra Us (typ_fvars Xs)).
Qed.

Lemma kenv_ok_rename : forall Xs Xs' Ks,
  list_forall (fun o : kind => All_kind_types type o)
    (kinds_open Ks (typ_fvars Xs)) ->
  fresh (kind_fv_list Ks) (length Xs') Xs ->
  list_forall (fun o : kind => All_kind_types type o)
    (kinds_open Ks (typ_fvars Xs')).
Proof.
  induction Ks; simpl; intros. auto.
  inversions H.
  constructor.
    auto.
  clear -H0 H4.
  unfold kind_open in *.
  apply All_kind_types_map.
  puts (All_kind_types_inv _ _ H4).
  apply* All_kind_types_imp.
  clear H H4; simpl; intros.
  apply (typ_open_other_type (Vs:=typ_fvars Xs') _ _ H).
  split. unfold typ_fvars; repeat rewrite map_length.
    rewrite* (fresh_length _ _ _ H0).
  clear. unfold typ_fvars; induction Xs'; simpl; auto.
Qed.

Lemma kenv_ok_swap : forall (K K1 K2 : kenv),
  kenv_ok (K & K1 & K2) -> kenv_ok (K & K2 & K1).
Proof.
  intros.
  destruct H.
  destruct (ok_concat_inv _ _ H).
  destruct (ok_concat_inv _ _ H1).
  split.
    apply* disjoint_ok.
  intro; intros.
  apply (H0 x).
  destruct* (in_app_or _ _ _ H5).
  destruct* (in_app_or _ _ _ H6).
Qed.

Lemma scheme_extra : forall U Ks Xs K,
  let Ks' :=
    List.map (kind_map (typ_generalize (Xs ++ list_fst K))) (list_snd K) in
  length Ks = length Xs ->
  kenv_ok K ->
  scheme (Sch U Ks) ->
  scheme (Sch U (Ks ++ Ks')).
Proof.
  intros until Ks'; intros HXs HK HM; intro; intros.
  simpl in *. rewrite app_length in H.
  rewrite HXs in H. unfold Ks' in H.
  rewrite map_length in H.
  rewrite <- length_fst_snd in H.
  rewrite <- app_length in H.
  destruct (HM Xs). simpl*.
  simpl in *.
  split.
    unfold typ_open_vars.
    apply (typ_open_other_type (typ_fvars (Xs ++ list_fst K))).
      rewrite typ_fvars_app.
      rewrite* <- typ_open_extra.
    unfold typ_fvars; rewrite map_length. rewrite H.
    apply types_typ_fvars.
  apply list_forall_app.
    clear -H1 H.
    induction H1. auto.
    constructor. auto.
    apply* All_kind_types_imp. intros. simpl in *.
    clear -H H2. unfold typ_open_vars in *.
    apply (typ_open_other_type (typ_fvars (Xs ++ list_fst K))).
      rewrite typ_fvars_app.
      rewrite* <- typ_open_extra.
    unfold typ_fvars; rewrite map_length. rewrite H.
    apply types_typ_fvars.
  unfold Ks'.
  destruct HK.
  rewrite <- (combine_fst_snd K) in H3.
  use (env_prop_list_forall _ _ H3). rewrite combine_fst_snd in H4.
  use (H4 H2 (length_fst_snd K)).
  clear -H5 H.
  induction H5; simpl*.
  constructor. auto.
  apply All_kind_types_map.
  apply* All_kind_types_imp. clear -H; intros.
  unfold typ_open_vars.
  apply (typ_open_other_type (typ_fvars (Xs ++ list_fst K))).
    rewrite* typ_generalize_reopen.
  unfold typ_fvars. rewrite map_length; rewrite H.
  apply types_typ_fvars.
Qed.

Lemma typing_remove_gc_let : forall L1 L2 LK E M F K K1 Xs t1 t2 T2,
  (forall x,
    x \notin L2 ->
    forall LK F,
      env_weaker (E & x ~ M) F -> env_ok F ->
      exists K',
        disjoint (dom K') LK /\ K & K'; F | (false, GcAny) |= t2 ^ x ~: T2) ->
  env_weaker E F -> env_ok F -> scheme M ->
  fresh (L1 \u env_fv F \u sch_fv M \u dom K \u fv_in kind_fv K)
    (sch_arity M) Xs ->
  disjoint (dom K1)
    (LK \u mkset Xs \u env_fv F \u sch_fv M \u dom K \u fv_in kind_fv K) ->
  K & kinds_open_vars (sch_kinds M) Xs & K1; F |(false, GcAny)|= t1 ~: M ^ Xs ->
  exists K' : Env.env kind,
    disjoint (dom K') LK /\
    K & K'; F | (false, GcAny) |= trm_let t1 t2 ~: T2.
Proof.
  intros until T2. intros H2 H3 H4 HM HXs HD1 Typ1.
  use (kenv_ok_swap K (kinds_open_vars (sch_kinds M) Xs) K1
          (proj41 (typing_regular Typ1))).
  poses Typ1a (typing_kenv_incl Typ1 (incl_swap _ _ _ (proj1 H)) H).
  clear Typ1 H.
  pose (Ks' :=
    List.map (kind_map (typ_generalize (Xs ++ list_fst K1))) (list_snd K1)).
  destruct M as [U Ks]; simpl in *.
  destruct (var_fresh (L2 \u trm_fv t2 \u dom F)) as [x Hx].
  rewrite concat_assoc in Typ1a.
  assert (HKM: kenv_ok (K1 & kinds_open_vars Ks Xs)) by auto.
  assert (env_weaker (E & x ~ Sch U Ks) (F & x ~ Sch U (Ks++Ks'))).
    apply* env_weaker_push.
  assert (Hx': x \notin L2) by auto.
  assert (HK1: kenv_ok K1) by auto.
  assert (HM': scheme (Sch U (Ks ++ Ks')))
    by (unfold Ks'; apply* scheme_extra).
  destruct* (H2 x Hx' LK (F & x ~ Sch U (Ks ++ Ks'))) as [K2 [HD2 Typ2]];
    clear H2 Hx'.
  exists K2; split2*.
  assert (LenS: length (Ks ++ Ks') = length (Xs ++ list_fst K1)).
    repeat rewrite app_length; unfold list_fst; rewrite map_length.
    unfold Ks', list_snd; repeat rewrite map_length.
    rewrite* (fresh_length _ _ _ HXs).
  apply* (@typing_let (false,GcAny) (Sch U (Ks++Ks'))
             (L1 \u dom K \u dom K2 \u mkset (Xs ++ list_fst K1))
             (L2 \u dom F \u {{x}} \u trm_fv t2)).
    intros.
    apply typing_weaken_kinds.
      simpl.
      apply (@typing_rename_typ F (Sch U (Ks++Ks')) K (Xs ++ list_fst K1)).
          simpl.
          apply* disjoint_fresh.
            unfold kinds_open_vars in HKM.
            rewrite LenS.
            rewrite <- (combine_fst_snd K1) in HKM.
            unfold concat in HKM.
            rewrite <- combine_app in HKM.
            apply~ (ok_fresh _ _ (L:={}) (proj1 HKM)).
              do 2 rewrite app_length.
              unfold kinds_open; rewrite map_length. rewrite* length_fst_snd.
            unfold kinds_open; rewrite map_length.
            rewrite* (fresh_length _ _ _ HXs).
          puts (kinds_generalize_disjoint (Xs ++ list_fst K1) (list_snd K1)).
          fold Ks' in H1.
          rewrite mkset_app.
          unfold sch_fv in *; simpl in *.
          rewrite kind_fv_list_app.
          assert (mkset (list_fst K1) = dom K1).
            rewrite <- (dom_combine (list_fst K1) (list_snd K1)).
              rewrite* combine_fst_snd. 
            unfold list_fst, list_snd; auto.
          rewrite <- H2 in *.
          clear -HD1 HXs H1.
          rewrite mkset_app in H1.
          disjoint_solve.
        rewrite* <- LenS.
      simpl.
      unfold sch_open_vars, typ_open_vars in *.
      simpl typ_open in *.
      unfold typ_fvars in *. rewrite map_app.
      rewrite* <- typ_open_extra.
      unfold kinds_open_vars. unfold kinds_open.
      rewrite map_app. rewrite combine_app.
        fold (kinds_open Ks' (typ_fvars (Xs ++ list_fst K1))).
        unfold Ks'; rewrite* kind_list_generalize_reopen.
          rewrite combine_fst_snd.
          replace
            (List.map (fun k => kind_open k (typ_fvars (Xs ++ list_fst K1))) Ks)
            with (kinds_open Ks (typ_fvars Xs)).
            apply Typ1a.
          unfold kinds_open.
          destruct (HM Xs). simpl*.
          simpl in H2.
          clear -H2; induction H2. simpl*.
          simpl. rewrite IHlist_forall. clear -H.
          rewrite typ_fvars_app.
          rewrite* <- kind_open_extra.
          unfold kind_open.
          apply* All_kind_types_map.
        rewrite <- (combine_fst_snd K1) in HK1.
        apply* env_prop_list_forall.
        apply length_fst_snd.
      rewrite map_length. symmetry. auto*.
    kenv_ok_solve. apply* ok_combine_fresh.
    simpl.
    apply list_forall_env_prop.
    unfold kinds_open.
    destruct* (HM' Xs0). simpl in H16.
    apply* list_forall_map.
    intros.
    unfold kind_open.
    apply* All_kind_types_map.
  intros.
  simpl gc_raise.
  replace (F & x0 ~ Sch U (Ks++Ks')) with (F & x0 ~ Sch U (Ks++Ks') & empty)
    in * by (simpl; auto).
  replace (F & x ~ Sch U (Ks++Ks')) with (F & x ~ Sch U (Ks++Ks') & empty)
    in Typ2 by (simpl; auto).
  rewrite* (@trm_subst_intro x t2 (trm_fvar x0)).
  apply (typing_rename (y:=x0) _ _ _ Typ2). simpl.
  puts (trm_fv_open (trm_fvar x) t2 0). simpl in H1.
  unfold trm_open. auto.
Qed.

Lemma typing_remove_gc : forall gc K E t T,
  K ; E |gc|= t ~: T ->
  forall LK F,
    env_weaker E F -> env_ok F ->
    exists K',
      disjoint (dom K') LK /\ K & K' ; F |(false,GcAny)|= t ~: T.
Proof.
  induction 1; intros.
  (* Var *)
  apply (typing_remove_gc_var LK H H0 H1 H2 H3 H4).
  (* Abs *)
  clear H0 gc.
  destruct (var_fresh (L \u trm_fv t1 \u dom F)) as [x Hx].
  assert (Hx' : x \notin L) by auto.
  assert (HF : env_weaker (E & x ~ Sch U nil) (F & x ~ Sch U nil)).
    intro; intros.
    binds_cases H0.
      destruct (H2 x0 T0 Ks B) as [Ks' HB].
      exists* Ks'.
    exists (nil(A:=kind)). 
    rewrite <- app_nil_end. auto.
  destruct (H1 x Hx' LK _ HF) as [K' [HD Typ]]; clear H1 Hx'.
    split2*. destruct H3; apply* env_prop_concat.
    intro; intros. destruct* H3. inversions H3.
    intro; intros. simpl. split2*. unfold typ_open_vars.
    clear -H; induction H; simpl*.
  exists K'; split2*.
  apply* (@typing_abs (false,GcAny) (L \u dom F \u trm_fv t1 \u {{x}})).
  intros.
  replace (F & x0 ~ Sch U nil) with (F & x0 ~ Sch U nil & empty)
    by (simpl; auto).
  rewrite* (@trm_subst_intro x t1 (trm_fvar x0)).
  apply* typing_rename.
  assert (x0 \notin trm_fv (t1 ^ x)).
    apply* (notin_subset (trm_fv_open (trm_fvar x) t1 0)).
    simpl; auto.
  simpl; auto.
  (* Let *)
  destruct (var_freshes (L1 \u env_fv F \u sch_fv M \u dom K \u
      fv_in kind_fv K) (sch_arity M)) as [Xs HXs].
  assert (HXs': fresh L1 (sch_arity M) Xs) by auto.
  use (H Xs HXs').
  destruct* (H0 Xs HXs' (LK \u mkset Xs \u env_fv F \u sch_fv M
                         \u dom K \u fv_in kind_fv K) _ H3)
    as [K1 [HD1 Typ1]].
  assert (scheme M).
    destruct (var_fresh L2). puts (proj42 (typing_regular (H1 _ n))).
    apply* (proj2 H6 x).
  clear H H0 H1 H5 HXs'.
  apply* typing_remove_gc_let.
  (* App *)
  clear H H0.
  destruct (IHtyping1 LK F H1 H2) as [K1 [HD1 Typ1]].
  destruct (IHtyping2 (LK \u dom K1) F H1 H2) as [K2 [HD2 Typ2]].
  exists (K1 & K2).
  assert (kenv_ok (K & K1 & K2)) by auto.
  split2*.
  rewrite <- concat_assoc.
  eapply typing_app.
    apply* typing_weaken_kinds'.
  simpl. apply* typing_weaken_kinds.
  (* Cst *)
  exists (empty(A:=kind)).
  simpl*.
  (* GC *)
  destruct (var_freshes (L \u LK) (length Ks)) as [Xs Hs].
  assert (fresh L (length Ks) Xs) by auto.
  destruct (H1 Xs H4 LK F H2 H3) as [K' [HD Typ]].
  exists (kinds_open_vars Ks Xs & K').
  rewrite dom_concat.
  rewrite* dom_kinds_open_vars.
  rewrite* <- concat_assoc.
Qed.

(* End of removing GC *)

End Mk2.

End MkRename.
