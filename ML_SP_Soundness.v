(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Charguéraud, March 2007, Coq v8.1                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import Arith List Metatheory 
  ML_SP_Definitions
  ML_SP_Infrastructure.

Module MkSound(Cstr:CstrIntf)(Const:CstIntf).

Module Infra := MkInfra(Cstr)(Const).
Import Infra.
Import Defs.

Module Mk2(Delta:DeltaIntf).
Module JudgInfra := MkJudgInfra(Delta).
Import JudgInfra.
Import Judge.

(* ********************************************************************** *)
(** Typing is preserved by weakening *)

Lemma typing_weaken : forall gc G E F K t T,
   K ; (E & G) |gc|= t ~: T -> 
   ok (E & F & G) ->
   K ; (E & F & G) |gc|= t ~: T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* (@typing_abs gc) as y. apply_ih_bind* H1.
  apply_fresh* (@typing_let gc M L1) as y. apply_ih_bind* H2.
  auto*.
  auto.
  apply_fresh* (@typing_gc gc Ks) as y.
Qed.

Lemma proper_instance_weaken : forall K K' K'' M Us,
  ok (K & K' & K'') ->
  proper_instance (K & K'') M Us ->
  proper_instance (K & K' & K'') M Us.
Proof.
  intros.
  destruct* H0 as [TM [SM FM]]; split3*.
  rewrite <- list_map_id.
  rewrite <- (list_map_id (kinds_open (sch_kinds M) Us)).
  apply (For_all2_map _ (well_kinded (K&K'&K'')) _ _ _ _
                        (well_kinded_weaken K K' K'' H) FM).
Qed.

Lemma typing_weaken_kinds : forall gc K K' K'' E t T,
  K & K''; E |gc|= t ~: T ->
  kenv_ok (K & K' & K'') ->
  K & K' & K''; E |gc|= t ~: T.
Proof.
  introv Typ. gen_eq (K & K'') as H. gen K''.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* proper_instance_weaken.
  apply_fresh* (@typing_abs gc) as y.
  apply_fresh* (@typing_let gc M (L1 \u dom(K&K'&K''))) as y.
    intros. clear H1 H2.
    unfold concat. rewrite <- app_ass. unfold concat in H0.
    apply* H0; clear H0. rewrite* app_ass.
    rewrite app_ass. fold ((K'' ++ K' ++ K) & kinds_open_vars (sch_kinds M) Xs).
    unfold kinds_open_vars.
    split. apply* disjoint_ok.
      apply* ok_combine_fresh.
      rewrite mkset_dom.
      apply disjoint_comm.
      apply* fresh_disjoint.
      destruct* (fresh_union_r _ _ _ _ H3).
      unfold kinds_open. rewrite map_length.
      rewrite* <- (fresh_length _ _ _ H3).
    intro; intros.
    destruct Ok as [_ Ok].
    destruct (binds_concat_inv H0) as [[Fr B]|B]; clear H0.
      apply* (Ok x).
    use (typing_regular (H Xs (proj1 (fresh_union_r _ _ _ _ H3)))).
    apply* (proj2 (proj41 H0) x).
  auto*.
  apply* typing_cst. apply* proper_instance_weaken.
  apply_fresh* (@typing_gc gc Ks) as y.
  intros.
  rewrite concat_assoc.
  apply* (H1 Xs); clear H1.
    rewrite* concat_assoc.
  rewrite* <- concat_assoc.
  forward~ (H0 Xs) as Typ; clear H0.
  split.
    apply* disjoint_ok. destruct* (typing_regular Typ). destruct* H0.
      destruct* (ok_concat_inv _ _ H0).
    unfold kinds_open_vars.
    apply disjoint_comm.
    rewrite mkset_dom.
    apply (fresh_disjoint (length Ks)).
    repeat rewrite dom_concat. auto*.
    unfold kinds_open. rewrite map_length.
    rewrite* (fresh_length _ _ _ H2).
  intros x a B.
  elim (binds_concat_inv B).
    intros [Hx Ha]. apply* (proj2 Ok x).
  intro. destruct (typing_regular Typ).
  apply* (proj2 H1 x).
Qed.

Lemma typing_weaken_kinds' : forall gc K K' E t T,
  kenv_ok (K & K') ->
  K ; E |gc|= t ~: T -> K & K' ; E |gc|= t ~: T.
Proof.
  intros.
  replace (K & K') with (K & K' & empty) by simpl*.
  apply* typing_weaken_kinds.
Qed.

Definition well_subst K K' S :=
  forall Z k,
    binds Z k K ->
    well_kinded K' (kind_subst S k) (typ_subst S (typ_fvar Z)).

Lemma well_kinded_subst: forall S K K' k T,
  well_subst K K' S ->
  well_kinded K k T ->
  well_kinded K' (kind_subst S k) (typ_subst S T).
Proof.
  intros.
  induction H0.
    constructor.
  generalize (H x _ H0); intro HW.
  inversions HW.
  simpl typ_subst.
  case_eq (get x S); intros; rewrite H2 in H3.
    subst.
    simpl. apply* wk_kind.
    apply* entails_trans.
    apply* kind_subst_entails.
  simpl.
  inversions H3.
  apply* wk_kind.
  apply* entails_trans.
  apply* kind_subst_entails.
Qed.

Lemma proper_instance_subst : forall K K' K'' M Us S,
  env_prop type S ->
  proper_instance (K & K' & K'') M Us ->
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  proper_instance (K & map (kind_subst S) K'') (sch_subst S M)
    (List.map (typ_subst S) Us).
Proof.
  introv TS PI WS.
  destruct* PI.
  split. rewrite sch_subst_arity. apply* typ_subst_type_list.
  split*.
  destruct H0.
  destruct M as [Ma Mt Mk]; simpl in *.
  rewrite* <- kinds_subst_open.
  apply* (For_all2_map (well_kinded (K&K'&K''))); intros.
  apply* well_kinded_subst.
Qed.

Lemma well_subst_fresh : forall K K' K'' S Ys Ks,
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  fresh (dom S \u dom K \u dom K'') (length Ks) Ys ->
  well_subst (K & K' & K'' & kinds_open_vars Ks Ys)
    (K & map (kind_subst S) (K'' & kinds_open_vars Ks Ys)) S.
Proof.
  introv WS Fr.
  assert (KxYs: disjoint (dom K \u dom K'')
                         (dom (kinds_open_vars Ks Ys))).
    unfold kinds_open_vars.
    intro v.
    destruct* (in_vars_dec v (dom K \u dom K'')).
    right; intro.
    elim (fresh_rev _ _ Fr (x:=v)).
    rewrite <- union_assoc.
    auto with sets.
    apply (in_dom_combine _ _ H0).
  intro x; intros.
  rewrite map_concat. rewrite <- concat_assoc.
  destruct* (binds_concat_inv H) as [[N B]|B]; clear H.
    apply* well_kinded_extend.
    rewrite dom_map. rewrite dom_concat; rewrite* dom_map.
  destruct k; try constructor.
  simpl. rewrite get_notin_dom.
    apply* wk_kind. apply* binds_prepend.
      use (binds_map (kind_subst S) B).
      simpl in H; apply H.
    apply entails_refl.
  intro; elim (binds_fresh B); clear B.
  unfold kinds_open_vars.
  intro. use (in_dom_combine _ _ H0).
  elim (fresh_disjoint _ _ _ Fr x).
    intro. elim (H2 (in_mkset _ _ H1)).
  intro. elim H2. apply S.union_2. apply* S.union_2.
Qed.

Lemma kenv_ok_subst : forall K K' K'' S,
  env_prop type S ->
  kenv_ok (K & K' & K'') -> kenv_ok (K & map (kind_subst S) K'').
Proof.
  introv HS H. split*.
  intro; intros. destruct H.
  binds_cases H0. apply* (H1 x).
    apply* binds_concat_ok.
    apply* binds_concat_ok. destruct* (ok_concat_inv _ _ H).
  case_eq (get x K''); intros.
    use (binds_map (kind_subst S) H0).
    rewrite (binds_inj B0 H2).
    clear B0 a.
    destruct* (H1 x k); clear H1 H0.
    destruct k; simpl*.
    destruct c as [kc kr].
    split*.
    clear H2 H4.
    unfold All_kind_types in *; simpl in *.
    rewrite map_map; simpl.
    induction kr; simpl. auto.
    simpl in H3.
    split*.
    unfold kind_ok in H4. auto*.
  elim (binds_fresh B0). apply get_none_notin. apply* map_get_none.
Qed.

(* ********************************************************************** *)
(** Type substitution preserves typing *)

Lemma typing_typ_subst : forall gc F K'' S K K' E t T,
  disjoint (dom S) (env_fv E \u fv_in kind_fv K) ->
  env_prop type S ->
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  K & K' & K''; E & F |gc|= t ~: T -> 
  K & map (kind_subst S) K''; E & (map (sch_subst S) F) |gc|=
    t ~: (typ_subst S T).
Proof.
  introv. intros Dis TS WS Typ.
  gen_eq (K & K' & K'') as GK; gen_eq (E & F) as G; gen K''; gen F.
  induction Typ; introv WS EQ EQ'; subst; simpls typ_subst.
  (* Var *)
  rewrite~ sch_subst_open. apply* typing_var.
    apply* kenv_ok_subst.
    binds_cases H1.
      apply* binds_concat_fresh.
       rewrite* sch_subst_fresh. use (fv_in_spec sch_fv B).
       intro v. destruct* (Dis v).
       destruct* (proj1 (notin_union _ _ _) H3).
      auto*.
    apply* proper_instance_subst.
  (* Abs *)
  apply_fresh* (@typing_abs gc) as y.
   replace (Sch (typ_subst S U) nil) with (sch_subst S (Sch U nil)) by auto.
   apply_ih_map_bind* H1.
  (* Let *)
  apply_fresh* (@typing_let gc (sch_subst S M)
                            (L1 \u dom S \u dom K \u dom K'')) as y.
   clear H H1 H2. clear L2 T2 t2 Dis.
   simpl. intros Ys Fr. 
   rewrite* <- sch_subst_open_vars.
   rewrite* <- kinds_subst_open_vars.
   rewrite concat_assoc. rewrite <- map_concat.
   unfold sch_arity in Fr; simpl in Fr; rewrite map_length in Fr.
   apply* H0; clear H0.
     apply* well_subst_fresh.
   rewrite* concat_assoc.
   apply_ih_map_bind* H2.
  (* App *)
  auto*.
  (* Cst *)
  rewrite* sch_subst_open.
  assert (disjoint (dom S) (sch_fv (Delta.type c))).
    intro x. rewrite* Delta.closed.
  rewrite* sch_subst_fresh.
  apply* typing_cst.
    apply* kenv_ok_subst.
  rewrite* <- (sch_subst_fresh S H2).
  apply* proper_instance_subst.
  (* GC *)
  apply* (@typing_gc gc (List.map (kind_subst S) Ks)
                     (L \u dom S \u dom K \u dom K'')).
   rewrite map_length; intros.
   rewrite* <- kinds_subst_open_vars.
   rewrite concat_assoc. rewrite <- map_concat.
   apply* (H1 Xs); clear H1.
     apply* well_subst_fresh.
   rewrite* concat_assoc.
Qed.

Lemma typing_typ_substs : forall gc K' S K E t T,
  disjoint (dom S) (env_fv E \u fv_in kind_fv K \u dom K) -> 
  env_prop type S ->
  well_subst (K & K') K S ->
  K & K'; E |gc|= t ~: T -> 
  K ; E |gc|= t ~: (typ_subst S T).
Proof.
  intros.
  generalize (@typing_typ_subst gc empty empty); intro TTS.
  simpl in TTS.
  apply* TTS; clear TTS.
    intro v; destruct* (H v).
Qed.
  
(* ********************************************************************** *)
(** Typing schemes for expressions *)

Definition has_scheme_vars gc L (K:kenv) E t M := forall Xs,
  fresh L (sch_arity M) Xs ->
  K & kinds_open_vars (sch_kinds M) Xs; E |gc|= t ~: (M ^ Xs).

Definition has_scheme gc K E t M := forall Vs,
  types (sch_arity M) Vs ->
  For_all2 (well_kinded K) (kinds_open (sch_kinds M) Vs) Vs ->
  K ; E |gc|= t ~: (M ^^ Vs).

(* ********************************************************************** *)
(** Type schemes of terms can be instanciated *)

Lemma kind_subst_open_combine : forall Xs Vs Ks,
  fresh (typ_fv_list Vs \u kind_fv_list Ks) (length Ks) Xs ->
  types (length Xs) Vs ->
  forall k : kind,
    In k Ks ->
    kind_open k Vs = kind_subst (combine Xs Vs) (kind_open k (typ_fvars Xs)).
Proof.
  introv Fr TV. intros.
  destruct TV.
  rewrite* kind_subst_open.
    rewrite* kind_subst_fresh.
      rewrite* (fresh_subst {}).
      rewrite* <- H0.
    rewrite* mkset_dom.
    apply (fresh_disjoint (length Ks)).
    apply* (kind_fv_fresh k Ks).
  apply* list_forall_env_prop.
Qed.

Lemma well_subst_open_vars : forall (K:kenv) Vs (Ks:list kind) Xs,
  fresh (fv_in kind_fv K) (length Ks) Xs ->
  fresh (typ_fv_list Vs \u kind_fv_list Ks) (length Ks) Xs ->
  types (length Xs) Vs ->
  For_all2 (well_kinded K) (kinds_open Ks Vs) Vs ->
  well_subst (K & kinds_open_vars Ks Xs) K (combine Xs Vs).
Proof.
  introv Fr Fr' TV WK.
  intro x; intros.
  destruct* (binds_concat_inv H) as [[N B]|B]; clear H.
    unfold kinds_open_vars in N.
    rewrite* kind_map_fresh.
     simpl.
     rewrite* get_notin_dom.
      destruct k; try constructor.
      eapply wk_kind. apply B.
      apply entails_refl.
     rewrite mkset_dom in N.
      rewrite* mkset_dom.
     unfold kinds_open, typ_fvars. rewrite* map_length.
     rewrite* (fresh_length _ _ _ Fr).
    rewrite* mkset_dom.
    apply* (fresh_disjoint (length Ks)).
    apply (fresh_sub (length Ks) Xs Fr (fv_in_spec kind_fv B)).
   unfold kinds_open_vars, kinds_open in *.
   case_eq (get x (combine Xs Vs)); intros.
    case_eq (get x (combine Xs Ks)); intros.
     fold (binds x k (combine Xs Ks)) in H0.
     generalize (binds_map (fun k : kind => kind_open k (typ_fvars Xs)) H0);
       simpl; rewrite map_combine; intro.
     generalize (binds_func B H1); intro. subst k.
     apply* (For_all2_get (well_kinded K) Xs).
      use (binds_map (kind_subst (combine Xs Vs)) B).
      clear Fr WK H H0 H1 B.
      simpl in H2; rewrite map_combine in H2.
      rewrite list_map_comp in H2.
      rewrite*
        (list_map_ext Ks _ _ (kind_subst_open_combine Xs Ks (Vs:=Vs) Fr' TV)).
     rewrite* H.
    elim (get_contradicts _ _ _ _ H H0); auto.
    rewrite* <- (fresh_length _ _ _ Fr).
  elim (get_contradicts _ _ _ _ B H); auto.
Qed.

Lemma has_scheme_from_vars : forall gc L K E t M,
  has_scheme_vars gc L K E t M ->
  has_scheme gc K E t M.
Proof.
  intros gc L K E t [T Ks] H Vs TV. unfold sch_open. simpls.
  fold kind in K. fold kenv in K.
  pick_freshes (length Ks) Xs.
  unfold sch_arity in TV; simpl in TV.
  rewrite (fresh_length _ _ _ Fr) in TV.
  rewrite~ (@typ_subst_intro Xs Vs T).
  unfolds has_scheme_vars sch_open_vars. simpls.
  intro WK.
  apply* (@typing_typ_substs gc (kinds_open_vars Ks Xs)).
      rewrite* mkset_dom.
      apply* (fresh_disjoint (length Ks)).
    apply list_forall_env_prop. destruct* TV.
  apply* well_subst_open_vars.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by term substitution *)

Lemma typing_trm_subst : forall gc F M K E t T z u, 
  K ; E & z ~ M & F |(gc,GcAny)|= t ~: T ->
  (exists L:vars, has_scheme_vars (gc,GcAny) L K E u M) -> 
  term u ->
  K ; E & F |(gc,GcAny)|= (trm_subst z u t) ~: T.
Proof.
  introv Typt. intros Typu Wu. 
  gen_eq (E & z ~ M & F) as G. gen_eq (gc, GcAny) as gc0. gen F.
  induction Typt; introv EQ1 EQ2; subst; simpl trm_subst;
    destruct Typu as [Lu Typu].
  case_var.
    binds_get H1. apply_empty* (@typing_weaken (gc,GcAny)).
      destruct H2; apply* (has_scheme_from_vars Typu).
    binds_cases H1; apply* typing_var.
  apply_fresh* (@typing_abs (gc,GcAny)) as y. 
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H1. 
  apply_fresh* (@typing_let (gc,GcAny) M0 L1) as y. 
   intros; apply* H0.
     exists (Lu \u mkset Xs); intros Ys TypM.
     assert (fresh Lu (sch_arity M) Ys). auto*.
     generalize (Typu Ys H4); intro; clear H4.
     apply* typing_weaken_kinds.
     clear H0 H1 H2 L2 t2 T2 Wu Typu.
     split.
       apply* disjoint_ok.
       destruct* (typing_regular (H Xs H3)).
       unfold kinds_open_vars.
       apply* ok_combine_fresh.
       rewrite dom_concat.
       apply disjoint_union.
         apply ok_disjoint. destruct* (typing_regular H5).
       apply disjoint_comm.
       unfold kinds_open_vars.
       rewrite mkset_dom. rewrite mkset_dom.
         apply* (fresh_disjoint (sch_arity M)).
         unfold kinds_open. rewrite map_length.
           rewrite* <- (fresh_length _ _ _ H3).
         unfold kinds_open. rewrite map_length.
       rewrite* <- (fresh_length _ _ _ TypM).
     intro; intros.
     destruct (binds_concat_inv H0) as [[Fr B]|B]; clear H0.
       apply* (proj2 (proj41 (typing_regular (H Xs H3))) x).
     apply* (proj2 (proj41 (typing_regular H5))).
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H2.
  assert (exists L : vars, has_scheme_vars (gc,GcAny) L K E u M). exists* Lu.
  auto*.
  auto.
  apply_fresh* (@typing_gc (gc,GcAny) Ks) as y.
   intros Xs Fr.
   apply* H1; clear H1.
   exists (Lu \u dom K \u mkset Xs); intros Ys Fr'.
   forward~ (Typu Ys) as Typu'.
   apply* typing_weaken_kinds.
   use (proj1 (typing_regular Typu')).
   forward~ (H0 Xs) as Typx.
   use (proj1 (typing_regular Typx)).
   clear Typu Typu' Typx H0.
   split*. apply* disjoint_ok.
     unfold kinds_open_vars. apply* ok_combine_fresh.
     unfold kinds_open_vars.
     rewrite dom_concat; repeat rewrite* mkset_dom.
     apply disjoint_comm.
     apply* (fresh_disjoint (sch_arity M)).
     unfold sch_arity in Fr'.
     unfold kinds_open. rewrite map_length. rewrite* (fresh_length _ _ _ Fr').
     unfold kinds_open. rewrite map_length. rewrite* (fresh_length _ _ _ Fr).
   intros x a B.
   destruct (binds_concat_inv B); clear B.
     apply* (proj2 H2 x).
   apply* (proj2 H1 x).
Qed.

(* ********************************************************************** *)
(** Adding and removing typing_gc *)

Lemma typing_gc_any : forall gc K E t T,
  K ; E |gc|= t ~: T -> K ; E |(true,GcAny)|= t ~: T.
Proof.
  induction 1; auto*.
  apply* typing_gc. simpl; auto.
Qed.

Lemma typing_gc_raise : forall gc K E t T,
  K ; E |gc|= t ~: T -> K ; E |gc_raise gc|= t ~: T.
Proof.
  induction 1; destruct gc; destruct g; simpl; auto*.
  apply* typing_gc. simpl; auto.
Qed.

Definition typing_gc_let K E t T := K; E |(true,GcLet)|= t ~: T.
  
Lemma typing_gc_ind : forall (P: kenv -> env -> trm -> typ -> Prop),
  (forall K E t T, K; E |(false,GcLet)|= t ~: T -> P K E t T) ->
  (forall Ks L K E t T,
    (forall Xs : list var,
      fresh L (length Ks) Xs -> P (K & kinds_open_vars Ks Xs) E t T) ->
    P K E t T) ->
  forall K E t T, typing_gc_let K E t T -> P K E t T.
Proof.
  intros.
  unfold typing_gc_let in H1.
  gen_eq (true,GcLet) as gc.
  induction H1; intros; subst; try solve [apply* H].
  apply* H0.
Qed.

Lemma trm_fv_open : forall t' t n,
  trm_fv (trm_open_rec n t' t) << trm_fv t \u trm_fv t'.
Proof.
  induction t; simpl; intros; intros x Hx; auto*.
  destruct (n0 === n). rewrite* union_empty_l.
    elim (in_empty Hx).
  apply* S.union_2.
  apply* (IHt (S n)).
  destruct (S.union_1 Hx).
    destruct* (S.union_1 (IHt1 n x H)); auto with sets.
    destruct* (S.union_1 (IHt2 (S n) x H)); auto with sets.
  destruct (S.union_1 Hx).
    destruct* (S.union_1 (IHt1 n x H)); auto with sets.
    destruct* (S.union_1 (IHt2 n x H)); auto with sets.
  elim (in_empty Hx).
Qed.

Lemma notin_subset : forall S1 S2,
  S1 << S2 ->
  forall x, x \notin S2 -> x \notin S1.
Proof.
  intros.
  intro. elim H0. apply* (H x).
Qed.

Lemma ok_rename : forall (A:Set) E x y (M:A) E',
  ok (E & x ~ M & E') ->
  y \notin dom E \u dom E' ->
  ok (E & y ~ M & E').
Proof.
  intros.
  destruct (ok_concat_inv _ _ H).
  apply* disjoint_ok.
    apply* ok_push.
    destruct* (ok_concat_inv _ _ H1).
  intro.
  destruct* (ok_disjoint _ _ H x0).
  destruct (x0 == y).
    subst. right*.
  left. rewrite dom_concat.
  apply* notin_union_l.
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
  assert (ok (E & y ~ M & E')) by apply* ok_rename.
  destruct (x0 == x).
    subst.
    use (binds_mid _ _ _ _ H0).
    use (binds_func H1 H5).
    subst; clear H5.
    apply* typing_var.
  apply* typing_var.
  binds_cases H1.
    apply* binds_concat_fresh.
    apply* binds_concat_fresh.
    simpl.
    simpl in H4. auto.
  apply* binds_prepend.
  (* Abs *)
  clear H0.
  apply* (@typing_abs gc (L \u {{y}} \u {{x}})).
  intros.
  assert (x0 \notin L) by auto.
  use (H1 x0 H2 (E' & x0 ~ Sch U nil)).
  repeat rewrite <- concat_assoc in H4.
  rewrite trm_subst_open in H4; auto.
  simpl trm_subst in H4.
  destruct (x0 == x).
    subst. elim H0; auto with sets.
  apply* H4.
  simpl. simpl in H3.
  assert (y \notin {{x0}}) by auto.
  assert (y \notin trm_fv (t1 ^ x0)).
    eapply notin_subset. unfold trm_open; apply* trm_fv_open. simpl; auto.
  auto.
  (* Let *)
  clear H H1.
  apply* (@typing_let gc M0 L1 (L2 \u {{y}} \u {{x}})).
    clear H2; intros.
    apply* H0.
    simpl in H4. auto.
  clear H0; intros.
  assert (x0 \notin L2) by auto.
  use (H2 x0 H0 (E' & x0 ~ M0)). clear H0 H2.
  repeat rewrite <- concat_assoc in H1.
  rewrite trm_subst_open in H1; auto.
  simpl trm_subst in H1.
  destruct (x0 == x).
    subst. elim H; auto with sets.
  apply* H1.
  simpl. simpl in H4.
  assert (y \notin {{x0}}) by auto.
  assert (y \notin trm_fv (t2 ^ x0)).
    eapply notin_subset. unfold trm_open; apply* trm_fv_open. simpl; auto.
  auto.
  (* App *)
  simpl in H0.
  apply* (@typing_app gc K (E & y ~ M & E') S).
  (* Cst *)
  apply* typing_cst.
  apply* ok_rename.
  (* GC *)
  apply* typing_gc.
Qed.

Lemma kenv_ok_open_fresh : forall K Ks Xs,
  kenv_ok K ->
  kenv_ok (kinds_open_vars Ks Xs) -> 
  fresh (dom K) (length Ks) Xs ->
  kenv_ok (K & kinds_open_vars Ks Xs).
Proof.
  intros.
  split*.
    unfold kinds_open_vars.
    apply* disjoint_ok.
    rewrite mkset_dom. apply disjoint_comm.
    apply* (fresh_disjoint (length Ks)).
    unfold kinds_open. rewrite map_length.
    rewrite* (fresh_length _ _ _ H1).
  intros x a B.
  binds_cases B.
    apply* (proj2 H x).
  apply* (proj2 H0 x).
Qed.

Lemma kenv_ok_concat_inv : forall K1 K2,
  kenv_ok (K1 & K2) -> kenv_ok K1 /\ kenv_ok K2.
Proof.
  intros.
  split; split; destruct H; destruct* (ok_concat_inv _ _ H);
    intro; intros; apply* (H0 x a).
Qed.

Lemma kenv_ok_concat : forall K1 K2,
  kenv_ok K1 -> kenv_ok K2 -> disjoint (dom K1) (dom K2) -> kenv_ok (K1 & K2).
Proof.
  intros.
  split. apply* disjoint_ok.
  intro; intros.
  binds_cases H2. apply (proj2 H x a B).
  apply (proj2 H0 x a B0).
Qed.

Lemma dom_kinds_open_vars : forall Ks Xs,
  length Ks = length Xs ->
  dom (kinds_open_vars Ks Xs) = mkset Xs.
Proof.
  unfold kinds_open_vars.
  intros; rewrite* mkset_dom.
  unfold kinds_open. rewrite map_length. rewrite* H.
Qed.

Lemma typing_canonize : forall gc K E t T,
  K ; E |gc|= t ~: T -> K ; E |(true,GcLet)|= t ~: T.
Proof.
  induction 1; auto*.
  (* Abs *)
  clear H0 gc.
  destruct (var_fresh (L \u trm_fv t1)) as [x Hx].
  assert (Hx' : x \notin L) by auto.
  use (H1 x Hx'); clear H1 Hx'.
  gen_eq (E & x ~ Sch U nil) as E'.
  gen_eq (t1 ^ x) as t1'.
  fold (typing_gc_let K E' t1' T) in H0.
  induction H0 using typing_gc_ind; intros; subst.
    apply* (@typing_abs (true,GcLet) (L \u dom E \u trm_fv t1 \u {{x}})).
    intros.
    replace (E & x0 ~ Sch U nil) with (E & x0 ~ Sch U nil & empty)
      by (simpl; auto).
    rewrite* (@trm_subst_intro x t1 (trm_fvar x0)).
    apply* typing_rename.
    assert (x0 \notin trm_fv (t1 ^ x)).
      apply* (notin_subset (trm_fv_open (trm_fvar x) t1 0)).
      simpl; auto.
    simpl; auto.
  apply* (@typing_gc (true,GcLet) Ks L0).
  simpl; auto.
  (* Let *)
  clear H H1.
  destruct (var_fresh (L2 \u trm_fv t2)) as [x Hx].
  assert (Hx': x \notin L2) by auto.
  use (H2 x Hx'); clear H2 Hx'.
  gen_eq (E & x ~ M) as E'.
  gen_eq (t2 ^ x) as t2'.
  fold (typing_gc_let K E' t2' T2) in H. gen L1 H0.
  apply (proj2 (A:=kenv_ok K)).
  induction H using typing_gc_ind.
    split*; intros; subst.
    apply* (@typing_let (true,GcLet) M L1 (L2 \u dom E \u trm_fv t2 \u {{x}})).
    intros.
    replace (E & x0 ~ M) with (E & x0 ~ M & empty) by (simpl; auto).
    rewrite* (@trm_subst_intro x t2 (trm_fvar x0)).
    apply* typing_rename.
    assert (x0 \notin trm_fv (t2 ^ x)).
      apply* (notin_subset (trm_fv_open (trm_fvar x) t2 0)).
      simpl; auto.
    simpl; auto.
  split.
    destruct (var_freshes L (length Ks)) as [Xs HXs].
    destruct (H Xs HXs); clear H.
    destruct* (kenv_ok_concat_inv _ _ H0).
  intros; subst.
  apply* (@typing_gc (true,GcLet) Ks L).
    simpl; auto.
  intros.
  destruct (H Xs H1).
  apply* (H3 (L1 \u mkset Xs)); clear H H3.
  intros.
  apply* typing_weaken_kinds.
  assert (fresh L1 (sch_arity M) Xs0) by auto.
  use (proj41 (typing_regular (H0 Xs0 H3))); clear H0 H3.
  apply* kenv_ok_concat.
    destruct* (kenv_ok_concat_inv _ _ H4).
  rewrite dom_concat.
  intro.
  clear -H1 H H4.
  destruct* (fresh_disjoint _ _ _ H x0).
    right; rewrite* dom_kinds_open_vars.
    apply (fresh_length _ _ _ H).
  destruct* (ok_disjoint _ _ (proj1 H4) x0).
  left; rewrite* dom_kinds_open_vars.
  apply* fresh_length.
  (* App *)
  clear H H0.
  gen IHtyping1.
  fold (typing_gc_let K E t2 S) in IHtyping2.
  apply (proj2 (A:=kenv_ok K)).
  induction IHtyping2 using typing_gc_ind.
    split*; intros; subst.
    gen H. gen_eq (typ_arrow T0 T) as S.
    fold (typing_gc_let K E t1 S) in IHtyping1.
    apply (proj2 (A:=kenv_ok K)).
    induction IHtyping1 using typing_gc_ind.
      split*; intros; subst.
      apply* typing_app.
    split.
      destruct (var_freshes L (length Ks)) as [Xs HXs].
      destruct (H Xs HXs); clear H.
      destruct* (kenv_ok_concat_inv _ _ H0).
    intros; subst.
    apply* (@typing_gc (true,GcLet) Ks L).
      simpl; auto.
    intros.
    destruct (H Xs H0); clear H.
    apply* H3; clear H3.
    apply* typing_weaken_kinds'.
  split.
    destruct (var_freshes L (length Ks)) as [Xs HXs].
    destruct (H Xs HXs); clear H.
    destruct* (kenv_ok_concat_inv _ _ H0).
  intros.
  apply* (@typing_gc (true,GcLet) Ks L).
    simpl; auto.
  intros.
  destruct (H Xs H0); clear H.
  apply* H2; clear H2.
  apply* typing_weaken_kinds'.
  (* GC *)
  apply* typing_gc.
  simpl; auto.
Qed.

(* ********************************************************************** *)
(** Extra hypotheses for main results *)

Module Type SndHypIntf.
  Parameter delta_typed : forall n t1 t2 tl K E T,
    Delta.rule n t1 t2 ->
    list_for_n term n tl ->
    K ; E |(false,GcLet)|= trm_inst t1 tl ~: T ->
    K ; E |(true,GcAny)|= trm_inst t2 tl ~: T.
  Parameter const_arity_ok : forall c vl K T,
    list_for_n value (S(Const.arity c)) vl ->
    K ; empty |(false,GcLet)|= const_app c vl ~: T ->
    exists n:nat, exists t1:trm, exists t2:trm, exists tl:list trm,
      Delta.rule n t1 t2 /\ list_for_n term n tl /\
      const_app c vl = trm_inst t1 tl.
  Parameter delta_arity : forall n t1 t2,
    Delta.rule n t1 t2 ->
    exists c, exists pl, t1 = const_app c pl /\ length pl = S(Const.arity c).
End SndHypIntf.

Module Mk3(SH:SndHypIntf).
Import SH.

(* ********************************************************************** *)
(** Preservation: typing is preserved by reduction *)

Lemma typ_open_vars_nil : forall T,
  type T -> typ_open_vars T nil = T.
Proof.
  induction T; unfold typ_open_vars; simpl; intros; auto*.
    inversion H.
  unfold typ_open_vars in *; simpls.
  rewrite IHT1. rewrite* IHT2. inversion* H. inversion* H.
Qed.

Lemma typing_abs_inv : forall gc K E t1 t2 T1 T2,
  K ; E |(gc,GcAny)|= trm_abs t1 ~: typ_arrow T1 T2 ->
  K ; E |(gc,GcAny)|= t2 ~: T1 ->
  K ; E |(gc,GcAny)|= t1 ^^ t2 ~: T2.
Proof.
  introv Typ1 Typ2.
  gen_eq (gc,GcAny) as gcs.
  gen_eq (trm_abs t1) as t.
  gen_eq (typ_arrow T1 T2) as T.
  induction Typ1; intros; subst; try discriminate.
    inversions H2; inversions H3; clear H2 H3.
    pick_fresh x. 
    rewrite* (@trm_subst_intro x). 
    apply_empty* (@typing_trm_subst gc).
    exists {}. intro. unfold sch_arity, kinds_open_vars, sch_open_vars; simpl.
    destruct* Xs. simpl. rewrite* typ_open_vars_nil.
    simpl. intuition.
  apply* (@typing_gc (gc,GcAny) Ks L).
  intros.
  use (H0 Xs H2); clear H0.
  apply* H1.
  apply* typing_weaken_kinds'.
  apply (proj41 (typing_regular H3)).
Qed.

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen_eq (true, GcAny) as gc. gen t'.
  induction Typ; introv EQ Red; subst; inversions Red;
    try solve [apply* typing_gc].
  destruct (SH.delta_arity H4) as [a [pl [e1 e2]]]; subst.
    destruct (trm_inst_app_inv a pl tl) as [EQ|[t1' [t2' EQ]]]; rewrite EQ in *;
    discriminate.
  destruct (SH.delta_arity H3) as [a [pl [e1 e2]]]; subst.
    destruct (trm_inst_app_inv a pl tl) as [EQ|[t1' [t2' EQ]]]; rewrite EQ in *;
    discriminate.
  (* Let *)
  pick_fresh x. rewrite* (@trm_subst_intro x). 
   apply_empty* (@typing_trm_subst true).
   exists* L1.
  destruct (SH.delta_arity H4) as [a [pl [e1 e2]]]; subst.
    destruct (trm_inst_app_inv a pl tl) as [EQ|[t1' [t2' EQ]]]; rewrite EQ in *;
    discriminate.
  (* Let *)
  apply* (@typing_let (true,GcAny) M L1).
  (* Beta *)
  apply* typing_abs_inv.
  (* Delta *)
  assert (K;E |(true,GcAny)|= trm_app t1 t2 ~: T). auto*.
  use (typing_canonize H2).
  fold (typing_gc_let K E (trm_app t1 t2) T) in H3.
  rewrite <- H in *.
  clear -H0 H1 H3.
  gen_eq (trm_inst t0 tl) as t1.
  induction H3 using typing_gc_ind; intros; subst.
    apply* delta_typed.
  apply* typing_gc. simpl; auto.
  (* App1 *)
  auto*.
  (* App2 *)
  auto*.
  (* Delta/cst *)
  apply* delta_typed.
  rewrite* H2.
Qed. 

(* ********************************************************************** *)
(** Progress: typed terms are values or can reduce *)

Lemma value_app_const : forall t1 t2 n,
  valu n (trm_app t1 t2) ->
  exists c:Const.const, exists vl:list trm,
    length vl + n = Const.arity c /\ trm_app t1 t2 = const_app c vl /\
    list_forall value vl.
Proof.
  induction t1; intros; inversions H; try (inversion H3; fail).
    clear IHt1_2.
    destruct (IHt1_1 _ _ H3) as [c [vl [Hlen [Heq Hv]]]].
    exists c. exists (vl ++ t2 :: nil).
    split. rewrite app_length. rewrite <- Hlen. simpl. ring.
    split. rewrite Heq. unfold const_app.
      rewrite fold_left_app. simpl. auto.
    apply* list_forall_concat.
    constructor; auto. exists* n2.
  exists c. exists (t2 :: nil).
  inversions H3. rewrite H1.
  unfold const_app. simpl; auto.
  split3*. constructor; auto. exists* n2.
Qed.

Lemma progress_delta : forall K t0 t3 t2 T,
  K; empty |(false,GcLet)|= trm_app (trm_app t0 t3) t2 ~: T ->
  valu 0 (trm_app t0 t3) ->
  value t2 ->
  exists t' : trm, trm_app (trm_app t0 t3) t2 --> t'.
Proof.
  intros.
  destruct (value_app_const H0) as [c [vl [Hlen [Heq Hv]]]].
  destruct (const_arity_ok (c:=c) (vl:=vl ++ t2 :: nil) (K:=K) (T:=T)).
    split. rewrite <- Hlen. rewrite app_length. simpl; ring.
    apply* list_forall_concat.
    rewrite Heq in H.
    unfold const_app in *. rewrite* fold_left_app.
  destruct H2 as [t1' [t3' [tl [R [Htl Heq']]]]].
  exists (trm_inst t3' tl).
  rewrite Heq.
  unfold const_app in *.
  rewrite fold_left_app in Heq'; simpl in Heq'.
  rewrite Heq'.
  apply* red_delta.
Qed.

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (empty:env) as E. gen_eq (true,GcAny) as gc.
  poses Typ' Typ.
  induction Typ; intros; subst;
    try (pick_freshes (length Ks) Xs; apply* (H0 Xs)).
  inversions H1.
  left. exists* 0.
  right. pick_freshes (sch_arity M) Ys.
    destructi~ (@H0 Ys) as [[n Val1] | [t1' Red1]].
      assert (value t1). exists* n.
      exists* (t2 ^^ t1).
      exists* (trm_let t1' t2).
  destruct~ IHTyp1 as [Val1 | [t1' Red1]]. 
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      use (typing_canonize Typ').
      remember (empty(A:=sch)) as E.
      remember (trm_app t1 t2) as t.
      clear Typ1 Typ2 Typ'.
      fold (typing_gc_let K E t T) in H.
      apply (proj2 (A:=kenv_ok K)).
      induction H using typing_gc_ind.
        split*; intros; subst.
        destruct Val1 as [n Val1]; inversions Val1.
        right; exists* (t0 ^^ t2).
        case_eq (Const.arity c); intros.
          right. rewrite H0 in Val1.
          destruct (const_arity_ok (c:=c)(vl:=t2::nil)(K:=K)(T:=T)).
            rewrite H0. constructor; simpl; auto.
          unfold const_app; simpl*.
          destruct H1 as [t1' [t3' [tl [R [Htl Heq]]]]].
          exists (trm_inst t3' tl).
          unfold const_app in Heq; simpl in Heq; rewrite Heq.
          apply* red_delta.
        left. exists n. rewrite H0 in Val1. destruct* Val2.
        destruct n.
          right; apply* progress_delta.
        left. destruct Val2. exists* n.
      destruct (var_freshes L (length Ks)) as [Xs HXs].
      destruct* (H Xs); clear H.
      split*.
      destruct* (kenv_ok_concat_inv _ _ H0).
      right; exists* (trm_app t1 t2').
    right; exists* (trm_app t1' t2).
  left; exists* (Const.arity c).
  destruct (var_freshes L (length Ks)) as [Xs HXs].
  apply* (H1 Xs).
Qed.

Lemma value_irreducible : forall t t',
  value t -> ~(t --> t').
Proof.
  induction t; introv HV; destruct HV as [k HV']; inversions HV';
    intro R; inversions R.
       destruct (delta_arity H0) as [c [pl [Heq Hlen]]]. rewrite Heq in H.
       destruct* (trm_inst_app_inv c pl tl). subst. discriminate.
       destruct H3; destruct H3; rewrite H3 in H. discriminate.
      inversions H2.
     clear IHt1 IHt2 H1.
     destruct (delta_arity H0) as [c [pl [Heq Hlen]]]. rewrite Heq in H.
     destruct (value_app_const HV').
     destruct H1 as [vl [Hl [He Hv]]].
     rewrite He in H; clear He.
     unfold trm_inst in H.
     rewrite trm_inst_app in H.
     destruct (const_app_eq _ _ _ _ H). subst.
     rewrite map_length in Hl.
     omega.
    elim (IHt1 t1'). exists* (S k). auto.
   elim (IHt2 t2'). exists* n2. auto.
  destruct (delta_arity H0) as [c' [pl [Heq Hlen]]]. rewrite Heq in H.
  unfold trm_inst in H.
  rewrite trm_inst_app in H.
  assert (const_app c nil = trm_cst c). auto.
  rewrite <- H2 in H.
  destruct (const_app_eq _ _ _ _ H). subst.
  rewrite <- (map_length (trm_inst_rec 0 tl)) in Hlen.
  rewrite H4 in Hlen. discriminate.
Qed.

End Mk3.

End Mk2.

End MkSound.
