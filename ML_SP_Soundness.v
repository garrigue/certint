(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - May 2008                                *
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

Lemma kenv_ok_concat : forall K1 K2,
  kenv_ok K1 -> kenv_ok K2 -> disjoint (dom K1) (dom K2) -> kenv_ok (K1 & K2).
Proof.
  intros.
  split. apply* disjoint_ok.
  intro; intros.
  binds_cases H2. apply (proj2 H x a B).
  apply (proj2 H0 x a B0).
Qed.

Lemma kenv_ok_concat_inv : forall K1 K2,
  kenv_ok (K1 & K2) -> kenv_ok K1 /\ kenv_ok K2.
Proof.
  intros.
  split; split; destruct H; destruct* (ok_concat_inv _ _ H);
    intro; intros; apply* (H0 x a).
Qed.

Lemma typing_canonize : forall gc K E t T,
  K ; E |gc|= t ~: T -> K ; E |(true,GcLet)|= t ~: T.
Proof.
  induction 1; auto*.
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

Lemma binds_dom : forall (A:Set) x (a:A) E,
  binds x a E -> x \in dom E.
Proof.
  unfold binds; induction E; simpl; intros. discriminate.
  destruct a0. destruct (x==v). rewrite e. auto with sets.
  apply* S.union_3.
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
  split*.
  destruct* (Z' == v0).
  subst.
  destruct (fresh_disjoint _ _ _ H0 v0).
    elim H2.
    rewrite <- (mkset_dom Ys Ks).
      apply (binds_dom HG).
    rewrite <- (fresh_length _ _ _ H0). rewrite* H3.
  elim H2; auto with sets.
Qed.

Lemma kinds_subst_fresh : forall S Ks,
  disjoint (dom S) (kind_fv_list Ks) ->
  List.map (kind_subst S) Ks = Ks.
Proof.
  induction Ks; intros. auto.
  simpl in *.
  rewrite kind_map_fresh.
    rewrite* IHKs.
    intro x; destruct* (H x).
  intro x; destruct* (H x).
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

Definition env_incl (A:Set) E1 E2 :=
  forall x (k:A), binds x k E1 -> binds x k E2.

Lemma For_all2_imp : forall (A B:Set) (P P':A->B->Prop) l1 l2,
  For_all2 P l1 l2 ->
  (forall x y, P x y -> P' x y) ->
  For_all2 P' l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros; intuition.
Qed.

Lemma dom_kinds_open_vars : forall Ks Xs,
  length Ks = length Xs ->
  dom (kinds_open_vars Ks Xs) = mkset Xs.
Proof.
  unfold kinds_open_vars.
  intros; rewrite* mkset_dom.
  unfold kinds_open. rewrite map_length. rewrite* H.
Qed.

Lemma typing_kenv_incl : forall gc K E t T,
  K; E |gc|= t ~: T ->
  forall K',
    env_incl K K' -> kenv_ok K' -> K'; E |gc|= t ~:T.
Proof.
  induction 1; intros; auto*.
  apply* typing_var.
  destruct H2; split*.
  destruct H5; split*.
  apply (For_all2_imp _ (well_kinded K') _ _ H6).
  intros.
  inversions H7. apply wk_any.
  apply* wk_kind.
  apply* (@typing_let gc M (L1 \u dom K')).
  intros.
  assert (kenv_ok (K' & kinds_open_vars (sch_kinds M) Xs)).
    apply* kenv_ok_concat.
    assert (fresh L1 (sch_arity M) Xs) by auto.
    destruct* (kenv_ok_concat_inv _ _ (proj1 (typing_regular (H Xs H6)))).
    apply disjoint_comm.
    rewrite dom_kinds_open_vars. apply* (fresh_disjoint (sch_arity M)).
    unfold sch_arity in H5; apply* fresh_length.
  apply* H0.
  intro; intros.
  binds_cases H7.
    destruct H6; apply* binds_concat_ok.
  apply* binds_prepend.
  apply* typing_cst.
  destruct H1; split; intuition.
  apply (For_all2_imp _ (well_kinded K') _ _ H6).
  intros.
  inversions H4. apply wk_any.
  apply* wk_kind.
  apply* (@typing_gc gc Ks (L \u dom K')).
  intros.
  assert (kenv_ok (K' & kinds_open_vars Ks Xs)).
    apply* kenv_ok_concat.
    assert (fresh L (length Ks) Xs) by auto.
    destruct* (kenv_ok_concat_inv _ _ (proj1 (typing_regular (H0 Xs H5)))).
    apply disjoint_comm.
    rewrite dom_kinds_open_vars. apply* (fresh_disjoint (length Ks)).
    unfold sch_arity in H4; apply* fresh_length.
  apply* (H1 Xs).
  intro; intros.
  binds_cases H6.
    destruct H5; apply* binds_concat_ok.
  apply* binds_prepend.
Qed.

Lemma typ_fv_typ_fvars : forall Xs,
  typ_fv_list (typ_fvars Xs) = mkset Xs.
Proof.
  induction Xs; simpl. auto.
  rewrite* IHXs.
Qed.

Lemma disjoint_fresh : forall Xs L1 L2,
  fresh L1 (length Xs) Xs ->
  disjoint (mkset Xs) L2 ->
  fresh L2 (length Xs) Xs.
Proof.
  induction Xs; simpl; intros. auto.
  split. destruct* (H0 a). elim H1; auto with sets.
  destruct H; apply* IHXs.
  intro. destruct* (H0 x).
  destruct* (fresh_disjoint _ _ _ H1 x).
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
  assert (DS: dom S = mkset Xs).
    unfold S; rewrite mkset_dom. auto.
    unfold typ_fvars; rewrite map_length. apply* fresh_length.
  assert (TS: env_prop type S).
    unfold S; apply list_forall_env_prop.
    clear; induction Ys; simpl; auto.
  unfold sch_open_vars, typ_open_vars.
  rewrite (typ_subst_intro Xs (Us:=typ_fvars Ys)).
    fold S.
    replace E with (E & map (sch_subst S) empty) by auto.
    replace (kinds_open_vars (sch_kinds M) Ys) with
      (map(kind_subst S)(combine Ys (kinds_open (sch_kinds M) (typ_fvars Xs)))).
      apply* typing_typ_subst.
        rewrite DS; apply* (fresh_disjoint (length Xs)).
      instantiate (1 := kinds_open_vars (sch_kinds M) Xs).
      intro; intros.
      destruct k as [[kc kr]|].
        binds_cases H2.
          rewrite typ_subst_fresh.
            rewrite kind_subst_fresh.
              apply* wk_kind. apply entails_refl.
            rewrite DS; apply (fresh_disjoint (length Xs)).
            apply* (@fresh_sub (length Xs) Xs (fv_in kind_fv K)).
            fold (kind_fv (Some (Kind kc kr))).
            apply* fv_in_spec.
          rewrite DS; simpl.
          apply (fresh_disjoint (length Xs)).
          apply* (@fresh_sub (length Xs) Xs (dom K)).
          intro; intros.
          apply* binds_dom.
          rewrite* <- (S.singleton_1 H2).
        unfold kinds_open_vars in B1.
          assert (length (kinds_open (sch_kinds M) (typ_fvars Xs)) = length Xs).
            unfold kinds_open; rewrite map_length.
            apply* fresh_length.
          destruct (binds_rename _ _ _ _ H2 H0 B1) as [Z' [HT HG]].
          unfold S at 3. rewrite HT.
          simpl; apply* wk_kind.
            apply binds_prepend.
            use (binds_map (kind_subst S) HG).
            simpl in H3; apply H3.
          apply entails_refl.
        rewrite typ_subst_fresh.
          unfold kind_subst. simpl.
          eapply wk_kind.
            apply binds_prepend.
            use (binds_map (kind_map (typ_subst S)) B0).
            simpl in H2. apply H2.
          apply entails_refl.
        rewrite DS; simpl.
        destruct (fresh_disjoint _ _ _ H0 Z).
          use (binds_dom B0).
          rewrite mkset_dom in H3. elim (H2 H3).
        symmetry; unfold kinds_open, typ_fvars.
        repeat rewrite map_length.
        unfold sch_arity in H.
        rewrite (fresh_length _ _ _ H). apply* fresh_length.
        intro.
        destruct (x == Z); subst; auto.
      simpl kind_subst; apply wk_any.
      apply* typing_weaken_kinds'.
      apply* kenv_ok_concat.
        split. apply* ok_combine_fresh.
        destruct (proj2 (kenv_ok_concat_inv _ _ (proj41 (typing_regular H1)))).
        unfold kinds_open_vars in H3.
        intro; intros.
        rewrite <- (fresh_length _ _ _ H) in H0.
        rewrite (fresh_length _ _ _ H0) in H.
        assert (length (kinds_open (sch_kinds M) (typ_fvars Xs)) = length Ys).
          unfold kinds_open; rewrite map_length.
          apply* fresh_length.
        destruct (binds_rename _ _ _ _ H5 H H4) as [x' [_ HB]].
        apply (H3 _ _ HB).
      apply disjoint_comm.
      rewrite dom_concat; unfold kinds_open_vars; repeat rewrite mkset_dom.
          apply* (fresh_disjoint (length Xs)).
        unfold kinds_open. rewrite map_length.
        rewrite* <- (fresh_length _ _ _ H).
      unfold kinds_open. rewrite map_length.
      rewrite <- (fresh_length _ _ _ H0).
      rewrite* <- (fresh_length _ _ _ H).
    rewrite map_combine.
    rewrite* kinds_subst_open.
    rewrite kinds_subst_fresh.
      unfold S.
      assert (fresh {} (length (typ_fvars Ys)) Xs).
        unfold typ_fvars; rewrite map_length.
        rewrite* <- (fresh_length _ _ _ H0).
      rewrite* (fresh_subst _ _ _ H2).
    rewrite DS; apply (fresh_disjoint (sch_arity M)).
    unfold sch_fv in H. auto.
   unfold sch_fv in H.
   apply* fresh_union_l.
   rewrite typ_fv_typ_fvars.
   apply* disjoint_fresh. apply* fresh_resize.
   apply disjoint_comm. apply* (fresh_disjoint (length Xs)).
  unfold types.
  split. unfold typ_fvars; rewrite map_length; apply* fresh_length.
  clear. induction Ys; simpl; intuition.
Qed.

Lemma fv_in_concat : forall (A:Set) (fv:A->vars) E F,
  fv_in fv (E & F) = fv_in fv F \u fv_in fv E.
Proof.
  induction F; simpl. rewrite* union_empty_l.
  destruct a. rewrite* IHF. rewrite* union_assoc.
Qed.

Lemma kenv_ok_merge : forall (K K1 K2 : kenv),
  kenv_ok (K & K1) ->
  kenv_ok (K & K2) ->
  disjoint (dom K1) (dom K2) -> kenv_ok (K & K1 & K2).
Proof.
  intros.
  destruct (kenv_ok_concat_inv _ _ H0).
  apply* kenv_ok_concat.
  intro v; destruct* (H1 v).
  destruct* (ok_disjoint _ _ (proj1 H0) v).
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
    intro x. destruct* (ok_disjoint _ _ H1 x).
    destruct* (ok_disjoint _ _ H x).
  intro; intros.
  binds_cases H5; apply* (H0 x).
Qed.

Lemma typ_fv_open : forall Us T,
  typ_fv (typ_open T Us) << typ_fv T \u typ_fv_list Us.
Proof.
  induction T; simpl; intros x Hx.
    gen n; induction Us; destruct n; simpl;
      intros; try solve [elim (in_empty Hx)].
      auto with sets.
      use (IHUs n Hx). rewrite union_empty_l in *. auto with sets.
    auto with sets.
  destruct (S.union_1 Hx).
    use (IHT1 x H). destruct (S.union_1 H0); auto with sets.
  use (IHT2 x H). destruct (S.union_1 H0); auto with sets.
Qed.

Lemma kind_fv_open : forall Us k,
  kind_fv (kind_open k Us) << kind_fv k \u typ_fv_list Us.
Proof.
  destruct k as [[kc kr]|]; unfold kind_fv; simpl.
    rewrite map_map. simpl.
    induction kr; simpl. apply subset_empty_l.
    intros x Hx.
    destruct (S.union_1 Hx).
    destruct (S.union_1 (typ_fv_open _ _ H)); auto with sets.
    rewrite <- union_assoc.
    use (IHkr _ H). auto with sets.
  apply subset_empty_l.
Qed.

Lemma fv_in_kinds_open_vars : forall Ks Xs,
  fv_in kind_fv (kinds_open_vars Ks Xs) << kind_fv_list Ks \u mkset Xs.
Proof.
  unfold kinds_open_vars.
  intros.
  rewrite <- typ_fv_typ_fvars.
  set (Us := typ_fvars Xs); clearbody Us.
  gen Ks; induction Xs; destruct Ks; simpl;
    intros x Hx; try solve [elim (in_empty Hx)].
  destruct (S.union_1 Hx).
    destruct (S.union_1 (kind_fv_open _ _ H)); auto with sets.
  rewrite <- union_assoc.
  use (IHXs Ks _ H). auto with sets.
Qed.

Definition env_weaker E F :=
  forall x T Ks,
    binds x (Sch T Ks) E -> scheme (Sch T Ks) ->
    exists Ks', scheme (Sch T (Ks++Ks')) /\ binds x (Sch T (Ks++Ks')) F.

Lemma in_list_forall : forall (A:Set) (P:A->Prop) x l,
  list_forall P l -> In x l -> P x.
Proof.
  induction 1; simpl; intros. elim H.
  destruct* H1. subst*.
Qed.

Lemma list_forall_app_inv : forall (A:Set) (P:A->Prop) l1 l2,
  list_forall P (l1 ++ l2) -> list_forall P l2.
Proof.
  induction l1; simpl; intros. auto.
  inversion* H.
Qed.

Lemma typ_open_other_type : forall Us Vs T,
  type (typ_open T Us) ->
  types (length Us) Vs ->
  type (typ_open T Vs).
Proof.
  induction T; simpl; intros.
      destruct H0.
      gen Us Vs; induction n; destruct Us; destruct Vs;
        simpl in *; intros; try discriminate;
        inversion* H1.
    simpl*.
  inversion* H.
Qed.

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
  destruct k as [[kc kr]|]; simpl*; intros.
  apply (f_equal (@Some ckind)).
  apply (f_equal (Kind kc)).
  induction kr; simpl in *. auto.
  destruct H.
  rewrite* (typ_open_extra Us Vs).
  rewrite* IHkr.
Qed.

Lemma kind_open_ok : forall k Us,
  kind_ok k -> kind_ok (kind_open k Us).
Proof.
  intros.
  destruct k as [[kc kr]|]; intros.
    destruct H.
    split*.
  simpl*.
Qed.

Lemma env_weaker_ok : forall Us U Ks Ks' k Xs,
  types (length Ks) Us ->
  length Ks' = length Xs ->
  scheme (Sch U (Ks ++ Ks')) ->
  In k (kinds_open Ks' (Us ++ typ_fvars Xs)) ->
  All_kind_types type k /\ kind_ok k.
Proof.
  intros.
  destruct H.
  destruct H1. simpl in *.
  destruct H1 as [L Hs].
  destruct (var_freshes L (length (Ks ++ Ks'))) as [Xs' Fr].
  destruct (Hs Xs' Fr) as [_ HA]; clear Hs.
  rewrite app_length in Fr. rewrite H0 in Fr; clear H0. rewrite H in Fr.
  use (list_forall_app_inv _ _ H4); clear H4.
  use (list_forall_app_inv _ _ HA); clear HA.
  induction Ks'; simpl in *. elim H2.
  inversions H1; clear H1.
  inversions H0; clear H0.
  destruct H2; subst.
    clear -H H3 Fr H7 H8.
    destruct a as [[kc kr]|].
      split.
        clear H8.
        induction kr; simpl in *; auto.
        unfold All_kind_types in *; simpl in *. intuition.
        unfold typ_open_vars in H0.
        eapply typ_open_other_type. apply H0.
        unfold typ_fvars.
        split.
          rewrite app_length. repeat rewrite map_length.
          rewrite* <- (fresh_length _ _ _ Fr).
        clear -H3. induction H3; simpl*.
        induction Xs; simpl*.
      apply* kind_open_ok.
    simpl*.
  apply* IHKs'.
Qed.

Lemma For_all2_app : forall (A B:Set) (P:A->B->Prop) l2 l2' l1 l1',
  For_all2 P l1 l1' ->
  For_all2 P l2 l2' ->
  For_all2 P (l1 ++ l2) (l1' ++ l2').
Proof.
  induction l1; destruct l1'; simpl; intros; try contradiction.
    auto.
  destruct H; split*.
Qed.

Lemma For_all2_map_iff1 : forall (A B C:Set) (P:A->B->Prop) (f:C->A) l1 l2,
    For_all2 P (List.map f l1) l2 <-> For_all2 (fun x => P (f x)) l1 l2.
Proof.
  induction l1; destruct l2; simpl; intuition; destruct* (IHl1 l2).
Qed.

Lemma For_all2_binds : forall (A:Set) (Ks':list A) Xs K,
  fresh (dom K) (length Ks') Xs ->
  For_all2 (fun y x => binds x y (combine Xs Ks' & K)) Ks' Xs.
Proof.
  induction Ks'; destruct Xs; simpl; intros; try contradiction.
    auto.
  destruct H.
  split. apply* binds_concat_fresh. apply (binds_head v a (combine Xs Ks')).
  replace (((v, a) :: combine Xs Ks') & K)
    with (combine Xs Ks' & (v ~ a & K)).
    apply IHKs'. rewrite dom_concat. simpl. auto.
  unfold concat. rewrite app_ass. reflexivity.
Qed.

Lemma For_all2_map:
  forall (A B C D:Set)(P:A->B->Prop)(P':C->D->Prop) f g l1 l2,
    (forall x y, P x y -> P' (f x) (g y)) ->
    For_all2 P l1 l2 ->
    For_all2 P' (List.map f l1) (List.map g l2).
Proof.
  induction l1; introv; elim l2; simpls; auto*.
Qed.

Lemma well_kinded_combine : forall K Ks' Xs Us,
  fresh (dom K) (length Ks') Xs ->
  For_all2 (well_kinded
    (K & combine Xs (List.map (fun k => kind_open k (Us ++ typ_fvars Xs)) Ks')))
   (List.map (fun k => kind_open k (Us ++ typ_fvars Xs)) Ks') (typ_fvars Xs).
Proof.
  intros.
  assert (fresh (dom (empty(A:=kind))) (length Ks') Xs) by auto.
  use (For_all2_binds _ _ _ H0).
  simpl in H1.
  unfold typ_fvars; apply* For_all2_map.
  simpl; intros.
  destruct x; try apply wk_any.
  simpl.
  apply* wk_kind.
    apply binds_prepend.
    rewrite <- map_combine.
    use (binds_map (fun k => kind_open k (Us ++ List.map typ_fvar Xs)) H2).
    simpl in H3. apply H3.
  apply entails_refl.
Qed.

Lemma well_kinded_combine2 : forall K U Ks Us Ks' Xs,
  proper_instance K (Sch U Ks) Us ->
  scheme (Sch U (Ks ++ Ks')) ->
  fresh (dom K) (length Ks') Xs ->
  For_all2
    (well_kinded (K & combine Xs (kinds_open Ks' (Us ++ typ_fvars Xs))))
    (kinds_open (sch_kinds (Sch U (Ks ++ Ks'))) (Us ++ typ_fvars Xs))
    (Us ++ typ_fvars Xs).
Proof.
  introv PI HS Fr.
  destruct PI as [HT [HS0 HW]].
  simpl in *.
  unfold kinds_open. rewrite map_app.
  apply For_all2_app.
    unfold kinds_open in HW.
    destruct (proj1 HS0) as [L' HF].
    destruct (var_freshes L' (length Ks)) as [Xs' Fr'].
    use (proj2 (HF Xs' Fr')).
    unfold sch_arity in HT.
    simpl in *.
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
    destruct HW; inversion H0; inversions H; clear H H0.
    split*. clear IHKs.
    clear -H2 Fr Fr' H1 H8.
    destruct a; simpl in *; try apply wk_any.
    destruct t; inversions H2; clear H2.
    eapply wk_kind.
      apply* binds_concat_fresh.
      apply* notin_combine_fresh.
      use (binds_dom H4). auto with sets.
    destruct c as [kc kr]; simpl in *.
    destruct H5; split*. clear H.
    intros.
    apply H0; clear H0.
    unfold All_kind_types in H8; simpl in *.
    clear -Fr' H8 H H1.
    induction kr; simpl in *. auto.
    destruct H8; destruct* H.
    clear IHkr H2; left; subst.
    rewrite* (typ_open_extra Us (typ_fvars Xs)).
    unfold typ_open_vars in H0.
    apply (typ_open_other_type (typ_fvars Xs')). auto.
    split. unfold typ_fvars. rewrite map_length.
        rewrite* (fresh_length _ _ _ Fr').
    auto.
  clear -Fr.
  apply* well_kinded_combine.
Qed.

Fixpoint bvar_subst (A:Set) (n:nat) (K:Env.env A) {struct K} : Env.env typ :=
  match K with
  | nil => nil
  | (x,_)::K' => (x,typ_bvar n) :: bvar_subst (S n) K'
  end.

Lemma env_incl_swap : forall (A:Set) (E E1 E2:Env.env A),
  ok (E & E1 & E2) -> env_incl (E & E2 & E1) (E & E1 & E2).
Proof.
  intros; intro; intros.
  binds_cases H0; auto.
Qed.

Definition list_snd (A B:Set) := List.map (@snd A B).

Lemma env_weaker_push : forall E F x U Ks Ks',
  env_weaker E F -> x # F ->
  (scheme (Sch U Ks) -> scheme (Sch U (Ks++Ks'))) ->
  env_weaker (E & x ~ Sch U Ks) (F & x ~ Sch U (Ks++Ks')).
Proof.
  intros; intro; intros.
  binds_cases H2.
    destruct (H _ _ _ B H3) as [Ks1 [HS HB]].
    exists* Ks1.
  inversions H4.
  exists* Ks'.
Qed.

Lemma app_length_inv : forall (A:Set) n (l:list A),
  n <= length l ->
  exists l1, exists l2, length l1 = n /\ l = l1 ++ l2.
Proof.
  induction n; intros.
    exists (nil(A:=A)); exists l; simpl; auto.
  destruct l. elimtype False. simpl in H. omega.
  destruct (IHn l) as [l1 [l2 [Hl1 Happ]]]. simpl in H; omega.
  exists (a::l1); exists l2; rewrite Happ; simpl*.
Qed.

Lemma fresh_app_firsts : forall n Ys m Xs L,
  fresh L (m+n) (Xs ++ Ys) ->
  m = length Xs -> fresh L m Xs.
Proof.
  induction m; destruct Xs; simpl; intros; try discriminate; auto.
  injection H0; destruct H; split; auto.
Qed.

Lemma list_forall_app : forall (A:Set) (P:A->Prop) l1 l2,
  list_forall P l1 -> list_forall P l2 -> list_forall P (l1 ++ l2).
Proof.
  induction 1; intros; simpl; auto.
Qed.

Definition list_fst (A B:Set) := List.map (@fst A B).

Lemma combine_fst_snd : forall (A B:Set) (l:list(A*B)),
  combine (list_fst l) (list_snd l) = l.
Proof.
  induction l; simpl. auto.
  destruct a; simpl; rewrite* IHl.
Qed.

Lemma combine_app : forall (A B:Set) (l1 l2:list A) (l1' l2':list B),
  length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; simpl; intros; try discriminate. auto.
  rewrite* IHl1.
Qed.

Lemma app_eq : forall (A:Set) (l1 l2 l1' l2':list A),
  l1 = l1' -> l2 = l2' -> l1 ++ l2 = l1' ++ l2'.
Proof. congruence. Qed.

Lemma env_prop_list_forall : forall (A : Set) (P : A -> Prop) Xs Vs,
  env_prop P (combine Xs Vs) ->
  ok (combine Xs Vs) -> length Xs = length Vs -> list_forall P Vs.
Proof.
  induction Xs; destruct Vs; simpl; intros; try discriminate; auto.
  inversion H1; inversions H0.
  constructor.
    apply* (IHXs Vs).
    intro; intros. apply* (H x).
    unfold binds; simpl.
    destruct (x == a). subst.
      elim (binds_fresh H2 H7).
    apply H2.
  apply (H a). apply (binds_head a a0 (combine Xs Vs)).
Qed.

Lemma get_bvar_subst : forall (A:Set) X (K:Env.env A) m n,
  get X (bvar_subst n K) = Some (typ_bvar m) ->
  get X (bvar_subst (S n) K) = Some (typ_bvar (S m)).
Proof.
  induction K; simpl; intros. discriminate.
  destruct a. simpl in *.
  destruct (X == v). inversion* H.
  apply* IHK.
Qed.

Lemma bvar_subst_bvar : forall (A:Set) (K:Env.env A) n,
  env_prop (fun x => exists m, x = typ_bvar m) (bvar_subst n K).
Proof.
  induction K; simpl; intros; intro; intros.
    elim (binds_empty H).
  unfold binds in H; destruct a; simpl in H.
  destruct (x==v). inversions H; exists* n.
  apply (IHK (S n) x). apply H.
Qed.

Lemma get_bvar_subst_none : forall (A:Set) X (K:Env.env A) n,
  get X (bvar_subst n K) = None ->
  get X (bvar_subst (S n) K) = None.
Proof.
  induction K; simpl; intros. auto.
  destruct a. simpl in *.
  destruct (X == v). discriminate.
  apply* IHK.
Qed.

Lemma kinds_reopen_weaker : forall K1 Ks Xs,
  let S := bvar_subst 0 (K1 & kinds_open_vars Ks Xs) in
  let Ks' := List.map (kind_subst S) (list_snd K1) in
  length Ks = length Xs ->
  kenv_ok (K1 & kinds_open_vars Ks Xs) ->
  kinds_open_vars (Ks ++ Ks') (Xs ++ list_fst K1) = K1 & kinds_open_vars Ks Xs.
Proof.
  intros.
  unfold kinds_open_vars, kinds_open, concat.
  rewrite map_app.
  rewrite combine_app.
  apply app_eq.
    apply (f_equal (combine(B:=kind) Xs)).
    destruct H0.
      assert (list_forall (fun o => All_kind_types type o /\ kind_ok o)
                (kinds_open Ks (typ_fvars Xs))).
        apply* env_prop_list_forall.
        intro; intros.
        apply (H1 x).
        apply binds_prepend. unfold kinds_open_vars; apply H2.
        destruct (ok_concat_inv _ _ H0). apply H3.
        unfold kinds_open. rewrite* map_length.
      clear -H2.
      unfold kinds_open in H2.
      unfold typ_fvars; rewrite map_app.
      induction Ks; simpl in *. auto.
      inversions H2.
      destruct H3.
      rewrite* <- kind_open_extra.
      rewrite* IHKs.
    unfold Ks'.
    rewrite map_map.
    pattern K1 at 4. rewrite <- (combine_fst_snd K1).
    apply (f_equal (combine (B:=kind) (list_fst K1))).
    destruct H0.
    clear Ks'.
    assert (list_forall (All_kind_types type) (list_snd K1)).
      apply* env_prop_list_forall.
        intro; intros.
        rewrite <- (combine_fst_snd K1) in H1.
        destruct* (H1 x a).
        apply binds_concat_ok. apply H2. rewrite* combine_fst_snd.
       rewrite combine_fst_snd. destruct* (ok_concat_inv _ _ H0).
      unfold list_fst, list_snd; repeat rewrite* map_length.
    induction (list_snd K1); simpl. auto.
    inversions H2; rewrite* IHl.
    apply (f_equal (fun x => x::l)).
    clear -H6 H.
    destruct a as [[kc kr]|].
      unfold All_kind_types in H6.
      simpl in *.
      apply (f_equal (fun x => Some (Kind kc x))).
      induction kr; simpl in *. auto.
      destruct H6; rewrite* IHkr.
      clear IHkr; destruct a.
      simpl in *; apply (f_equal (fun x => (v,x)::kr)).
      clear H1 kr kc v.
      induction H0; simpl.
        unfold S. clear S.
        unfold kinds_open_vars.
        set (Us:=typ_fvars Xs); clearbody Us.
        gen Ks; induction Xs; destruct Ks; simpl; intros; try discriminate.
          induction K1; simpl. auto.
          destruct a; simpl.
          destruct (X == v). subst. simpl*.
          case_eq (get X (bvar_subst 0 K1)); intros.
            rewrite H0 in IHK1.
            destruct (bvar_subst_bvar _ _ H0). subst.
            rewrite (get_bvar_subst X K1 0 H0).
            simpl*.
          rewrite* (get_bvar_subst_none _ _ _ H0).
        destruct (X==a).
          subst; simpl*.
        inversion H; clear H.
        use (IHXs Ks H1); clear IHXs.
        case_eq (get X (bvar_subst 0 (K1 & combine Xs (kinds_open Ks Us))));
          intros.
          destruct (bvar_subst_bvar _ _ H0). subst.
          rewrite (get_bvar_subst _ _ _ H0).
          rewrite H0 in H.
          simpl*.
        rewrite* (get_bvar_subst_none _ _ _ H0).
      congruence.
    simpl*.
  rewrite* map_length.
Qed.

Lemma typing_remove_gc : forall gc K E t T,
  K ; E |gc|= t ~: T ->
  forall LK F,
    env_weaker E F -> ok F ->
    exists K',
      disjoint (dom K') LK /\ K & K' ; F |(false,GcAny)|= t ~: T.
Proof.
  induction 1; intros.
  (* Var *)
  destruct M as [U Ks].
  destruct (H3 x _ _ H1) as [Ks' [HS HB]]. destruct* H2.
  destruct (var_freshes (LK \u dom K) (length Ks')) as [Xs Fr].
  exists (combine Xs (kinds_open Ks' (Us ++ typ_fvars Xs))).
  assert (dom (A:=kind) (combine Xs (kinds_open Ks' (Us ++ typ_fvars Xs)))
             = mkset Xs).
    rewrite* mkset_dom. unfold kinds_open.
    rewrite map_length. rewrite* (fresh_length _ _ _ Fr).
  split.
    rewrite H5. apply* (fresh_disjoint (length Ks')).
  replace (sch_open (Sch U Ks) Us)
    with (sch_open (Sch U (Ks++Ks')) (Us ++ typ_fvars Xs)).
    apply* typing_var.
      destruct H.
      split.
        apply* disjoint_ok. apply* ok_combine_fresh.
        apply disjoint_comm. rewrite H5; apply* (fresh_disjoint (length Ks')).
      intro; intros.
      binds_cases H7. apply* (H6 x0).
      eapply env_weaker_ok.
            destruct H2. unfold sch_arity in H2; simpl in H2.
            apply H2.
          apply (fresh_length _ _ _ Fr).
        apply HS.
      apply (binds_combine _ _ B0).
    split.
      destruct (proj1 H2).
      split.
        rewrite app_length; rewrite <- H6.
        unfold sch_arity; simpl. rewrite app_length.
        rewrite (fresh_length _ _ _ Fr).
        unfold typ_fvars; rewrite* map_length.
      clear -H7; induction Us; simpl; inversion* H7.
      induction Xs; simpl*.
    split*.
    apply* well_kinded_combine2.
  unfold sch_open. simpl.
  assert (K; E |gc|= trm_fvar x ~: (Sch U Ks) ^^ Us) by auto.
  assert (type ((Sch U Ks) ^^ Us)) by auto. auto.
  unfold sch_open in H7. simpl in H7.
  rewrite* (typ_open_extra Us (typ_fvars Xs)).
  (* Abs *)
  clear H0 gc.
  destruct (var_fresh (L \u trm_fv t1 \u dom F)) as [x Hx].
  assert (Hx' : x \notin L) by auto.
  assert (HF : env_weaker (E & x ~ Sch U nil) (F & x ~ Sch U nil)).
    intro; intros.
    binds_cases H0.
      destruct (H2 x0 T0 Ks B H4) as [Ks' [HS HB]].
      exists Ks'; split*.
    exists (nil(A:=kind)). 
    rewrite <- app_nil_end. auto.
  destruct (H1 x Hx' LK _ HF) as [K' [HD Typ]]; clear H1 Hx'.
    auto.
  exists K'; split*.
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
  destruct* (H0 Xs HXs' (LK \u mkset Xs \u dom K \u fv_in kind_fv K) _ H3)
    as [K1 [HD1 Typ1]].
  clear H H0 H1 H5 HXs'.
  use (kenv_ok_swap K (kinds_open_vars (sch_kinds M) Xs) K1
          (proj41 (typing_regular Typ1))).
  poses Typ1a (typing_kenv_incl Typ1 (env_incl_swap _ _ _ (proj1 H)) H).
  clear Typ1 H.
  pose (S := bvar_subst 0 (K1 & kinds_open_vars (sch_kinds M) Xs)).
  pose (Ks' := List.map (kind_subst S) (list_snd K1)).
  destruct M as [U Ks].
  destruct (var_fresh (L2 \u trm_fv t2 \u dom F)) as [x Hx].
  assert (env_weaker (E & x ~ Sch U Ks) (F & x ~ Sch U (Ks++Ks'))).
    apply* env_weaker_push.
          
          
        
    induction (list_snd

Search list_forall.

Lemma scheme_weaker_let : forall K1 Ks Xs U,
  let S := bvar_subst 0 (K1 & kinds_open_vars Ks Xs) in
  let Ks' := List.map (kind_subst S) (list_snd K1) in
  length Ks = length Xs ->
  kenv_ok (K1 & kinds_open_vars Ks Xs) ->
  scheme (Sch U Ks) -> scheme (Sch U (Ks ++ Ks')).
Proof.
  intros.
  destruct H1; split.
    clear H2; destruct H1 as [LS HS].
    exists LS; intros. simpl in *.
    rewrite app_length in H1.
    destruct (app_length_inv (n:=length Ks) Xs0) as [Ys [Ys' [HYs Heq]]].
      rewrite <- (fresh_length _ _ _ H1).  omega.
    subst.
    unfold typ_open_vars, typ_fvars. rewrite map_app.
    unfold typ_open_vars, typ_fvars in HS.
    destruct (HS Ys); clear HS. apply* fresh_app_firsts.
    split.
      rewrite* <- typ_open_extra.
    apply list_forall_app.
      clear -H3. induction H3; simpl; auto.
      constructor. auto.
      clear -H; unfold All_kind_types in *.
      induction (kind_types x); simpl in *; auto.
      destruct H; split*.
      rewrite* <- typ_open_extra.
    destruct H0.
    clear H2 H3.
Lemm
    
    
Qed.
    split.
      exists (dom K).
      simpl.
      intros.
      split.
        
        
  assert (Hx': x \notin L2) by auto.
  destruct (H2 x Hx' LK) as [K2 [HD2 Typ2]]; clear H2 Hx'.
Lemma typing_remove_gc_let : forall x L2 t2 K2 LK E M T2 L1 K Xs K1 t1,
  x \notin L2 \u trm_fv t2 ->
  disjoint (dom K2) LK ->
  K & K2; E & x ~ M | (false, GcAny) |= t2 ^ x ~: T2 ->
  fresh (L1 \u env_fv E \u sch_fv M \u dom K \u dom K2 \u
         fv_in kind_fv (K & K2)) (sch_arity M) Xs ->
  disjoint (dom K1) (LK \u mkset Xs \u dom K2 \u fv_in kind_fv K2) ->
  K & kinds_open_vars (sch_kinds M) Xs & K1; E
    |(false, GcAny)|= t1 ~: sch_open_vars M Xs ->
  exists K' : kenv,
    disjoint (dom K') LK /\ K & K'; E |(false, GcAny)|= trm_let t1 t2 ~: T2.
Proof.
  intros until t1; intros Hx HD2 Typ2 HXs HD1 Typ1.
  exists (K1 & K2).
  split.
    rewrite dom_concat. rewrite fv_in_concat in *.
    intro v. destruct* (HD2 v).
    destruct* (HD1 v).
  rewrite <- concat_assoc.
  assert (Hok: kenv_ok (K & K1 & K2 & kinds_open_vars (sch_kinds M) Xs)).
    rewrite concat_assoc.
    apply kenv_ok_swap.
    rewrite <- concat_assoc.
    rewrite concat_assoc.
    apply* kenv_ok_merge.
      rewrite <- concat_assoc.
      apply (proj41 (typing_regular Typ1)).
    rewrite dom_concat.
    rewrite dom_kinds_open_vars.
      intro v; destruct* (fresh_disjoint _ _ _ HXs v).
      destruct* (HD1 v).
    unfold sch_arity in HXs; apply* fresh_length.
  apply* (@typing_let (false,GcAny) M (L1 \u dom (K & K1 & K2) \u mkset Xs)
              (L2 \u dom E \u trm_fv t2 \u {{x}})).
    intros.
    apply* (@typing_rename_typ E M (K&K1&K2) Xs Xs0).
        repeat rewrite dom_concat.
        rewrite (fresh_length _ _ _ HXs) in *.
        apply* disjoint_fresh.
        repeat rewrite fv_in_concat in *.
        intro v; destruct* (fresh_disjoint _ _ _ HXs v).
        clear -H0 HD1.
        destruct* (HD1 v).
      rewrite* <- (fresh_length _ _ _ HXs).
    apply* typing_kenv_incl.
    intro; intros.
    destruct (ok_concat_inv _ _ (proj1 Hok)) as [Hok1 _].
    binds_cases H0. repeat apply* binds_concat_ok.
      apply* binds_prepend.
    do 2 apply* binds_concat_ok.
  intros.
  destruct (kenv_ok_concat_inv _ _ Hok).
  apply* typing_weaken_kinds.
  replace (E & x0 ~ M) with (E & x0 ~ M & empty) by (simpl; auto).
  rewrite* (@trm_subst_intro x t2 (trm_fvar x0)).
  apply* typing_rename.
  assert (x0 \notin trm_fv (t2 ^ x)).
    apply* (notin_subset (trm_fv_open (trm_fvar x) t2 0)).
    simpl; auto.
  simpl; auto.
Qed.
  apply* typing_remove_gc_let.
  (* App *)
  clear H H0.
  destruct (IHtyping1 LK) as [K1 [D1 Typ1]].
  destruct (IHtyping2 (LK \u dom K1)) as [K2 [D2 Typ2]].
  exists (K1 & K2).
  rewrite <- concat_assoc.
  split.
    rewrite dom_concat. rewrite fv_in_concat.
    intro v; destruct* (D1 v). destruct* (D2 v).
  assert (kenv_ok (K&K1&K2)).
    apply* kenv_ok_merge. intro v; destruct* (D2 v).
  apply* typing_app.
    simpl; apply* typing_weaken_kinds'.
  apply* typing_weaken_kinds.
  (* GC *)
  set (M := Sch T Ks).
  destruct (var_freshes (L \u sch_fv M) (length Ks)) as [Xs Fr].
  assert (fresh L (length Ks) Xs) by auto.
  destruct (H1 Xs H2 LK) as [K' [DK' Typ]].
  destruct (var_freshes (L \u sch_fv M \u LK) (length Ks)) as [Xs' Fr'].
  exists (K' & kinds_open_vars Ks Xs').
  rewrite dom_concat; rewrite <- concat_assoc.
  rewrite fv_in_concat.
  split.
    intro v; destruct* (DK' v).
    rewrite dom_kinds_open_vars.
      destruct* (fresh_disjoint _ _ _ Fr' v).
      left; notin_simpls; auto.
      apply* (notin_subset (fv_in_kinds_open_vars Ks Xs')).
      
  
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
*)

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
