(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - June 2008                               *
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

Hint Immediate disjoint_ok.

Lemma kenv_ok_concat : forall K1 K2,
  kenv_ok K1 -> kenv_ok K2 -> disjoint (dom K1) (dom K2) -> kenv_ok (K1 & K2).
Proof.
  intros.
  destruct H; destruct H0.
  split*.
Qed.

Lemma env_ok_concat : forall E1 E2,
  env_ok E1 -> env_ok E2 -> disjoint (dom E1) (dom E2) -> env_ok (E1 & E2).
Proof.
  intros.
  destruct H; destruct H0.
  split*.
Qed.

Definition kenv_ok_def K H1 H2 : kenv_ok K := conj H1 H2.
Definition env_ok_def E H1 H2 : env_ok E := conj H1 H2.

Lemma kenv_ok_merge : forall (K K1 K2 : kenv),
  kenv_ok (K & K1) ->
  kenv_ok (K & K2) ->
  disjoint (dom K1) (dom K2) -> kenv_ok (K & K1 & K2).
Proof.
  intros.
  destruct (kenv_ok_concat_inv _ _ H0).
  apply* kenv_ok_concat.
  rewrite* dom_concat.
  disjoint_solve.
Qed.

Hint Resolve kenv_ok_merge.

Lemma env_ok_remove : forall F E G,
  env_ok (E & F & G) -> env_ok (E & G).
Proof.
  split*.
  destruct (env_ok_concat_inv _ _ H).
  destruct* (env_ok_concat_inv _ _ H0).
Qed.

Lemma kenv_ok_remove : forall F E G,
  kenv_ok (E & F & G) -> kenv_ok (E & G).
Proof.
  split*.
  destruct (kenv_ok_concat_inv _ _ H).
  destruct* (kenv_ok_concat_inv _ _ H0).
Qed.

Hint Immediate env_ok_remove kenv_ok_remove.

Lemma ok_kinds_open_vars : forall K Ks Xs,
  ok K -> fresh (dom K) (length Ks) Xs ->
  ok (K & kinds_open_vars Ks Xs).
Proof.
  intros.
  unfold kinds_open_vars.
  apply* disjoint_ok.
    apply* ok_combine_fresh.
  rewrite dom_combine.
    apply* fresh_disjoint.
  unfold kinds_open. rewrite map_length.
  symmetry; auto*.
Qed.

Hint Resolve ok_kinds_open_vars.

(* ********************************************************************** *)
(** Typing is preserved by weakening *)

Lemma typing_weaken : forall gc G E F K t T,
   K ; (E & G) |gc|= t ~: T -> 
   env_ok (E & F & G) ->
   K ; (E & F & G) |gc|= t ~: T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* (@typing_abs gc) as y. apply_ih_bind* H1.
    forward~ (H0 y) as Q.
    destruct (env_ok_concat_inv _ _ (proj42 (typing_regular Q))). split*.
  apply_fresh* (@typing_let gc M L1) as y. apply_ih_bind* H2.
    forward~ (H1 y) as Q.
    destruct (env_ok_concat_inv _ _ (proj42 (typing_regular Q))). split*.
  auto*.
  auto.
  apply_fresh* (@typing_gc gc Ks) as y.
Qed.

Lemma proper_instance_weaken : forall K K' K'' Ks Us,
  ok (K & K' & K'') ->
  proper_instance (K & K'') Ks Us ->
  proper_instance (K & K' & K'') Ks Us.
Proof.
  intros.
  destruct* H0 as [TM FM]; split*.
  rewrite <- list_map_id.
  rewrite <- (list_map_id (kinds_open Ks Us)).
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
    rewrite concat_assoc.
    apply* H0; clear H0. rewrite* concat_assoc.
    rewrite <- concat_assoc.
    split*.
    apply* env_prop_concat.
    puts (typing_regular (H Xs (proj1 (fresh_union_r _ _ _ _ H3)))).
    use (proj2 (proj41 H0)).
  apply* typing_app.
  apply* typing_cst. apply* proper_instance_weaken.
  apply_fresh* (@typing_gc gc Ks) as y.
  intros.
  rewrite concat_assoc.
  apply* (H1 Xs); clear H1.
    rewrite* concat_assoc.
  rewrite* <- concat_assoc.
  forward~ (H0 Xs) as Typ; clear H0.
  split. apply* ok_kinds_open_vars. repeat rewrite dom_concat. auto.
  apply* env_prop_concat.
  destruct* (kenv_ok_concat_inv _ _ (proj41 (typing_regular Typ))).
Qed.

Lemma typing_weaken_kinds' : forall gc K K' E t T,
  kenv_ok (K & K') ->
  K ; E |gc|= t ~: T -> K & K' ; E |gc|= t ~: T.
Proof.
  intros.
  replace (K & K') with (K & K' & empty) by simpl*.
  apply* typing_weaken_kinds.
Qed.

Lemma proper_instance_subst : forall K K' K'' Ks Us S,
  env_prop type S ->
  proper_instance (K & K' & K'') Ks Us ->
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  proper_instance (K & map (kind_subst S) K'') (List.map (kind_subst S) Ks)
    (List.map (typ_subst S) Us).
Proof.
  introv TS PI WS.
  destruct* PI.
  split. rewrite map_length. apply* typ_subst_type_list.
  rewrite* <- kinds_subst_open.
  apply* For_all2_map. intros.
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
    rewrite* dom_kinds_open_vars. disjoint_solve.
  intro x; intros.
  rewrite map_concat. rewrite <- concat_assoc.
  destruct* (binds_concat_inv H) as [[N B]|B]; clear H.
    apply* well_kinded_extend.
    rewrite dom_map. rewrite dom_concat; rewrite* dom_map.
  destruct k; try constructor.
  simpl. rewrite get_notin_dom.
    apply* wk_kind. apply* binds_prepend.
      use (binds_map (kind_subst S) B).
    apply entails_refl.
  intro; elim (binds_fresh B); clear B.
  rewrite* dom_kinds_open_vars.
  assert (disjoint (dom S) (mkset Ys)) by disjoint_solve.
  destruct* (H0 x).
Qed.

Lemma All_kind_types_subst : forall k S,
  All_kind_types type k ->
  env_prop type S -> All_kind_types type (kind_subst S k).
Proof.
  intros; unfold kind_subst; apply All_kind_types_map.
  apply* All_kind_types_imp.
Qed.

Hint Resolve All_kind_types_subst.

Lemma kenv_ok_subst : forall K K' K'' S,
  env_prop type S ->
  kenv_ok (K & K' & K'') -> kenv_ok (K & map (kind_subst S) K'').
Proof.
  introv HS H. split*.
  intro; intros. destruct H.
  destruct (in_app_or _ _ _ H0).
    destruct (in_map_inv _ _ _ _ H2) as [b [Hb B]].
    subst*.
  apply* (H1 x).
Qed.

Lemma env_ok_subst : forall E E' S,
  env_prop type S ->
  env_ok (E & E') -> env_ok (E & map (sch_subst S) E').
Proof.
  introv HS H. split*.
  intro; intros. destruct H.
  destruct (in_app_or _ _ _ H0).
    destruct (in_map_inv _ _ _ _ H2) as [b [Hb B]].
    subst*.
  apply* (H1 x).
Qed.

Hint Resolve env_ok_subst.

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
       rewrite* sch_subst_fresh. use (fv_in_spec sch_fv _ _ _ (binds_in B)).
       intro v. destruct* (Dis v).
       destruct* (proj1 (notin_union _ _ _) H3).
      auto*.
    destruct M as [T Ks]. simpl.
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
   rewrite map_length in Fr.
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
  destruct (Delta.type c) as [T Ks]; simpl.
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
  apply* TTS; clear TTS. disjoint_solve.
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
  fresh (kind_fv_list Ks) (length Xs) Xs ->
  types (length Xs) Vs ->
  forall k : kind,
    In k Ks ->
    kind_open k Vs = kind_subst (combine Xs Vs) (kind_open k (typ_fvars Xs)).
Proof.
  introv Fr. intros.
  destruct H.
  rewrite* kind_subst_open.
  rewrite* kind_subst_fresh.
    rewrite* (fresh_subst {}).
    rewrite* <- H.
  rewrite* dom_combine.
  apply disjoint_comm.
  apply (fresh_disjoint (length Xs)).
  apply* (kind_fv_fresh k Ks).
Qed.

Lemma well_subst_open_vars : forall (K:kenv) Vs (Ks:list kind) Xs,
  fresh (fv_in kind_fv K) (length Ks) Xs ->
  fresh (kind_fv_list Ks) (length Xs) Xs ->
  types (length Xs) Vs ->
  For_all2 (well_kinded K) (kinds_open Ks Vs) Vs ->
  well_subst (K & kinds_open_vars Ks Xs) K (combine Xs Vs).
Proof.
  introv Fr Fr' TV WK.
  intro x; intros.
  destruct* (binds_concat_inv H) as [[N B]|B]; clear H.
    unfold kinds_open_vars in N.
    rewrite* kind_subst_fresh.
      simpl.
      rewrite* get_notin_dom.
        destruct* k.
        eapply wk_kind. apply B.
        apply entails_refl.
      rewrite dom_combine in N.
        rewrite* dom_combine.
      unfold kinds_open, typ_fvars. rewrite* map_length.
    rewrite* dom_combine.
    apply disjoint_comm.
    apply* (fresh_disjoint (length Ks)).
    apply (fresh_sub (length Ks) Xs Fr (fv_in_spec kind_fv _ _ _ (binds_in B))).
  unfold kinds_open_vars, kinds_open in *.
  rewrite <- map_combine in B.
  destruct (binds_map_inv _ _ B) as [k0 [Hk0 Bk0]]. subst.
  puts (binds_map (kind_subst (combine Xs Vs)) B).
  simpl in H; do 2 rewrite map_combine in H.
  rewrite list_map_comp in H.
  apply* (For_all2_get (well_kinded K) Xs).
    rewrite* (list_map_ext Ks _ _ (kind_subst_open_combine _ _ Fr' TV)).
  simpl; case_eq (get x (combine Xs Vs)); intros. auto.
  elim (get_contradicts _ _ _ _ Bk0 H0); auto.
Qed.

Lemma has_scheme_from_vars : forall gc L K E t M,
  has_scheme_vars gc L K E t M ->
  has_scheme gc K E t M.
Proof.
  intros gc L K E t [T Ks] H Vs TV. unfold sch_open. simpls.
  fold kind in K. fold kenv in K.
  pick_freshes (length Ks) Xs.
  rewrite (fresh_length _ _ _ Fr) in TV.
  rewrite~ (@typ_subst_intro Xs Vs T).
  unfolds has_scheme_vars sch_open_vars. simpls.
  intro WK.
  apply* (@typing_typ_substs gc (kinds_open_vars Ks Xs)).
      rewrite* dom_combine. disjoint_solve.
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
     puts (proj41 (typing_regular (H Xs H3))).
     apply* kenv_ok_merge.
     repeat rewrite* dom_kinds_open_vars.
     disjoint_solve.
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H2.
  assert (exists L : vars, has_scheme_vars (gc,GcAny) L K E u M). exists* Lu.
  auto*.
  auto*.
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
   apply* kenv_ok_merge.
   repeat rewrite* dom_kinds_open_vars. disjoint_solve.
Qed.

(* ********************************************************************** *)
(** Canonical derivations *)

(* less than 100 lines! *)

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

(* End of canonical derivations *)

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
    exists {}. intro. unfold kinds_open_vars, sch_open_vars; simpl.
    destruct* Xs. simpl. rewrite* typ_open_vars_nil.
    simpl. intuition.
  apply* (@typing_gc (gc,GcAny) Ks L).
  intros.
  use (H0 Xs H2); clear H0.
  apply* H1.
  apply* typing_weaken_kinds'.
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
