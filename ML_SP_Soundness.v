(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - June 2008                               *
***************************************************************************)

Set Implicit Arguments.
Require Import Arith List Metatheory 
  ML_SP_Definitions ML_SP_Infrastructure.

Module MkSound(Cstr:CstrIntf)(Const:CstIntf).

Module Infra := MkInfra(Cstr)(Const).
Import Infra.
Import Defs.

Module Mk2(Delta:DeltaIntf).
Module JudgInfra := MkJudgInfra(Delta).
Import JudgInfra.
Import Judge.

Lemma kenv_ok_concat : forall K1 K2,
  kenv_ok K1 -> kenv_ok K2 -> disjoint (dom K1) (dom K2) -> kenv_ok (K1 & K2).
Proof. auto. Qed.

Lemma ok_kinds_open_vars : forall K Ks Xs,
  ok K -> fresh (dom K) (length Ks) Xs ->
  ok (K & kinds_open_vars Ks Xs).
Proof.
  intros.
  unfold kinds_open_vars.
  apply* disjoint_ok.
  apply* ok_combine_fresh.
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
  apply_fresh* (@typing_let gc M L1) as y. apply_ih_bind* H2.
    forward~ (H1 y) as Q.
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
    forward~ (H Xs) as Typ.
  apply* typing_app.
  apply* typing_cst. apply* proper_instance_weaken.
  apply_fresh* (@typing_gc gc Ks) as y.
  intros.
  rewrite concat_assoc.
  apply* (H1 Xs); clear H1.
    rewrite* concat_assoc.
  forward~ (H0 Xs) as Typ; clear H0.
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
Qed.

Lemma well_subst_fresh : forall K K' K'' S Ys Ks,
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  fresh (dom S \u dom K \u dom K'') (length Ks) Ys ->
  well_subst (K & K' & K'' & kinds_open_vars Ks Ys)
    (K & map (kind_subst S) (K'' & kinds_open_vars Ks Ys)) S.
Proof.
  introv WS Fr.
  assert (KxYs: disjoint (dom K \u dom K'')
                         (dom (kinds_open_vars Ks Ys))) by auto.
  intro x; intros.
  rewrite map_concat. rewrite <- concat_assoc.
  destruct* (binds_concat_inv H) as [[N B]|B]; clear H.
  destruct k; try constructor.
  simpl. rewrite get_notin_dom by auto.
  puts (binds_map (kind_subst S) B).
  apply* wk_kind.
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
  introv HS H.
  kenv_ok_solve. auto.
  intro; intros.
  destruct (in_map_inv _ _ _ _ H1) as [b [Hb B]].
  subst*.
Qed.

Lemma env_ok_subst : forall E E' S,
  env_prop type S ->
  env_ok (E & E') -> env_ok (E & map (sch_subst S) E').
Proof.
  introv HS H.
  env_ok_solve. auto.
  intro; intros.
  destruct (in_map_inv _ _ _ _ H0) as [b [Hb B]].
  subst*.
Qed.

Hint Resolve kenv_ok_subst env_ok_subst.

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
    binds_cases H1.
      apply* binds_concat_fresh.
      rewrite* sch_subst_fresh.
      use (fv_in_spec sch_fv _ _ _ (binds_in B)).
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
  apply* TTS.
Qed.
  
(* ********************************************************************** *)
(** Typing schemes for expressions *)

Definition has_scheme_vars gc L (K:kenv) E t M := forall Xs,
  fresh L (sch_arity M) Xs ->
  K & kinds_open_vars (sch_kinds M) Xs; E |gc|= t ~: (M ^ Xs).

Definition has_scheme gc K E t M := forall Vs,
  types (sch_arity M) Vs ->
  list_forall2 (well_kinded K) (kinds_open (sch_kinds M) Vs) Vs ->
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
  use (kind_fv_fresh _ _ _ _ H0 Fr).
Qed.

Lemma well_subst_open_vars : forall (K:kenv) Vs (Ks:list kind) Xs,
  fresh (fv_in kind_fv K) (length Ks) Xs ->
  fresh (kind_fv_list Ks) (length Xs) Xs ->
  types (length Xs) Vs ->
  list_forall2 (well_kinded K) (kinds_open Ks Vs) Vs ->
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
    use (fv_in_spec kind_fv _ _ _ (binds_in B)).
  unfold kinds_open_vars, kinds_open in *.
  rewrite <- map_combine in B.
  destruct (binds_map_inv _ _ B) as [k0 [Hk0 Bk0]]. subst.
  puts (binds_map (kind_subst (combine Xs Vs)) B).
  simpl in H; do 2 rewrite map_combine in H.
  rewrite list_map_comp in H.
  refine (list_forall2_get (P:=well_kinded K) Xs _ H _).
    instantiate (1:=Vs).
    rewrite* <- (list_map_ext Ks _ _ (kind_subst_open_combine _ _ Fr' TV)).
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
     forward~ (Typu Ys) as Typu'; clear Typu.
     apply* typing_weaken_kinds.
     forward~ (H Xs).
   rewrite* trm_subst_open_var.
   apply_ih_bind* H2.
  assert (exists L : vars, has_scheme_vars (gc,GcAny) L K E u M). exists* Lu.
  auto*.
  auto*.
  apply_fresh* (@typing_gc (gc,GcAny) Ks) as y.
   intros Xs Fr.
   apply* H1; clear H1.
   exists (Lu \u dom K \u mkset Xs); intros Ys Fr'.
   forward~ (Typu Ys) as Typu'; clear Typu.
   apply* typing_weaken_kinds.
   forward~ (H0 Xs).
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
      destruct* (H Xs HXs).
    intros; subst.
    apply* (@typing_gc (true,GcLet) Ks L).
      simpl; auto.
    intros.
    destruct (H Xs H0); clear H.
    apply* H3; clear H3.
    apply* typing_weaken_kinds'.
  split.
    destruct (var_freshes L (length Ks)) as [Xs HXs].
    destruct* (H Xs HXs).

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
  Parameter delta_typed : forall c tl vl K E gc T,
    K ; E |(false,gc)|= const_app c tl ~: T ->
    K ; E |(false,gc)|= @Delta.reduce c tl vl ~: T.
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
    destruct Xs; simpl*. rewrite* typ_open_vars_nil.
  apply* (@typing_gc (gc,GcAny) Ks L).
  intros.
  puts (H0 Xs H2); clear H0.
  apply* H1.
  apply* typing_weaken_kinds'.
Qed.

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen_eq (true, GcAny) as gc. gen t'.
  induction Typ; introv EQ Red; subst; inversions Red;
    try solve [apply* typing_gc];
    try (destruct (const_app_inv c tl) as [eq | [T1' [T2' eq]]];
         rewrite eq in *; discriminate).
  (* Let *)
  pick_fresh x. rewrite* (@trm_subst_intro x). 
   apply_empty* (@typing_trm_subst true).
  (* Let *)
  apply* (@typing_let (true,GcAny) M L1).
  (* Beta *)
  apply* typing_abs_inv.
  (* Delta *)
  assert (K;E |(true,GcAny)|= trm_app t1 t2 ~: T) by auto*.
  use (typing_canonize H).
  fold (typing_gc_let K E (trm_app t1 t2) T) in H1.
  rewrite <- H0 in *.
  clear -H1.
  gen_eq (const_app c tl) as t1.
  induction H1 using typing_gc_ind; intros; subst.
    apply* typing_gc_any.
    apply* delta_typed.
  apply* typing_gc. simpl*.
  (* App1 *)
  auto*.
  (* App2 *)
  auto*.
  (* Delta/cst *)
  apply* (@typing_gc_any (false,GcAny)).
  apply* delta_typed.
  rewrite* H3.
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
  unfold const_app in *.
  rewrite Heq in *.
  change (exists t', fold_left trm_app (t2::nil) (const_app c vl) --> t').
  unfold const_app; rewrite <- fold_left_app.
  assert (list_for_n value (S(Const.arity c)) (vl ++ t2 :: nil)).
    split*. apply* list_forall_app.
  exists (Delta.reduce H2).
  apply red_delta.
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
  destruct~ IHTyp2 as [Val2 | [t2' Red2]].
    destruct~ IHTyp1 as [Val1 | [t1' Red1]]. 
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
          assert (list_for_n value 1 (t2 :: nil)) by split*.
          rewrite <- H0 in H1.
          exists (Delta.reduce H1).
          apply (red_delta H1).
        left. exists n. rewrite H0 in Val1. destruct* Val2.
        destruct n.
          right; apply* progress_delta.
        left. destruct Val2. exists* n.
      destruct (var_freshes L (length Ks)) as [Xs HXs].
      destruct* (H Xs); clear H.
      right; exists* (trm_app t1' t2).
    right; exists* (trm_app t1 t2').
  left; exists* (Const.arity c).
  destruct (var_freshes L (length Ks)) as [Xs HXs].
  apply* (H1 Xs).
Qed.

Lemma value_irreducible : forall t t',
  value t -> ~(t --> t').
Proof.
  induction t; introv HV; destruct HV as [k HV']; inversions HV';
    intro R; inversions R.
       destruct (const_app_inv c tl) as [eq | [t1' [t2' eq]]];
         rewrite eq in *; discriminate.
      inversions H2.
     destruct (value_app_const HV').
     destruct H as [vl' [Hl [He Hv]]].
     rewrite He in H0; clear He.
     destruct (const_app_eq _ _ _ _ H0). subst.
     clear -vl Hl; destruct vl.
     omega.
    elim (IHt1 t1'). exists* (S k). auto.
   elim (IHt2 t2'). exists* n2. auto.
  clear -vl H0.
  destruct vl.
  destruct (const_app_inv c0 tl) as [eq | [t1' [t2' eq]]];
    rewrite eq in *; discriminate.
Qed.

End Mk3.

End Mk2.

End MkSound.
