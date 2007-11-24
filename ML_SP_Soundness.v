(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007                                           *
***************************************************************************)

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

Set Implicit Arguments.

(** Extra hypotheses *)

Definition const_arg_inst K E Ks Us tl t T :=
  proper_instance K (Sch T Ks) Us /\
  K ; E |= trm_inst t tl ~: (Sch T Ks) ^^ Us.

Module Type SndHypIntf.
  Parameter const_closed : forall c, sch_fv (delta_scheme c) = {}.
  Parameter delta_typed : forall n c tl1 t2 tl K E Us,
    Delta.rule n c tl1 t2 ->
    list_for_n term n tl ->
    kenv_ok K ->
    ok E ->
    let (M, TL) := Delta.type c in
    proper_instance K M Us ->
    For_all2 (const_arg_inst K E (sch_kinds M) Us tl) tl1 TL ->
    K ; E |= trm_inst t2 tl ~: M ^^ Us.
  Parameter const_arity_ok : forall c vl K T,
    list_for_n value (S(Const.arity c)) vl ->
    K ; empty |= const_app c vl ~: T ->
    exists n, exists tl1, exists t2, exists tl,
      Delta.rule n c tl1 t2 /\ list_for_n term n tl /\
      For_all2 (fun v t1 => v = trm_inst t1 tl) vl tl1.
  (*
  Parameter delta_arity : forall n t1 t2,
    Delta.rule n t1 t2 ->
    exists c, exists pl, t1 = const_app c pl /\ length pl = S(Const.arity c).
  *)
End SndHypIntf.

Module Mk3(SH:SndHypIntf).
Import SH.

(* ********************************************************************** *)
(** Type substitution preserves typing *)

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

Lemma well_subst_fresh : forall K K' K'' S Ys L1 K0,
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  fresh (L1 \u dom S \u dom (K & K'')) (length K0) Ys ->
  well_subst (K & K' & K'' & kinds_open_vars K0 Ys)
    (K & map (kind_subst S) (K'' & kinds_open_vars K0 Ys)) S.
Proof.
  introv WS Fr.
  assert (KxYs: disjoint (dom K \u dom K'') (dom (kinds_open_vars K0 Ys))).
    unfold kinds_open_vars.
    intro v.
    destruct* (in_vars_dec v (dom K \u dom K'')).
    right; intro.
    elim (fresh_rev _ _ Fr (x:=v)).
    rewrite* dom_concat. auto with sets.
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
  use (proj2 (fresh_union_r _ _ _ _ (proj1 (fresh_union_r _ _ _ _ Fr)))).
  intro. destruct* (fresh_rev _ _ H0 (x:=x)).
  apply (in_dom_combine _ _ H1).
Qed.

Lemma kenv_ok_subst : forall K K' K'' S,
  kenv_ok (K & K' & K'') -> kenv_ok (K & map (kind_subst S) K'').
Proof.
  intros. split*.
  intro; intros. destruct H.
  binds_cases H0. apply* (H1 x).
    apply* binds_concat_ok.
    apply* binds_concat_ok. destruct* (ok_concat_inv _ _ H).
  case_eq (get x K''); intros.
    use (binds_map (kind_subst S) H0).
    rewrite (binds_inj B0 H2).
    clear B0 a. destruct o. simpl.
      assert (Cstr.valid (kind_cstr c) /\ coherent c).
        apply (H1 x (Some c)).
        apply* binds_prepend.
      destruct c.
      split*.
    simpl*.
  elim (binds_fresh B0). apply get_none_notin. apply* map_get_none.
Qed.

Lemma typing_typ_subst : forall F K'' S K K' E t T,
  disjoint (dom S) (env_fv E \u fv_in kind_fv K) ->
  env_prop type S ->
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  K & K' & K''; E & F |= t ~: T -> 
  K & map (kind_subst S) K''; E & (map (sch_subst S) F) |= t ~: (typ_subst S T).
Proof.
  introv. intros Dis TS WS Typ.
  gen_eq (K & K' & K'') as GK; gen_eq (E & F) as G; gen K''; gen F.
  induction Typ; introv WS EQ EQ'; subst; simpls typ_subst.
  rewrite~ sch_subst_open. apply* typing_var.
    apply* kenv_ok_subst.
    binds_cases H1.
      apply* binds_concat_fresh.
       rewrite* sch_subst_fresh. use (fv_in_spec sch_fv B).
       intro v. destruct* (Dis v).
       destruct* (proj1 (notin_union _ _ _) H3).
      auto*.
    apply* proper_instance_subst.
  apply_fresh* typing_abs as y.
   assert (r: Sch (typ_subst S U) nil = sch_subst S (Sch U nil)); auto.
   rewrite r; apply_ih_map_bind* H1.
  apply_fresh* (@typing_let (sch_subst S M) (L1 \u dom S \u dom (K&K''))) as y.
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
  auto*.
  rewrite* sch_subst_open.
  assert (disjoint (dom S) (sch_fv (delta_scheme c))).
    intro x. rewrite* (const_closed c).
  rewrite* sch_subst_fresh.
  apply* typing_cst.
    apply* kenv_ok_subst.
  rewrite* <- (sch_subst_fresh S H2).
  apply* proper_instance_subst.
Qed.

Lemma typing_typ_substs : forall K' S K E t T,
  disjoint (dom S) (env_fv E \u fv_in kind_fv K \u dom K) -> 
  env_prop type S ->
  well_subst (K & K') K S ->
  K & K'; E |= t ~: T -> 
  K ; E |= t ~: (typ_subst S T).
Proof.
  intros.
  generalize (typing_typ_subst empty empty); intro TTS.
  simpl in TTS.
  apply* TTS; clear TTS.
    intro v; destruct* (H v).
Qed.
  
(* ********************************************************************** *)
(** Typing schemes for expressions *)

Definition has_scheme_vars L (K:kenv) E t M := forall Xs,
  fresh L (sch_arity M) Xs ->
  K & kinds_open_vars (sch_kinds M) Xs; E |= t ~: (M ^ Xs).

Definition has_scheme K E t M := forall Vs,
  types (sch_arity M) Vs ->
  For_all2 (well_kinded K) (kinds_open (sch_kinds M) Vs) Vs ->
  K ; E |= t ~: (M ^^ Vs).

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

Lemma has_scheme_from_vars : forall L K E t M,
  has_scheme_vars L K E t M ->
  has_scheme K E t M.
Proof.
  intros L K E t [T Ks] H Vs TV. unfold sch_open. simpls.
  fold kind in K. fold kenv in K.
  pick_freshes (length Ks) Xs.
  unfold sch_arity in TV; simpl in TV.
  rewrite (fresh_length _ _ _ Fr) in TV.
  rewrite~ (@typ_subst_intro Xs Vs T).
  unfolds has_scheme_vars sch_open_vars. simpls.
  intro WK.
  apply* (typing_typ_substs (kinds_open_vars Ks Xs)).
      rewrite* mkset_dom.
      apply* (fresh_disjoint (length Ks)).
    apply list_forall_env_prop. destruct* TV.
  apply* well_subst_open_vars.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by weakening *)

Lemma typing_weaken : forall G E F K t T,
   K ; (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   K ; (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H1.
  apply_fresh* (@typing_let M L1) as y. apply_ih_bind* H2.
  auto*.
  auto.
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

Lemma typing_weaken_kinds : forall K K' K'' E t T,
  K & K''; E |= t ~: T ->
  kenv_ok (K & K' & K'') ->
  K & K' & K''; E |= t ~: T.
Proof.
  introv Typ. gen_eq (K & K'') as H. gen K''.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* proper_instance_weaken.
  apply_fresh* typing_abs as y.
  apply_fresh* (@typing_let M (L1 \u dom(K&K'&K''))) as y.
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
Qed.

(* ********************************************************************** *)
(** Typing is preserved by term substitution *)

Lemma typing_trm_subst : forall F M K E t T z u, 
  K ; E & z ~ M & F |= t ~: T ->
  (exists L:vars, has_scheme_vars L K E u M) -> 
  term u ->
  K ; E & F |= (trm_subst z u t) ~: T.
Proof.
  introv Typt. intros Typu Wu. 
  gen_eq (E & z ~ M & F) as G. gen F.
  induction Typt; introv EQ; subst; simpl trm_subst; destruct Typu as [Lu Typu].
  case_var.
    binds_get H1. apply_empty* typing_weaken.
      destruct H2; apply* (has_scheme_from_vars Typu).
    binds_cases H1; apply* typing_var.
  apply_fresh* typing_abs as y. 
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H1. 
  apply_fresh* (@typing_let M0 L1) as y. 
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
  assert (exists L : vars, has_scheme_vars L K E u M). exists* Lu.
  auto*.
  auto.
Qed.

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

Lemma trm_inst_app_inv : forall c tl t tl1,
  trm_inst (const_app c tl1) tl = t ->
  trm_cst c = t \/
  exists t1, exists tl1', tl1' ++ t1 :: nil = tl1 /\
    trm_app (trm_inst (const_app c tl1') tl) (trm_inst t1 tl) = t.
Proof.
  induction tl1 using rev_ind; unfold const_app, trm_inst; simpl; intros.
    auto.
  rewrite fold_left_app in H; simpl in H.
  right; exists x; exists* tl1.
Qed.

Lemma typing_inst_app_inv : forall K E c M tl tl1 TL TL' T,
  K; E |= trm_inst (const_app c tl1) tl ~: T ->
  length TL = length tl1 ->
  Delta.type c = (M, TL ++ TL') ->
  let M' := Sch (fold_right typ_arrow (sch_type M) TL') (sch_kinds M) in
  exists Us, T = sch_open M' Us  /\ proper_instance K M' Us /\
    For_all2 (const_arg_inst K E (sch_kinds M) Us tl) tl1 TL.
Proof.
  induction tl1 using rev_ind; introv Typ Len Delta; inversions Typ; clear Typ;
    try (unfold const_app, trm_inst in H; rewrite fold_left_app in H;
         discriminate).
    destruct TL; simpl in *; try discriminate.
    unfold delta_scheme in *; rewrite Delta in *; simpl in *.
    exists* Us.
  inversions H; clear H.
  induction TL using rev_ind.
    rewrite app_length in Len; simpl in Len.
    rewrite plus_comm in Len; discriminate.
  clear IHTL.
  rewrite app_ass in Delta.
  unfold const_app, trm_inst in H2; rewrite fold_left_app in H2.
  simpl in H2; inversions H2; clear H2.
  destruct* (IHtl1 TL (x0::TL') (typ_arrow S T)) as [Us [He [Hp Hf]]];
    clear IHtl1.
    clear -Len.
    repeat rewrite app_length in Len; simpl in Len.
    rewrite plus_comm in Len.
    rewrite (plus_comm (length tl1)) in Len.
    simpl in Len; inversion* Len.
  exists Us.
  unfold sch_open in He; simpl in He. inversions He; clear He.
  unfold sch_open; simpl in *.
  intuition.
    split; destruct* Hp.
    split; destruct H1; simpl in *.
      destruct H1 as [L F].
      exists L.
      intros; destruct* (F Xs); clear F.
      split.
        unfold typ_open_vars in *; simpl in *.
        inversion* H4.
      simpl in *; trivial.
    auto.
  apply* For_all2_app.
  simpl. split*.
  split*.
  split; destruct* Hp.
  split; destruct* H1; simpl in *.
  destruct H1 as [L F].
  exists L.
  intros; destruct* (F Xs); clear F.
  split*.
  unfold typ_open_vars in *; simpl in *.
  inversion* H4.
Qed.

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; subst; inversions Red.
  destruct (trm_inst_app_inv _ _ _ H3) as [Hc|[t1'[tl1'[_ Ha]]]]; discriminate.
  destruct (trm_inst_app_inv _ _ _ H2) as [Hc|[t1'[tl1'[_ Ha]]]]; discriminate.
  pick_fresh x. rewrite* (@trm_subst_intro x). 
   apply_empty* typing_trm_subst.
   exists* L1.
  destruct (trm_inst_app_inv _ _ _ H3) as [Hc|[t1'[tl1'[_ Ha]]]]; discriminate.
  apply* (@typing_let M L1).
  inversions Typ1. pick_fresh x. 
   rewrite* (@trm_subst_intro x). 
   apply_empty* typing_trm_subst.
   exists {}. intro. unfold sch_arity, kinds_open_vars, sch_open_vars; simpl.
     destruct* Xs. simpl. rewrite* typ_open_vars_nil.
     simpl. intuition.
  use (typing_app Typ1 Typ2).
   clear Typ1 IHTyp1 Typ2 IHTyp2.
   rewrite <- H in *.
   destruct* (typing_inst_app_inv tl tl1 (snd(Delta.type c)) nil H2
                (M:=fst(Delta.type c))) as [Us [He [Hp Ha]]].
   apply (sym_equal (proj2 (Delta.arity H0))).
   destruct (Delta.type c). rewrite <- app_nil_end. simpl*.
   subst.
   use (delta_typed Us H0 H1 (K:=K) (E:=E)).
   destruct (Delta.type c) as [M TL]; simpl in H3.
   apply* H3; clear H3.
  auto*.
  auto*.
  induction tl1 using rev_ind.
    use H2.
    unfold trm_inst, const_app in H5. simpl in H5. inversions H5; clear H5.
    use (delta_typed Us H3 H4 (K:=K) (E:=E)).
    unfold delta_scheme in *.
    use (proj2 (Delta.arity H3)).
    destruct (Delta.type c) as [M TL]; simpl in *.
    destruct TL; try discriminate.
    apply* H5; clear H5.
  unfold trm_inst, const_app in H2; rewrite fold_left_app in H2.
  discriminate.
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
  K; empty |= trm_app (trm_app t0 t3) t2 ~: T ->
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
  destruct H2 as [tl1' [t3' [tl [R [Htl Heq']]]]].
  exists (trm_inst t3' tl).
  rewrite Heq.
  replace (trm_app (const_app c vl) t2)
    with (trm_inst (const_app c tl1') tl).
    apply* red_delta.
  clear -Heq'.
  unfold trm_inst; rewrite (trm_inst_app c tl tl1').
  replace (trm_app (const_app c vl) t2)
    with (const_app c (vl ++ t2 :: nil)).
    unfold const_app.
    apply* (f_equal (fun l => fold_left trm_app l (trm_cst c))).
    symmetry.
    apply* For_all2_eq.
    replace (vl ++ t2 :: nil)
      with (List.map (fun x:trm => x) (vl ++ t2 :: nil)).
    apply* For_all2_map.
    simpl; intros. apply H.
    clear; induction vl; simpl; auto. rewrite* IHvl.
  unfold const_app; rewrite fold_left_app; simpl*.
Qed.

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (empty:env) as E. poses Typ' Typ.
  induction Typ; intros; subst.
  inversions H1.
  left. exists* 0.
  right. pick_freshes (sch_arity M) Ys.
    destructi~ (@H0 Ys) as [[n Val1] | [t1' Red1]].
      assert (value t1). exists* n.
      exists* (t2 ^^ t1).
      exists* (trm_let t1' t2).
  destruct~ IHTyp1 as [Val1 | [t1' Red1]]. 
    destruct~ IHTyp2 as [Val2 | [t2' Red2]]. 
      inversions Typ1; destruct Val1 as [n Val1]; inversions Val1.
        right; exists* (t0 ^^ t2).
      destruct n.
        right; apply* progress_delta.
      left. destruct Val2. exists* n.
      case_eq (Const.arity c); intro.
        right. rewrite H2 in Val1.
        destruct (const_arity_ok (c:=c)(vl:=t2::nil)(K:=K)(T:=T)).
          rewrite H2. constructor; simpl; auto.
        unfold const_app; simpl*.
        destruct H3 as [tl1' [t3' [tl [R [Htl Heq]]]]].
        exists (trm_inst t3' tl).
        simpl in Heq; destruct* tl1'; destruct* tl1'; destruct* Heq.
        rewrite H3.
        replace (trm_app (trm_cst c) (trm_inst t tl))
          with (trm_inst (const_app c (t::nil)) tl) by reflexivity.
        apply* red_delta.
      left. exists n. rewrite H2 in Val1. destruct* Val2.
      right; exists* (trm_app t1 t2'). 
    right; exists* (trm_app t1' t2).
  left. exists* (Const.arity c).
Qed.

Lemma value_irreducible : forall t t',
  value t -> ~(t --> t').
Proof.
  induction t; introv HV; destruct HV as [k HV']; inversions HV';
    intro R; inversions R;
    try (destruct (trm_inst_app_inv _ _ _ H) as [Hc|[t1'[tl1'[He Ha]]]];
         discriminate).
       inversion* H2.
       destruct (value_app_const HV') as [c' [vl [Len [Eq _]]]].
       use (proj1 (Delta.arity H0)).
       rewrite Eq in H; clear Eq.
       unfold trm_inst in H; rewrite trm_inst_app in H.
       destruct (const_app_eq _ _ _ _ H); clear H. subst.
       rewrite map_length in Len. rewrite H4 in Len. omega.
     elim (IHt1 t1'). exists* (S k). auto.
    elim (IHt2 t2'). exists* n2. auto.
  induction tl1 using rev_ind; unfold trm_inst, const_app in H; simpl in H.
    inversions H.
    use (proj1 (Delta.arity H0)).
    discriminate.
  rewrite fold_left_app in H; discriminate.
Qed.

End Mk3.

End Mk2.

End MkSound.
