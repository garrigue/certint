(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Charguéraud, March 2007, Coq v8.1                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import List Metatheory 
  ML_SP_Definitions
  ML_SP_Infrastructure.

Module MkSound(Cstr:CstrIntf).

Module Infra := MkInfra(Cstr).
Import Infra.
Import Defs.

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
  inversion HW. clear k0 H2 K0 H4 HW.
  simpl typ_subst.
  case_eq (get x S); intros; rewrite H2 in H3.
    rewrite <- H3; clear t H2 H3.
    simpl. eapply wk_kind. apply H5.
    eapply entails_trans. apply H6.
    apply* kind_subst_entails.
  simpl.
  inversion H3. rewrite H7 in *; clear x0 H3 H2 H7.
  eapply wk_kind. apply H5.
  eapply entails_trans. apply H6.
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
  
Lemma well_subst_fresh : forall K K' K'' S Ys L1 M,
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  fresh (L1 \u dom S \u dom (K & K'')) (length (sch_kinds M)) Ys ->
  well_subst (K & K' & K'' & kind_open_vars (sch_kinds M) Ys)
    (K & map (kind_subst S) (K'' & kind_open_vars (sch_kinds M) Ys)) S.
Proof.
  introv WS Fr.
  assert (KxYs: disjoint (dom K \u dom K'')
                         (dom (kind_open_vars (sch_kinds M) Ys))).
    unfold kind_open_vars.
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
    eapply wk_kind. eapply binds_prepend.
      use (binds_map (kind_subst S) B).
      simpl in H; apply H.
    apply entails_refl.
  intro; elim (binds_fresh B); clear B.
  use (proj2 (fresh_union_r _ _ _ _ (proj1 (fresh_union_r _ _ _ _ Fr)))).
  intro; destruct* (fresh_rev _ _ H0 (x:=x)).
  apply (in_dom_combine _ _ H1).
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
  K & kind_open_vars (sch_kinds M) Xs; E |= t ~: (M ^ Xs).

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
  apply* (typing_typ_substs (kind_open_vars Ks Xs)).
      rewrite* mkset_dom.
      apply* (fresh_disjoint (length Ks)).
    apply* types_combine.
  clear H.
  intro x; intros.
  destruct* (binds_concat_inv H) as [[N B]|B]; clear H.
    unfold kind_open_vars in N.
    rewrite* kind_map_fresh.
     simpl.
     rewrite* get_notin_dom.
      destruct k; try constructor.
      eapply wk_kind. apply B.
      apply entails_refl.
     rewrite mkset_dom in N.
      rewrite* mkset_dom.
     rewrite <- (fresh_length _ _ _ Fr).
     unfold kinds_open, typ_fvars. rewrite* map_length.
    rewrite* mkset_dom.
    apply* (fresh_disjoint (length Ks)).
    assert (Fr': fresh (fv_in kind_fv K) (length Ks) Xs). auto*.
    apply (fresh_sub (length Ks) Xs Fr' (fv_in_spec kind_fv B)).
   unfold kind_open_vars, kinds_open in *.
   case_eq (get x (combine Xs Vs)); intros.
    case_eq (get x (combine Xs Ks)); intros.
     fold (binds x k (combine Xs Ks)) in H0.
     generalize (binds_map (fun k : kind => kind_open k (typ_fvars Xs)) H0);
       simpl; rewrite map_combine; intro.
     generalize (binds_func B H1); intro. subst k.
     clear H1.
     apply* (For_all2_get (well_kinded K) Xs).
      use (binds_map (kind_subst (combine Xs Vs)) B).
      simpl in H1; rewrite map_combine in H1.
      rewrite list_map_comp in H1.
      assert (fresh (typ_fv_list Vs \u kind_fv_list Ks) (length Ks) Xs).
        auto*.
      rewrite*
        (list_map_ext Ks _ _ (kind_subst_open_combine Xs Ks (Vs:=Vs) H2 TV)).
     rewrite H. apply H.
    elim (get_contradicts _ _ _ _ H H0); auto.
    rewrite* <- (fresh_length _ _ _ Fr).
  elim (get_contradicts _ _ _ _ B H); auto.
Qed.

(* ********************************************************************** *)
(** A term that has type T has type scheme "forall(no_var).T" *)

Lemma has_scheme_from_typ : forall K E t T,
  K ; E |= t ~: T -> has_scheme K E t (Sch T nil).
Proof.
  introz. unfold sch_open. simpls.
  rewrite* <- typ_open_type.
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
Qed.

Lemma typing_weaken_kinds : forall K K' K'' E t T,
  K & K''; E |= t ~: T ->
  ok (K & K' & K'') ->
  K & K' & K''; E |= t ~: T.
Proof.
  introv Typ. gen_eq (K & K'') as H. gen K''.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. destruct* H2 as [TM [SM FM]]; split3*.
    rewrite <- list_map_id.
    rewrite <- (list_map_id (kinds_open (sch_kinds M) Us)).
    apply (For_all2_map _ (well_kinded (K&K'&K'')) _ _ _ _
                          (well_kinded_weaken K K' K'' Ok) FM).
  apply_fresh* typing_abs as y.
  apply_fresh* (@typing_let M (L1 \u dom(K&K'&K''))) as y.
    intros. clear H H1 H2.
    unfold concat. rewrite <- app_ass. unfold concat in H0.
    apply* H0. rewrite* app_ass.
    rewrite app_ass. fold ((K'' ++ K' ++ K) & kind_open_vars (sch_kinds M) Xs).
    unfold kind_open_vars.
    apply* disjoint_ok.
    apply* ok_combine_fresh.
    rewrite mkset_dom.
    apply disjoint_comm.
    apply* fresh_disjoint.
    destruct* (fresh_union_r _ _ _ _ H3).
    unfold kinds_open. rewrite map_length.
    rewrite* <- (fresh_length _ _ _ H3).
  auto*.
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
     apply* disjoint_ok.
     destruct* (typing_regular (H Xs H3)).
     unfold kind_open_vars.     
     apply* ok_combine_fresh.
     rewrite dom_concat.
     apply disjoint_union.
       apply ok_disjoint. destruct* (typing_regular H5).
     apply disjoint_comm.
     unfold kind_open_vars.
     rewrite mkset_dom. rewrite mkset_dom.
       apply* (fresh_disjoint (sch_arity M)).
       unfold kinds_open. rewrite map_length.
         rewrite* <- (fresh_length _ _ _ H3).
       unfold kinds_open. rewrite map_length.
         rewrite* <- (fresh_length _ _ _ TypM).
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H2.
  assert (exists L : vars, has_scheme_vars L K E u M). exists* Lu.
  auto*.
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

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; subst; inversions Red.
  pick_fresh x. rewrite* (@trm_subst_intro x). 
   apply_empty* typing_trm_subst.
   exists* L1.
  apply* (@typing_let M L1).
  inversions Typ1. pick_fresh x. 
   rewrite* (@trm_subst_intro x). 
   apply_empty* typing_trm_subst.
   exists {}. intro. unfold sch_arity, kind_open_vars, sch_open_vars; simpl.
     destruct* Xs. simpl. rewrite* typ_open_vars_nil.
     simpl. intuition.
  auto*.
  auto*.
Qed. 

(* ********************************************************************** *)
(** Progress: typed terms are values or can reduce *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (empty:env) as E. poses Typ' Typ.
  induction Typ; intros; subst.
  inversions H1.
  left*. 
  right. pick_freshes (sch_arity M) Ys.
    destructi~ (@H0 Ys) as [Val1 | [t1' Red1]]. 
      exists* (t2 ^^ t1). 
      exists* (trm_let t1' t2).
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]]. 
    destruct~ IHTyp2 as [Val2 | [t2' Red2]]. 
      inversions Typ1; inversion Val1. exists* (t0 ^^ t2).
      exists* (trm_app t1 t2'). 
    exists* (trm_app t1' t2).
Qed.

End MkSound.
