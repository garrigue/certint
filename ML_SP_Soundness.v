(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Charguéraud, March 2007, Coq v8.1                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import List Metatheory 
  ML_SP_Definitions
  ML_SP_Infrastructure.

(* ********************************************************************** *)
(** Typing schemes for expressions *)

Definition has_scheme_vars L K E t M := forall Xs, 
  fresh L (sch_arity M) Xs ->
  K & kind_open_vars (sch_kinds M) Xs ; E |= t ~: (M ^ Xs).

Definition has_scheme K E t M := forall Vs,
  types (sch_arity M) Vs ->
  For_all2 (well_kinded K) (kinds_open (sch_kinds M) Vs) Vs ->
  K ; E |= t ~: (M ^^ Vs).

(* ********************************************************************** *)
(** Type substitution preserves typing *)

Definition binds_prop (A : Set) (P : var -> A -> Prop) (E : Env.env A) :=
  forall x a, binds x a E -> P x a.

Definition well_subst K K' S :=
  binds_prop
    (fun Z k =>
      well_kinded K' (kind_map (typ_subst S) k) (typ_subst S (typ_fvar Z)))
    K.

Lemma For_all2_map: forall (A B:Set)(P P':A->B->Prop) f g l1 l2,
  (forall x y, P x y -> P' (f x) (g y)) ->
  For_all2 P l1 l2 ->
  For_all2 P' (List.map f l1) (List.map g l2).
Proof.
  induction l1; introv; elim l2; simpls; auto*.
Qed.

Definition comp(A:Set)(f g:A->A) := fun x => f (g x).

Lemma map_comp : forall (A:Set) (f g:A->A) l,
  List.map f (List.map g l) = List.map (fun x:A => f (g x)) l.
Proof.
  induction l; simpl*. rewrite* IHl.
Qed.

Lemma kind_map_id : forall k, kind_map (fun T:typ => T) k = k.
Proof.
  intros.
  unfold kind_map.
  destruct* k as [[c r]|]; simpl.
  apply (f_equal (fun r => Some (Kind c r))).
  induction r; simpl; auto. rewrite* IHr.
Qed.

Lemma kinds_map_id : forall K,
  List.map (kind_map (fun T:typ => T)) K = K.
Proof.
  induction K; intros; simpl; auto*.
  rewrite* IHK.
  rewrite* kind_map_id.
Qed.

Lemma kind_map_comp : forall f g k,
  kind_map f (kind_map g k) = kind_map (fun T:typ => f (g T)) k.
Proof.
  intros.
  destruct* k as [[kc kr]|].
  unfold kind_map; simpl.
  rewrite* map_comp.
Qed.

Lemma kinds_map_comp : forall f g K,
  List.map (fun k:kind => kind_map f (kind_map g k)) K =
  List.map (kind_map (fun T:typ => f (g T))) K.
Proof.
  induction K; simpl; intros; auto.
  rewrite* IHK.
  rewrite* kind_map_comp.
Qed.

Lemma fresh_sub : forall n Xs L1 L2,
  fresh L1 n Xs -> L2 << L1 -> fresh L2 n Xs.
Proof.
  induction n; destruct Xs; intros; try (inversion H; discriminate).
    simpl*.
  simpl in *.
  destruct H.
  split; auto*.
  eapply IHn. apply H1.
  apply (proj2 (subset_union_l L2 {{v}} (L1 \u {{v}}))).
  split.
  eapply subset_trans.
    apply H0.
    apply subset_union_weak_l.
  apply subset_union_weak_r.
Qed.

Lemma kind_subst_open : forall S k Us,
  env_prop type S ->
  kind_map (typ_subst S) (kind_open k Us) =
  kind_open (kind_map (typ_subst S) k) (List.map (typ_subst S) Us).
Proof.
  intros.
  destruct* k as [[kc kr]|].
  simpl.
  apply (f_equal (fun kr => Some (Kind kc kr))).
  induction* kr.
  simpl. rewrite <- IHkr.
  rewrite* typ_subst_open.
Qed.

Lemma kinds_subst_open : forall S Ks Us,
  env_prop type S ->
  List.map (kind_map (typ_subst S)) (kinds_open Ks Us) =
  kinds_open (List.map (kind_subst S) Ks) (List.map (typ_subst S) Us).
Proof.
  intros.
  unfold kinds_open.
  induction* Ks.
  simpl; rewrite <- IHKs.
  rewrite* kind_subst_open.
Qed.

Lemma For_all2_In: forall (A B:Set) (P:A->B->Prop) x l1 l2,
  In x l1 -> For_all2 P l1 l2 -> exists y:B, In y l2 /\ P x y.
Proof.
  induction l1; destruct l2; intros; try contradiction.
  simpl in *; destruct H; destruct H0.
    exists b; intuition.
    rewrite* <- H.
  destruct (IHl1 l2 H H1).
  exists* x0.
Qed.

Parameter cstr_entails_trans : forall k1 k2 k3,
  cstr_entails k1 k2 -> cstr_entails k2 k3 -> cstr_entails k1 k3.

Lemma entails_trans : forall k1 k2 k3,
  entails k1 k2 -> entails k2 k3 -> entails k1 k3.
Proof.
  intros.
  destruct H; destruct H0.
  split.
  apply* (cstr_entails_trans H H0).
  intros; auto.
Qed.

Lemma kind_subst_entails : forall S k k',
  entails k' k ->
   entails
     (Kind (kind_cstr k')
        (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT)))
           (kind_rel k')))
     (Kind (kind_cstr k)
        (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT)))
           (kind_rel k))).
Proof.
  intros.
  destruct H.
  split; simpl*.
  intros.
  destruct (proj1 (in_map_iff _ _ _) H1) as [T' [e i]].
  rewrite <- e.
  apply* (in_map (fun XT : var * typ => (fst XT, typ_subst S (snd XT)))).
Qed.

Lemma well_kinded_subst: forall S K K' k T,
  well_subst K K' S ->
  well_kinded K k T ->
  well_kinded K' (kind_map (typ_subst S) k) (typ_subst S T).
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

Lemma get_none_notin : forall (A : Set) x (S : Env.env A),
  get x S = None -> x # S.
Proof.
  induction S; intro; simpl; auto*.
  destruct* a.
  simpl in H. destruct* (eq_var_dec x v).
    discriminate.
  intro. destruct* (proj1 (in_union _ _ _) H0).
  elim n; apply (proj1 (in_singleton _ _) H1).
Qed.

Lemma map_get_none : forall (A : Set) (f : A -> A) x E,
  get x E = None -> get x (map f E) = None.
Proof.
  induction E; simpl; intros; auto*.
  destruct a. simpl. destruct* (eq_var_dec x v).
    discriminate.
Qed.

(*
Lemma well_subst_map : forall K S,
  well_subst K S -> well_subst (map (kind_subst S) K) S.
Proof.
  intros. intro x.
  case_eq (get x K); intros.
    generalize (binds_map (kind_subst S) H0); intro.
    unfold binds in *.
    rewrite H1 in H2; inversion H2 as [e]; rewrite e in *; clear a e H2.
    generalize (H x k H0); intro HW.
    inversion HW.
      unfold kind_subst; rewrite <- H4. apply wk_any.
    unfold kind_subst; rewrite <- H2.
    simpl; rewrite <- H3.
    eapply wk_kind.
      generalize (binds_map (kind_map (typ_subst S)) H5); intro B.
      simpl in B. apply B.
    apply* kind_subst_entails.
  unfold binds in H1.
  rewrite (map_get_none (kind_subst S) _ _ H0) in H1.
  discriminate.
Qed.
*)

Lemma map_combine : forall (A:Set) (f:A->A) Xs Ys,
  map f (combine Xs Ys) = combine Xs (List.map f Ys).
Proof.
  induction Xs; destruct Ys; simpl*.
  rewrite* IHXs.
Qed.

Lemma kind_subst_open_vars : forall S k Xs,
  fresh (dom S) (length Xs) Xs ->
  env_prop type S ->
  kind_subst S (kind_open k (typ_fvars Xs)) =
  kind_open (kind_subst S k) (typ_fvars Xs).
Proof.
  intros.
  destruct* k as [[kc kr]|].
  simpl.
  apply (f_equal (fun kr => Some (Kind kc kr))).
  induction* kr.
  simpl. fold (typ_open_vars (snd a) Xs).
  rewrite* <- typ_subst_open_vars.
  rewrite* IHkr.
Qed.
  

Lemma kinds_subst_open_vars : forall S Ks Xs,
  fresh (dom S) (length Xs) Xs ->
  env_prop type S ->
  map (kind_subst S) (kind_open_vars Ks Xs) =
  kind_open_vars (List.map (kind_subst S) Ks) Xs.
Proof.
  unfold kind_open_vars.
  intros.
  rewrite map_combine.
  apply (f_equal (combine Xs (B:=kind))).
  unfold kinds_open.
  induction* Ks.
  simpls. rewrite IHKs.
  rewrite* kind_subst_open_vars.
Qed.

Lemma kinds_map_fresh : forall K S,
  disjoint (dom S) (fv_in kind_fv K) ->
  map (kind_subst S) K = K.
Proof.
  intros.
  induction* K.
  destruct* a. simpl in *.
  rewrite IHK; clear IHK.
  unfold kind_subst.
  unfold kind_fv in *.
  destruct* o as [[kc kr]|].
    simpl.
    apply (f_equal (fun kr => (v,Some(Kind kc kr))::K)).
    induction* kr.
    destruct a; simpl.
    rewrite* IHkr.
    rewrite* typ_subst_fresh.
  intro x; destruct* (H x).
  simpl in H0; auto*.
  intro x; destruct* (H x).
  simpl in *. auto*.
  intro x; destruct* (H x).
Qed.

Lemma well_kinded_extend : forall K K' x T,
  disjoint (dom K) (dom K') ->
  well_kinded K x T -> well_kinded (K & K') x T.
Proof.
  induction 2.
    apply wk_any.
  eapply wk_kind.
  apply* binds_concat_fresh.
    destruct* (H x).
    elim (binds_fresh H0 H2).
  assumption.
Qed.

Parameter cstr_entails_refl : forall c, cstr_entails c c.

Lemma entails_refl : forall k, entails k k.
Proof.
  intros. split; auto. apply cstr_entails_refl.
Qed.

Lemma typing_typ_subst : forall F S K K' E t T,
  disjoint (dom S) (env_fv E \u fv_in kind_fv K) ->
  disjoint (dom K) (dom K') ->
  env_prop type S ->
  well_subst (K & K') (K & map (kind_subst S) K') S ->
  K & K' ; E & F |= t ~: T -> 
  K & map (kind_subst S) K'; E & (map (sch_subst S) F) |= t ~: (typ_subst S T).
Proof.
  introv. intros Dis DisK TS WS Typ.
  gen_eq (K & K') as GK; gen_eq (E & F) as G; gen K'; gen F.
  induction Typ; introv DisK WS EQ EQ'; subst; simpls typ_subst.
  rewrite~ sch_subst_open. apply* typing_var.
    binds_cases H1.
      apply* binds_concat_fresh.
       rewrite* sch_subst_fresh. use (fv_in_spec sch_fv B).
       intro v. destruct* (Dis v).
       destruct* (proj1 (notin_union _ _ _) H3).
      auto*.
    destruct* H2.
    split.
      rewrite~ sch_subst_arity. apply* typ_subst_type_list.
    split.
      apply* sch_subst_type.
    intuition.
    destruct M as [Ma Mt Mk]; simpl in *.
    rewrite* <- kinds_subst_open.
    apply* (For_all2_map (well_kinded (K&K'))); intros.
    apply* well_kinded_subst.
  apply_fresh* typing_abs as y.
   (* rewrite sch_subst_fold. *)
   assert (r: Sch 0 (typ_subst S U) nil = sch_subst S (Sch 0 U nil)).
     auto.
   rewrite r; clear r.
   apply_ih_map_bind* H1.
  apply_fresh* (@typing_let (sch_subst S M) (L1 \u dom S \u dom (K&K'))) as y.
   simpl. intros Ys Fr. 
   rewrite* <- sch_subst_open_vars.
   rewrite* <- kinds_subst_open_vars.
   rewrite concat_assoc. rewrite <- map_concat.
   assert (KxYs: disjoint (dom K \u dom K')
                    (dom (kind_open_vars (sch_kinds M) Ys))).
     clear H H0 H1 H2.
     unfold kind_open_vars.
     intro v.
     case_eq (S.mem v (dom K \u dom K')); intros.
       generalize (S.mem_2 H); intro; clear H.
       right; intro.
       elim (fresh_rev _ _ Fr (x:=v)).
       rewrite* dom_concat. auto with sets.
       apply (in_dom_combine _ _ H).
     left; intro inK; rewrite (S.mem_1 inK) in H. discriminate.
   apply* H0; clear H H0 H1 H2.
     intro x; destruct* (KxYs x). destruct* (DisK x).
     intro x; intros.
     destruct* (binds_concat_inv H).
       destruct H0. generalize (WS x a H1); intro HW; clear H WS.
       rewrite map_concat. rewrite <- concat_assoc.
       apply* well_kinded_extend.
       rewrite dom_map. rewrite dom_concat; rewrite* dom_map.
     rewrite map_concat. rewrite <- concat_assoc.
     destruct a; try constructor.
     simpl. rewrite get_notin_dom.
     eapply wk_kind. eapply binds_prepend.
     generalize (binds_map (kind_subst S) H0); intro B.
     simpl in B; apply B; clear B.
     apply entails_refl.
     intro.
     generalize (proj2 (fresh_union_r _ _ _ _
         (proj1 (fresh_union_r _ _ _ _ Fr))));
       intro FrS.
     elim (binds_fresh H0).
     intro.
     elim (fresh_rev _ _ FrS (x:=x)). auto.
     apply (in_dom_combine _ _ H2).
   rewrite* concat_assoc.
  apply_ih_map_bind* H2.
  auto*.
Qed.

(* ********************************************************************** *)
(** Type schemes of terms can be instanciated *)

Lemma has_scheme_from_vars : forall L K E t M,
  has_scheme_vars L K E t M ->
  has_scheme K E t M.
Proof.
  intros L K E t [n T Ks] H Vs TV. unfold sch_open. simpls.
  pick_freshes n Xs.
  rewrite (fresh_length _ _ _ Fr) in TV, H.

  rewrite~ (@typ_substs_intro Xs Vs T).
  unfolds has_scheme_vars sch_open_vars. simpls.
  apply* typing_typ_substs.
Qed.

(* ********************************************************************** *)
(** A term that has type T has type scheme "forall(no_var).T" *)

Lemma has_scheme_from_typ : forall E t T,
  E |= t ~: T -> has_scheme E t (Sch 0 T).
Proof.
  introz. unfold sch_open. simpls.
  rewrite* <- typ_open_type.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by weakening *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H1.
  apply_fresh* (@typing_let M L1) as y. apply_ih_bind* H2.
  auto*.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by term substitution *)

Lemma typing_trm_subst : forall F M E t T z u, 
  E & z ~ M & F |= t ~: T ->
  has_scheme E u M -> 
  term u ->
  E & F |= (trm_subst z u t) ~: T.
Proof.
  introv Typt. intros Typu Wu. 
  gen_eq (E & z ~ M & F) as G. gen F.
  induction Typt; introv EQ; subst; simpl trm_subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y. 
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H1. 
  apply_fresh* (@typing_let M0 L1) as y. 
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H2. 
  auto*.
Qed.

(* ********************************************************************** *)
(** Preservation: typing is preserved by reduction *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; subst; inversions Red.
  pick_fresh x. rewrite* (@trm_subst_intro x). 
   apply_empty* typing_trm_subst. 
   apply* (@has_scheme_from_vars L1). 
  apply* (@typing_let M L1).
  inversions Typ1. pick_fresh x. 
   rewrite* (@trm_subst_intro x). 
   apply_empty* typing_trm_subst.
   apply* has_scheme_from_typ.
  auto*.
  auto*.
Qed. 

(* ********************************************************************** *)
(** Progress: typed terms are values or can reduce *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (empty:env) as E. poses Typ' Typ.
  induction Typ; intros; subst. 
  inversions H0.
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


