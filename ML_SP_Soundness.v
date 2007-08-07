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

Lemma For_all2_map: forall (A B:Set)(P P':A->B->Prop) f g l1 l2,
  (forall x y, P x y -> P' (f x) (g y)) ->
  For_all2 P l1 l2 ->
  For_all2 P' (List.map f l1) (List.map g l2).
Proof.
  induction l1; introv; elim l2; simpls; auto*.
Qed.

Definition well_subst K Zs Us :=
  For_all2 (fun Z T => exists k:kind, binds Z k K /\
            well_kinded K (kind_map (typ_substs Zs Us) k) T)
           Zs Us.

Definition comp(A:Set)(f g:A->A) := fun x => f (g x).

Lemma map_comp : forall (A:Set) (f g:A->A) l,
  List.map f (List.map g l) = List.map (fun x:A => f (g x)) l.
Proof.
  induction l; simpl*. rewrite* IHl.
Qed.

Lemma typ_substs_open : forall Xs Us T1 T2,
  types (length Xs) Us -> 
  typ_substs Xs Us (typ_open T1 T2) = 
   typ_open (typ_substs Xs Us T1) (List.map (typ_substs Xs Us) T2).
Proof.
  induction Xs; destruct Us; simpl in *; intros;
    try (inversion H; discriminate).
    rewrite* list_map_id.
  rewrite <- map_comp.
  destruct H.
  inversion H0. clear H0 L x H1 H2.
  rewrite* typ_subst_open.
Qed.

Lemma sch_substs_open : forall Zs Us M Vs,
  types (length Zs) Us ->
    typ_substs Zs Us (sch_open M Vs)
  = sch_open (sch_substs Zs Us M) (List.map (typ_substs Zs Us) Vs).
Proof.
  unfold sch_open. intros. destruct M. simpl.
  rewrite* <- typ_substs_open.
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

Lemma sch_substs_fresh : forall Xs Us M,
  fresh (sch_fv M) (length Us) Xs ->
  sch_substs Xs Us M = M.
Proof.
  induction Xs; destruct Us; intros; try (inversion H; discriminate).
    unfold sch_substs; destruct M; simpl.
    unfold kinds_substs.
    rewrite* kinds_map_id.
  unfold sch_substs; simpl.
  unfold kinds_substs.
  rewrite <- (kinds_map_comp (typ_substs Xs Us) (typ_subst a t)).
  rewrite <- map_comp.
  destruct M as [Ma Mt Mk]; simpl.
  simpl in H. destruct H.
  rewrite <- (sch_subst_fresh t H).
  rewrite <- (IHXs Us (sch_subst a t (Sch Ma Mt Mk))).
  auto.
  rewrite* sch_subst_fresh.
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

Lemma sch_substs_arity : forall Xs Us M,
  sch_arity (sch_substs Xs Us M) = sch_arity M.
Proof.
  intros; destruct* M.
Qed.

Lemma typ_substs_type_list : forall Zs Us Ts n,
  types (length Zs) Us -> types n Ts -> 
  types n (List.map (typ_substs Zs Us) Ts).
Proof.
  unfold types, list_for_n.
  induction Ts; destruct n; simpl; intuition.
    discriminate.
    rewrite* map_length.
  constructor.
    destruct* (IHTs (length Ts)).
    inversion* H3.
  apply typ_substs_types.
    constructor; auto*.
  inversion* H3.
Qed.

Lemma sch_substs_type : forall Zs Us M,
  types (length Zs) Us -> scheme M -> scheme (sch_substs Zs Us M).
Proof.
  induction Zs; destruct Us; intros; unfold sch_substs;
    try (inversion H; discriminate).
    simpl.
    unfold kinds_substs; rewrite* kinds_map_id.
  destruct M as [Ma Mt Mk]; simpl.
  unfold kinds_substs; simpl.
  rewrite* <- (kinds_map_comp (typ_substs Zs Us)).
  rewrite <- map_comp.
  destruct H; simpl in H.
  inversion H; clear H.
  apply (IHZs Us (sch_subst a t (Sch Ma Mt Mk))).
    split*.
    inversion* H1.
  apply sch_subst_type; inversion* H1.
Qed.

Lemma kind_substs_open : forall Zs Vs k Us,
  types (length Zs) Vs ->
  kind_map (typ_substs Zs Vs) (kind_open k Us) =
  kind_open (kind_map (typ_substs Zs Vs) k) (List.map (typ_substs Zs Vs) Us).
Proof.
  intros.
  destruct* k as [[kc kr]|].
  simpl.
  apply (f_equal (fun kr => Some (Kind kc kr))).
  induction* kr.
  simpl. rewrite <- IHkr.
  rewrite* typ_substs_open.
Qed.

Lemma kinds_substs_open : forall Zs Vs Ks Us,
  types (length Zs) Vs ->
  List.map (kind_map (typ_substs Zs Vs)) (kinds_open Ks Us) =
  kinds_open (kinds_substs Zs Vs Ks) (List.map (typ_substs Zs Vs) Us).
Proof.
  intros.
  unfold kinds_substs, kinds_open.
  induction* Ks.
  simpl; rewrite <- IHKs.
  rewrite* kind_substs_open.
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

Lemma well_kinded_substs: forall Zs Vs K k T,
  well_subst K Zs Vs ->
  well_kinded K k T ->
  well_kinded K (kind_map (typ_substs Zs Vs) k) (typ_substs Zs Vs T).
Proof.
  intros.
  induction H0.
    constructor.
  destruct (In_dec eq_var_dec x Zs).
    unfold well_subst in H.
    destruct (For_all2_In _ _ Zs Vs i H) as [T [HT [k'' [HB HW]]]].
    unfold binds in H0, HB.


Qed.

Lemma typing_typ_substs : forall F Zs Vs K E t T,
  fresh (env_fv E) (length Vs) Zs -> 
  types (length Zs) Vs ->
  well_subst K Zs Vs ->
  K ; E & F |= t ~: T -> 
  K ; E & (map (sch_substs Zs Vs) F) |= t ~: (typ_substs Zs Vs T).
Proof.
  introv. intros FZs Dis WS Typ. gen_eq (E & F) as G. gen F.
  induction Typ; introv EQ; subst; simpls typ_substs.
  rewrite~ sch_substs_open. apply* typing_var.
    binds_cases H1.
      apply* binds_concat_fresh.
       rewrite* sch_substs_fresh. use (fv_in_spec sch_fv B).
       apply (fresh_sub _ _ FZs H1).
      auto*.
    destruct* H2.
    split.
      rewrite~ sch_substs_arity. apply* typ_substs_type_list.
    split.
      apply* sch_substs_type.
    intuition.
    destruct M as [Ma Mt Mk]; simpl in *.
    rewrite <- kinds_substs_open.
    apply* (For_all2_map (well_kinded K)); intros.
      clear H5.
      destruct* x0 as [[Kc Kr]|].
        inversion H3.
      rewrite <- H8 in *; rewrite <- H9 in *; clear x0 y H6 H7 H8 H9.
      unfold kind_map. simpl. apply wk_any.
    rewrite <- H10 in *; rewrite <- H11 in *; clear x0 y H8 H9 H10 H11.
    simpls.
    case_eq (x1 == Z); intros e _.
      rewrite e in *.
      unfold is_any_kind in *.
      unfold binds in *.
      rewrite KZ in H6; inversion H6. rewrite <- H9 in *; clear k' H6 H9.
      destruct H7.
      unfold kind_open in H6; simpl in H6.
      destruct k; simpl in *.
      rewrite (cstr_entails_KU H6) in *.
      case_eq kind_rel; intros.
        apply wk_any.
      destruct p; rewrite H8 in H7.
      elim (H7 (v, typ_open t Vs)).
      simpl; auto.
    eapply wk_kind.
      binds_cases H6.

  apply_fresh* typing_abs as y.
   rewrite sch_subst_fold.   
   apply_ih_map_bind* H1.
  apply_fresh* (@typing_let (sch_subst Z U M) (L1 \u {{Z}})) as y.
   simpl. intros Ys Fr. 
   rewrite* <- sch_subst_open_vars.
   apply_ih_map_bind* H2.
  auto*.
Qed.

(* ********************************************************************** *)
(** Iterated type substitution preserves typing *)

Lemma typing_typ_substs : forall Zs Us E t T,
  fresh (env_fv E) (length Zs) Zs -> 
  types (length Zs) Us ->
  E |= t ~: T -> 
  E |= t ~: (typ_substs Zs Us T).
Proof.
  induction Zs; destruct Us; simpl; introv Fr WU Tt;
   destruct Fr; inversions WU; 
   simpls; try solve [ auto | contradictions* ].
  inversions H2. inversions H1. clear H2 H1.
  apply* IHZs. apply_empty* typing_typ_subst.
Qed.

(* ********************************************************************** *)
(** Type schemes of terms can be instanciated *)

Lemma has_scheme_from_vars : forall L E t M,
  has_scheme_vars L E t M ->
  has_scheme E t M.
Proof.
  intros L E t [n T] H Vs TV. unfold sch_open. simpls.
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


