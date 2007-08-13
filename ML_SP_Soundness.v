(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Charguéraud, March 2007, Coq v8.1                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import List Metatheory 
  ML_SP_Definitions
  ML_SP_Infrastructure.

(* ********************************************************************** *)
(** Type substitution preserves typing *)

Definition binds_prop (A : Set) (P : var -> A -> Prop) (E : Env.env A) :=
  forall x a, binds x a E -> P x a.

Definition well_subst K K' S :=
  binds_prop
    (fun Z k => well_kinded K' (kind_subst S k) (typ_subst S (typ_fvar Z)))
    K.

Lemma For_all2_map: forall (A B:Set)(P P':A->B->Prop) f g l1 l2,
  (forall x y, P x y -> P' (f x) (g y)) ->
  For_all2 P l1 l2 ->
  For_all2 P' (List.map f l1) (List.map g l2).
Proof.
  induction l1; introv; elim l2; simpls; auto*.
Qed.

Definition comp(A:Set)(f g:A->A) := fun x => f (g x).

Lemma list_map_comp : forall (A:Set) (f g:A->A) l,
  List.map f (List.map g l) = List.map (fun x:A => f (g x)) l.
Proof.
  induction l; simpl*. rewrite* IHl.
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
  kind_subst S (kind_open k Us) =
  kind_open (kind_subst S k) (List.map (typ_subst S) Us).
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
  List.map (kind_subst S) (kinds_open Ks Us) =
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

Lemma kind_map_fresh : forall S k,
  disjoint (dom S) (kind_fv k) ->
  kind_subst S k = k.
Proof.
  unfold kind_subst, kind_fv.
  intros; destruct* k as [[kc kr]|].
  simpl.
  apply (f_equal (fun kr => Some(Kind kc kr))).
  induction* kr.
  destruct a; simpl.
  rewrite* IHkr.
    rewrite* typ_subst_fresh.
    intro x; destruct* (H x).
    simpl in H0; auto*.
  intro x; destruct* (H x).
  simpl in *. auto*.
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

Lemma entails_refl : forall k, entails k k.
Proof.
  intros. split*.
Qed.

Fixpoint mkset (l:list var) {struct l} : vars :=
  match l with
  | nil => {}
  | h :: t => {{h}} \u mkset t
  end.

Lemma mkset_dom : forall (A:Set) Xs (As:list A),
  length Xs = length As -> dom (combine Xs As) = mkset Xs.
Proof.
  induction Xs; destruct As; simpl; intros; try discriminate.
    auto.
  rewrite* IHXs.
Qed.

Lemma fresh_disjoint : forall n Xs L,
  fresh L n Xs -> disjoint (mkset Xs) L.
Proof.
  induction n; destruct Xs; simpl; intros; auto*.
    intro; auto.
  destruct H.
  intro x.
  assert (fresh L n Xs). auto*.
  destruct* (IHn Xs L H1 x).
  destruct* (eq_var_dec x v).
Qed.

Lemma in_vars_dec : forall x L,
  x \in L \/ x \notin L.
Proof.
  intros.
  case_eq (S.mem x L); intros; auto with sets.
  right; intro inL. rewrite (S.mem_1 inL) in H. discriminate.
Qed.

Lemma disjoint_comm : forall A B,
  disjoint A B -> disjoint B A.
Proof.
  intros. intro x; destruct* (H x).
Qed.

Lemma disjoint_union : forall A B C,
  disjoint A C -> disjoint B C -> disjoint (A \u B) C.
Proof.
  intros. intro x; destruct* (H x); destruct* (H0 x).
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
  split. rewrite~ sch_subst_arity. apply* typ_subst_type_list.
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
  destruct a; try constructor.
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
   simpl. intros Ys Fr. 
   rewrite* <- sch_subst_open_vars.
   rewrite* <- kinds_subst_open_vars.
   rewrite concat_assoc. rewrite <- map_concat.
   unfold sch_arity in Fr; simpl in Fr; rewrite map_length in Fr.
   apply* H0; clear H H0 H1 H2.
     destruct* (fresh_union_r _ _ _ _ Fr).
     destruct* (fresh_union_r _ _ _ _ H).
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

Definition has_scheme_vars L K E t M := forall Xs,
  fresh L (sch_arity M) Xs ->
  K & kind_open_vars (sch_kinds M) Xs; E |= t ~: (M ^ Xs).

Definition has_scheme K E t M := forall Vs,
  types (sch_arity M) Vs ->
  For_all2 (well_kinded K) (kinds_open (sch_kinds M) Vs) Vs ->
  K ; E |= t ~: (M ^^ Vs).

(* ********************************************************************** *)
(** Type schemes of terms can be instanciated *)

Lemma incr_subst_fresh : forall a t S Xs,
  fresh {{a}} (length Xs) Xs ->
  List.map (typ_subst ((a, t) :: S)) (typ_fvars Xs) =
  List.map (typ_subst S) (typ_fvars Xs).
Proof.
  induction Xs; simpl; intros. auto.
  destruct* (eq_var_dec a0 a).
    rewrite e in H. destruct* H. elim H. auto.
  rewrite* IHXs.
Qed.

Lemma fresh_subst : forall L Xs Vs,
  fresh L (length Vs) Xs ->
  List.map (typ_subst (combine Xs Vs)) (typ_fvars Xs) = Vs.
Proof.
  induction Xs; destruct Vs; intros; try contradiction; simpl*.
  destruct* (eq_var_dec a a).
  simpl in H.
  rewrite incr_subst_fresh. rewrite* IHXs.
  destruct* H.
Qed.

Fixpoint map_get (A:Set) (l:list var) (E:Env.env A) {struct l} : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match get h E with
    | Some x => x :: map_get t E
    | None => map_get t E
    end
  end.

Lemma map_get_fresh : forall (A:Set) a (a0:A) S Xs,
  fresh {{a}} (length Xs) Xs ->
  map_get Xs ((a, a0) :: S) = map_get Xs S.
Proof.
  induction Xs; simpl; intros.
    auto.
  destruct* (eq_var_dec a1 a).
    rewrite e in H. destruct* H. elim H. auto.
  rewrite* IHXs.
Qed.

Lemma For_all2_get : forall (A B:Set) (P:A->B->Prop) Xs Ys Zs x y z,
  For_all2 P Ys Zs ->
  binds x y (combine Xs Ys) ->
  binds x z (combine Xs Zs) ->
  P y z.
Proof.
  induction Xs; destruct Ys; destruct Zs; simpl; intros; auto*;
    try discriminate.
  unfold binds in H0, H1; simpl in H0, H1.
  destruct (eq_var_dec x a).
  generalize (proj1 H). inversion H0; inversion* H1.
  apply* (IHXs _ _ _ _ _ (proj2 H) H0 H1).
Qed.

Lemma kind_fv_fresh : forall k Ks n Xs,
  In k Ks ->
  fresh (kind_fv_list Ks) n Xs ->
  fresh (typ_fv_list (kind_types k)) n Xs.
Proof.
  induction Ks; intros. elim H.
  simpl in H; destruct H.
    rewrite H in H0; destruct (fresh_union_r _ _ _ _ H0).
    unfold kind_fv in H1. auto.
  apply* IHKs.
  simpls; auto*.
Qed.

Lemma list_forall_env_prop : forall (A:Set) (P:A->Prop) Xs Vs,
  list_forall P Vs -> env_prop P (combine Xs Vs).
Proof.
  induction Xs; destruct Vs; simpl; intros; intro; intros;
    unfold binds in H0; simpl in H0; try discriminate.
  destruct* (eq_var_dec x a).
    inversion H. generalize H4; inversion* H0.
  inversion H.
  apply (IHXs Vs H3 x a1 H0).
Qed.

Lemma list_map_ext : forall (A B:Set) (l:list A) (f1 f2:A->B),
  (forall x, In x l -> f1 x = f2 x) ->
  List.map f1 l = List.map f2 l.
Proof.
  intros. induction l. auto.
  simpl. rewrite* H. rewrite* IHl.
Qed.

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
      rewrite <- H0.
      rewrite <- (fresh_length _ _ _ Fr).
      apply* fresh_empty.
    rewrite* mkset_dom.
    apply (fresh_disjoint (length Ks)).
    apply* (kind_fv_fresh k Ks).
  apply* list_forall_env_prop.
Qed.

Lemma in_mkset : forall x Xs,
  In x Xs -> x \in mkset Xs.
Proof.
  induction Xs; intros. elim H.
  simpl in H; destruct H.
    simpl; rewrite* H. auto with sets.
  simpl. eauto with sets.
Qed.

Lemma get_contradicts : forall (A B:Set) x (a:A) Xs Vs (Ks:list B),
  get x (combine Xs Vs) = Some a ->
  get x (combine Xs Ks) = None ->
  length Xs = length Ks -> False.
Proof.
  intros.
  elim (binds_fresh H).
  intro.
  elim (get_none_notin _ H0).
  rewrite* mkset_dom.
  apply in_mkset.
  apply* in_dom_combine.
Qed.

Lemma types_length : forall n Us,
  types n Us -> n = length Us.
Proof.
  intros. destruct* H.
Qed.

Hint Resolve types_length.
        
Lemma has_scheme_from_vars : forall L K E t M,
  has_scheme_vars L K E t M ->
  has_scheme K E t M.
Proof.
  intros L K E t [T Ks] H Vs TV. unfold sch_open. simpls.
  pick_freshes (length Ks) Xs.
  unfold sch_arity in TV; simpl in TV.
  rewrite (fresh_length _ _ _ Fr) in TV.
  rewrite~ (@typ_subst_intro Xs Vs T).
  unfolds has_scheme_vars sch_open_vars. simpls.
  intro WK.
  apply* (typing_typ_substs (kind_open_vars Ks Xs)).
     rewrite* mkset_dom.
     apply* (fresh_disjoint (length Ks)).
     fresh_simpl; auto*.
     destruct* (fresh_union_r _ _ _ _ Fr).
     destruct* (fresh_union_r _ _ _ _ H0).
     destruct* (fresh_union_r _ _ _ _ H2).
    apply* types_combine.
   clear H.
   intro x; intros.
   destruct* (binds_concat_inv H) as [[N B]|B]; clear H.
    unfold kind_open_vars in N.
    rewrite* kind_map_fresh.
     simpl.
     rewrite* get_notin_dom.
      destruct a; try constructor.
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
     generalize (binds_func B H1); intro. subst a.
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
  apply* H.
  unfold sch_arity. simpl*.
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

Lemma well_kinded_comm : forall K K' K'',
  ok (K & K' & K'') ->
  forall x T,
  well_kinded (K & K'' & K') x T ->
  well_kinded (K & K' & K'') x T.
Proof.
  introv OK; introv WK. gen_eq (K & K'' & K') as H. gen K''.
  induction WK; introv Ok EQ; subst.
    apply wk_any.
  eapply wk_kind.
    destruct* (binds_concat_inv H).
    destruct H1.
    destruct* (binds_concat_inv H2).
  assumption.
Qed.

Lemma ok_disjoint : forall (A:Set) (E F:Env.env A),
  ok (E & F) -> disjoint (dom E) (dom F).
Proof.
  induction F; simpls; intros.
    intro; right*.
  destruct a; simpl.
  inversion H.
  clear x a0 H0 H1 H3.
  intro y.
  destruct* (eq_var_dec y v).
    rewrite* e.
  destruct* (IHF H2 y).
Qed.

Lemma well_kinded_weaken : forall K K' K'',
  ok (K & K' & K'') ->
  forall x T,
  well_kinded (K & K'') x T ->
  well_kinded (K & K' & K'') x T.
Proof.
  intros. apply* well_kinded_comm.
  apply* well_kinded_extend.
    rewrite dom_concat.
    apply disjoint_union.
      apply ok_disjoint. destruct* (ok_concat_inv _ _ H).
  apply disjoint_comm.
  unfold concat in H. rewrite <- app_ass in H.
  destruct* (ok_concat_inv _ _ H).
  apply* ok_disjoint.
Qed.

Lemma ok_cons : forall (A:Set) (E:Env.env A) x (a:A),
  ok E -> x # E -> ok ((x,a) :: E).
Proof.
  intros.
  assert (r: E = nil ++ E). simpl*.
  rewrite r; rewrite app_comm_cons.
  apply* (ok_push (A:=A) a (E:=E) (x:=x)).
Qed.

Lemma disjoint_ok : forall (A:Set) (E F:Env.env A),
  ok E -> ok F -> disjoint (dom E) (dom F) -> ok (E & F).
Proof.
  induction F; simpl; intros. auto.
  destruct a; unfold concat.
  apply ok_cons.
    apply* IHF. inversion* H0.
    intro x; destruct* (H1 x).
  fold (E&F). rewrite dom_concat.
  apply (proj2 (notin_union v (dom E) (dom F))).
  split. destruct* (H1 v).
    elim H2. auto with sets.
  inversion* H0.
Qed.

Lemma ok_combine_fresh : forall (A:Set) L n Xs (Vs:list A),
  fresh L n Xs -> ok (combine Xs Vs).
Proof.
  induction n; destruct Xs; simpl; intros; auto*.
    apply (ok_empty A).
  destruct* Vs. apply (ok_empty A).
  apply* ok_cons.
  destruct H as [_ Fr].
  clear IHn a.
  gen n L Vs. induction Xs; simpl; intros.
    auto with sets.
  destruct* Vs.
    auto with sets.
  destruct n. elim Fr.
  simpl.
  apply (proj2 (notin_union v {{a}} (dom (combine Xs Vs)))).
  split; destruct* Fr.
  apply* IHXs.
  rewrite union_comm in H0.
  rewrite union_assoc in H0.
  apply H0.
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


