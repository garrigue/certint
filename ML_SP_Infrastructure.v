(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Infrastructure             *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - May 2008                                *
***************************************************************************)

Set Implicit Arguments.
Require Import List Metatheory ML_SP_Definitions.

Module MkInfra(Cstr:CstrIntf)(Const:CstIntf).

Module Defs := MkDefs(Cstr)(Const).
Import Defs.

(* ====================================================================== *)
(** * Additional Definitions used in the Proofs *)

(* ********************************************************************** *)
(** ** Free Variables *)

(** Variants looking up a kinding environment *)

Fixpoint close_fvars (n:nat)(K:kenv)(VK:vars)(Vs:vars) {struct n} : vars :=
  match n with
  | 0 => Vs
  | S n' =>
    match S.choose (S.inter VK Vs) with
    | None => Vs
    | Some x =>
        let VK' := S.diff VK {{x}} in
        match get x K with
        | None => Vs
        | Some k =>
          close_fvars n' K VK' (Vs \u kind_fv k)
        end
    end
  end.
    
Definition typ_fvk K T :=
  close_fvars (length K) K (dom K) (typ_fv T).

Definition typ_fvk_list K Ts :=
  close_fvars (length K) K (dom K) (typ_fv_list Ts).

(** Computing free variables of a term. *)

Fixpoint trm_fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => {}
  | trm_fvar x    => {{x}}
  | trm_abs t1    => (trm_fv t1)
  | trm_let t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_app t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_cst c     => {}
  end.

(* ********************************************************************** *)
(** ** Substitution for free names *)

Definition subs := Env.env typ.

(** Substitution for names for types *)

Fixpoint typ_subst (S : subs) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar i      => typ_bvar i
  | typ_fvar X      =>
    match get X S with
    | None => T
    | Some T' => T'
    end
  | typ_arrow T1 T2 => typ_arrow (typ_subst S T1) (typ_subst S T2)
  end.

(** Substitution for names for schemes. *)

Definition kind_subst S := kind_map (typ_subst S).

Definition sch_subst S M := 
  Sch (typ_subst S (sch_type M)) (List.map (kind_subst S) (sch_kinds M)).

(** Substitution for name in a term. *)

Fixpoint trm_subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => if x == z then u else (trm_fvar x)
  | trm_abs t1    => trm_abs (trm_subst z u t1) 
  | trm_let t1 t2 => trm_let (trm_subst z u t1) (trm_subst z u t2) 
  | trm_app t1 t2 => trm_app (trm_subst z u t1) (trm_subst z u t2)
  | trm_cst c     => trm_cst c
  end.

Notation "[ z ~> u ] t" := (trm_subst z u t) (at level 68).


(* ====================================================================== *)
(** * Tactics *)

(* ********************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : trm => trm_fv x) in
  let E := gather_vars_with (fun x : typ => typ_fv x) in
  let F := gather_vars_with (fun x : list typ => typ_fv_list x) in
  let G := gather_vars_with (fun x : env => env_fv x) in
  let H := gather_vars_with (fun x : sch => sch_fv x) in
  let I := gather_vars_with (fun x : kenv => dom x) in
  let J := gather_vars_with (fun x : kenv => fv_in kind_fv x) in
  let K := gather_vars_with (fun x : list kind => kind_fv_list x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "pick_freshes" constr(n) ident(x) :=
  let L := gather_vars in (pick_freshes_gen L n x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.


(* ********************************************************************** *)
(** ** Automation *)

Hint Constructors type term.

Lemma typ_def_fresh : typ_fv typ_def = {}.
Proof.
  auto.
Qed.

Hint Extern 1 (_ \notin typ_fv typ_def) =>
  rewrite typ_def_fresh.

Hint Extern 1 (types _ _) => split; auto.


(* ====================================================================== *)
(** ** Properties of fv *)

Lemma fv_list_map : forall ts1 ts2,
  typ_fv_list (ts1 ++ ts2) = typ_fv_list ts1 \u typ_fv_list ts2.
Proof.
  induction ts1; simpl; intros. 
  rewrite* union_empty_l.
  rewrite IHts1. rewrite* union_assoc.
Qed.


(* ====================================================================== *)
(** * Properties of terms *)

(* begin hide *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma trm_open_rec_core :forall t j v i u, i <> j ->
  {j ~> v}t = {i ~> u}({j ~> v}t) -> t = {i ~> u}t.
Proof.
  induction t; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*. 
Qed.

Lemma trm_open_rec : forall t u,
  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; f_equal*. 
  unfolds trm_open. pick_fresh x.
   apply* (@trm_open_rec_core t1 0 (trm_fvar x)).
  unfolds trm_open. pick_fresh x.
   apply* (@trm_open_rec_core t2 0 (trm_fvar x)).
Qed.

(* end hide *)

(** Substitution for a fresh name is identity. *)

Lemma trm_subst_fresh : forall x t u, 
  x \notin trm_fv t ->  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; f_equal*.
  case_var*. notin_contradiction.
Qed.

(** Substitution distributes on the open operation. *)

Lemma trm_subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold trm_open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* trm_open_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma trm_subst_open_var : forall x y u e, y <> x -> term u ->
  ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
Proof.
  introv Neq Wu. rewrite* trm_subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma trm_subst_intro : forall x t u, 
  x \notin (trm_fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* trm_subst_open.
  rewrite* trm_subst_fresh. simpl. case_var*.
Qed.

(** Terms are stable by substitution *)

Lemma trm_subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpl*.
  case_var*.
  apply_fresh term_abs as y. rewrite* trm_subst_open_var.
  apply_fresh* term_let as y. rewrite* trm_subst_open_var.
Qed.

Hint Resolve trm_subst_term.

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> term_body t1.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma body_to_term_abs : forall t1, 
  term_body t1 -> term (trm_abs t1).
Proof.
  intros. inversion* H.
Qed.

Lemma term_let_to_body : forall t1 t2, 
  term (trm_let t1 t2) -> term_body t2.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma body_to_term_let : forall t1 t2, 
  term_body t2 -> term t1 -> term (trm_let t1 t2).
Proof.
  intros. inversion* H.
Qed.

Hint Resolve body_to_term_abs body_to_term_let.

Hint Extern 1 (term_body ?t) =>
  match goal with 
  | H: context [trm_abs t] |- _ => 
    apply term_abs_to_body 
  | H: context [trm_let ?t1 t] |- _ => 
    apply (@term_let_to_body t1) 
  end.

(** ** Opening a body with a term gives a term *)

Lemma trm_open_term : forall t u,
  term_body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@trm_subst_intro y).
Qed.

Hint Resolve trm_open_term.


(* ====================================================================== *)
(** * Properties of types *)

(** Open on a type is the identity. *)

Lemma typ_open_type : forall T Us,
  type T -> T = typ_open T Us.
Proof.
  introv W. induction T; simpls; inversions W; f_equal*.
Qed.

(** Substitution for a fresh name is identity. *)

Definition disjoint s1 s2 :=
  forall x, x \notin s1 \/ x \notin s2.

Lemma self_in_singleton : forall v, v \in {{v}}.
Proof.
  intros; apply* (proj2 (in_singleton v v)).
Qed.

Hint Resolve self_in_singleton.

Lemma disjoint_notin : forall s v,
  disjoint s {{v}} -> v \notin s.
Proof.
  intros.
  destruct* (H v).
Qed.

Hint Resolve disjoint_notin.

Lemma get_notin_dom : forall A x (S : Env.env A),
  x # S -> get x S = None.
Proof.
  induction S; intros. auto.
  destruct a; simpl in *.
  destruct (eq_var_dec x v).
    rewrite e in H. elim H. auto with sets.
  auto with sets.
Qed.

Lemma typ_subst_fresh : forall S T, 
  disjoint (dom S) (typ_fv T) ->
  typ_subst S T = T.
Proof.
  intros. induction T; simpls; f_equal*.
    rewrite* get_notin_dom.
    apply IHT1.
    intro v; destruct* (H v).
  apply IHT2.
  intros v; destruct* (H v).
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

Lemma typ_subst_fresh_list : forall S ts,
  disjoint (dom S) (typ_fv_list ts) ->
  ts = List.map (typ_subst S) ts.
Proof.
  induction ts; simpl; intros Fr.
  auto. f_equal. rewrite~ typ_subst_fresh.
    intro v; destruct* (Fr v).
  apply IHts.
    intro v; destruct* (Fr v).
Qed.

Lemma typ_subst_fresh_trm_fvars : forall S xs,
  fresh (dom S) (length xs) xs ->
  typ_fvars xs = List.map (typ_subst S) (typ_fvars xs).
Proof.
  intros. apply typ_subst_fresh_list.
  induction xs; intro v; simpls. auto.
    destruct H.
    destruct* (eq_var_dec v a).
  destruct (fresh_union_r _ _ _ _ H0).
  destruct* (IHxs H1 v).
Qed.

(** Substitution distributes on the open operation. *)

Lemma typ_subst_open : forall S T1 T2, env_prop type S -> 
  typ_subst S (typ_open T1 T2) = 
   typ_open (typ_subst S T1) (List.map (typ_subst S) T2).
Proof.
  intros. induction T1; intros; simpl; f_equal*.
  apply list_map_nth. apply* typ_subst_fresh.
    intro; auto.
  case_eq (get v S); intros. apply* typ_open_type. apply (H v t H0).
  auto.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma typ_subst_open_vars : forall S Ys T, 
  fresh (dom S) (length Ys) Ys -> 
  env_prop type S ->
     typ_open_vars (typ_subst S T) Ys
   = typ_subst S (typ_open_vars T Ys).
Proof.
  introv Fr Tu. unfold typ_open_vars.
  rewrite* typ_subst_open. f_equal.
  induction Ys; simpls. auto.
  destruct Fr.
  rewrite* get_notin_dom.
  rewrite* <- IHYs.
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

Lemma map_combine : forall (A:Set) (f:A->A) Xs Ys,
  map f (combine Xs Ys) = combine Xs (List.map f Ys).
Proof.
  induction Xs; destruct Ys; simpl*.
  rewrite* IHXs.
Qed.

Lemma kinds_subst_open_vars : forall S Ks Xs,
  fresh (dom S) (length Xs) Xs ->
  env_prop type S ->
  map (kind_subst S) (kinds_open_vars Ks Xs) =
  kinds_open_vars (List.map (kind_subst S) Ks) Xs.
Proof.
  unfold kinds_open_vars.
  intros.
  rewrite map_combine.
  apply (f_equal (combine Xs (B:=kind))).
  unfold kinds_open.
  induction* Ks.
  simpls. rewrite IHKs.
  rewrite* kind_subst_open_vars.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma typ_subst_nil : forall T,
  typ_subst nil T = T.
Proof.
  induction T; simpl; auto.
  rewrite IHT1; rewrite* IHT2.
Qed.

Lemma typ_subst_nth : forall n S Xs Us,
  fresh (dom S) (length Xs) Xs ->
  types (length Xs) Us ->
  nth n Us typ_def =
  typ_subst (combine Xs Us & S) (typ_open_vars (typ_bvar n) Xs).
Proof.
  induction n; intros;
    destruct H0; destruct Xs; destruct Us; try discriminate; simpls; auto.
    assert (Bv: binds v t ((v, t) :: combine Xs Us)).
      unfold binds; simpl.
      destruct* (eq_var_dec v v).
    rewrite* (binds_concat_fresh S Bv).
  destruct H.
  unfold typ_open_vars in *; simpl in *.
  rewrite* (IHn (S ++ (v,t)::nil) Xs).
    unfold concat. rewrite* app_ass.
    fold (((v,t)::nil) & S).
    rewrite* dom_concat.
  split. inversion* H0.
  inversion* H1.
Qed.

Lemma fresh_rev : forall x L n xs,
  fresh L n xs -> x \in L -> ~In x xs.
Proof.
  induction n; destruct xs; simpl; intros; auto.
  intros [e | i].
    elim (proj1 H); rewrite e; auto.
  elim (IHn xs); auto*.
Qed.

Lemma in_dom_combine : forall (A:Set) v Xs (Us:list A),
  v \in dom (combine Xs Us) -> In v Xs.
Proof.
  induction Xs; destruct Us; simpl; auto; intros.
    elim (in_empty H).
  destruct (proj1 (in_union _ _ _) H).
    rewrite* (proj1 (in_singleton _ _) H0).
  auto*.
Qed.

Lemma typ_subst_intro : forall Xs Us T, 
  fresh (typ_fv T \u typ_fv_list Us) (length Xs) Xs -> 
  types (length Xs) Us ->
  (typ_open T Us) = typ_subst (combine Xs Us) (typ_open_vars T Xs).
Proof.
  induction T; simpls; intros.
    rewrite <- (concat_empty (combine Xs Us)).
    apply* typ_subst_nth.
    rewrite* get_notin_dom.
    destruct (fresh_union_r _ _ _ _ H).
    intro; elim (fresh_rev _ _ H1 (x:=v)). auto.
    eapply in_dom_combine. apply H3.
  rewrite* IHT1.
  rewrite* IHT2.
Qed.

(** Types are stable by type substitution *)

Lemma typ_subst_type : forall S T,
  env_prop type S -> type T -> type (typ_subst S T).
Proof.
  induction 2; simpl*.
  case_eq (get X S); intros; auto*.
    apply* (H X).
Qed.

Hint Resolve typ_subst_type.

(** List of types are stable by type substitution *)

Lemma typ_subst_type_list : forall S Ts n,
  env_prop type S -> types n Ts -> 
  types n (List.map (typ_subst S) Ts).
Proof.
  unfold types, list_for_n.
  induction Ts; destruct n; simpl; intros TU [EQ TT]. 
  auto. auto. inversion EQ.
  inversions TT. forward~ (IHTs n) as [K1 K2].
Qed.

(** ** Opening a body with a list of types gives a type *)

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

Lemma typ_open_types : forall T Us Ks,
  typ_body T Ks ->
  types (length Ks) Us -> 
  type (typ_open T Us).
Proof. 
  introv [L K] WT. pick_freshes (length Ks) Xs.
  rewrite* (@typ_subst_intro Xs). apply* typ_subst_type.
    apply list_forall_env_prop. destruct* WT.
    destruct* (K Xs).
  rewrite* <- (fresh_length _ _ _ Fr).
Qed.


(* ====================================================================== *)
(** * Properties of schemes *)

(** Substitution for a fresh name is identity. *)

Lemma kind_subst_fresh : forall S K,
  disjoint (dom S) (typ_fv_list (kind_types K)) ->
  kind_subst S K = K.
Proof.
  intros.
  destruct* K as [[C R]|].
  unfold kind_map; simpl.
  apply (f_equal (fun R => Some (Kind C R))).
  unfold kind_types in H. simpl in H.
  induction* R.
  destruct a; simpl in H.
  simpl; rewrite* IHR.
    rewrite* typ_subst_fresh.
    intro x; destruct* (H x).
  intro x; destruct* (H x).
Qed.

Lemma sch_subst_fresh : forall S M, 
  disjoint (dom S) (sch_fv M) -> 
  sch_subst S M = M.
Proof.
  intros. destruct M as [T K]. unfold sch_subst.
  rewrite* typ_subst_fresh.
    simpl. apply (f_equal (Sch T)).
    induction* K. unfold sch_fv in *; simpl in *; rewrite* IHK.
      rewrite* kind_subst_fresh.
      unfold kind_fv in H.
      intro x; destruct* (H x).
    intro x; destruct* (H x).
  intro x; destruct* (H x).
  right; unfold sch_fv in H0; simpl in *. auto.
Qed.

(** Trivial lemma to unfolding definition of [sch_subst] by rewriting. *)

Lemma sch_subst_fold : forall S T K,
  Sch (typ_subst S T) (List.map (kind_subst S) K) = sch_subst S (Sch T K).
Proof.
  auto.
Qed. 

(** Distributivity of type substitution on opening of scheme. *)

Lemma sch_subst_open : forall S M Us,
   env_prop type S ->
    typ_subst S (sch_open M Us)
  = sch_open (sch_subst S M) (List.map (typ_subst S) Us).
Proof.
  unfold sch_open. intros. destruct M. simpl.
  rewrite* <- typ_subst_open.
Qed.

(** Distributivity of type substitution on opening of scheme with variables. *)

Lemma sch_subst_open_vars : forall S M Xs,
   fresh (dom S) (length Xs) Xs -> 
   env_prop type S ->
    typ_subst S (sch_open_vars M Xs)
  = sch_open_vars (sch_subst S M) Xs.
Proof.
  unfold sch_open_vars. intros. destruct M.
  rewrite* <- typ_subst_open_vars.
Qed.

(** Distributivity of type substitution on opening of kinds. *)

Lemma kind_subst_open : forall S k Us,
  env_prop type S ->
  kind_subst S (kind_open k Us) =
  kind_open (kind_subst S k) (List.map (typ_subst S) Us).
Proof.
  intros.
  destruct* k as [[kc kr]|].
  simpl; unfold ckind_map; simpl.
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

(** Properties of wellkindedness *)

Lemma well_kinded_extend : forall K K' x T,
  disjoint (dom K) (dom K') ->
  well_kinded K x T -> well_kinded (K & K') x T.
Proof.
  induction 2.
    apply wk_any.
  apply* wk_kind.
  apply* binds_concat_fresh.
  destruct* (H x).
  elim (binds_fresh H0 H2).
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
  apply* wk_kind.
  destruct* (binds_concat_inv H).
  destruct H1.
  destruct* (binds_concat_inv H2).
Qed.

Lemma disjoint_union : forall A B C,
  disjoint A C -> disjoint B C -> disjoint (A \u B) C.
Proof.
  intros. intro x; destruct* (H x); destruct* (H0 x).
Qed.

Lemma disjoint_comm : forall A B,
  disjoint A B -> disjoint B A.
Proof.
  intros. intro x; destruct* (H x).
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

(** Properties of constants *)

Definition const_app c vl := fold_left trm_app vl (trm_cst c).

Lemma trm_inst_app : forall c tl pl,
  trm_inst_rec 0 tl (const_app c pl) =
  const_app c (List.map (trm_inst_rec 0 tl) pl).
Proof.
  introv.
  rewrite <- (rev_involutive pl).
  induction (rev pl). simpl. auto.
  unfold const_app in *. simpl in *.
  rewrite map_app.
  rewrite fold_left_app.
  rewrite fold_left_app.
  simpl. unfold trm_inst. simpl. rewrite <- IHl. auto.
Qed.

Lemma const_app_inv : forall c pl,
  pl = nil \/
  exists t1, exists t2, const_app c pl = trm_app t1 t2.
Proof.
  intros.
  destruct* pl.
  right.
  destruct* (exists_last (l:=t::pl)). intro; discriminate.
  destruct s. rewrite e. unfold const_app.
  rewrite fold_left_app. simpl.
  exists (fold_left trm_app x (trm_cst c)).
  exists* x0.
Qed.
  
Lemma trm_inst_app_inv : forall c pl tl,
  pl = nil \/
  exists t1, exists t2,
    trm_inst (const_app c pl) tl = trm_app t1 t2.
Proof.
  intros.
  destruct* (const_app_inv c pl).
  right.
  destruct H as [x1 [x2 e]].
  rewrite e.
  exists (trm_inst x1 tl).
  exists* (trm_inst x2 tl).
Qed.

Lemma const_app_eq : forall c1 vl1 c2 vl2,
  const_app c1 vl1 = const_app c2 vl2 -> c1 = c2 /\ vl1 = vl2.
Proof.
  intros.
  rewrite <- (rev_involutive vl1) in *.
  rewrite <- (rev_involutive vl2) in *.
  generalize (rev vl2) H. clear vl2 H.
  induction (rev vl1). intros; destruct l.
    inversion H. auto.
    unfold const_app in H. simpl in H; rewrite fold_left_app in H. discriminate.
  intros; destruct l0;
    unfold const_app in H; simpl in H; rewrite fold_left_app in H.
      discriminate.
  destruct (IHl l0); rewrite fold_left_app in H; simpl in H; inversion* H.
  simpl. subst c1; rewrite* H1.
Qed.



(* Extra properties *)

Lemma list_forall_map(A B:Set)(f:A->B)(PA:A->Prop)(PB:B->Prop)(l:list A):
  (forall x, In x l -> PA x -> PB (f x)) ->
  list_forall PA l ->
  list_forall PB (List.map f l).
Proof.
  intros; induction l.
    simpl*.
  inversion H0.
  simpl; constructor; auto.
Qed.

Lemma list_for_n_map(A B:Set)(f:A->B)(PA:A->Prop)(PB:B->Prop)(n:nat)(l:list A):
  (forall x, In x l -> PA x -> PB (f x)) ->
  list_for_n PA n l ->
  list_for_n PB n (List.map f l).
Proof.
  intros.
  destruct H0; split. rewrite* map_length.
  apply* list_forall_map.
Qed.

Lemma All_kind_types_map (f:typ->typ) (P : typ -> Prop) k:
  (forall x, P x -> P (f x)) ->
  All_kind_types P k -> All_kind_types P (kind_map f k).
Proof.
  intros. unfold All_kind_types in *.
  unfold kind_types in *.
  simpl.
  destruct* k as [[kc kr]|].
  simpl in *.
  induction* kr.
  destruct a. simpl in *. 
  destruct H0; split; auto.
Qed.

Lemma For_all2_map: forall (A B:Set)(P P':A->B->Prop) f g l1 l2,
  (forall x y, P x y -> P' (f x) (g y)) ->
  For_all2 P l1 l2 ->
  For_all2 P' (List.map f l1) (List.map g l2).
Proof.
  induction l1; introv; elim l2; simpls; auto*.
Qed.

Lemma list_map_comp : forall (A:Set) (f g:A->A) l,
  List.map f (List.map g l) = List.map (fun x:A => f (g x)) l.
Proof.
  induction l; simpl*. rewrite* IHl.
Qed.

Lemma list_map_ext : forall (A B:Set) (l:list A) (f1 f2:A->B),
  (forall x, In x l -> f1 x = f2 x) ->
  List.map f1 l = List.map f2 l.
Proof.
  intros. induction l. auto.
  simpl. rewrite* H. rewrite* IHl.
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

Lemma binds_combine : forall (A:Set) x (c:A) Ys Ks,
  binds x c (combine Ys Ks) -> In c Ks.
Proof.
  induction Ys; destruct Ks; simpl; intros; try (elim (binds_empty H)).
  unfold binds in H. simpl in H.
  destruct* (eq_var_dec x a). inversion* H.
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

Lemma in_mkset : forall x Xs,
  In x Xs -> x \in mkset Xs.
Proof.
  induction Xs; intros. elim H.
  simpl in H; destruct H.
    simpl; rewrite* H. auto with sets.
  simpl. eauto with sets.
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

Lemma ok_cons : forall (A:Set) (E:Env.env A) x (a:A),
  ok E -> x # E -> ok ((x,a) :: E).
Proof. exact ok_push. Qed.

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

Lemma notin_combine_fresh : forall (A:Set) Xs v (Vs:list A) n L,
  fresh L n Xs -> v \in L -> v # (combine Xs Vs).
Proof.
  induction Xs; simpl; intros. auto.
  destruct* Vs. auto with sets.
  destruct n. elim H.
  destruct H.
  apply (proj2 (notin_union v {{a}} (dom (combine Xs Vs)))).
  split.
    intro Hv. elim H.
    rewrite* <- (proj1 (in_singleton _ _) Hv).
  apply* IHXs. auto with sets.
Qed.

Lemma ok_combine_fresh : forall (A:Set) L n Xs (Vs:list A),
  fresh L n Xs -> ok (combine Xs Vs).
Proof.
  induction n; destruct Xs; simpl; intros; destruct* Vs;
    try apply (ok_empty A).
  apply* ok_cons.
  apply* notin_combine_fresh.
  destruct H; auto with sets.
Qed.

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
        
(** Properties of entailment. *)

Lemma entails_refl : forall k, entails k k.
Proof.
  intros. split*.
Qed.

Lemma entails_trans : forall k1 k2 k3,
  entails k1 k2 -> entails k2 k3 -> entails k1 k3.
Proof.
  intros.
  destruct H; destruct H0.
  split.
  apply* (Cstr.entails_trans H H0).
  intros; auto.
Qed.

Lemma kind_subst_entails : forall S k k',
  entails k' k ->
  entails (ckind_map (typ_subst S) k') (ckind_map (typ_subst S) k).
Proof.
  intros.
  destruct H.
  destruct k as [kc kr]; destruct k' as [kc' kr'].
  split; simpl*.
  intros; simpl in *.
  destruct (proj1 (in_map_iff _ _ _) H1) as [T' [e i]].
  rewrite <- e.
  apply* (in_map (fun XT : var * typ => (fst XT, typ_subst S (snd XT)))).
Qed.

Lemma map_coherent : forall f k,
  coherent k -> coherent (ckind_map f k).
Proof.
  intros. intro; intros.
  destruct k as [kc kr].
  use (H x); simpl in *.
  destruct (proj1 (in_map_iff _ _ _) H1) as [[x' T'] [Heq Hin]].
  simpl in Heq; inversions Heq.
  destruct (proj1 (in_map_iff _ _ _) H2) as [[x' U'] [Heq' Hin']].
  simpl in Heq'; inversions Heq'.
  rewrite* (H3 T' U').
Qed.

Hint Resolve map_coherent.

(** Schemes are stable by type substitution. *)

Lemma sch_subst_type : forall S M,
  env_prop type S -> scheme M -> scheme (sch_subst S M).
Proof.
  unfold scheme. intros S [T Ks] TU [[L K] TK].
  simpls. split.
    exists (L \u dom S).
    unfold sch_arity in *; simpl; rewrite map_length; introv Fr.
      simpls; destruct* (K Xs); clear K. destruct* (fresh_union_r _ _ _ _ Fr).
    split.
      rewrite* typ_subst_open_vars.
    apply* list_forall_map.
    clear H0; intros.
    unfold kind_subst; apply* All_kind_types_map.
    intros; rewrite* typ_subst_open_vars.
  simpl sch_kinds in *.
  apply* list_forall_map.
  intros.
  destruct x; simpl; auto.
  unfold kind_ok in H0.
  destruct c as [kc kr].
  auto*.
Qed.

Hint Resolve sch_subst_type.

(** Scheme arity is preserved by type substitution. *)

Lemma sch_subst_arity : forall S M, 
  sch_arity (sch_subst S M) = sch_arity M.
Proof.
  intros; unfold sch_arity. simpl; rewrite* map_length.
Qed.

(** ** Opening a scheme with a list of types gives a type *)

Lemma sch_open_types : forall M Us,
  scheme M ->
  types (sch_arity M) Us ->
  type (sch_open M Us).
Proof. 
  unfold scheme, sch_open. intros [T K] Us WB [Ar TU].
  simpls. apply* typ_open_types.
Qed.

Hint Resolve sch_open_types.

(* ====================================================================== *)
(** * Properties of judgments *)

Module MkJudgInfra(Delta:DeltaIntf).
Module Judge := MkJudge(Delta).
Import Judge.
Hint Constructors typing valu red.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall gc K E e T,
  typing gc K E e T -> kenv_ok K /\ ok E /\ term e /\ type T.
Proof.
  split4; induction* H.
  (* ok *)
  pick_fresh y. apply* (H1 y).
  pick_fresh y. apply* (H2 y).
  pick_freshes (length Ks) Xs. forward~ (H1 Xs).
    intro. split.
      destruct* (ok_concat_inv _ _ (proj1 H2)).
    intros x k B. apply (proj2 H2 x k).
    apply* binds_concat_ok. destruct* H2.
  pick_fresh y. forward~ (H1 y) as G. inversions* G.
  pick_fresh y. forward~ (H2 y) as G. inversions* G.
  pick_freshes (length Ks) Xs. forward~ (H1 Xs).
  (* term *) 
  apply_fresh* term_let as y.
    pick_freshes (sch_arity M) Xs.
    forward~ (H0 Xs) as G.
  pick_freshes (length Ks) Xs. forward~ (H1 Xs).
  (* type *)
  pick_fresh y. unfold proper_instance in H2. auto*.
  pick_fresh y. forward~ (H1 y).
  pick_fresh y. forward~ (H2 y).
  inversion* IHtyping1.
  (* const *)
  destruct (Delta.type c) as [ct ck].
  destruct H1 as [[Hlen HT] [Hc _]].
  unfold scheme in Hc; unfold sch_open; simpl in *.
  apply* typ_open_types.
  pick_freshes (length Ks) Xs. forward~ (H1 Xs).
Qed.

Lemma kenv_ok_is_ok : forall K, kenv_ok K -> ok K.
Proof.
  unfold kenv_ok. tauto.
Qed.

Hint Resolve kenv_ok_is_ok.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  intros. destruct H. induction H; auto.
Qed.

(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  induction 1; use value_regular.
  apply* Delta.term.
Qed.

(* ********************************************************************** *)
(** ** Automation *)

(** Automation for reasoning on well-formedness. *)

Hint Extern 1 (kenv_ok ?K) =>
  match goal with
  | H: typing _ K _ _ _ |- _ => apply (proj41 (typing_regular H))
  end.

Hint Extern 1 (ok ?E) =>
  match goal with
  | H: typing _ _ E _ _ |- _ => apply (proj42 (typing_regular H))
  end.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: typing _ _ _ t _ |- _ => apply (proj43 (typing_regular H))
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  | H: value t |- _ => apply (value_regular H)
  end.

Hint Extern 1 (type ?T) => match goal with
  | H: typing _ _ _ _ T |- _ => apply (proj44 (typing_regular H))
  end.

End MkJudgInfra.

End MkInfra.
