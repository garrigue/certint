(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Infrastructure             *
* Arthur Charguéraud, March 2007, Coq v8.1                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import List Metatheory ML_SP_Definitions.


(* ====================================================================== *)
(** * Additional Definitions used in the Proofs *)

(* ********************************************************************** *)
(** ** Free Variables *)

(** Computing free variables of a type. *)

Fixpoint typ_fv (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar i      => {}
  | typ_fvar x      => {{x}}
  | typ_arrow T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

(** Computing free variables of a list of terms. *)

Definition typ_fv_list :=
  List.fold_right (fun t acc => typ_fv t \u acc) {}.

(** Variants looking up a kinding environment *)

Definition kind_fv k :=
  typ_fv_list (kind_types k).

Definition kind_fv_list :=
  List.fold_right (fun t acc => kind_fv t \u acc) {}.

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

(** Computing free variables of a type scheme. *)

Definition sch_fv M := 
  typ_fv_list (sch_type M :: flat_map kind_types (sch_kinds M)).

(** Computing free type variables of the values of an environment. *)

Definition env_fv := 
  fv_in sch_fv.

(** Computing free variables of a term. *)

Fixpoint trm_fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => {}
  | trm_fvar x    => {{x}}
  | trm_abs t1    => (trm_fv t1)
  | trm_let t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_app t1 t2 => (trm_fv t1) \u (trm_fv t2)
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

Definition kind_map f K :=
  match K with
  | None => None
  | Some k =>
    Some (Kind (kind_cstr k)
               (List.map (fun XT:var*typ => (fst XT, f (snd XT)))
                 (kind_rel k)))
  end.

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

Hint Constructors type term typing value red.

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

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma typ_subst_nil : forall T,
  typ_subst nil T = T.
Proof.
  induction T; simpl; auto.
  rewrite IHT1; rewrite* IHT2.
Qed.

(*
Lemma typ_substs_intro_ind : forall T Xs Us Vs, 
  fresh (typ_fv T \u typ_fv_list Vs \u typ_fv_list Us) (length Xs) Xs -> 
  types (length Xs) Us ->
  types (length Vs) Vs ->
  typ_open T (Vs ++ Us) =
  typ_subst (combine Xs Us) (typ_open T (Vs ++ (typ_fvars Xs))).
Proof.
  induction Xs; simpl; introv Fr Tu Tv; 
   destruct Tu; destruct Us; try solve [ contradictions ].
   rewrite* typ_subst_nil.
  auto.
  inversions H0. inversions Fr. clear H0 Fr. simpls.
  rewrite list_concat_right.
  forward (IHXs Us (Vs++t::nil)) as K; clear IHXs.
    rewrite* fv_list_map.
    auto. 
    split~. inversions Tv. apply* list_forall_concat.  
  rewrite K. clear K.
  f_equal. rewrite~ typ_subst_open. rewrite~ typ_subst_fresh.
  f_equal. rewrite map_app.
  simpl. case_var; try solve [ contradictions* ].
  rewrite <- list_concat_right. 
  f_equal. apply~ typ_subst_fresh_list.
  f_equal. apply* typ_subst_fresh_trm_fvars.
Qed.
*)

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

Lemma types_combine : forall Xs Us,
  types (length Xs) Us -> env_prop type (combine Xs Us).
Proof.
  induction Xs; destruct Us; intros; destruct* H; try discriminate;
    intros v u; unfold binds; simpl; intro B.
    discriminate.
  destruct (eq_var_dec v a).
    inversion B as [e']; rewrite <- e'. inversion* H0.
  assert (HT: types (length Xs) Us).
    split. simpl in H; inversion* H.
    inversion* H0.
  apply* (IHXs Us HT v).
Qed.

Lemma typ_open_types : forall T Us Ks,
  typ_body (length Us) T Ks ->
  types (length Us) Us -> 
  type (typ_open T Us).
Proof. 
  introv [L K] WT. pick_freshes (length Us) Xs. poses Fr' Fr.
  rewrite (fresh_length _ _ _  Fr) in WT, Fr'.
  rewrite* (@typ_subst_intro Xs). apply* typ_subst_type.
    apply* types_combine.
  destruct* (K Xs).
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
  unfold kind_map. simpl. apply (f_equal (fun R => Some (Kind C R))).
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
      rewrite fv_list_map in H; auto*.
      intro x; destruct* (H x).
    rewrite fv_list_map in H.
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
  destruct* k as [k|].
  simpl.
  induction* (kind_rel k).
  destruct a; simpl in *.
  destruct H0; split; auto.
Qed.

(** Schemes are stable by type substitution. *)

Lemma sch_subst_type : forall S M,
  env_prop type S -> scheme M -> scheme (sch_subst S M).
Proof.
  unfold scheme, sch_subst. intros S [T Ks] TU TS.
  simpls. destruct TS as [L K]. exists (L \u dom S).
  unfold sch_arity in *; simpl; rewrite map_length; introv Fr.
    simpls; destruct* (K Xs); clear K. destruct* (fresh_union_r _ _ _ _ Fr).
  split.
    rewrite* typ_subst_open_vars.
  apply* list_for_n_map.
  clear H0; intros.
  unfold kind_subst; apply* All_kind_types_map.
  intros; rewrite* typ_subst_open_vars.
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
  simpls. rewrite Ar in *. apply* typ_open_types.
Qed.

Hint Resolve sch_open_types.


(* ====================================================================== *)
(** * Properties of judgments *)

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall K E e T,
  typing K E e T -> ok E /\ term e /\ type T.
Proof.
  split3; induction* H.
  (* ok *)
  pick_fresh y. forward~ (H1 y) as G. inversions* G.
  pick_fresh y. forward~ (H2 y) as G. inversions* G.
  (* term *) 
  apply_fresh* term_let as y.
    pick_freshes (sch_arity M) Xs.
    forward~ (H0 Xs) as G.
    unfold proper_instance in H2. auto*.
  (* type *)
  pick_fresh y. forward~ (H1 y). 
  pick_fresh y. forward~ (H2 y).   
  inversion* IHtyping1.
Qed. 

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  induction 1; auto*.
Qed.

(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  induction 1; use value_regular.
Qed.

(* ********************************************************************** *)
(** ** Automation *)

(** Automation for reasoning on well-formedness. *)

Hint Extern 1 (ok ?E) =>
  match goal with
  | H: typing E _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: typing _ t _ |- _ => apply (proj32 (typing_regular H))
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  | H: value t |- _ => apply (value_regular H)
  end.

Hint Extern 1 (type ?T) => match goal with
  | H: typing _ _ T |- _ => apply (proj33 (typing_regular H))
  end.



