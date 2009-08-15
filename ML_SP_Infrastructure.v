(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Infrastructure             *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - May 2008                                *
***************************************************************************)

Set Implicit Arguments.
Require Import List Metatheory ML_SP_Definitions.
Require Import ProofIrrelevance.

(* ====================================================================== *)
(** * The infrastructure needs to be parameterized over definitions *)

Module MkInfra(Cstr:CstrIntf)(Const:CstIntf).

Module Defs := MkDefs(Cstr)(Const).
Import Defs.

(* These tactics needs definitions *)

Ltac length_hyps :=
  instantiate_fail;
  repeat match goal with
  | H: fresh _ _ _ |- _ => puts (fresh_length _ _ _ H); clear H
  | H: types _ _ |- _ => puts (proj1 H); clear H
  | H: list_for_n _ _ _ |- _ => puts (proj1 H); clear H
  | H: list_forall2 _ _ _ |- _ => puts (list_forall2_length H); clear H
  | H: split _ = (_,_) |- _ => puts (split_length _ H); clear H
  end;
  repeat progress
    (simpl in *; unfold typ_fvars, kinds_open_vars, kinds_open in *;
      try rewrite map_length in *; try rewrite app_length in *).

Hint Extern 1 (_ = length _) => length_hyps; omega.
Hint Extern 1 (length _ = _) => length_hyps; omega.

Lemma dom_kinds_open_vars : forall Xs Ks,
  length Ks = length Xs ->
  dom (kinds_open_vars Ks Xs) = mkset Xs.
Proof.
  intros. unfold kinds_open_vars; rewrite* dom_combine.
Qed.

Ltac disjoint_simpls :=
  repeat match goal with
  | H: fresh _ _ _ |- _ =>
    let Hf := fresh "Hf" in poses Hf (fresh_disjoint _ _ H);
    let Hn := fresh "Hn" in poses Hn (fresh_length _ _ _ H); clear H
  | H: ok (_ & _) |- _ =>
    let Ho := fresh "Ho" in poses Ho (ok_disjoint _ _ H); clear H
  | H: kenv_ok (_ & _) |- _ =>
    let Hk := fresh "Hk" in poses Hk (ok_disjoint _ _ (proj1 H)); clear H
  | H: binds _ _ _ |- _ =>
    let Hb := fresh "Hb" in poses Hb (binds_dom H); clear H
  | H: get _ _ = None |- _ =>
    let Hn := fresh "Hn" in poses Hn (get_none_notin _ H); clear H
  | H: In _ _ |- _ =>
    let Hi := fresh "Hi" in poses Hi (in_mkset H); clear H
  | H: ~In _ _ |- _ =>
    let Hn := fresh "Hn" in poses Hn (notin_mkset _ H); clear H
  | x := ?y : env _ |- _ => subst x
  end.

Ltac disjoint_solve :=
  instantiate_fail;
  disjoint_simpls;
  fold kind in *; unfold env_fv in *;
  repeat progress
    (simpl dom in *; simpl fv_in in *; simpl typ_fv in *;
     try rewrite dom_concat in *; try rewrite fv_in_concat in *;
     try rewrite dom_map in *;
     try (rewrite dom_combine in * by (length_hyps; omega));
     try (rewrite dom_kinds_open_vars in * by (length_hyps; omega)));
  sets_solve.

Hint Extern 1 (_ \in _) => solve [disjoint_solve].
Hint Extern 1 (_ << _) => solve [disjoint_solve].
Hint Extern 1 (_ \notin _) => solve [disjoint_solve].
Hint Extern 1 (disjoint _ _) => solve [disjoint_solve].

Lemma disjoint_fresh : forall n L1 Xs L2,
  fresh L1 n Xs ->
  disjoint L2 (mkset Xs) ->
  fresh L2 n Xs.
Proof.
  induction n; destruct Xs; simpl; intros; auto; try discriminate.
  split*.
Qed.

Ltac env_ok_hyps :=
  repeat match goal with
  | H: env_ok _ |- _ => destruct H
  end.

Ltac kenv_ok_hyps :=
  repeat match goal with
  | H: kenv_ok _ |- _ => destruct H
  end.

Ltac env_ok_solve :=
  env_ok_hyps; split; [ok_solve | env_prop_solve].

Ltac kenv_ok_solve :=
  kenv_ok_hyps; split; [ok_solve | env_prop_solve].

Hint Extern 2 (env_ok _) => solve [env_ok_solve].
Hint Extern 2 (kenv_ok _) => solve [kenv_ok_solve].

(* ====================================================================== *)
(** * Additional Definitions used in the Proofs *)

(* ********************************************************************** *)
(** ** Free Variables *)

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

Hint Constructors type term well_kinded.

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
  trm_open_rec j v t = trm_open_rec i u (trm_open_rec j v t) ->
  t = trm_open_rec i u t.
Proof.
  induction t; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*. 
Qed.

Lemma trm_open_rec : forall t u,
  term t -> forall k, t = trm_open_rec k u t.
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

Lemma typ_subst_fresh : forall S T, 
  disjoint (dom S) (typ_fv T) ->
  typ_subst S T = T.
Proof.
  intros. induction T; simpls; f_equal*.
  rewrite* get_notin_dom.
Qed.

Lemma ckind_pi : forall k k',
  kind_cstr k = kind_cstr k' ->
  kind_rel k = kind_rel k' ->
  k = k'.
Proof.
  intros [kc kv kr kh] [kc' kv' kr' kh']; simpl; intros.
  subst.
  rewrite (proof_irrelevance _ kv kv').
  rewrite (proof_irrelevance _ kh kh').
  auto.
Qed.

Lemma kind_pi : forall k k',
  kind_cstr k = kind_cstr k' ->
  kind_rel k = kind_rel k' ->
  Some k = Some k'.
Proof.
  intros. rewrite* (ckind_pi k k').
Qed.

Lemma kind_subst_fresh : forall S k,
  disjoint (dom S) (kind_fv k) ->
  kind_subst S k = k.
Proof.
  unfold kind_subst, kind_fv, kind_types.
  intros; destruct k as [[kc kv kr kh]|]; simpl*.
  apply* kind_pi; simpl in *.
  clear -H; induction* kr; intros.
  destruct a; simpl.
  rewrite* IHkr.
    rewrite* typ_subst_fresh. simpl in H. auto.
  simpl in *. auto.
Qed.

Lemma typ_subst_fresh_list : forall S ts,
  disjoint (dom S) (typ_fv_list ts) ->
  ts = List.map (typ_subst S) ts.
Proof.
  induction ts; simpl; intros Fr.
  auto. f_equal*. rewrite~ typ_subst_fresh.
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
  use (IHxs H1).
Qed.

(** Substitution distributes on the open operation. *)

Lemma typ_subst_open : forall S T1 T2, env_prop type S -> 
  typ_subst S (typ_open T1 T2) = 
   typ_open (typ_subst S T1) (List.map (typ_subst S) T2).
Proof.
  intros. induction T1; intros; simpl; f_equal*.
  apply list_map_nth. apply* typ_subst_fresh.
  case_eq (get v S); intros. apply* typ_open_type.
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
  destruct* k as [[kc kv kr kh]|].
  simpl.
  apply* kind_pi; simpl.
  clear kh; induction* kr.
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

Lemma typ_subst_nth : forall S1 n S Xs Us,
  fresh (dom S) (length Xs) Xs ->
  types (length Xs) Us ->
  nth n Us typ_def =
  typ_subst (S1 & combine Xs Us & S) (typ_open_vars (typ_bvar n) Xs).
Proof.
  induction n; intros; destruct H0; destruct Xs; destruct Us;
    rewrite concat_assoc; simpls; try discriminate; auto.
    assert (Bv: binds v t ((v, t) :: combine Xs Us)).
      unfold binds; simpl.
      destruct* (eq_var_dec v v).
    destruct H; assert (v # S) by auto.
    rewrite* (binds_prepend S1 (binds_concat_fresh S Bv H3)).
  destruct H.
  unfold typ_open_vars in *; simpl in *.
  rewrite* (IHn (S ++ (v,t)::nil) Xs).
    fold (((v,t)::nil) & S).
    repeat rewrite <- concat_assoc. simpl*.
  fold (((v,t)::nil) & S).
  rewrite* dom_concat.
Qed.

Lemma typ_subst_intro0 : forall S Xs Us T, 
  fresh (typ_fv T) (length Xs) Xs -> 
  types (length Xs) Us ->
  env_prop type S ->
  typ_open (typ_subst S T) Us =
  typ_subst (S & combine Xs Us) (typ_open_vars T Xs).
Proof.
  induction T; simpls; intros.
      rewrite <- (concat_empty (combine Xs Us)).
      rewrite <- concat_assoc.
      apply* typ_subst_nth.
    case_eq (get v S); intros.
      rewrite* (binds_concat_fresh (combine Xs Us) H2).
      rewrite* <- typ_open_type.
    rewrite* get_notin_dom.
  rewrite* IHT1. rewrite* IHT2.
Qed.

Lemma typ_subst_intro : forall Xs Us T, 
  fresh (typ_fv T) (length Xs) Xs -> 
  types (length Xs) Us ->
  (typ_open T Us) = typ_subst (combine Xs Us) (typ_open_vars T Xs).
Proof.
  intros.
  rewrite (app_nil_end (combine Xs Us)).
  fold (empty(A:=typ)).
  pattern T at 1.
  rewrite <- (typ_subst_fresh empty T).
    apply* (typ_subst_intro0 (S:=empty) Xs T (Us:=Us) H).
    intro; intros.
    elim H1.
  simpl; intro; auto.
Qed.

(** Types are stable by type substitution *)

Lemma typ_subst_type : forall S T,
  env_prop type S -> type T -> type (typ_subst S T).
Proof.
  induction 2; simpl*.
  case_eq (get X S); intros; auto*.
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

Lemma typ_open_types : forall T Us Ks,
  typ_body T Ks ->
  types (length Ks) Us -> 
  type (typ_open T Us).
Proof. 
  introv K WT. pick_freshes (length Ks) Xs.
  rewrite* (@typ_subst_intro Xs).
    apply* typ_subst_type. destruct* WT.
    destruct* (K Xs).
  rewrite* <- (fresh_length _ _ _ Fr).
Qed.


(* ====================================================================== *)
(** * Properties of schemes *)

(** Substitution for a fresh name is identity. *)

Lemma sch_subst_fresh : forall S M, 
  disjoint (dom S) (sch_fv M) -> 
  sch_subst S M = M.
Proof.
  intros. destruct M as [T K]. unfold sch_subst.
  unfold sch_fv in H; simpl in H.
  rewrite* typ_subst_fresh.
  simpl. apply (f_equal (Sch T)).
  induction* K.
  simpl in *; rewrite* IHK.
  rewrite* kind_subst_fresh.
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
  destruct* k as [[kc kv kr kh]|]; simpl.
  apply* kind_pi; simpl.
  clear kh; induction* kr.
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

(** Properties of entailment. *)

Lemma entails_refl : forall k, entails k k.
Proof.
  intros. split*.
Qed.
Hint Resolve entails_refl.

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
  destruct T.
  destruct (map_snd_inv _ _ _ _ H1) as [T' [e i]].
  rewrite <- e.
  apply* in_map_snd.
Qed.
Hint Resolve kind_subst_entails.

(** Properties of well-kindedness *)

Lemma well_kinded_extend : forall K K' x T,
  disjoint (dom K) (dom K') ->
  well_kinded K x T -> well_kinded (K & K') x T.
Proof.
  induction 2.
    apply wk_any.
  apply* wk_kind.
Qed.
Hint Resolve well_kinded_extend.

Lemma well_kinded_comm : forall K K' K'',
  ok (K & K' & K'') ->
  forall x T,
  well_kinded (K & K'' & K') x T ->
  well_kinded (K & K' & K'') x T.
Proof.
  introv OK; introv WK. gen_eq (K & K'' & K') as H. gen K''.
  induction WK; introv Ok EQ; subst.
    apply wk_any.
  apply* (@wk_kind k').
  destruct* (binds_concat_inv H).
  destruct H1.
  destruct* (binds_concat_inv H2).
Qed.

Lemma well_kinded_weaken : forall K K' K'',
  ok (K & K' & K'') ->
  forall x T,
  well_kinded (K & K'') x T ->
  well_kinded (K & K' & K'') x T.
Proof.
  intros. apply* well_kinded_comm.
Qed.
Hint Resolve well_kinded_weaken.

(** Well substitutions *)

(* Need to define typ_subst first *)
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
    refine (entails_trans H6 _); auto.
  simpl.
  inversions H3.
  apply* wk_kind.
  refine (entails_trans H6 _); auto.
Qed.
Hint Resolve well_kinded_subst.

(** Properties of instantiation and constants *)

Lemma trm_inst_nil : forall t, trm_inst t nil = t.
Proof.
  unfold trm_inst; intros.
  generalize 0; induction t; intros; simpl*.
     destruct* (Compare_dec.le_lt_dec n0 n).
     destruct* (n-n0).
    rewrite* IHt.
   rewrite IHt1; rewrite* IHt2.
  rewrite IHt1; rewrite* IHt2.
Qed.

Lemma const_app_app : forall c l l',
  const_app c (l++l') = fold_left trm_app l' (const_app c l).
Proof.
  intros. unfold const_app. apply fold_left_app.
Qed.

Lemma trm_inst_app : forall c tl pl,
  trm_inst_rec 0 tl (const_app c pl) =
  const_app c (List.map (trm_inst_rec 0 tl) pl).
Proof.
  introv.
  rewrite <- (rev_involutive pl).
  induction (rev pl). simpl. auto.
  simpl in *.
  rewrite map_app.
  repeat rewrite const_app_app.
  simpl. congruence.
Qed.

Lemma const_app_inv : forall c pl,
  pl = nil \/
  exists t1, exists t2, const_app c pl = trm_app t1 t2.
Proof.
  intros.
  destruct* pl.
  right.
  destruct* (exists_last (l:=t::pl)). intro; discriminate.
  destruct s. rewrite e.
  rewrite const_app_app. simpl.
  esplit; esplit; reflexivity.
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
  gen vl2.
  induction vl1 using rev_ind; intros.
    unfold const_app in H.
    destruct vl2 using rev_ind; simpl in H.
      inversions* H.
    rewrite fold_left_app in H. simpl in H. discriminate.
  destruct vl2 using rev_ind; repeat rewrite const_app_app in H.
    discriminate.
  inversions H; clear H.
  destruct (IHvl1 _ H1).
  subst*.
Qed.


(* Extra properties *)

Lemma All_kind_types_None : forall P, All_kind_types P None.
Proof.
  unfold All_kind_types. simpl*.
Qed.

Hint Resolve All_kind_types_None.

Lemma All_kind_types_imp (P P' : typ -> Prop) k:
  (forall x, P x -> P' x) ->
  All_kind_types P k -> All_kind_types P' k.
Proof.
  intros.
  destruct* k as [[kc kv kr kh]|].
  unfold All_kind_types, kind_types in *.
  simpl in *.
  clear -H H0; induction kr; simpl in *. auto.
  inversions* H0.
Qed.

Lemma All_kind_types_map : forall P f a,
  All_kind_types (fun x => P (f x)) a ->
  All_kind_types P (kind_map f a).
Proof.
  intros.
  destruct a as [[kc kv kr kh]|]; simpl*.
  unfold All_kind_types in *; simpl in *.
  clear kv kh; induction kr. simpl*.
  simpl in *. inversions* H.
Qed.

Lemma All_kind_types_inv: forall P f a,
  All_kind_types P (kind_map f a) ->
  All_kind_types (fun x => P (f x)) a.
Proof.
  intros.
  destruct a as [[kc kv kr kh]|]; simpl*.
  unfold All_kind_types in *; simpl in *.
  clear kv kh; induction kr. simpl*.
  simpl in *. inversions* H.
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

Lemma typ_fv_typ_fvars : forall Ys,
  typ_fv_list (typ_fvars Ys) = mkset Ys.
Proof.
  induction Ys; simpl*.
  rewrite* IHYs.
Qed.

Lemma typ_fvars_app : forall Xs Ys,
  typ_fvars (Xs++Ys) = typ_fvars Xs ++ typ_fvars Ys.
Proof.
  unfold typ_fvars; intros; apply map_app.
Qed.

Lemma types_typ_fvars : forall Xs,
  types (length Xs) (typ_fvars Xs).
Proof.
  unfold typ_fvars; intro; split.
    rewrite* map_length.
  induction Xs; simpl*.
Qed.
Hint Immediate types_typ_fvars.

(** Schemes are stable by type substitution. *)

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

Lemma typ_open_vars_type : forall Xs Ys T,
  type (typ_open_vars T Xs) ->
  length Ys = length Xs ->
  type (typ_open_vars T Ys).
Proof.
  intros.
  unfold typ_open_vars.
  apply (typ_open_other_type (typ_fvars Xs)). apply H.
  replace (length (typ_fvars Xs)) with (length Ys).
    apply types_typ_fvars.
  unfold typ_fvars. rewrite* map_length.
Qed.

Lemma sch_subst_type : forall S M,
  env_prop type S -> scheme M -> scheme (sch_subst S M).
Proof.
  unfold scheme. intros S [T Ks] TU K.
  simpls.
  introv Len.
  rewrite map_length in Len.
  destruct (var_freshes (dom S) (length Ks)) as [Ys Fr].
  destruct* (K Ys); clear K.
  assert (LenYs: length Xs = length Ys) by rewrite* <- Len.
  split.
    apply* (typ_open_vars_type Ys).
    rewrite* typ_subst_open_vars.
  apply* list_forall_map.
  clear H0; intros.
  unfold kind_subst.
  apply All_kind_types_map.
  apply* All_kind_types_imp.
  simpl; intros.
  apply* (typ_open_vars_type Ys).
  rewrite* typ_subst_open_vars.
Qed.

Hint Resolve sch_subst_type.

(** Scheme arity is preserved by type substitution. *)

Lemma sch_subst_arity : forall S M, 
  sch_arity (sch_subst S M) = sch_arity M.
Proof.
  intros. simpl; rewrite* map_length.
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

Definition kenv_ok_is_ok K (H:kenv_ok K) := proj1 H.
Definition env_ok_is_ok E (H:env_ok E) := proj1 H.
Definition kenv_ok_env_prop K (H:kenv_ok K) := proj2 H.
Definition env_ok_env_prop E (H:env_ok E) := proj2 H.

Hint Immediate kenv_ok_is_ok env_ok_is_ok kenv_ok_env_prop env_ok_env_prop.

Ltac env_hyps T :=
  match T with
  | sch => env_ok_hyps
  | kind => kenv_ok_hyps
  end.

Hint Extern 2 (@env_prop ?T _ ?E) =>
  progress env_hyps T; solve [env_prop_solve].

Hint Extern 2 (@ok ?T ?E) =>
  progress env_hyps T; solve [ok_solve].

Lemma env_prop_binds : forall (A:Set) (P:A->Prop) x (a:A) E,
  binds x a E -> env_prop P E -> P a.
Proof.
  intros. apply* (H0 x).
Qed.

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
  typing gc K E e T -> kenv_ok K /\ env_ok E /\ term e /\ type T.
Proof.
  split4; induction* H; auto.
  (* ok *)
  pick_fresh y. apply* (H1 y).
  pick_fresh y. apply* (H2 y).
  pick_freshes (length Ks) Xs. forward~ (H1 Xs) as G.
  pick_fresh y. forward~ (H1 y) as G.
  pick_fresh y. forward~ (H2 y) as G.
  pick_freshes (length Ks) Xs. forward~ (H1 Xs).
  (* term *) 
  apply_fresh* term_let as y.
    pick_freshes (sch_arity M) Xs.
    forward~ (H0 Xs) as G.
  pick_freshes (length Ks) Xs. forward~ (H1 Xs).
  (* type *)
  assert (scheme M) by apply* env_prop_binds.
  pick_fresh y. destruct* H2.
  pick_fresh y. forward~ (H1 y).
  pick_fresh y. forward~ (H2 y).
  inversion* IHtyping1.
  (* const *)
  puts (Delta.scheme c).
  destruct H1. auto*.
  pick_freshes (length Ks) Xs. forward~ (H1 Xs).
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  intros. destruct H. induction H; auto.
Qed.

Hint Resolve value_regular.

(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  induction 1; auto*.
  split.
    destruct vl.
    clear H; unfold const_app.
    assert (term (trm_cst c)) by auto.
    revert H; generalize (trm_cst c); induction H0; simpl*.
  apply* Delta.term.
Qed.

(* ********************************************************************** *)
(** ** Automation *)

(** Automation for reasoning on well-formedness. *)

Ltac kenv_ok_hyps ::=
  repeat match goal with
  | H: typing _ ?K _ _ _ |- _ => destruct (proj41 (typing_regular H)); clear H
  | H: kenv_ok ?K |- _ => destruct H
  end.

Ltac env_ok_hyps ::=
  repeat match goal with
  | H: typing _ _ ?E _ _ |- _ => destruct (proj42 (typing_regular H)); clear H
  | H: env_ok ?E |- _ => destruct H
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
