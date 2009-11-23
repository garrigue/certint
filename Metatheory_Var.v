(***************************************************************************
* Generic Variables for Programming Language Metatheory                    *
* Brian Aydemir & Arthur Charguéraud, July 2007, Coq v8.1      é            *
***************************************************************************)

Set Implicit Arguments.
Require Import List Max Omega OrderedType OrderedTypeEx.
Require Import Lib_Tactic Lib_ListFacts Lib_FinSet Lib_FinSetImpl.
Require Export Lib_ListFactsMore.

(* ********************************************************************** *)
(** * Abstract Definition of Variables *)

Module Type VARIABLES.

(** We leave the type of variables abstract. *)

Parameter var : Set.

(** This type is inhabited. *)

Parameter var_default : var.

(** Variables are ordered. *)

Declare Module Var_as_OT : UsualOrderedType with Definition t := var.

(** We can form sets of variables. *)

Declare Module Import VarSet : FinSet with Module E := Var_as_OT.
Open Local Scope set_scope.
Open Local Scope Z_scope.

Definition vars := VarSet.S.t.

(** Finally, we have a means of generating fresh variables. *)

Parameter var_generate : vars -> var.
Parameter var_generate_spec : forall E, (var_generate E) \notin E.
Parameter var_fresh : forall (L : vars), { x : var | x \notin L }.

Parameter var_maj : vars -> Z.
Parameter var_next : forall (n : Z),
  {x : var | forall L, var_maj L <= n -> x \notin L}.
Parameter maj_grow : forall L1 L2, L1 << L2 -> var_maj L1 <= var_maj L2.

(** Variables can be enumerated *)

Parameter var_of_Z : Z -> var.
Parameter Z_of_var : var -> Z.

End VARIABLES.


(* ********************************************************************** *)
(** * Concrete Implementation of Variables *)

Module Variables : VARIABLES.

Open Scope Z_scope.

Definition var := Z.

Definition var_default : var := 0.

Definition var_of_Z x : var := x.
Definition Z_of_var x : Z := x.

Module Var_as_OT := Z_as_OT.

Module Import VarSet : FinSet with Module E := Var_as_OT :=
  Lib_FinSetImpl.Make Var_as_OT.
Open Local Scope set_scope.

Definition vars := VarSet.S.t.

Fixpoint var_maj_list (l : list var) : Z :=
  match l with
  | nil => 0
  | n :: l' => Zmax n (var_maj_list l')
  end.

Definition var_maj L := var_maj_list (S.elements L).

Lemma maj_grow : forall L1 L2, L1 << L2 -> var_maj L1 <= var_maj L2.
Proof.
  intros.
  unfold var_maj.
  assert (incl (S.elements L1) (S.elements L2)).
    intro; intros.
    assert (InA S.E.eq a (S.elements L2)).
      apply S.elements_1.
      apply H.
      apply S.elements_2.
      apply In_InA; intros; auto.
      reflexivity.
    clear -H1.
    induction H1.
      inversion H.
      subst*.
    auto.
  induction (S.elements L1).
    simpl.
    clear.
    induction (S.elements L2). auto with zarith.
    simpl. apply (Zle_trans _ _ _ IHl). apply Zle_max_r.
  simpl.
  apply (Zmax_case a (var_maj_list l)).
    assert (In a (S.elements L2)).
      apply H0. auto.
    clear -H1; induction (S.elements L2). elim H1.
    simpls.
    destruct H1. subst. apply Zle_max_l.
    apply (Zle_trans _ _ _ (IHl H)).
    apply Zle_max_r.
  apply IHl.
  intro; intros. apply H0. auto.
Qed.

Definition var_next : forall (n : Z),
  {x : var | forall L, var_maj L <= n -> x \notin L}.
Proof.
  intros.
  exists (1+n).
  unfold var_maj.
  intros; intro.
  puts (S.elements_1 H0).
  clear H0; induction H1.
    simpl in H.
    inversions H0.
    revert H.
    apply Zmax_case_strong; intros; omega.
  apply IHInA.
  simpl in H.
  revert H.
  apply Zmax_case_strong; intros; omega.
Defined.

Definition var_generate L : var := proj1_sig (var_next (var_maj L)).
Lemma var_generate_spec : forall E, (var_generate E) \notin E.
Proof.
  intros.
  unfold var_generate.
  destruct (var_next (var_maj E)).
  simpl.
  apply n.
  auto with zarith.
Qed.
  
Definition var_fresh : forall (L : vars), { x : var | x \notin L }.
  intros.
  exists (var_generate L).
  apply var_generate_spec.
Qed.

End Variables.


(* ********************************************************************** *)
(** * Properties of variables *)

Export Variables.
Export Variables.VarSet.
Module Export VarSetFacts := FinSetFacts VarSet.

Open Scope set_scope.

(** Equality on variables is decidable. *)

Module Import Var_as_OT_Facts := OrderedTypeFacts Variables.Var_as_OT.

Lemma eq_var_dec : forall x y : var, {x = y} + {x <> y}.
Proof.
  exact Var_as_OT_Facts.eq_dec.
Qed.

(* ********************************************************************** *)
(** ** Dealing with list of variables *)

(** Freshness of n variables from a set L and from one another. *)

Fixpoint fresh (L : vars) (n : nat) (xs : list var) {struct xs} : Prop :=
  match xs, n with
  | nil, O => True
  | x::xs', S n' => x \notin L /\ fresh (L \u {{x}}) n' xs'
  | _,_ => False
  end.

Hint Extern 1 (fresh _ _ _) => simpl.

(** Triviality : If a list xs contains n fresh variables, then
    the length of xs is n. *)

Lemma fresh_length : forall xs L n,
  fresh L n xs -> n = length xs.
Proof.
  induction xs; simpl; intros; destruct n; 
  try solve [ contradictions* | f_equal* ].
Qed.

(* It is possible to build a list of n fresh variables. *)

Lemma var_freshes : forall L n, 
  { xs : list var | fresh L n xs }.
Proof.
  intros. gen L. induction n; intros L.
  exists* (nil : list var).
  destruct (var_fresh L) as [x Fr].
   destruct (IHn (L \u {{x}})) as [xs Frs].
   exists* (x::xs).
Qed.


(* ********************************************************************** *)
(** ** Tactics: Case Analysis on Variables *)

(** We define notations for the equality of variables (our free variables)
  and for the equality of naturals (our bound variables represented using
  de Bruijn indices). *)

Notation "x == y" := (eq_var_dec x y) (at level 67).
Notation "i === j" := (Peano_dec.eq_nat_dec i j) (at level 70).

(** Tactic for comparing two bound or free variables. *)

Ltac case_nat :=
  let destr x y := destruct (x === y); [try subst x | idtac] in
  match goal with
  | H: context [?x === ?y] |- _ => destr x y
  | |- context [?x === ?y]      => destr x y
  end.

Tactic Notation "case_nat" "*" := case_nat; auto*.

Tactic Notation "case_var" :=
  let destr x y := destruct (x == y); [try subst x | idtac] in
  match goal with
  | H: context [?x == ?y] |- _ => destr x y
  | |- context [?x == ?y]      => destr x y
  end.

Tactic Notation "case_var" "*" := case_var; auto*.


(* ********************************************************************** *)
(** ** Tactics: Picking Names Fresh from the Context *)

(** [gather_vars_for_type T F] return the union of all the finite sets
  of variables [F x] where [x] is a variable from the context such that
  [F x] type checks. In other words [x] has to be of the type of the
  argument of [F]. The resulting union of sets does not contain any
  duplicated item. This tactic is an extreme piece of hacking necessary
  because the tactic language does not support a "fold" operation on
  the context. *)

Ltac gather_vars_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | {} => gather FH
      | context [FH] => fail 1
      | _ => gather (FH \u V)
      end
    | _ => V
    end in
  let L := gather {} in eval simpl in L.

(** [beautify_fset V] assumes that [V] is built as a union of finite
  sets and return the same set cleaned up: empty sets are removed and
  items are laid out in a nicely parenthesized way *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | ?E1 \u ?E2 => let Acc1 := go Acc E1 in
                     go Acc1 E2
     | {}  => Acc
     | ?E1 => match Acc with
              | {} => E1
              | _ => constr:(Acc \u E1)
              end
     end
  in go {} V.

(** [pick_fresh_gen L Y] expects [L] to be a finite set of variables
  and adds to the context a variable with name [Y] and a proof that
  [Y] is fresh for [L]. *)

Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (var_fresh L) as [Y Fr]).

(** [pick_fresh_gens L n Y] expects [L] to be a finite set of variables
  and adds to the context a list of variables with name [Y] and a proof 
  that [Y] is of length [n] and contains variable fresh for [L] and
  distinct from one another. *)

Ltac pick_freshes_gen L n Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (var_freshes L n) as [Y Fr]).

(** Demo of pick_fresh_gen *)

Ltac test_pick_fresh_filter Y :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let C := gather_vars_with (fun x : var => {}) in
  pick_fresh_gen (A \u B \u C) Y.

Lemma test_pick_fresh : forall (x y z : var) (L1 L2 L3: vars), True.
Proof.
  intros. test_pick_fresh_filter k. auto.
Qed.

(** The above invokation of [pick_fresh] generates a
  variable [k] and the hypothesis
  [k \notin L1 \u L2 \u L3 \u {{x}} \u {{y}} \u {{z}}] *)


(* ********************************************************************** *)
(** ** Tactics: Applying Lemmas With Quantification Over Cofinite Sets *)

(** [apply_fresh_base] tactic is a helper to build tactics that apply an
  inductive constructor whose first argument should be instanciated
  by the set of names already used in the context. Those names should
  be returned by the [gather] tactic given in argument. For each premise
  of the inductive rule starting with an universal quantification of names
  outside the set of names instanciated, a subgoal with be generated by
  the application of the rule, and in those subgoal we introduce the name
  quantified as well as its proof of freshness. *)

Ltac apply_fresh_base_simple lemma gather :=
  let L0 := gather in let L := beautify_fset L0 in
  first [apply (@lemma L) | eapply (@lemma L)].

Ltac apply_fresh_base lemma gather var_name :=
  apply_fresh_base_simple lemma gather;
  try match goal with |- forall _, _ \notin _ -> _ =>
    let Fr := fresh "Fr" in intros var_name Fr end.


(** [inst_notin H y as H'] expects [H] to be of the form
  [forall x, x \notin L, P x] and creates an hypothesis [H']
  of type [P y]. It tries to prove the subgoal [y \notin L]
  by [auto]. This tactic is very useful to apply induction
  hypotheses given in the cases with binders. *)

Tactic Notation "inst_notin" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  let go L := let Fr := fresh in assert (Fr : var \notin L);
     [ auto | poses hyp_name (@lemma var Fr); clear Fr ] in
  match type of lemma with
  | forall _, _ \notin ?L -> _ => go L
  | forall _, (_ \in ?L -> False) -> _ => go L
  end.

Tactic Notation "inst_notin" "*" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  inst_notin lemma var as hyp_name; auto*.


