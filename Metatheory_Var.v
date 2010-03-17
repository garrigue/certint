(***************************************************************************
* Generic Variables for Programming Language Metatheory                    *
* Brian Aydemir & Arthur Charguéraud, July 2007, Coq v8.1      é            *
***************************************************************************)

Set Implicit Arguments.
Require Import List ZArith Omega OrderedType OrderedTypeEx.
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

Definition vars := VarSet.S.t.

(** Finally, we have a means of generating fresh variables. *)

Parameter vars_rep : vars -> var.
Parameter var_shift : var -> positive -> var.
Definition var_generate L := var_shift (vars_rep L) 1.
Parameter var_generate_spec : forall E, (var_generate E) \notin E.
Parameter var_fresh : forall (L : vars), { x : var | x \notin L }.
Parameter var_is_fresh : forall L, proj1_sig (var_fresh L) = var_generate L.

Parameter var_max : var -> var -> var.
Parameter var_singleton : forall v, vars_rep {{v}} = v.
Parameter var_union : forall L1 L2,
  vars_rep (L1 \u L2) = var_max (vars_rep L1) (vars_rep L2).
Parameter var_add : forall L,
  vars_rep (L \u {{var_generate L}}) = var_generate L.

(** Variables can be enumerated *)

Parameter var_of_Z : Z -> var.
Parameter Z_of_var : var -> Z.
Parameter Z_of_var_inj : forall v, var_of_Z (Z_of_var v) = v.
Parameter var_max_hom : forall v w,
  Z_of_var (var_max v w) = Zmax (Z_of_var v) (Z_of_var w).

End VARIABLES.


(* ********************************************************************** *)
(** * Concrete Implementation of Variables *)

Module Variables : VARIABLES.

Open Scope positive_scope.

Definition var := positive.

Definition var_default : var := 1.

Definition var_of_Z x : var :=
  match x with
  | Zpos n => n
  | Z0 => var_default
  | Zneg n => n
  end.
Definition Z_of_var (x : var) : Z := Zpos x.

Lemma Z_of_var_inj : forall v, var_of_Z (Z_of_var v) = v.
Proof.
  intros. reflexivity.
Qed.

Module Var_as_OT := Positive_as_OT.

Module Import VarSet : FinSet with Module E := Var_as_OT :=
  Lib_FinSetImpl.Make Var_as_OT.
Open Local Scope set_scope.

Definition vars := VarSet.S.t.

Definition var_max p q :=
  match (p ?= q) Eq with
  | Gt => p
  | Eq => p
  | Lt => q
  end.

Lemma var_max_hom : forall v w,
  Z_of_var (var_max v w) = Zmax (Z_of_var v) (Z_of_var w).
Proof.
  intros.
  unfold var_max, Zmax, Z_of_var.
  simpl.
  destruct ((v ?= w) Eq); reflexivity.
Qed.

Lemma Zle_Ple : forall p q, Zle (Z_of_var p) (Z_of_var q) -> p <= q.
Proof.
  intros. apply H.
Qed.

Lemma Ple_Zle : forall p q, p <= q -> Zle (Z_of_var p) (Z_of_var q).
Proof.
  intros. apply H.
Qed.

Definition var_list_max := fold_right var_max 1.

Lemma var_max_l : forall x y, x <= var_max x y.
Proof.
  intros.
  apply Zle_Ple.
  rewrite var_max_hom.
  apply Zle_max_l.
Qed.

Lemma finite_var_list_max : forall l x,
  In x l -> x <= var_list_max l.
Proof.
  induction l as [ | l ls IHl ]; intros x H.
    inversion H.
  simpl.
  simpl in H; destruct H.
    subst.
    apply var_max_l.
  apply Zle_Ple.
  rewrite var_max_hom.
  eapply Zle_trans.
    apply Ple_Zle. apply IHl. auto.
  apply Zle_max_r.
Qed.

Definition vars_rep L := var_list_max (S.elements L).

Definition var_shift v p := v + p.

Definition var_generate L := var_shift (vars_rep L) 1.
Lemma InA_In : forall v L, SetoidList.InA E.eq v L -> In v L.
  induction 1; auto.
Qed.

Lemma var_generate_spec : forall E, (var_generate E) \notin E.
Proof.
  unfold var_generate. intros E n.
  puts (InA_In (S.elements_1 n)).
  puts (finite_var_list_max _ _ H).
  unfold var_shift, vars_rep in *.
  remember (var_list_max (S.elements E)) as x.
  assert ((Z_of_var x+1 <= Z_of_var x)%Z).
    apply H0.
  omega.
Qed.

Lemma var_fresh : forall (L : vars), { x : var | x \notin L }.
Proof.
  intros L. exists (var_generate L). apply var_generate_spec.
Defined.

Lemma elements_singleton : forall v, S.elements {{v}} = v :: nil.
Proof.
  intros.
  generalize (S.elements_1 (S.singleton_2 (refl_equal v))).
  generalize (S.elements_3w {{v}}).
  case_eq (S.elements {{v}}); intros.
    inversion H1.
  assert (v = e).
    apply S.singleton_1.
    apply S.elements_2.
    rewrite H.
    constructor. reflexivity.
  subst e.
  destruct l. reflexivity.
  assert (v = e).
    apply S.singleton_1.
    apply S.elements_2.
    rewrite H.
    apply InA_cons_tl.
    constructor. reflexivity.
  subst e.
  inversion H0.
  elim H4. constructor. reflexivity.
Qed.

Lemma var_singleton : forall v, vars_rep {{v}} = v.
Proof.
  intros.
  unfold vars_rep.
  rewrite elements_singleton.
  simpl.
  unfold var_max.
  destruct v; simpl; auto.
Qed.

Lemma elements_incl_1 : forall L1 L2,
  incl (S.elements (L1 \u L2)) (S.elements L1 ++ S.elements L2).
Proof.
  introv a H.
  puts (S.elements_2
          (@In_InA _ Positive_as_OT.eq Positive_as_OT.eq_refl _ _ H)).
  destruct (S.union_1 H0); puts (S.elements_1 H1); apply in_or_app.
    left; apply* InA_In.
  right; apply* InA_In.
Qed.

Lemma elements_incl_2 : forall L1 L2,
  incl (S.elements L1 ++ S.elements L2) (S.elements (L1 \u L2)).
Proof.
  introv a H.
  apply InA_In.
  apply S.elements_1.
  destruct (in_app_or _ _ _ H);
  puts (S.elements_2
          (@In_InA _ Positive_as_OT.eq Positive_as_OT.eq_refl _ _ H0)).
    apply* S.union_2.
  apply* S.union_3.
Qed.

Require Import Zmax.

Lemma var_list_max_le : forall l1 l2,
  incl l1 l2 -> var_list_max l1 <= var_list_max l2.
Proof.
  intros; induction l1.
    unfold Ple; destruct (var_list_max l2); intro; discriminate.
  simpl.
  apply Zle_Ple. rewrite var_max_hom.
  apply Zmax_lub.
    apply Ple_Zle. apply finite_var_list_max. apply* H.
  apply IHl1.
  intros b Hb; apply* H.
Qed.

Lemma var_max_plus_r : forall p q r,
  var_max p q + r = var_max (p + r) (q + r).
Proof.
  intros.
  unfold var_max.
  case_eq ((p ?= q) Eq); intros.
      rewrite (Pcompare_Eq_eq _ _ H).
      rewrite Pcompare_refl.
      reflexivity.
    puts (nat_of_P_lt_Lt_compare_morphism _ _ H).
    puts (plus_lt_compat_r _ _ (nat_of_P r) H0).
    repeat rewrite <- nat_of_P_plus_morphism in H1.
    rewrite (nat_of_P_lt_Lt_compare_complement_morphism _ _ H1).
    reflexivity.
  puts (nat_of_P_gt_Gt_compare_morphism _ _ H).
  puts (plus_lt_compat_r _ _ (nat_of_P r) H0).
  repeat rewrite <- nat_of_P_plus_morphism in H1.
  rewrite (nat_of_P_gt_Gt_compare_complement_morphism _ _ H1).
  reflexivity.
Qed.

Lemma var_union : forall L1 L2,
  vars_rep (L1 \u L2) = var_max (vars_rep L1) (vars_rep L2).
Proof.
  intros.
  unfold vars_rep.
  pose (vlm := fun x => var_list_max (S.elements x)).
  assert (vlm (L1 \u L2) <= var_max (vlm L1) (vlm L2)).
    puts (elements_incl_1 L1 L2).
    unfold vlm.
    induction (S.elements (L1 \u L2)).
      apply Zle_Ple.
      rewrite var_max_hom.
      destruct (S.elements L1); simpl.
        apply Zle_max_l.
      rewrite (var_max_hom e).
      unfold Z_of_var.
      apply (Zle_trans 1 (Zpos e)).
        apply Ple_Zle.
        unfold Ple.
        destruct e; simpl; intro; discriminate.
      eapply Zle_trans. apply Zle_max_l.
      apply Zle_max_l.
    simpl.
    apply Zle_Ple.
    rewrite var_max_hom.
    apply Zmax_lub.
      forward~ (H a) as Ha.
      rewrite var_max_hom.
      destruct (in_app_or _ _ _ Ha);
        puts (Ple_Zle (finite_var_list_max _ _ H0)).
        eapply Zle_trans. apply H1.
        apply Zle_max_l.
      eapply Zle_trans. apply H1.
      apply Zle_max_r.
    apply IHl.
    intros b Hb; apply* H.
  assert (var_max (vlm L1) (vlm L2) <= vlm (L1 \u L2)).
    puts (elements_incl_2 L1 L2).
    unfold vlm.
    apply Zle_Ple.
    rewrite var_max_hom.
    apply Zmax_lub; apply Ple_Zle; apply var_list_max_le;
      intros a Ha; apply H0; apply* in_or_app.
  puts (Zle_antisym _ _ (Ple_Zle H) H0).
  inversion H1.
  apply H3.
Qed.

Lemma var_is_fresh : forall L,
  proj1_sig (var_fresh L) = var_generate L.
Proof.
  reflexivity.
Qed.

Lemma Z_of_var_inj' : forall m n, Z_of_var m = Z_of_var n -> m = n.
Proof.
  intros.
  puts (f_equal var_of_Z H).
  repeat rewrite Z_of_var_inj in H0.
  assumption.
Qed.

Lemma var_add : forall L, vars_rep (L \u {{var_generate L}}) = var_generate L.
Proof.
  intros.
  unfold var_generate.
  rewrite var_union.
  rewrite var_singleton.
  apply Z_of_var_inj'.
  apply Zle_antisym.
    rewrite var_max_hom.
    apply Zmax_lub.
      unfold var_shift.
      unfold Z_of_var.
      rewrite Zpos_plus_distr. omega.
    apply Zle_refl.
  rewrite var_max_hom.
  apply Zle_max_r.
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

Fixpoint var_nexts v (n:nat) {struct n} : list var :=
  match n with
  | 0 => nil
  | S m => 
    let v' := var_shift v 1 in
    v' :: var_nexts v' m
  end.

Lemma var_nexts_fresh : forall L n,
  fresh L n (var_nexts (vars_rep L) n).
Proof.
  intros.
  revert L; induction n; intros.
    simpl*.
  constructor. apply var_generate_spec.
  fold (var_generate L).
  rewrite <- var_add at 2.
  apply IHn.
Qed.

Lemma var_freshes : forall L n, 
  { xs : list var | fresh L n xs }.
Proof.
  intros. exists (var_nexts (vars_rep L) n).
  apply var_nexts_fresh.
Defined.


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


