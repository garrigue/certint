(***************************************************************************
* Tactics to Automate Reasoning about Freshness                            *
* Brian Aydemir & Arthur Charguéraud, July 2007, Coq v8.1                  *
***************************************************************************)

Set Implicit Arguments.
Require Import Lib_Tactic List Metatheory_Var.


Ltac fresh_simpl_to_notin_in_context :=
  repeat (match goal with H: fresh _ _ _ |- _ =>
    progress (simpl in H; destructs H) end).


(* ********************************************************************** *)
(** ** Tactics for notin *)

(** For efficiency, we avoid rewrites by splitting equivalence. *)

Lemma notin_singleton_r : forall x y,
  x \notin {{y}} -> x <> y.
intros. rewrite* <- notin_singleton.
Qed.

Lemma notin_singleton_l : forall x y,
  x <> y -> x \notin {{y}}.
intros. rewrite* notin_singleton.
Qed.

Lemma notin_singleton_swap : forall x y,
  x \notin {{y}} -> y \notin {{x}}.
intros. apply notin_singleton_l.
apply sym_not_eq. apply* notin_singleton_r.
Qed.

Lemma notin_union_r : forall x E F,
  x \notin (E \u F) -> (x \notin E) /\ (x \notin F).
intros. rewrite* <- notin_union.
Qed.

Lemma notin_union_l : forall x E F,
  x \notin E -> x \notin F -> x \notin (E \u F).
intros. rewrite* notin_union.
Qed.

(** Tactics to deal with notin. It interacts with union
    singleton and empty, but not inclusion. *)

Ltac notin_solve_from x E H :=
  match type of H with x \notin ?L =>
    match L with context[E] =>
      match L with
      | E => exact H
      | ?F \u ?G =>
        let P := constr:(@notin_union_r x F G H) in
        let PF := eval simpl in (proj1 P) in
        let PG := eval simpl in (proj2 P) in
        solve [ notin_solve_from x E PF
              | notin_solve_from x E PG ]
      end
    end
  end.

Ltac notin_solve_from_context x E :=
  match goal with H: x \notin _ |- _ =>
    notin_solve_from x E H end.

Ltac notin_solve_one :=
  match goal with
  | |- _ \notin {} =>
    apply notin_empty
  | |- ?x \notin {{?y}} => (* by x <> y or y <> x *)
    apply notin_singleton_l; solve
    [ assumption | apply sym_not_eq; assumption ]
  | |- ?x \notin {{?y}} => (* by y \notin {{x}} *)
    apply notin_singleton_swap; notin_solve_from_context y ({{x}})
  | |- ?x \notin ?E  =>    (* default search *)
    notin_solve_from_context x E
  end.

Ltac notin_simpl :=
  try match goal with |- _ \notin (_ \u _) =>
    apply notin_union_l; notin_simpl end.

Ltac notin_simpl_hyps := (* forward-chaining *)
  try match goal with
  | H: _ \notin {} |- _ =>
     clear H; notin_simpl_hyps
  | H: ?x \notin {{?y}} |- _ =>
     puts (@notin_singleton_r x y H);
     clear H; notin_simpl_hyps
   | H: ?x \notin (?E \u ?F) |- _ =>
     let H1 := fresh "Fr" in let H2 := fresh "Fr" in
     destruct (@notin_union_r x E F H) as [H1 H2];
     clear H; notin_simpl_hyps
  end.

Ltac notin_simpls :=
  notin_simpl_hyps; notin_simpl.

Ltac notin_solve :=
  fresh_simpl_to_notin_in_context; 
  notin_simpl; notin_solve_one.

Ltac notin_contradiction :=
  match goal with H: ?x \notin ?E |- _ =>
    match E with context[x] =>
      let K := fresh in assert (K : x \notin {{x}});
        [ notin_solve_one
        | contradictions; apply (notin_same K) ]
    end
  end.

Ltac notin_neq_solve :=
  apply notin_singleton_r; notin_solve.


(* ********************************************************************** *)
(** Demo for notin *)

Lemma test_notin_solve_1 : forall x E F G,
  x \notin E \u F -> x \notin G -> x \notin (E \u G).
intros. notin_solve.
Qed.

Lemma test_notin_solve_2 : forall x y E F G,
  x \notin E \u {{y}} \u F -> x \notin G ->
  x \notin {{y}} /\ y \notin {{x}}.
intros. split. notin_solve. notin_solve.
Qed.

Lemma test_notin_solve_3 : forall x y,
  x <> y -> x \notin {{y}} /\ y \notin {{x}}.
intros. split. notin_solve. notin_solve.
Qed.

Lemma test_notin_contradiction : forall x y E F G,
  x \notin (E \u {{x}} \u F) -> y \notin G.
intros. notin_contradiction.
Qed.

Lemma test_neq_solve : forall x y E F,
  x \notin (E \u {{y}} \u F) -> y \notin E ->
  y <> x /\ x <> y.
intros. split. notin_neq_solve. notin_neq_solve.
Qed.



(***************************************************************************)
(** Automation: hints to solve "notin" subgoals automatically. *)

Hint Extern 1 (_ \notin _) => notin_solve.

Hint Extern 1 (_ \in _ -> False) =>
  repeat match goal with
  | H: context [?x \in ?E -> False] |- _ => 
    fold (not (x \in E)) in H 
  | |- context [?x \in ?E -> False] => 
    fold (not (x \in E)) end.

Hint Extern 1 (_ <> _ :> var) => notin_neq_solve.
Hint Extern 1 (_ <> _ :> S.elt) => notin_neq_solve.


(* ********************************************************************** *)
(** ** Tactics for fresh *)

Hint Extern 1 (fresh _ _ _) => simpl.

Lemma fresh_union_r : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L1 n xs /\ fresh L2 n xs.
Proof.
  induction xs; simpl; intros; destruct n;
  try solve [ contradictions* ]. auto.
  destruct H. splits~.
  forward* (@IHxs (L1 \u {{a}}) L2 n).
   rewrite union_comm.
   rewrite union_comm_assoc.
   rewrite* union_assoc.
  forward* (@IHxs L1 (L2 \u {{a}}) n).
   rewrite* union_assoc.
Qed.

Lemma fresh_union_l : forall xs L1 L2 n,
  fresh L1 n xs -> fresh L2 n xs -> fresh (L1 \u L2) n xs.
Proof.
  induction xs; simpl; intros; destruct n;
  try solve [ contradictions* ]. auto.
  destruct H. destruct H0. split~.
  forward~ (@IHxs (L1 \u {{a}}) (L2 \u {{a}}) n). 
  intros K.
  rewrite <- (union_same {{a}}).
  rewrite union_assoc.
  rewrite <- (@union_assoc L1).
  rewrite (@union_comm L2).
  rewrite (@union_assoc L1).
  rewrite* <- union_assoc.
Qed.

Lemma fresh_empty : forall L n xs,
  fresh L n xs -> fresh {} n xs.
Proof.
  intros. rewrite <- (@union_empty_r L) in H.
  destruct* (fresh_union_r _ _ _ _ H).
Qed.

Lemma fresh_length : forall xs L n,
  fresh L n xs -> n = length xs.
Proof.
  induction xs; simpl; intros L n Fr; destruct n;
   try solve [contradictions*]. auto.
  rewrite* <- (@IHxs (L \u {{a}}) n).
Qed.

Lemma fresh_resize : forall n xs L,
  fresh L n xs -> fresh L (length xs) xs.
Proof.
  introv Fr. rewrite* <- (fresh_length _ _ _ Fr).
Qed.

Ltac fresh_solve_from xs n E H :=
  match type of H with fresh ?L _ _ =>
    match L with context[E] =>
      match L with
      | E => exact H
      | ?F \u ?G =>
        let P := constr:(@fresh_union_r xs F G n H) in
        let PF := eval simpl in (proj1 P) in
        let PG := eval simpl in (proj2 P) in
        solve [ fresh_solve_from xs n E PF
              | fresh_solve_from xs n E PG ]
      end
    end
  end.

Ltac fresh_solve_from_context xs n E :=
  match goal with H: fresh _ n xs |- _ =>
    fresh_solve_from xs n E H end.

Ltac fresh_solve_one :=
  assumption ||
  match goal with
  | |- fresh {} ?n ?xs =>
    match goal with H: fresh ?L n xs |- _ =>
      apply (@fresh_empty L n xs H) end
  (* | H: fresh _ ?n ?xs |- fresh ?E ?n ?xs =>   
    fresh_solve_from xs n E H *)
  | |- fresh _ (length ?xs) ?xs =>  
    match goal with H: fresh _ ?n xs |- _ =>
      progress (apply (@fresh_resize n)); fresh_solve_one end
  end.

Ltac fresh_simpl :=
  try match goal with |- fresh (_ \u _) _ _ =>
    apply fresh_union_l; fresh_simpl end.

Ltac fresh_split :=
  match goal with
  | H: fresh (?L1 \u ?L2) ?n ?xs |- fresh _ _ ?xs =>
      destruct (fresh_union_r xs L1 L2 n H); clear H; fresh_split
  | _ => try fresh_simpl
  end.

Ltac fresh_simpl_to_notin_in_goal :=
  simpl; splits.

Ltac fresh_simpl_to_notin_solve :=
  fresh_simpl_to_notin_in_context;
  fresh_simpl_to_notin_in_goal;
  notin_solve.

Ltac fresh_solve :=
  (fresh_split; fresh_solve_one) || (fresh_simpl; fresh_simpl_to_notin_solve).


(* ********************************************************************** *)
(** Demo for notin *)

Lemma test_fresh_solve_1 : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L1 n xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_2 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh L2 n xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_3 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh {} n xs.
Proof. 
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_4 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh L1 (length xs) xs.
Proof. 
  intros. fresh_solve.
Qed.

(***************************************************************************)
(** Automation: hints to solve "fresh" subgoals automatically. *)

Hint Extern 1 (fresh _ _ _) => fresh_solve.


