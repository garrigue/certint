(***************************************************************************
* General useful tactics for Coq                                           *
* Brian Aydemir & Arthur Charguéraud, March 2007, Coq v8.1                 *
***************************************************************************)

(* Very useful tactic, for development only *)
Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].


(* ********************************************************************** *)
(** * Simple variations on existing tactics *)

(** [contradictions] replace the goal by False and prove it if False is
   derivable from the context or if [discriminate] applies. *)

Ltac contradictions :=
  assert False; [ try discriminate | contradiction ].

(** [cuts] does [cut] then [intro] in the first subgoal. *)

Ltac cuts H E :=
  cut (E); [ intro H | idtac ].

(** [inversions H] is a shortcut for [inversion H] followed by [subst]. *)

Ltac inversions H :=
  inversion H; subst.

(** [poses H E] adds an hypothesis with name H and with type the type of E. *)

Ltac poses H E :=
  pose (H := E); clearbody H.

(** [puts] is a version of [poses] where Coq chooses the name introduced. *)

Ltac puts E :=
  let H := fresh in poses H E.

(** [asserts H E] is a synonymous for [assert (X : E)] provided for
   uniformity with the rest of the syntax. *)

Ltac asserts H E :=
  assert (H : E).

(** [sets X E] replaces all occurences of E by a name X, and forgets the
   fact that X is equal to X -- it makes the goal more general *)

Ltac sets X E :=
  set (X := E) in *; clearbody X.

(** [introz] repeats [intro] as long as possible. Contrary to [intros],
    it unfolds any definition on the way. *)

Ltac introz :=
  intro; try introz.

(* ********************************************************************** *)
(** * Unfolding *)

(** [folds] is a shortcut for [fold in *] *)

Tactic Notation "folds" constr(H) :=
  fold H in *.
Tactic Notation "folds" constr(H1) constr(H2) :=
  folds H1; folds H2.
Tactic Notation "folds" constr(H1) constr(H2) constr(H3) :=
  folds H1; folds H2; folds H3.

(** [unfolds] is a shortcut for [unfold in *] *)

Tactic Notation "unfolds" reference(F1) :=
  unfold F1 in *.
Tactic Notation "unfolds" reference(F1) reference(F2) :=
  unfold F1 in *; unfold F2 in *.
Tactic Notation "unfolds" reference(F1) reference(F2) reference(F3) :=
  unfold F1 in *; unfold F2 in *; unfold F3 in *.

(** [unfold_hd] unfolds the definition at the head of the goal. *)

Tactic Notation "unfold_hd" :=
  match goal with
  | |- ?P => unfold P
  | |- ?P _ => unfold P
  | |- ?P _ _ => unfold P
  | |- ?P _ _ _ => unfold P
  | |- ?P _ _ _ _ => unfold P
  end. 


(* ********************************************************************** *)
(** * Simplification *)

(** [simpls] is a shortcut for [simpl in *] *)

Tactic Notation "simpls" :=
  simpl in *.
Tactic Notation "simpls" reference(F1) :=
  simpl F1 in *.
Tactic Notation "simpls" reference(F1) reference(F2) :=
  simpl F1 in *; simpl F2 in *.
Tactic Notation "simpls" reference(F1) reference(F2) reference(F3) :=
  simpl F1 in *; simpl F2 in *; simpl F3 in *.

(** [unsimpl E] replaces all occurence of X by E, where X is the result 
   which tactic [simpl] would give when applied to E. *)

Tactic Notation "unsimpl" constr(E) := 
  let F := (eval simpl in E) in change F with E.

Tactic Notation "unsimpl" constr(E) "in" hyp(H) := 
  let F := (eval simpl in E) in change F with E in H.


(* ********************************************************************** *)
(** * Rewriting *)

(** [rewrites] is an iterated version of [rewrite]. Beware of loops! *)

Tactic Notation "rewrites" constr(E) :=
  repeat rewrite E.
Tactic Notation "rewrites" "<-" constr(E) :=
  repeat rewrite <- E.
Tactic Notation "rewrites" constr(E) "in" ident(H) :=
  repeat rewrite E in H.
Tactic Notation "rewrites" "<-" constr(E) "in" ident(H) :=
  repeat rewrite <- E in H.

(** [asserts_rew] can be used to assert an equality holds and rewrite it
   straight away in the current goal *)

Tactic Notation "asserts_rew" constr(E) :=
  let EQ := fresh in (assert (EQ : E);
  [ idtac | rewrite EQ; clear EQ ]).
Tactic Notation "asserts_rew" "<-" constr(E) :=
  let EQ := fresh in (assert (EQ : E);
  [ idtac | rewrite <- EQ; clear EQ ]).
Tactic Notation "asserts_rew" constr(E) "in" hyp(H) :=
  let EQ := fresh in (assert (EQ : E);
  [ idtac | rewrite EQ in H; clear EQ ]).
Tactic Notation "asserts_rew" "<-" constr(E) "in" hyp(H) :=
  let EQ := fresh in (assert (EQ : E);
  [ idtac | rewrite <- EQ in H; clear EQ ]).

(** [do_rew] is used to perform the sequence: 
  rewrite the goal, execute a tactic, rewrite the goal back *)

Tactic Notation "do_rew" constr(E) tactic(T) :=
  rewrite E; T; try rewrite <- E.

Tactic Notation "do_rew" "<-" constr(E) tactic(T) :=
  rewrite <- E; T; try rewrite E.

(** [do_rew_2] is the same as [do_rew] but it does rewrite twice *)

Tactic Notation "do_rew_2" constr(E) tactic(T) :=
  do 2 rewrite E; T; try do 2 rewrite <- E.

Tactic Notation "do_rew_2" "<-" constr(E) tactic(T) :=
  do 2 rewrite <- E; T; try do 2 rewrite E.


(* ********************************************************************** *)
(** * Generalization *)

(**
  [gen_eq c as x H] takes all occurrences of [c] in the current goal's
  conclusion, replaces them by the variable [x], and introduces the equality
  [x = c] as the hypothesis H.  Useful if one needs to generalize the goal
  prior to applying an induction tactic.
*)

Tactic Notation "gen_eq" constr(c) "as" ident(x) ident(H) :=
  set (x := c); assert (H : x = c) by reflexivity; clearbody x.

(**
  A variation on the above in which all occurrences of [c] in the goal are
  replaced, not only those in the conclusion.
*)

Tactic Notation "gen_eq" constr(c) "as" ident(x) :=
  set (x := c) in *;
  let H := fresh in (assert (H : x = c) by reflexivity; clearbody x; revert H).

(** [gen] is a shortname for the [generalize dependent] tactic. *)

Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4)  :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.


(* ********************************************************************** *)
(** * Splitting N-ary Conjonctions *)

(** [split3] and [split4] respectively destruct a triple and a quadruple
  of propositions. *)

Tactic Notation "split3" :=
  split; [ idtac | split ].
Tactic Notation "split4" :=
  split; [ idtac | split3 ].

(** [splits] calls [split] recursively as long as possible. *)

Tactic Notation "splits" :=
  repeat split.

(** [esplitN] are iterated version of [esplit], used to introduce
  uninstanciated variables in goal of the form [exists x, P x]. *)

Tactic Notation "esplit2" := 
  esplit; esplit.
Tactic Notation "esplit3" := 
  esplit; esplit; esplit.
Tactic Notation "esplit4" := 
  esplit; esplit; esplit; esplit.


(* ********************************************************************** *)
(** * Branching N-ary Disjunction *)

(** Short-hand tactics for branching when the goal is of the form 
    [P1 \/ P2 \/ P3]. *)

Tactic Notation "or_31" := left.
Tactic Notation "or_32" := right; left.
Tactic Notation "or_33" := right; right.


(* ********************************************************************** *)
(** * Destructing conjonctions behind implications *)

(** [destructi T] is to be used on a [T] of the form 
    [A1 -> .. -> AN -> X /\ Y]. It generates the [Ai] as subgoals
    and adds two hypotheses X and Y to the current goal. *)

Tactic Notation "destructi" constr(T) :=
  let rec doit H :=
    match type of H with
    | ?P -> ?Q => let A := fresh "A" in 
      (assert (A : P); [ idtac | doit (H A); clear A ])
    | _ => first [destruct H | puts H]
    end in doit T.

Tactic Notation "destructi" constr(T) "as" simple_intropattern(I) :=
  let rec doit H :=
    match type of H with
    | ?P -> ?Q => let A := fresh "A" in 
      (assert (A : P); [ idtac | doit (H A); clear A ])
    | _ => first [destruct H as I | poses I H]
    end in doit T.

(** [destructs T] calls [destruct] recursively on [T] as long as possible *) 

Ltac destructs H :=
  let X := fresh in let Y := fresh in  
  first [ destruct H as [X Y]; destructs X; destructs Y | idtac ].


(* ********************************************************************** *)
(** * Introduction *)

(** [introv] is used to repeat intro on all dependent variables; basically
    it introduces all the names which are mentionned further in the goal. *)

Tactic Notation "introv" :=
  let rec go _ := match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; try go tt
  end in first [ go tt | intro; go tt ].

Tactic Notation "introv" simple_intropattern(I) :=
  introv; intros I.
Tactic Notation "introv" simple_intropattern(I1) ident(I2) :=
  introv; intros I1 I2.
Tactic Notation "introv" simple_intropattern(I1) ident(I2) ident(I3) :=
  introv; intros I1 I2 I3.
Tactic Notation "introv" simple_intropattern(I1) ident(I2) ident(I3) ident(I4) :=
  introv; intros I1 I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) ident(I2) ident(I3) ident(I4) ident(I5) :=
  introv; intros I1 I2 I3 I4 I5.


(* ********************************************************************** *)
(** * Exists *)

(** [exists T1 ... TN] is a shorthand for [exists T1; ...; exists TN]. *)

Tactic Notation "exists" constr(T1) :=
  exists T1.
Tactic Notation "exists" constr(T1) constr(T2) :=
  exists T1; exists T2.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) :=
  exists T1; exists T2; exists T3.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1; exists T2; exists T3; exists T4.


(* ********************************************************************** *)
(** * Forward Chaining - Adapted from a suggestion by Xavier Leroy *)

Lemma modus_ponens : forall (P Q : Prop), 
  P -> (P -> Q) -> Q.
Proof. auto. Qed.

Implicit Arguments modus_ponens [P Q].

Tactic Notation "forward" constr(x) "as" simple_intropattern(H) :=
    (refine (modus_ponens (x _ _ _ _ _ _ _ _ _) _); [ | | | | | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _ _ _ _) _); [ | | | | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _ _ _) _); [ | | | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _ _) _); [ | | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _) _); [ | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _) _); [ | | | | intros H ])
 || (refine (modus_ponens (x _ _ _) _); [ | | | intros H ])
 || (refine (modus_ponens (x _ _) _); [ | | intros H ])
 || (refine (modus_ponens (x _) _); [ | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _ _ _ _ _) _); [ | | | | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _ _ _ _) _); [ | | | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _ _ _) _); [ | | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _ _) _); [ | | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _ _) _); [ | | | | intros H ])
 || (refine (modus_ponens (x _ _ _ _) _); [ | | | intros H ])
 || (refine (modus_ponens (x _ _ _) _); [ | | intros H ])
 || (refine (modus_ponens (x _ _) _); [ | intros H ])
 || (refine (modus_ponens (x _) _); [ intros H ]).

Tactic Notation "forward" constr(x) :=
    refine (modus_ponens (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modus_ponens (x _ _ _ _ _ _ _ _ _) _)
 || refine (modus_ponens (x _ _ _ _ _ _ _ _) _)
 || refine (modus_ponens (x _ _ _ _ _ _ _) _)
 || refine (modus_ponens (x _ _ _ _ _ _) _)
 || refine (modus_ponens (x _ _ _ _ _) _)
 || refine (modus_ponens (x _ _ _ _) _)
 || refine (modus_ponens (x _ _ _) _)
 || refine (modus_ponens (x _ _) _)
 || refine (modus_ponens (x _) _).


(* ********************************************************************** *)
(** * Tactics with Automation *)

(** The name of a tactic followed by a star means: apply the tactic, then
    applies [auto*] on the generated subgoals. [auto*] is a tactic
    which tries to solve the goal with either auto or intuition eauto. 
    It leaves the goal unchanged if it can't solve the goal. *)

(** Exceptions to the naming convention are: [take] which stands for [exists*] 
    and [use] which stands for [puts*]. Exceptions to the behaviour for
    [asserts*] which only calls [auto*] in the new subgoal, and [apply*]
    which first tries [apply] and if it fails it tries [eapply] and then
    in both cases calls [auto*]. *)

Tactic Notation "auto" "*" :=
  try solve [ auto | intuition eauto ].
Tactic Notation "auto" "*" int_or_var(n) :=
  try solve [ auto | intuition (eauto n) ].
Tactic Notation "asserts" "*" ident(H) constr(E) :=
  assert (H : E); [ auto* | idtac ].
Tactic Notation "apply" "*" constr(H) :=
  first [ apply H | eapply H ]; auto*.
Tactic Notation "apply" "*" constr(H) :=
  first [ apply H | eapply H ]; auto*.
Tactic Notation "contradictions" "*" :=
  contradictions; auto*.
Tactic Notation "destruct" "*" constr(H) :=
  destruct H; auto*.
Tactic Notation "destruct" "*" constr(H) "as" simple_intropattern(I) :=
  destruct H as I; auto*.
Tactic Notation "f_equal" "*" :=
  f_equal; auto*.
Tactic Notation "induction" "*" constr(H) :=
  induction H; auto*.
Tactic Notation "inversion" "*" constr(H) :=
  inversion H; auto*.
Tactic Notation "inversions" "*" constr(H) :=
  inversions H; auto*.
Tactic Notation "rewrite" "*" constr(H) :=
  rewrite H; auto*.
Tactic Notation "rewrite" "*" "<-" constr(H) :=
  rewrite <- H; auto*.
Tactic Notation "do_rew" "*" constr(E) tactic(T) :=
  (do_rew E T); auto*.
Tactic Notation "do_rew" "*" "<-" constr(E) tactic(T) :=
  (do_rew <- E T); auto*.
Tactic Notation "do_rew_2" "*" constr(E) tactic(T) :=
  (do_rew_2 E T); auto*.
Tactic Notation "do_rew_2" "*" "<-" constr(E) tactic(T) :=
  (do_rew_2 <- E T); auto*.
Tactic Notation "simpl" "*" :=
  simpl; auto*.
Tactic Notation "simpls" "*" :=
  simpls; auto*.
Tactic Notation "unsimpl" "*" constr(E) := 
  unsimpl E; auto*.
Tactic Notation "unsimpl" "*" constr(E) "in" hyp(H) := 
  unsimpl E in H; auto*.
Tactic Notation "split" "*" :=
  split; auto*.
Tactic Notation "split3" "*" := 
  split3; auto*.
Tactic Notation "split4" "*" := 
  split4; auto*.
Tactic Notation "splits" "*" :=
  splits; auto*.
Tactic Notation "esplit2" "*" := 
  esplit2; auto*.
Tactic Notation "esplit3" "*" := 
  esplit3; auto*.
Tactic Notation "esplit4" "*" := 
  esplit4; auto*.
Tactic Notation "right" "*" := 
  right; auto*.
Tactic Notation "left" "*" := 
  left; auto*.
Tactic Notation "or_31" "*" := 
  or_31; auto*.
Tactic Notation "or_32" "*" := 
  or_32; auto*.
Tactic Notation "or_33" "*" := 
  or_33; auto*.
Tactic Notation "destructi" "*" constr(H) :=
  destructi H; auto*.
Tactic Notation "subst" "*" :=
  subst; auto*.
Tactic Notation "use" constr(expr) :=
  puts expr; auto*.
Tactic Notation "use" constr(expr1) constr(expr2) :=
  puts expr1; use expr2.
Tactic Notation "use" constr(expr1) constr(expr2) constr(expr3) :=
  puts expr1; use expr2 expr3.
Tactic Notation "exists" "*" constr(T1) :=
  exists T1; auto*.
Tactic Notation "exists" "*" constr(T1) constr(T2) :=
  exists T1 T2; auto*.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) :=
  exists T1 T2 T3.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1 T2 T3 T4.
Tactic Notation "forward" "*" constr(x) "as" simple_intropattern(H) :=
  forward x; auto*.
Tactic Notation "forward" "*" constr(x) :=
  forward x; auto*.


(* ********************************************************************** *)
(** * Tactics with Limited Automation *)

Tactic Notation "rewrite" "~" constr(H) :=
  rewrite H; auto.
Tactic Notation "rewrite" "~" "<-" constr(H) :=
  rewrite <- H; auto.
Tactic Notation "apply" "~" constr(H) :=
  first [ apply H | eapply H ]; auto.
Tactic Notation "destructi" "~" constr(H) :=
  destructi H; auto.
Tactic Notation "destruct" "~" constr(H) :=
  destruct H; auto.
Tactic Notation "destruct" "~" constr(H) "as" simple_intropattern(I) :=
  destruct H as I; auto.
Tactic Notation "destructi" "~" constr(H) "as" simple_intropattern(I) :=
  destructi H as I; auto.
Tactic Notation "split" "~" :=
  split; auto.
Tactic Notation "split3" "~" :=
  split3; auto.
Tactic Notation "split4" "~" :=
  split4; auto.
Tactic Notation "splits" "~" :=
  splits; auto.
Tactic Notation "forward" "~" constr(x) "as" simple_intropattern(H) :=
  forward x as H; auto.
Tactic Notation "forward" "~" constr(x) :=
  forward x; auto.


(* ********************************************************************** *)
(** * Projections *)

(** Short-hand notations for projections from triples. *)

Notation "'proj31' P" := (proj1 P) (at level 69).
Notation "'proj32' P" := (proj1 (proj2 P)) (at level 69).
Notation "'proj33' P" := (proj2 (proj2 P)) (at level 69).

Notation "'proj41' P" := (proj1 P) (at level 69).
Notation "'proj42' P" := (proj1 (proj2 P)) (at level 69).
Notation "'proj43' P" := (proj1 (proj2 (proj2 P))) (at level 69).
Notation "'proj44' P" := (proj2 (proj2 (proj2 P))) (at level 69).




