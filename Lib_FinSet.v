(***************************************************************************
* A Library for Finite Sets with Leibnitz Equality                         *
* Brian Aydemir & Arthur Charguéraud, March 2007, Coq v8.1                 *
***************************************************************************)

Set Implicit Arguments.
Require Import OrderedTypeEx.
Require Import Lib_Tactic Lib_MyFSetInterface.

(* ********************************************************************** *)
(** * Interface for Finite Sets *)

Declare Scope set_scope.

Module Type FinSet.
Declare Module E : UsualOrderedType.

(** These finite sets are compatible with Coq's FSet library, except with
  respect to [Hint]s.  [MyFSetInterface.S] is a redeclaration of
  [FSetInterface.S] with all the [Hint]s placed in the [sets] database
  instead of [core].  This is mainly to avoid polluting the [core] database
  with lemmas that are only usable by [eauto]. *)

Declare Module S : Lib_MyFSetInterface.S with Module E := E.

(** Define aliases. *)

Definition fset := S.t.
Definition elt := S.elt.

(** Equality on these sets is extensional. *)

Parameter eq_ext :
  forall s s' : fset, (forall a : elt, S.In a s <-> S.In a s') -> s = s'.

Parameter eq_if_Equal :
  forall s s' : fset, S.Equal s s' -> s = s'.

(** Notations. *)

Notation "{}" := (S.empty) : set_scope.

Notation "{{ x }}" := (S.singleton x) : set_scope.

Notation "E \u F" := (S.union E F)
  (at level 68, left associativity) : set_scope.

Notation "x \in E" := (S.In x E) (at level 69) : set_scope.

Notation "x \notin E" := (~(S.In x E)) (at level 69) : set_scope.

Notation "E << F" := (S.Subset E F) (at level 70) : set_scope.

Bind Scope set_scope with S.t.
Bind Scope set_scope with fset.

End FinSet.

(* ********************************************************************** *)
(** * Facts *)

Module FinSetFacts (M : FinSet).

Import M.
Local Open Scope set_scope.

(** Interaction of in with constructions *)

Lemma in_empty : forall x,
  x \in {} -> False.
Proof.
  intros.
  assert (S.Empty {}) by auto using S.empty_1. unfold S.Empty in *.
  assert (x \notin {}) by auto.
  intuition.
Qed.

Lemma in_singleton : forall x y,
  x \in {{y}} <-> x = y.
Proof.
  intros; split.
  intro H. symmetry. apply S.singleton_1. trivial.
  intro H. apply S.singleton_2. unfold S.E.eq. auto.
Qed.

Lemma in_union : forall x E F,
  x \in (E \u F) <-> (x \in E) \/ (x \in F).
Proof.
  intros; split.
  auto using S.union_1.
  intro H; destruct H as [ H | H ]; auto using S.union_2, S.union_3.
Qed.

(** Properties of union *)

Lemma union_same : forall E,
  E \u E = E.
Proof.
  intros. apply eq_if_Equal.
  split; repeat rewrite in_union; intuition.
Qed.

Lemma union_comm : forall E F,
  E \u F = F \u E.
Proof.
  intros. apply eq_if_Equal.
  split; repeat rewrite in_union; intuition.
Qed.

Lemma union_assoc : forall E F G,
  E \u (F \u G) = (E \u F) \u G.
Proof.
  intros. apply eq_if_Equal.
  split; repeat rewrite in_union; intuition.
Qed.

Lemma union_empty_l : forall E,
  {} \u E = E.
Proof.
  intros. apply eq_if_Equal.
  split; repeat rewrite in_union; intuition.
  contradictions. apply* in_empty.
Qed.

(** More properties of in *)

Lemma in_same : forall x,
  x \in {{x}}.
intros. rewrite* in_singleton.
Qed.

(** More properties of union *)

Lemma union_empty_r : forall E,
  E \u {} = E.
intros. rewrite union_comm.
apply union_empty_l.
Qed.

Lemma union_comm_assoc : forall E F G,
  E \u (F \u G) = F \u (E \u G).
intros. rewrite union_assoc.
rewrite (union_comm E F).
rewrite* <- union_assoc.
Qed.

(** Subset relation properties *)

Lemma subset_refl : forall E,
  E << E.
introz. auto.
Qed.

Lemma subset_trans : forall F E G,
  E << F -> F << G -> E << G.
introz. auto.
Qed.

(** Interaction of subset with constructions *)

Lemma subset_empty_l : forall E,
  {} << E.
introz. contradictions. apply* in_empty.
Qed.

Lemma subset_singleton : forall x E,
  x \in E <-> {{x}} << E.
unfold S.Subset. split; intros.
rewrite in_singleton in H0. subst*.
apply (H x). apply in_same.
Qed.

Lemma subset_union_weak_l : forall E F,
  E << (E \u F).
introz. rewrite* in_union.
Qed.

Lemma subset_union_weak_r : forall E F,
  F << (E \u F).
introz. rewrite* in_union.
Qed.

Lemma subset_union_l : forall E F G,
  (E \u F) << G <-> (E << G) /\ (F << G).
unfold S.Subset. splits; introz.
apply H. apply* subset_union_weak_l.
apply H. apply* subset_union_weak_r.
rewrite in_union in H0. intuition auto.
Qed.

(** Interaction of notin with constructions *)

Lemma notin_empty : forall x,
  x \notin {}.
introz. apply* in_empty.
Qed.

Lemma notin_singleton : forall x y,
  x \notin {{y}} <-> x <> y.
split; introz.
apply H. rewrite* in_singleton.
apply H. rewrite* <- in_singleton.
Qed.

Lemma notin_same : forall x,
  x \notin {{x}} -> False.
intros. use in_same.
Qed.

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
splits; intros.
rewrite in_union in H. auto*.
rewrite in_union in H. auto*.
rewrite* in_union.
Qed.

End FinSetFacts.
