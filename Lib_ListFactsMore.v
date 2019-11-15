(***************************************************************************
* More properties about Lists                                              *
* Arthur Chargueraud, July 2007, Coq v8.1                                  *
***************************************************************************)

Set Implicit Arguments.
Require Import Lib_Tactic List.

(** Results on List.map *)

Lemma list_map_id : forall (A : Set) l,
  List.map (fun t : A => t) l = l.
Proof.
  induction l; simpl; f_equal*.
Qed.

Lemma list_concat_right : forall (A : Set) (x : A) l1 l2,
  l1 ++ (x :: l2) = (l1 ++ (x :: nil)) ++ l2.
Proof.
  intros. induction l1; simpl; f_equal*.
Qed.

Lemma list_map_nth : forall (A : Set) (f : A -> A) d l n,
  f d = d -> 
  f (List.nth n l d) = List.nth n (List.map f l) d.
Proof.
  induction l; simpl; introv Fix; destruct* n.
Qed.

(** Results on List.forall *)

Inductive list_forall (A : Set) (P : A -> Prop) : list A -> Prop :=
  | list_forall_nil : list_forall P nil
  | list_forall_cons : forall L x,
       list_forall P L -> P x -> list_forall P (x::L).

Hint Constructors list_forall : core.

Lemma list_forall_concat : forall (A : Set) (P : A -> Prop) L1 L2,
  list_forall P L1 -> 
  list_forall P L2 ->
  list_forall P (L1 ++ L2).
Proof.
  induction L1; simpl; intros. auto. inversions* H.
Qed.

(** Results on List.for_n *)

Definition list_for_n (A : Set) (P : A -> Prop) (n : nat) (L : list A) :=
  n = length L /\ list_forall P L.

Lemma list_for_n_concat : forall (A : Set) (P : A -> Prop) n1 n2 L1 L2,
  list_for_n P n1 L1 -> 
  list_for_n P n2 L2 ->
  list_for_n P (n1+n2) (L1 ++ L2).
Proof.
  unfold list_for_n. intros. split. 
  rewrite* app_length. apply* list_forall_concat.
Qed.

Hint Extern 1 (?n = length ?xs) => 
 match goal with H: list_for_n _ ?n ?xs |- _ => 
  apply (proj1 H) end : more.

Hint Extern 1 (length ?xs = ?n) => 
 match goal with H: list_for_n _ ?n ?xs |- _ => 
  apply (sym_eq (proj1 H)) end : more.



