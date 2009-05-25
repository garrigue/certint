(***************************************************************************
* Variation on FSet from library                                           *
* Brian Aydemir, March 2007, Coq v8.1                                      * 
***************************************************************************)


(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Eqdep_dec.
Require Import FSetList.
Require Import OrderedTypeEx.

Require Import Lib_ListFacts.
Require Import Lib_FinSet.

(* XXX modified functor name and signature *)

(** First, implement only [FSetInterface.S]. *)

Module MakeRaw (X : UsualOrderedType) <: FSetInterface.S with Module E := X.

 Module Raw := Raw X.
 Module E := X.

 (* XXX new code begins here *)

 Module OTFacts := OrderedTypeFacts E.

 Definition sort_bool (xs : Raw.t) :=
   (if (sort_dec E.lt OTFacts.lt_dec xs) then true else false) = true.

 Record slist : Type :=
  {this   :> Raw.t;
   sorted :  sort_bool this}.

 Definition from_sorted : forall (xs : Raw.t), sort E.lt xs -> sort_bool xs.
 Proof.
   intros xs H. unfold sort_bool.
   case (sort_dec E.lt OTFacts.lt_dec xs); tauto.
 Defined.

 Definition to_sorted : forall xs, sort_bool xs -> sort E.lt xs.
 Proof.
   unfold sort_bool. intros xs.
   case (sort_dec E.lt OTFacts.lt_dec xs); auto.
   intros. discriminate.
 Defined.

 Coercion to_sorted : sort_bool >-> sort.

 Definition Build_slist' (xs : Raw.t) (pf : sort E.lt xs) :=
   Build_slist (from_sorted pf).

 (* XXX new code ends here *)

 (* XXX lots of minor minor tweaks *)

 Definition t := slist.
 Definition elt := E.t.

 Definition In (x : elt) (s : t) : Prop := InA E.eq x s.(this).
 Definition Equal (s s':t) : Prop := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s':t) : Prop := forall a : elt, In a s -> In a s'.
 Definition Empty (s:t) : Prop := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop)(s:t) : Prop := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop)(s:t) : Prop := exists x, In x s /\ P x.

 Definition mem (x : elt) (s : t) : bool := Raw.mem x s.
 Definition add (x : elt)(s : t) : t := Build_slist' (Raw.add_sort (sorted s) x).
 Definition remove (x : elt)(s : t) : t := Build_slist' (Raw.remove_sort (sorted s) x).
 Definition singleton (x : elt) : t  := Build_slist' (Raw.singleton_sort x).
 Definition union (s s' : t) : t :=
   Build_slist' (Raw.union_sort (sorted s) (sorted s')).
 Definition inter (s s' : t) : t :=
   Build_slist' (Raw.inter_sort (sorted s) (sorted s')).
 Definition diff (s s' : t) : t :=
   Build_slist' (Raw.diff_sort (sorted s) (sorted s')).
 Definition equal (s s' : t) : bool := Raw.equal s s'.
 Definition subset (s s' : t) : bool := Raw.subset s s'.
 Definition empty : t := Build_slist' Raw.empty_sort.
 Definition is_empty (s : t) : bool := Raw.is_empty s.
 Definition elements (s : t) : list elt := Raw.elements s.
 Definition min_elt (s : t) : option elt := Raw.min_elt s.
 Definition max_elt (s : t) : option elt := Raw.max_elt s.
 Definition choose (s : t) : option elt  := Raw.choose s.
 Definition fold (B : Type) (f : elt -> B -> B) (s : t) : B -> B := Raw.fold (B:=B) f s.
 Definition cardinal (s : t) : nat := Raw.cardinal s.
 Definition filter (f : elt -> bool) (s : t) : t :=
   Build_slist' (Raw.filter_sort (sorted s) f).
 Definition for_all (f : elt -> bool) (s : t) : bool := Raw.for_all f s.
 Definition exists_ (f : elt -> bool) (s : t) : bool := Raw.exists_ f s.
 Definition partition (f : elt -> bool) (s : t) : t * t :=
   let p := Raw.partition f s in
   (@Build_slist' (fst p) (Raw.partition_sort_1 (sorted s) f),
   @Build_slist' (snd p) (Raw.partition_sort_2 (sorted s) f)).
 Definition eq (s s' : t) : Prop := Raw.eq s s'.
 Definition lt (s s' : t) : Prop := Raw.lt s s'.

 Section Spec.
  Variable s s' s'': t.
  Variable x y : elt.

  Lemma In_1 : E.eq x y -> In x s -> In y s.
  Proof. exact (fun H H' => Raw.MX.In_eq H H'). Qed.

  Lemma mem_1 : In x s -> mem x s = true.
  Proof. exact (fun H => Raw.mem_1 s.(sorted) H). Qed.
  Lemma mem_2 : mem x s = true -> In x s.
  Proof. exact (fun H => Raw.mem_2 H). Qed.

  Lemma equal_1 : Equal s s' -> equal s s' = true.
  Proof. exact (Raw.equal_1 s.(sorted) s'.(sorted)). Qed.
  Lemma equal_2 : equal s s' = true -> Equal s s'.
  Proof. exact (fun H => Raw.equal_2 H). Qed.

  Lemma subset_1 : Subset s s' -> subset s s' = true.
  Proof. exact (Raw.subset_1 s.(sorted) s'.(sorted)). Qed.
  Lemma subset_2 : subset s s' = true -> Subset s s'.
  Proof. exact (fun H => Raw.subset_2 H). Qed.

  Lemma empty_1 : Empty empty.
  Proof. exact Raw.empty_1. Qed.

  Lemma is_empty_1 : Empty s -> is_empty s = true.
  Proof. exact (fun H => Raw.is_empty_1 H). Qed.
  Lemma is_empty_2 : is_empty s = true -> Empty s.
  Proof. exact (fun H => Raw.is_empty_2 H). Qed.

  Lemma add_1 : E.eq x y -> In y (add x s).
  Proof. exact (fun H => Raw.add_1 s.(sorted) H). Qed.
  Lemma add_2 : In y s -> In y (add x s).
  Proof. exact (fun H => Raw.add_2 s.(sorted) x H). Qed.
  Lemma add_3 : ~ E.eq x y -> In y (add x s) -> In y s.
  Proof. exact (fun H => Raw.add_3 s.(sorted) H). Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x s).
  Proof. exact (fun H => Raw.remove_1 s.(sorted) H). Qed.
  Lemma remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
  Proof. exact (fun H H' => Raw.remove_2 s.(sorted) H H'). Qed.
  Lemma remove_3 : In y (remove x s) -> In y s.
  Proof. exact (fun H => Raw.remove_3 s.(sorted) H). Qed.

  Lemma singleton_1 : In y (singleton x) -> E.eq x y.
  Proof. exact (fun H => Raw.singleton_1 H). Qed.
  Lemma singleton_2 : E.eq x y -> In y (singleton x).
  Proof. exact (fun H => Raw.singleton_2 H). Qed.

  Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
  Proof. exact (fun H => Raw.union_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma union_2 : In x s -> In x (union s s').
  Proof. exact (fun H => Raw.union_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma union_3 : In x s' -> In x (union s s').
  Proof. exact (fun H => Raw.union_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma inter_1 : In x (inter s s') -> In x s.
  Proof. exact (fun H => Raw.inter_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma inter_2 : In x (inter s s') -> In x s'.
  Proof. exact (fun H => Raw.inter_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
  Proof. exact (fun H => Raw.inter_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma diff_1 : In x (diff s s') -> In x s.
  Proof. exact (fun H => Raw.diff_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma diff_2 : In x (diff s s') -> ~ In x s'.
  Proof. exact (fun H => Raw.diff_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
  Proof. exact (fun H => Raw.diff_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof. exact (Raw.fold_1 s.(sorted)). Qed.

  Lemma cardinal_1 : cardinal s = length (elements s).
  Proof. exact (Raw.cardinal_1 s.(sorted)). Qed.

  Section Filter.

  Variable f : elt -> bool.

  Lemma filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s.
  Proof. exact (@Raw.filter_1 s x f). Qed.
  Lemma filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true.
  Proof. exact (@Raw.filter_2 s x f). Qed.
  Lemma filter_3 :
      compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
  Proof. exact (@Raw.filter_3 s x f). Qed.

  Lemma for_all_1 :
      compat_bool E.eq f ->
      For_all (fun x => f x = true) s -> for_all f s = true.
  Proof. exact (@Raw.for_all_1 s f). Qed.
  Lemma for_all_2 :
      compat_bool E.eq f ->
      for_all f s = true -> For_all (fun x => f x = true) s.
  Proof. exact (@Raw.for_all_2 s f). Qed.

  Lemma exists_1 :
      compat_bool E.eq f ->
      Exists (fun x => f x = true) s -> exists_ f s = true.
  Proof. exact (@Raw.exists_1 s f). Qed.
  Lemma exists_2 :
      compat_bool E.eq f ->
      exists_ f s = true -> Exists (fun x => f x = true) s.
  Proof. exact (@Raw.exists_2 s f). Qed.

  Lemma partition_1 :
      compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof. exact (@Raw.partition_1 s f). Qed.
  Lemma partition_2 :
      compat_bool E.eq f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof. exact (@Raw.partition_2 s f). Qed.

  End Filter.

  Lemma elements_1 : In x s -> InA E.eq x (elements s).
  Proof. exact (fun H => Raw.elements_1 H). Qed.
  Lemma elements_2 : InA E.eq x (elements s) -> In x s.
  Proof. exact (fun H => Raw.elements_2 H). Qed.
  Lemma elements_3 : sort E.lt (elements s).
  Proof. exact (Raw.elements_3 s.(sorted)). Qed.
  Lemma elements_3w : NoDupA E.eq (elements s).
  Proof. exact (Raw.elements_3w s.(sorted)). Qed.

  Lemma min_elt_1 : min_elt s = Some x -> In x s.
  Proof. exact (fun H => Raw.min_elt_1 H). Qed.
  Lemma min_elt_2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
  Proof. exact (fun H => Raw.min_elt_2 s.(sorted) H). Qed.
  Lemma min_elt_3 : min_elt s = None -> Empty s.
  Proof. exact (fun H => Raw.min_elt_3 H). Qed.

  Lemma max_elt_1 : max_elt s = Some x -> In x s.
  Proof. exact (fun H => Raw.max_elt_1 H). Qed.
  Lemma max_elt_2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
  Proof. exact (fun H => Raw.max_elt_2 s.(sorted) H). Qed.
  Lemma max_elt_3 : max_elt s = None -> Empty s.
  Proof. exact (fun H => Raw.max_elt_3 H). Qed.

  Lemma choose_1 : choose s = Some x -> In x s.
  Proof. exact (fun H => Raw.choose_1 H). Qed.
  Lemma choose_2 : choose s = None -> Empty s.
  Proof. exact (fun H => Raw.choose_2 H). Qed.
  Lemma choose_3 : choose s = Some x -> choose s' = Some y -> 
   Equal s s' -> E.eq x y.
  Proof. exact (@Raw.choose_3 _ _ s.(sorted) s'.(sorted) x y). Qed.

  Lemma eq_refl : eq s s.
  Proof. exact (Raw.eq_refl s). Qed.
  Lemma eq_sym : eq s s' -> eq s' s.
  Proof. exact (@Raw.eq_sym s s'). Qed.
  Lemma eq_trans : eq s s' -> eq s' s'' -> eq s s''.
  Proof. exact (@Raw.eq_trans s s' s''). Qed.

  Lemma lt_trans : lt s s' -> lt s' s'' -> lt s s''.
  Proof. exact (@Raw.lt_trans s s' s''). Qed.
  Lemma lt_not_eq : lt s s' -> ~ eq s s'.
  Proof. exact (Raw.lt_not_eq s.(sorted) s'.(sorted)). Qed.

  Definition compare : Compare lt eq s s'.
  Proof.
  elim (Raw.compare s.(sorted) s'.(sorted));
   [ constructor 1 | constructor 2 | constructor 3 ];
   auto.
  Defined.

  Definition eq_dec : { eq s s' } + { ~ eq s s' }.
  Proof.
  change eq with Equal.
  case_eq (equal s s'); intro H; [left | right].
  apply equal_2; auto.
  intro H'; rewrite equal_1 in H; auto; discriminate.
  Defined.

 End Spec.

End MakeRaw.

(* XXX begin new code *)

(** Now, implement the [FinSet] interface. *)

Module Make (X : UsualOrderedType) <: FinSet with Module E := X.

  Module Import E := X.
  Module Import S := MakeRaw X.

  (** Define aliases. *)

  Definition fset := S.t.
  Definition elt := S.elt.

  (** Equality on these sets is extensional. *)

  Lemma bool_dec : forall x y : bool,
    x = y \/ x <> y.
  Proof.
    induction x; induction y; intuition.
  Qed.

  Theorem eq_ext : forall s s' : t, (forall a, In a s <-> In a s') -> s = s'.
  Proof.
    intros [s H] [s' J] K.
    assert (s = s').
      unfold Raw.t in *. eapply Sort_InA_eq_ext; eauto using to_sorted.
        eexact E.lt_trans.
        eexact E.lt_not_eq.
        intros. eapply OTFacts.lt_eq; eauto.
        intros. eapply OTFacts.eq_lt; eauto.
    intros. subst.
    rewrite (eq_proofs_unicity bool_dec H J).
    reflexivity.
  Qed.

  Theorem eq_if_Equal : forall s s' : t, Equal s s' -> s = s'.
  Proof.
    unfold Equal. intros s s'.
    auto using eq_ext.
  Qed.

End Make.
