(***************************************************************************
* Some facts about lists to complete standard library                      *
* Brian E. Aydemir                                                         *
***************************************************************************)

Require Import List.
Require Import SetoidList.
Require Import Sorting.
Require Import Relations.
Set Implicit Arguments.

(* ********************************************************************** *)
(** * List membership *)

Lemma not_in_cons :
  forall (A : Type) (ys : list A) x y,
  x <> y -> ~ In x ys -> ~ In x (y :: ys).
Proof.
  induction ys; simpl; intuition.
Qed.

Hint Resolve not_in_cons : core.

Lemma not_In_app :
  forall (A : Type) (xs ys : list A) x,
  ~ In x xs -> ~ In x ys -> ~ In x (xs ++ ys).
Proof.
  intros A xs ys x H J K.
  case (in_app_or _ _ _ K); auto.
Qed.

Hint Resolve not_In_app : core.

Lemma elim_not_In_cons :
  forall (A : Type) (y : A) (ys : list A) (x : A),
  ~ In x (y :: ys) -> x <> y /\ ~ In x ys.
Proof.
  intros. simpl in *. auto.
Qed.

Lemma elim_not_In_app :
  forall (A : Type) (xs ys : list A) (x : A),
  ~ In x (xs ++ ys) -> ~ In x xs /\ ~ In x ys.
Proof.
  split; auto using in_or_app.
Qed.

(* ********************************************************************** *)
(** * List inclusion *)

Lemma incl_nil :
  forall (A : Type) (xs : list A), incl nil xs.
Proof.
  unfold incl.
  intros A xs a H; inversion H.
Qed.

Hint Resolve incl_nil : core.

Lemma incl_trans :
  forall (A : Type) (xs ys zs : list A),
  incl xs ys -> incl ys zs -> incl xs zs.
Proof.
  unfold incl; firstorder.
Qed.

Hint Immediate incl_trans : core.

Lemma In_incl :
  forall (A : Type) (x : A) (ys zs : list A),
  In x ys -> incl ys zs -> In x zs.
Proof.
  unfold incl; auto.
Qed.

Hint Immediate In_incl : core.

Lemma elim_incl_cons :
  forall (A : Type) (x : A) (xs zs : list A),
  incl (x :: xs) zs -> In x zs /\ incl xs zs.
Proof.
  unfold incl; intros; split; auto with datatypes.
Qed.

Lemma elim_incl_app :
  forall (A : Type) (xs ys zs : list A),
  incl (xs ++ ys) zs -> incl xs zs /\ incl ys zs.
Proof.
  unfold incl; intros; split; auto with datatypes.
Qed.

(* ********************************************************************** *)
(** * Automation *)

(**
  The following are placed in the [datatypes] library by the List theory.
  It's convenient to also have them in [core].
*)

Hint Resolve in_eq : core.
Hint Resolve in_cons : core.
Hint Resolve incl_refl : core.
Hint Resolve incl_nil : core.
Hint Resolve incl_cons : core.
Hint Resolve incl_tl : core.
Hint Resolve incl_app : core.
Hint Immediate incl_trans : core.

(**
  The following tactics can be used to simply hypotheses concerning lists.
*)

Ltac simpl_list_hyp H :=
  let LH1 := fresh "LH" in
  let LH2 := fresh "LH" in
  match type of H with
    | incl (?J :: ?K) ?L =>
        destruct (elim_incl_cons H) as [LH1 LH2]; clear H;
        try simpl_list_hyp LH1; try simpl_list_hyp LH2
    | incl (?J ++ ?K) ?L =>
        destruct (elim_incl_app J K H) as [LH1 LH2]; clear H;
        try simpl_list_hyp LH1; try simpl_list_hyp LH2
    | incl nil _ =>
        clear H
    | In ?x (?y :: ?ys) =>
        destruct (in_inv H) as [LH1 | LH1]; clear H;
        try simpl_list_hyp LH1
    | In ?x (?ys ++ ?zs) =>
        destruct (in_app_or ys zs x H) as [LH1 | LH1]; clear H;
        try simpl_list_hyp LH1
    | In _ nil =>
        simpl in H; intuition
    | ~ In _ nil =>
        clear H
    | ~ In _ (_ :: _) =>
        destruct (elim_not_In_cons H) as [LH1 LH2]; clear H;
        try simpl_list_hyp LH1; try simpl_list_hyp LH2
    | ~ In ?x (?K ++ ?L) =>
        destruct (elim_not_In_app K L x H) as [LH1 LH2]; clear H;
        try simpl_list_hyp LH1; try simpl_list_hyp LH2
    | In _ _ =>
        progress (simpl in H)
    | incl _ _ =>
        progress (simpl in H)
    | ~ In _ _ =>
        progress (simpl in H)
  end.

Ltac simpl_list_hyps :=
  match goal with
    | H : _ |- _ => simpl_list_hyp H; simpl_list_hyps
    | H : ~ (?a = ?b \/ False), J : ?b = ?a |- _ => subst b; intuition
    | H : ~ (?a = ?b \/ False), J : ?a = ?b |- _ => subst a; intuition
    | _ => idtac
  end.

Hint Extern 4 (In ?x ?L) => simpl; simpl_list_hyps : core.
Hint Extern 4 (~ In ?x ?L) => simpl; simpl_list_hyps : core.
Hint Extern 4 (incl ?L1 ?L2) => simpl; simpl_list_hyps : core.

(* ********************************************************************** *)
(** * Setoid facts *)

Lemma InA_iff_In :
  forall (A : Set) x xs, InA (@eq A) x xs <-> In x xs.
Proof.
  induction xs as [ | y ys IH ].
  split; intros H; inversion H.
  split; intros H; inversion_clear H.
  subst x; auto with datatypes.
  assert (In x ys) by intuition; auto with datatypes.
  subst y; auto with datatypes.
  assert (InA (@eq A) x ys) by intuition; auto with datatypes.
Qed.

(* ********************************************************************** *)
(** * Decidable sorting *)

(**
  It is decidable to tell whether a list a sorted according to
  some relation.
*)

Section DecidableSorting.

Variable A : Type.
Variable leA : relation A.
Hypothesis leA_dec : forall x y, {leA x y} + {~ leA x y}.

Theorem lelistA_dec :
  forall a xs, {lelistA leA a xs} + {~ lelistA leA a xs}.
Proof.
  induction xs as [ | x xs IH ]; auto with datatypes.
  case (leA_dec a x); auto with datatypes.
  intros H. right. intros J. inversion J. auto.
Qed.

Theorem sort_dec :
  forall xs, {sort leA xs} + {~ sort leA xs}.
Proof.
  induction xs as [ | x xs IH ]; auto with datatypes.
  case IH; case (lelistA_dec x xs); auto with datatypes.
  intros H J. right. intros K. inversion K. auto.
  intros H J. right. intros K. inversion K. auto.
  intros H J. right. intros K. inversion K. auto.
Qed.

End DecidableSorting.

(* ********************************************************************** *)
(** * Equality on sorted lists *)

(**
  Two sorted lists are equal if they contain the same elements.
*)

Section Equality_ext.

Variable A : Type.
Variable ltA : relation A.
Hypothesis ltA_trans : forall x y z, ltA x y -> ltA y z -> ltA x z.
Hypothesis ltA_not_eqA : forall x y, ltA x y -> x <> y.
Hypothesis ltA_eqA : forall x y z, ltA x y -> y = z -> ltA x z.
Hypothesis eqA_ltA : forall x y z, x = y -> ltA y z -> ltA x z.

Hint Resolve ltA_trans : core.
Hint Immediate ltA_eqA eqA_ltA : core.

Notation Inf := (lelistA ltA).
Notation Sort := (sort ltA).

Lemma strictOrder_ltA : StrictOrder ltA.
Proof.
  try repeat (constructor; intuition).
  intro; intros; intro.
  apply (ltA_not_eqA H).
  auto.
Qed.
Hint Resolve strictOrder_ltA : core.

Lemma not_InA_if_Sort_Inf :
  forall xs a, Sort xs -> Inf a xs -> ~ InA (@eq A) a xs.
Proof.
  induction xs as [ | x xs IH ]; intros a Hsort Hinf H.
  inversion H.
  inversion H; subst.
    inversion Hinf; subst.
      assert (x <> x) by auto; intuition.
    inversion Hsort; inversion Hinf; subst.
      assert (Inf a xs) by eauto using InfA_ltA.
      assert (~ InA (@eq A) a xs) by auto.
      intuition.
Qed.

Lemma Sort_eq_head :
  forall x xs y ys,
  Sort (x :: xs) ->
  Sort (y :: ys) ->
  (forall a, InA (@eq A) a (x :: xs) <-> InA (@eq A) a (y :: ys)) ->
  x = y.
Proof.
  intros x xs y ys SortXS SortYS H.
  inversion SortXS; inversion SortYS; subst.
  assert (Q3 : InA (@eq A) x (y :: ys)) by firstorder.
  assert (Q4 : InA (@eq A) y (x :: xs)) by firstorder.
  inversion Q3; subst; auto.
  inversion Q4; subst; auto.
  assert (ltA y x) by (refine (SortA_InfA_InA _ _ _ H6 H7 H1); intuition).
  assert (ltA x y) by (refine (SortA_InfA_InA _ _ _ H2 H3 H4); intuition).
  assert (y <> y) by eauto.
  intuition.
Qed.

Lemma Sort_InA_eq_ext :
  forall xs ys,
  Sort xs ->
  Sort ys ->
  (forall a, InA (@eq A) a xs <-> InA (@eq A) a ys) ->
  xs = ys.
Proof.
  induction xs as [ | x xs IHxs ]; induction ys as [ | y ys IHys ];
      intros SortXS SortYS H; auto.
  (* xs -> nil, ys -> y :: ys *)
  assert (Q : InA (@eq A) y nil) by firstorder.
  inversion Q.
  (* xs -> x :: xs, ys -> nil *)
  assert (Q : InA (@eq A) x nil) by firstorder.
  inversion Q.
  (* xs -> x :: xs, ys -> y :: ys *)
  inversion SortXS; inversion SortYS; subst.
  assert (x = y) by eauto using Sort_eq_head.
  cut (forall a, InA (@eq A) a xs <-> InA (@eq A) a ys).
  intros. assert (xs = ys) by auto. subst. auto.
  intros a; split; intros L.
    assert (Q2 : InA (@eq A) a (y :: ys)) by firstorder.
      inversion Q2; subst; auto.
      assert (Q5 : ~ InA (@eq A) y xs) by auto using not_InA_if_Sort_Inf.
      intuition.
    assert (Q2 : InA (@eq A) a (x :: xs)) by firstorder.
      inversion Q2; subst; auto.
      assert (Q5 : ~ InA (@eq A) y ys) by auto using not_InA_if_Sort_Inf.
      intuition.
Qed.

End Equality_ext.
