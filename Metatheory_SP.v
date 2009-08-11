(***************************************************************************
* Extra lemmas  and tactics concerning lists, sets, and metatheory         *
* Jacques Garrigue, june 2009, Coq 8.2                                     *
***************************************************************************)

Set Implicit Arguments.
Require Import List Arith Lib_Tactic Lib_FinSet.
Require Import Metatheory_Var.
Require Import Metatheory_Fresh.
Require Import Metatheory_Env.
Import Env.
Open Scope set_scope.
Open Scope env_scope.

(** Rewriting programs *)

Ltac case_rewrite H t :=
  case_eq t; introv H; rewrite H in *; try discriminate.

(** Results on lists *)

Hint Resolve in_or_app.

Lemma in_app_mid : forall (A:Set) (x a:A) l1 l2,
  In x (l1 ++ a :: l2) -> a = x \/ In x (l1 ++ l2).
Proof.
  intros.
  destruct* (in_app_or _ _ _ H).
  simpl in H0; destruct* H0.
Qed.

Lemma InA_In : forall v L, SetoidList.InA E.eq v L -> In v L.
  induction 1; auto.
Qed.

Lemma cons_append : forall (A:Set) (a:A) l, a :: l = (a :: nil) ++ l.
Proof. auto.
Qed.

Section Nth.
  Variables (A : Set) (d : A).

  Lemma exists_nth : forall x Xs,
    In x Xs -> exists n, n < length Xs /\ x = nth n Xs d.
  Proof.
    induction Xs; intros. elim H.
    simpl in H; destruct* H.
      exists 0; rewrite H; simpl; split*. apply lt_O_Sn.
    destruct* IHXs as [n [Hlen EQ]].
    exists (S n). simpl; split*.
    apply* lt_n_S.
  Qed.
End Nth.

Section Index.
  Variable A : Set.
  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Fixpoint index (i:nat) (x:A) (l : list A) {struct l} : option nat :=
    match l with
    | nil   => None
    | y::l' => if eq_dec x y then Some i else index (S i) x l'
    end.

  Lemma index_none_notin : forall x l n,
    index n x l = None -> ~In x l.
  Proof.
    induction l; simpl; intros. auto.
    destruct* (eq_dec x a). discriminate.
  Qed.

  Lemma index_ok : forall def a l n,
    index 0 a l = Some n ->
    n < length l /\ nth n l def = a.
  Proof.
    intros.
    replace n with (n-0) by omega.
    apply (proj2 (A:= 0 <= n)).
    gen n; generalize 0.
    induction l; simpl; intros. discriminate.
    destruct (eq_dec a a0).
      subst.
      inversions H.
      split*.
      replace (n0 - n0) with 0 by omega.
      auto with arith.
    destruct (IHl _ _ H).
    split. omega.
    case_eq (n0 - n); intros.
      elimtype False; omega.
    replace n2 with (n0 - S n) by omega.
    destruct H1.
    auto with arith.
  Qed.
End Index.

Section Combine.
  Variables A B : Set.

  Definition list_fst := List.map (@fst A B).
  Definition list_snd := List.map (@snd A B).
  Lemma combine_fst_snd : forall l,
    combine (list_fst l) (list_snd l) = l.
  Proof.
    induction l; simpl. auto.
    destruct a; simpl; rewrite* IHl.
  Qed.

  Lemma length_fst_snd : forall l,
    length (list_fst l) = length (list_snd l).
  Proof.
    intros; unfold list_fst, list_snd.
    do 2 rewrite map_length. auto.
  Qed.

  Lemma split_combine : forall (l:list (A*B)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
  Proof.
    intros. puts (split_combine l). rewrite H in H0. auto.
  Qed.

  Lemma split_length : forall l (l1:list A) (l2:list B),
    split l = (l1, l2) -> length l1 = length l2.
  Proof.
    intros.
    use (split_length_l l).
    rewrite <- (split_length_r l) in H0.
    rewrite H in H0; apply H0.
  Qed.

  Lemma combine_app : forall (l1 l2:list A) (l1' l2':list B),
    length l1 = length l1' ->
    combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
  Proof.
    induction l1; destruct l1'; simpl; intros; try discriminate. auto.
    rewrite* IHl1.
  Qed.

  Definition map_snd (f:B->B) :=
    List.map (fun p:A*B => (fst p, f (snd p))).

  Lemma map_snd_inv : forall f x y (l:list(A*B)),
    In (x, y) (map_snd f l) ->
    exists z, f z = y /\ In (x,z) l.
  Proof.
    intros.
    destruct (proj1 (in_map_iff _ _ _) H) as [[x' T'] [Heq Hin]].
    simpl in Heq. inversions Heq.
    exists* T'.
  Qed.

  Lemma in_map_snd : forall f x y (l:list(A*B)),
    In (x,y) l -> In (x, f y) (map_snd f l).
  Proof.
    introv.
    refine (in_map _ _ _).
  Qed.

  Lemma list_fst_map_snd : forall f l,
    list_fst (map_snd f l) = list_fst l.
  Proof.
    induction l; simpl; intros. auto. congruence.
  Qed.

  Lemma list_snd_map_snd : forall f l,
    list_snd (map_snd f l) = List.map f (list_snd l).
  Proof.
    induction l; simpl; intros. auto. congruence.
  Qed.

  Variable eq_dec : forall x y:A, {x=y}+{x<>y}.

  Fixpoint assoc x (l:list (A*B)) {struct l} : option B :=
    match l with
    | nil => None
    | (y,z)::r => if eq_dec x y then Some z else assoc x r
    end.

  Lemma assoc_sound : forall x y l,
    assoc x l = Some y -> In (x,y) l.
  Proof.
    induction l; simpl; intros. discriminate.
    destruct a. destruct* (eq_dec x a). inversions* H.
  Qed.

  Lemma assoc_complete : forall x y l,
    assoc x l = None -> ~In (x,y) l.
  Proof.
    induction l; simpl; intros; intro. tauto.
    destruct a. 
    destruct (eq_dec x a). discriminate.
    destruct H0. inversions* H0.
    elim (IHl H H0).
  Qed.

  Lemma assoc_map : forall f x y l,
    assoc x l = y -> assoc x (map_snd f l) = option_map f y.
  Proof.
    induction l; simpl; intros. subst*.
    destruct a.
    simpl.
    destruct* (eq_dec x a).
    inversions* H.
  Qed.
End Combine.

Hint Resolve split_length in_map_snd.


Section Map.
  Variables A B : Set.

  Lemma list_map_comp : forall (f g:A->A) l,
    List.map f (List.map g l) = List.map (fun x:A => f (g x)) l.
  Proof.
    induction l; simpl*. rewrite* IHl.
  Qed.

  Lemma list_map_ext : forall (l:list A) (f1 f2:A->B),
    (forall x, In x l -> f1 x = f2 x) ->
    List.map f1 l = List.map f2 l.
  Proof.
    intros. induction l. auto.
    simpl. rewrite* H. rewrite* IHl.
  Qed.
End Map.

Section Forall.
  Variables (A:Set) (P:A->Prop).

  Definition map_prop (f : forall c, P c) l : list_forall P l.
    induction l; auto.
  Defined.

  Lemma list_forall_in : forall l,
    (forall x, In x l -> P x) -> list_forall P l.
  Proof.
    induction l; simpl*.
  Qed.

  Lemma list_forall_out : forall l,
    list_forall P l -> forall x, In x l -> P x.
  Proof.
    induction 1; simpl*; intros.
    destruct* H1. subst*.
  Qed.

  Lemma list_forall_app : forall l1 l2,
    list_forall P l1 -> list_forall P l2 -> list_forall P (l1 ++ l2).
  Proof.
    induction 1; intros; simpl; auto.
  Qed.

  Lemma list_forall_app_inv : forall l1 l2,
    list_forall P (l1 ++ l2) -> list_forall P l2.
  Proof.
    induction l1; simpl; intros. auto.
    inversion* H.
  Qed.

  Lemma list_forall_apply : forall (Q:A->Prop) l,
    list_forall (fun x => P x -> Q x) l ->
    list_forall P l -> list_forall Q l.
  Proof.
    intros; induction* H.
    inversion* H0.
  Qed.

  Lemma list_forall_imp : forall (Q:A->Prop) l,
    (forall x, P x -> Q x) -> list_forall P l -> list_forall Q l.
  Proof.
    induction l; intros; auto.
    inversions H0.
    constructor; auto.
  Qed.

  Lemma list_forall_rev : forall l,
    list_forall P l -> list_forall P (rev l).
  Proof.
    induction l; simpl; intros; auto.
    inversions H.
    apply* list_forall_concat.
  Qed.

  Variable (B:Set) (Q:B -> Prop).

  Lemma list_forall_map : forall f l,
    (forall x, In x l -> P x -> Q (f x)) ->
    list_forall P l ->
    list_forall Q (List.map f l).
  Proof.
    intros; induction l.
    simpl*.
    inversion H0.
    simpl; constructor; auto.
  Qed.

  Lemma list_for_n_map : forall f n l,
    (forall x, In x l -> P x -> Q (f x)) ->
    list_for_n P n l ->
    list_for_n Q n (List.map f l).
  Proof.
    intros.
    destruct H0; split. rewrite* map_length.
    apply* list_forall_map.
  Qed.
End Forall.

Hint Resolve list_forall_apply.

Ltac list_forall_find P l :=
  match goal with
  | H: list_forall P ?l1 |- _ =>
    match l1 with context[l] => apply* (list_forall_out H) end
  end.

Ltac list_forall_solve :=
  match goal with
  | |- list_forall ?P ?l =>
    apply list_forall_in; intros; list_forall_find P l
  | |- list_forall ?P (?l1++?l2) =>
    let a := fresh "a" in let H := fresh "Hin" in
    apply list_forall_in; intros a H;
    destruct (in_app_or _ _ _ H);
      [list_forall_find P l1 | list_forall_find P l2]
  | |- list_forall ?P (?a :: ?l) =>
    let x := fresh "x" in let H := fresh "Hin" in
    apply list_forall_in; intros x H; simpl in H;
    destruct H; [subst x; list_forall_find P a | list_forall_find P l]
  end.

Hint Extern 1 (list_forall _ _) => solve [list_forall_solve].

Section Forall2.

Inductive list_forall2 (A B:Set) (P:A->B->Prop) : list A -> list B -> Prop :=
  | list_forall2_nil : list_forall2 P nil nil
  | list_forall2_cons : forall a b la lb,
      P a b ->
      list_forall2 P la lb ->
      list_forall2 P (a::la) (b::lb).

Hint Constructors list_forall2.

Variables A B : Set.
Variable P : A -> B -> Prop.

Lemma list_forall2_app : forall l1 l2 l3 l4,
  list_forall2 P l1 l3 -> list_forall2 P l2 l4 ->
  list_forall2 P (l1 ++ l2) (l3 ++ l4).
Proof.
  intros until 1.
  revert l2 l4.
  induction H; simpl*.
Qed.

Lemma list_forall2_app_inv : forall l2 l4 l1 l3,
  list_forall2 P (l1 ++ l2) (l3 ++ l4) ->
  length l1 = length l3 ->
  list_forall2 P l1 l3 /\ list_forall2 P l2 l4.
Proof.
  induction l1; intros; destruct l3; try discriminate; simpl in *.
    auto.
  inversions H.
  destruct* (IHl1 l3).
Qed.

Lemma list_forall2_length : forall l1 l2,
  list_forall2 P l1 l2 -> length l1 = length l2.
Proof.
  induction 1; simpl*.
Qed.

Lemma list_forall2_In: forall x l1 l2,
  In x l1 -> list_forall2 P l1 l2 -> exists y:B, In y l2 /\ P x y.
Proof.
  induction 2. elim H.
  simpl in H; destruct H.
    subst*.
  destruct* IHlist_forall2.
Qed.

Lemma list_forall2_get : forall Xs Ys Zs x y z,
  list_forall2 P Ys Zs ->
  binds x y (combine Xs Ys) ->
  binds x z (combine Xs Zs) ->
  P y z.
Proof.
  intros.
  gen Xs; induction H; intros; destruct Xs; try discriminate.
  simpl in *.
  env_fix.
  binds_cases H1; binds_cases H2;
    try solve [elim Fr; apply S.singleton_2; reflexivity].
    apply* IHlist_forall2.
  subst*.
Qed.

Lemma list_forall2_nth : forall d1 d2 n l1 l2,
  list_forall2 P l1 l2 -> n < length l1 ->
  P (nth n l1 d1) (nth n l2 d2).
Proof.
  induction n; intros; inversions H; try elim (lt_n_O _ H0).
    auto.
  simpl. apply* IHn. simpl in H0; auto with arith.
Qed.

Lemma list_forall2_rev : forall l1 l2,
  list_forall2 P l1 l2 ->  list_forall2 P (rev l1) (rev l2).
Proof.
  induction 1; simpl. auto.
  apply* list_forall2_app.
Qed.

Variables C D : Set.
Variable P' : A -> B -> Prop.

Lemma list_forall2_map: forall (P1:C->D->Prop) f g l1 l2,
  list_forall2 P l1 l2 ->
  (forall x y, P x y -> P1 (f x) (g y)) ->
  list_forall2 P1 (List.map f l1) (List.map g l2).
Proof.
  clear P'.
  induction 1; simpls; auto*.
Qed.

Lemma list_forall2_imp : forall l1 l2,
  list_forall2 P l1 l2 ->
  (forall x y, P x y -> P' x y) ->
  list_forall2 P' l1 l2.
Proof.
  induction 1; simpls; auto*.
Qed.

Lemma For_all2_map_iff1 : forall (f:C->A) l1 l2,
  list_forall2 P (List.map f l1) l2 <-> list_forall2 (fun x => P (f x)) l1 l2.
Proof.
  induction l1; destruct l2; simpl; split; intros; inversions H; auto;
    destruct* (IHl1 l2).
Qed.

Lemma list_forall2_refl : forall (P:A->A->Prop),
  (forall x, P x x) ->
  forall l, list_forall2 P l l.
Proof.
  induction l; simpl*.
Qed.
End Forall2.

Hint Constructors list_forall2.
Hint Resolve list_forall2_app list_forall2_length
  list_forall2_map list_forall2_imp list_forall2_refl.

Section Cut.
  Variable A:Set.

  Fixpoint cut (n:nat) (l:list A) {struct n} : list A * list A :=
    match n with
    | 0 => (nil, l)
    | S n =>
      match l with
      | nil => (nil, nil)
      | a :: l => let (l1, l2) := cut n l in (a :: l1, l2)
      end
    end.

  Lemma cut_ok : forall n l l1 l2,
    n <= length l -> cut n l = (l1, l2) ->
    length l1 = n /\ l = l1 ++ l2.
  Proof.
    induction n; simpl; intros.
      inversions* H0.
    destruct l; simpl in *.
      elimtype False; omega.
    assert (n <= length l) by omega.
    case_rewrite R (cut n l).
    inversions* H0.
    destruct* (IHn l l0 l2).
    subst*.
  Qed.
End Cut.

(** Properties of mkset *)

Fixpoint mkset (l:list var) {struct l} : vars :=
  match l with
  | nil => {}
  | h :: t => {{h}} \u mkset t
  end.

Lemma in_mkset : forall x Xs,
  In x Xs -> x \in mkset Xs.
Proof.
  induction Xs; intros. elim H.
  simpl.
  simpl in H; destruct H.
    apply S.union_2. auto with sets.
  apply* S.union_3.
Qed.

(** Disjointness *)

Definition disjoint s1 s2 :=
  forall x, x \in s1 -> x \notin s2.

Lemma disjoint_comm : forall A B,
  disjoint A B -> disjoint B A.
Proof.
  intros. intros x Hx Hx'. elim (H _ Hx' Hx).
Qed.

(********************************************************************)
(* A clever tactic to handle finite sets                            *)

(* First, some properties of sets *)

Lemma mem_3 : forall v L, S.mem v L = false -> v \notin L.
Proof.
  intros. intro.
  rewrite (S.mem_1 H0) in H.
  discriminate.
Qed.

Hint Resolve mem_3.

Lemma in_vars_dec : forall v S, {v \in S}+{v \notin S}.
Proof.
  intros.
  case_eq (S.mem v S); intros; auto with sets.
Qed.

Lemma remove_4 : forall y x L, y \in S.remove x L -> ~E.eq x y.
Proof.
  intros; intro.
  elim (S.remove_1 H0 H).
Qed.

Ltac sets_simpl_hyps x :=
  match goal with
  | H: _ \in {} |- _ => elim (in_empty H)
  | H: x \in {{?y}} |- _ =>
    puts (proj1 (in_singleton _ _) H); clear H;
    subst y; try sets_simpl_hyps x
  | H: x \in S.diff _ _ |- _ =>
    let H1 := fresh "Hin" in let H2 := fresh "Hn" in
    poses H1 (S.diff_1 H); poses H2 (S.diff_2 H); clear H;
    try sets_simpl_hyps x
  | H: x \in S.inter _ _ |- _ =>
    let H1 := fresh "Hin" in let H2 := fresh "Hin" in
    poses H1 (S.inter_1 H); poses H2 (S.inter_2 H); clear H;
    try sets_simpl_hyps x
  | H: S.mem x _ = false |- _ =>
    let H1 := fresh "Hn" in
    poses H1 (mem_3 H); clear H; try sets_simpl_hyps x
  | H: x \in S.remove _ _ |- _ =>
    let H1 := fresh "Hin" in let H2 := fresh "Hn" in
    poses H1 (S.remove_3 H); poses H2 (remove_4 H); clear H;
    try sets_simpl_hyps x
  end.

Ltac sets_simpl :=
  match goal with |- ?x \in _ => try sets_simpl_hyps x end.

Ltac find_in_goal L :=
  match goal with |- ?x \in ?E =>
    match E with context[L] =>
      match goal with
      | |- x \in L => assumption
      | |- _ \in ?L1 \u ?L2 =>
        try (apply S.union_2; find_in_goal L);
          apply S.union_3; find_in_goal L
      | |- _ \in S.diff ?L1 ?L2 =>
        apply S.diff_3; [find_in_goal L | notin_solve]
      | |- _ \in S.remove ?y ?L1 =>
        let H1 := fresh "HE" in
        apply S.remove_2;
        [try assumption; intro HE; rewrite HE in *; solve [auto]
        | find_in_goal L]
      end
    end
  end.

Ltac find_in_solve x :=
  match goal with
  | |- ?y \in _ => puts (S.singleton_2 (S.E.eq_refl y)); find_in_goal {{y}}
  | H: x \in ?L |- _ => find_in_goal L
  end.

Ltac union_solve x :=
  try sets_simpl_hyps x;
  try match goal with
  | H: ~E.eq ?y ?y |- _ => elim H; reflexivity
  | H: ?y <> ?y |- _ => elim H; reflexivity
  | H: x \in _ \u _ |- _ =>
    destruct (S.union_1 H); clear H; union_solve x
  | H: x \notin ?L1 |- _ =>
    match L1 with context[{{x}}] =>
      elim H; find_in_solve x
    end ||
    match goal with
    | H': x \in L1 |- _ => elim (H H')
    | H': x \in ?L2 |- _ =>
      match L1 with context[L2] =>
        elim H; find_in_solve x
      end
    end
  | H: ?L1 << ?L2 |- _ =>
    match goal with
    | H': x \in L1 |- _ =>
      let H1 := fresh "Hin" in poses H1 (H _ H'); clear H; union_solve x
    | H': x \in ?L3 |- _ =>
      match L1 with context[L3] =>
        let H1 := fresh "Hin" in 
        assert (H1: x \in L2) by (apply H; find_in_solve x);
        clear H; union_solve x
      end
    end
  | H: disjoint ?L1 ?L2 |- _ =>
    match goal with
    | H': x \in L1 |- _ =>
      let H1 := fresh "Hin" in poses H1 (H _ H'); clear H; union_solve x
    | H': x \in L2 |- _ =>
      let H1 := fresh "Hin" in
      poses H1 (disjoint_comm H H'); clear H; union_solve x
    | H': x \in ?L3 |- _ =>
      match L1 with context[L3] =>
        let H1 := fresh "Hin" in 
        assert (H1: x \notin L2) by (apply H; find_in_solve x);
        clear H; union_solve x
      end ||
      match L2 with context[L3] =>
        let H1 := fresh "Hin" in 
        assert (H1: x \notin L1) by (apply (disjoint_comm H); find_in_solve x);
        clear H; union_solve x
      end
    end
  end.

Ltac sets_solve :=
  match goal with
  | |- ?x \in _ => try union_solve x; try find_in_solve x
  | |- _ << _ =>
    let y := fresh "y" in let Hy := fresh "Hy" in
    intros y Hy; sets_solve
  | |- ?x \notin _ =>
    let H := fresh "Hin" in intro H; try union_solve x
  | |- disjoint _ _ =>
    let y := fresh "y" in let Hy := fresh "Hy" in let Hy' := fresh "Hy'" in
    intros y Hy Hy'; try union_solve y
  end.

Lemma test_self : forall x, x \in {{x}}.
  intros; sets_solve.
Qed.

Lemma test_remove : forall x L1 L2,
  S.remove x (L1 \u L2) << S.remove x (L2 \u L1).
Proof.
  intros; sets_solve.
Qed.

Lemma test_subset : forall L1 L2 L3,
  L2 << L1 -> L1 \u L2 << L3 -> L2 << L3.
Proof.
  intros; sets_solve.
Qed.

Local Hint Extern 1 (_ \in _) => solve [sets_solve].
Local Hint Extern 1 (_ << _) => solve [sets_solve].
Local Hint Extern 1 (_ \notin _) => solve [sets_solve].
Local Hint Extern 1 (disjoint _ _) => solve [sets_solve].

(** More results on disjointness *)

Lemma disjoint_union : forall A B C,
  disjoint A B -> disjoint A C -> disjoint A (B \u C).
Proof.
  intros. auto.
Qed.

Lemma disjoint_empty : forall A, disjoint A {}.
  auto*.
Qed.

Lemma disjoint_empty_l : forall A, disjoint {} A.
  auto*.
Qed.

Lemma notin_disjoint : forall x A, x \notin A -> disjoint A {{x}}.
  auto*.
Qed.

Lemma notin_disjoint_l : forall x L, x \notin L -> disjoint {{x}} L.
  auto*.
Qed.

Lemma ok_disjoint : forall (A:Set) (E F:Env.env A),
  ok (E & F) -> disjoint (dom E) (dom F).
Proof.
  induction F; simpls; intros. auto.
  destruct a; simpl.
  inversions H.
  rewrite dom_concat in H4.
  use (IHF H2).
Qed.
Hint Resolve ok_disjoint.

Lemma fresh_disjoint : forall n Xs L,
  fresh L n Xs -> disjoint (mkset Xs) L.
Proof.
  induction n; destruct Xs; simpl; intros; auto*.
  destruct H.
  sets_solve.
  apply* (IHn _ _ H0).
Qed.
Hint Immediate fresh_disjoint.

Lemma neq_disjoint : forall x y, x <> y -> disjoint {{x}} {{y}}.
  auto*.
Qed.

Lemma disjoint_notin : forall s v, disjoint s {{v}} -> v \notin s.
  auto*.
Qed.

Lemma diff_disjoint : forall L1 L2, disjoint (S.diff L1 L2) L2.
  auto*.
Qed.

Lemma fresh_notin_mkset : forall n x Xs,
  fresh {{x}} n Xs -> x \notin mkset Xs.
Proof.
  intros.
  apply* disjoint_notin.
Qed.

(** Results on environments *)

Section Env.
  Variable A : Set.

  Definition in_concat_or (E F:env A) p (H:In p (E & F)) :=
    in_app_or F E p H.

  Definition in_or_concat (E F:env A) p H : In p (E & F) :=
    in_or_app F E p H.

  Hint Resolve in_or_concat.

  Lemma ok_cons : forall (E:env A) x (a:A),
    ok E -> x # E -> ok ((x,a) :: E).
  Proof (@ok_push A).

  Lemma ok_single : forall x (a:A), ok (x ~ a).
    intros. unfold single; apply ok_cons. apply (@ok_empty A).
    simpl*.
  Qed.

  Lemma binds_in : forall x (a:A) E,
    binds x a E -> In (x, a) E.
  Proof.
    unfold binds; induction E; intros. elim (binds_empty H).
    destruct a0; simpl in *.
    destruct* (x == v). inversions* H.
  Qed.

  Lemma in_dom : forall x (a:A) E,
    In (x,a) E -> x \in dom E.
  Proof.
    induction E; simpl; intros. elim H.
    destruct H.
      subst. auto.
    destruct a0.
    use (IHE H).
  Qed.

  Lemma binds_dom : forall x (a:A) E,
    binds x a E -> x \in dom E.
  Proof.
    intros; apply* in_dom; apply* binds_in.
  Qed.

  Lemma in_ok_binds : forall x (a:A) E,
    In (x,a) E -> ok E -> binds x a E.
  Proof.
    intros.
    unfold binds.
    induction H0. elim H.
    simpl.
    simpl in H; destruct H.
      inversions H.
      destruct* (x == x).
    destruct* (x == x0).
    subst.
    elim (binds_fresh (IHok H) H1).
  Qed.

  Lemma dom_binds : forall x E,
    x \in dom E -> exists y:A, binds x y E.
  Proof.
    induction E; simpl; intros. elim (in_empty H).
    destruct a.
    destruct (x == v); subst.
      exists a. apply (binds_head v a E).
    destruct* (S.union_1 H).
      elim n; rewrite* (proj1 (in_singleton x v) H0).
    destruct* IHE.
    exists x0.
    apply* (@binds_tail A x v x0 a E).
  Qed.

  Lemma binds_combine : forall x (c:A) Ys Ks,
    binds x c (combine Ys Ks) -> In c Ks.
  Proof.
    induction Ys; destruct Ks; simpl; intros; try (elim (binds_empty H)).
    unfold binds in H. simpl in H.
    destruct* (eq_var_dec x a). inversion* H.
  Qed.

  Lemma in_dom_combine : forall v Xs (Us:list A),
    v \in dom (combine Xs Us) -> In v Xs.
  Proof.
    induction Xs; destruct Us; simpl; auto; intros.
      elim (in_empty H).
    destruct (proj1 (in_union _ _ _) H).
      rewrite* (proj1 (in_singleton _ _) H0).
    auto*.
  Qed.

  (** More properties of get *)

  Lemma get_notin_dom : forall x (S :env A),
    x # S -> get x S = None.
  Proof.
    induction S; intros. auto.
    destruct a; simpl in *.
    destruct (eq_var_dec x v).
      rewrite e in H. elim H. auto with sets.
    auto with sets.
  Qed.

  Lemma dom_combine : forall Xs (As:list A),
    length Xs = length As -> dom (combine Xs As) = mkset Xs.
  Proof.
    induction Xs; destruct As; simpl; intros; try discriminate. auto.
    rewrite* IHXs.
  Qed.

  Lemma get_none_notin : forall x (S : env A),
    get x S = None -> x # S.
  Proof.
    induction S; intro; simpl; auto*.
    destruct* a.
    simpl in H. destruct* (eq_var_dec x v).
      discriminate.
    intro. destruct* (proj1 (in_union _ _ _) H0).
    elim n; apply (proj1 (in_singleton _ _) H1).
  Qed.

  Lemma get_none_notin_list : forall x (a:A) E,
    get x E = None -> ~In (x,a) E.
  Proof.
    induction E; simpl; intros. auto.
    destruct a0. destruct (x == v). discriminate.
    intro. destruct H0. inversions H0. elim n; auto.
    intuition.
  Qed.

Section Map.
  Variable f : A -> A.

  Lemma ok_map0 : forall E,
    ok E -> ok (map f E).
  Proof.
    intros.
    rewrite (app_nil_end (map f E)).
    fold (nil & map f E).
    apply ok_map.
    unfold concat; rewrite* <- (app_nil_end E).
  Qed.

  Lemma map_snd_env_map : forall l,
    List.map (fun X:var*A => (fst X, f (snd X))) l = Env.map f l.
  Proof.
    induction l; simpl*.
    destruct a. rewrite* IHl.
  Qed.

  Lemma map_get_none : forall x E,
    get x E = None -> get x (map f E) = None.
  Proof.
    induction E; simpl; intros; auto*.
    destruct a. simpl. destruct* (eq_var_dec x v).
    discriminate.
  Qed.

  Lemma in_map_inv : forall x a E,
    In (x,a) (map f E) -> exists b, f b = a /\ In (x,b) E.
  Proof.
    induction E; simpl; intros. elim H.
    destruct a0.
    simpl in H; destruct H.
      inversions H.
      exists* a0.
    destruct (IHE H).
    exists* x0.
  Qed.

  Lemma binds_map_inv : forall S x y,
    binds x y (map f S) -> exists z, f z = y /\ binds x z S.
  Proof.
    unfold binds.
    induction S; simpl; intros. discriminate.
    destruct a.
    simpl in H.
    destruct (x == v).
    inversions H.
      exists* a.
    apply* IHS.
  Qed.
End Map.

Section Env_prop.
  Variable P : A -> Prop.

  Lemma env_prop_single : forall x a, P a -> env_prop P (x ~ a).
  Proof.
    intros; intro; intros.
    destruct* H0.
    inversions* H0.
  Qed.

  Lemma env_prop_concat : forall l1 l2,
    env_prop P l1 -> env_prop P l2 -> env_prop P (l1 & l2).
  Proof.
    intros; intro; intros.
    destruct* (in_app_or _ _ _ H1).
  Qed.

  Lemma env_prop_concat_inv1 : forall l1 l2,
    env_prop P (l1 & l2) -> env_prop P l1.
  Proof.
    intros; intro; intros. apply* (H x).
  Qed.

  Lemma env_prop_concat_inv2 : forall l1 l2,
    env_prop P (l1 & l2) -> env_prop P l2.
  Proof.
    intros; intro; intros. apply* (H x).
  Qed.

  Lemma env_prop_map : forall (f:A->A) E,
    env_prop P (map f E) -> env_prop (fun x => P (f x)) E.
  Proof.
    intros; intro; intros.
    apply (H x).
    rewrite <- map_snd_env_map.
    use (in_map (fun X : var * A => (fst X, f (snd X))) _ _ H0).
  Qed.

  Lemma env_prop_list_forall : forall Xs Vs,
    env_prop P (combine Xs Vs) ->
    ok (combine Xs Vs) -> length Xs = length Vs -> list_forall P Vs.
  Proof.
    induction Xs; destruct Vs; simpl; intros; try discriminate; auto.
    inversion H1; inversions H0.
    constructor.
      apply* (IHXs Vs).
      intro; intros. apply* (H x).
    apply* (H a).
  Qed.

  Lemma list_forall_env_prop : forall Xs Vs,
    list_forall P Vs -> env_prop P (combine Xs Vs).
  Proof.
    intros; gen Xs.
    induction H; destruct Xs; intro; simpl; intros; try contradiction.
    destruct H1.
      inversions* H1.
    apply (IHlist_forall _ _ _ H1).
  Qed.
End Env_prop.

Section Fv_in.
  Variable fv : A -> vars.

  Lemma fv_in_concat : forall E F,
    fv_in fv (E & F) = fv_in fv F \u fv_in fv E.
  Proof.
    induction F; simpl.
      rewrite* union_empty_l.
    destruct a.
    rewrite <- union_assoc. rewrite* IHF.
  Qed.

  Lemma fv_in_subset_inv : forall F E,
    fv_in fv E << F <-> env_prop (fun a:A => fv a << F) E.
  Proof.
    split; intros.
      intro; intros.
      apply* subset_trans.
      apply* (fv_in_spec fv _ _ _ H0).
    induction E. simpl*.
    simpl in *. destruct a.
    sets_solve.
      refine (H v _ _ _ H0). auto.
    refine (IHE _ _ H0).
    intro; intros. apply* (H x).
  Qed.

  Lemma incl_fv_in_subset : forall E F,
    incl E F -> fv_in fv E << fv_in fv F.
  Proof.
    induction E; simpl; intros. auto.
    destruct a.
    assert (In (v,a) F) by auto.
    use (fv_in_spec fv _ _ _ H0).
    simpl in *.
    forward~ (IHE F) as G.
  Qed.

  Lemma fv_in_binds : forall x E,
    x \in fv_in fv E -> exists y, exists a, x \in fv a /\ In (y,a) E.
  Proof.
    induction E; intros. elim (in_empty H).
    destruct a; simpl in *.
    destruct (S.union_1 H); clear H.
      exists v; exists a; auto.
    destruct (IHE H0) as [y [b [Hx Hy]]].
    esplit. esplit. split*.
  Qed.
End Fv_in.
End Env.

Hint Resolve in_ok_binds ok_map0 ok_single env_prop_single env_prop_concat.
Hint Resolve list_forall_env_prop in_or_concat.
Hint Immediate binds_in env_prop_concat_inv1 env_prop_concat_inv2.
Hint Unfold extends.

Lemma get_contradicts : forall (A B:Set) x (a:A) Xs Vs (Ks:list B),
  get x (combine Xs Vs) = Some a ->
  get x (combine Xs Ks) = None ->
  length Xs = length Ks -> False.
Proof.
  intros.
  elim (binds_fresh H).
  intro.
  elim (get_none_notin _ H0).
  rewrite* dom_combine.
  apply in_mkset.
  apply* in_dom_combine.
Qed.

(** Results on fresh *)

Lemma fresh_app : forall m Xs' n Xs L,
  fresh L n Xs -> fresh (L \u mkset Xs) m Xs' -> fresh L (n+m) (Xs++Xs').
Proof.
  induction n; destruct Xs; simpl; intros; try contradiction. auto.
  destruct H; split*.
Qed.

Lemma fresh_sub : forall n Xs L1 L2,
  fresh L1 n Xs -> L2 << L1 -> fresh L2 n Xs.
Proof.
  induction n; destruct Xs; intros; try (inversion H; discriminate).
    simpl*.
  simpl in *.
  destruct H.
  split; auto*.
Qed.

Lemma notin_combine_fresh : forall (A:Set) Xs v (Vs:list A) n L,
  fresh L n Xs -> v \in L -> v # (combine Xs Vs).
Proof.
  induction Xs; simpl; intros. auto.
  destruct* Vs. auto with sets.
  destruct n. elim H.
  destruct H.
  apply (proj2 (notin_union v {{a}} (dom (combine Xs Vs)))).
  split.
    intro Hv. elim H.
    rewrite* <- (proj1 (in_singleton _ _) Hv).
  apply* IHXs.
Qed.

Lemma ok_combine_fresh : forall (A:Set) L n Xs (Vs:list A),
  fresh L n Xs -> ok (combine Xs Vs).
Proof.
  induction n; destruct Xs; simpl; intros; destruct* Vs;
    try apply (ok_empty A).
  apply* ok_cons.
  apply* notin_combine_fresh.
Qed.

Lemma fresh_rev : forall x L n xs,
  fresh L n xs -> x \in L -> ~In x xs.
Proof.
  induction n; destruct xs; simpl; intros; auto.
  intros [e | i].
    elim (proj1 H); rewrite e; auto.
  elim (IHn xs); auto*.
Qed.

Lemma in_fresh : forall x Xs L n,
  fresh L n Xs -> In x Xs -> x \notin L.
Proof.
  induction Xs; simpl; intros. elim H0.
  destruct* n.
  destruct H0.
    subst*.
  use (IHXs _ _ (proj2 H)).
Qed.

Lemma list_forall2_binds : forall (A:Set) (Ks':list A) Xs K,
  fresh (dom K) (length Ks') Xs ->
  list_forall2 (fun y x => binds x y (combine Xs Ks' & K)) Ks' Xs.
Proof.
  induction Ks'; destruct Xs; simpl; intros; try contradiction.
    auto.
  destruct H.
  constructor.
    apply* binds_concat_fresh. apply (binds_head v a (combine Xs Ks')).
  replace (((v, a) :: combine Xs Ks') & K)
    with (combine Xs Ks' & (v ~ a & K)).
    apply IHKs'. rewrite dom_concat. simpl. auto.
  unfold concat. rewrite app_ass. reflexivity.
Qed.

(** Results on \notin *)

Lemma notin_subset : forall S1 S2,
  S1 << S2 ->
  forall x, x \notin S2 -> x \notin S1.
Proof.
  auto*.
Qed.

Lemma notin_remove_self : forall v L, v \notin S.remove v L.
  auto*.
Qed.

Lemma notin_remove : forall x v L, v \notin L -> v \notin S.remove x L.
  auto*.
Qed.

Lemma notin_mkset : forall x l, ~In x l -> x \notin mkset l.
Proof.
  induction l; simpl; intros. auto.
  intuition.
  union_solve x; auto*.
Qed.

Hint Resolve notin_mkset.

(** Other results on sets *)

Lemma mkset_app : forall Xs Ys,
  mkset (Xs ++ Ys) = mkset Xs \u mkset Ys.
Proof.
  induction Xs; simpl; intros. rewrite* union_empty_l.
  rewrite IHXs.
  rewrite* union_assoc.
Qed.

Lemma mkset_in : forall x l, x \in mkset l -> In x l.
Proof.
  intros.
  destruct* (In_dec eq_var_dec x l).
  elim (notin_mkset _  n H).
Qed.

Lemma remove_notin : forall v L,
  v \notin L -> S.remove v L = L.
Proof.
  intros.
  apply eq_ext; intro; split; intro. eauto with sets.
  apply* S.remove_2.
  intro Hv; rewrite Hv in H; auto.
Qed.

Lemma remove_single : forall v, S.remove v {{v}} = {}.
Proof.
  intros; apply eq_ext; auto*.
Qed.

Lemma subset_incl_elements : forall L1 L2,
  L1 << L2 -> incl (S.elements L1) (S.elements L2).
Proof.
  intros; intro; intros. 
  apply InA_In; apply S.elements_1.
  use (S.elements_2 (SetoidList.In_InA E.eq_refl H0)).
Qed.

Lemma elements_singleton : forall x,
  S.elements {{x}} = (x :: nil).
Proof.
  intros.
  assert (x \in {{x}}) by auto.
  puts (S.elements_1 H).
  remember (S.elements {{x}}) as l.
  destruct l. inversion H0.
  destruct l.
    inversions H0. rewrite H2. auto.
    inversion H2.
  puts (S.elements_3 {{x}}).
  rewrite <- Heql in H1.
  inversions H1. inversions H5.
  assert (e \in {{x}}). apply S.elements_2.
    rewrite* <- Heql.
  assert (e0 \in {{x}}). apply S.elements_2.
    rewrite* <- Heql.
  rewrite <- (S.singleton_1 H2) in H3.
  rewrite <- (S.singleton_1 H6) in H3.
  elim (E.lt_not_eq _ _ H3). reflexivity.
Qed.

Lemma singleton_subset : forall v L, {{v}} << L -> v \in L.
  auto*.
Qed.

Lemma eq_subset : forall L1 L2, L1 = L2 -> L1 << L2.
Proof.
  unfold S.Subset; intros. rewrite* <- H.
Qed.

Lemma incl_subset_dom : forall (A:Set) (E1 E2:env A),
  incl E1 E2 -> dom E1 << dom E2.
Proof.
  intros; intros x Hx.
  case_eq (get x E1); intros.
    use (H _ (binds_in H0)).
    apply* in_dom.
  use (get_none_notin _ H0).
Qed.
