(***************************************************************************
* Extra lemmas  and tactics concerning lists, sets, and metatheory         *
* Jacques Garrigue, june 2009, Coq 8.2                                     *
***************************************************************************)

Set Implicit Arguments.
Require Import List Lib_Tactic Lib_FinSet.
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

Definition list_snd (A B:Set) := List.map (@snd A B).

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

Lemma list_forall_apply : forall (Q:A->Prop) l,
  list_forall (fun x => P x -> Q x) l ->
  list_forall P l -> list_forall Q l.
Proof.
  intros; induction* H.
  inversion* H0.
Qed.

Variable (B:Set)(Q:B -> Prop).

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


Section For_all2.
Variables A B : Set.

Fixpoint For_all2 (P:A->B->Prop) (l1:list A) (l2:list B) {struct l1}
  : Prop :=
  match (l1, l2) with
  | (nil,nil)   => True
  | (a::l1',b::l2') => P a b /\ For_all2 P l1' l2'
  | _ => False
  end.

Variable P : A -> B -> Prop.

Lemma For_all2_map: forall (P' : A -> B -> Prop) f g l1 l2,
  (forall x y, P x y -> P' (f x) (g y)) ->
  For_all2 P l1 l2 ->
  For_all2 P' (List.map f l1) (List.map g l2).
Proof.
  induction l1; introv; elim l2; simpls; auto*.
Qed.

Lemma For_all2_In: forall x l1 l2,
  In x l1 -> For_all2 P l1 l2 -> exists y:B, In y l2 /\ P x y.
Proof.
  induction l1; destruct l2; intros; try contradiction.
  simpl in *; destruct H; destruct H0.
    exists b; intuition.
    rewrite* <- H.
  destruct (IHl1 l2 H H1).
  exists* x0.
Qed.

Lemma For_all2_get : forall Xs Ys Zs x y z,
  For_all2 P Ys Zs ->
  binds x y (combine Xs Ys) ->
  binds x z (combine Xs Zs) ->
  P y z.
Proof.
  induction Xs; destruct Ys; destruct Zs; simpl; intros; auto*;
    try discriminate.
  unfold binds in H0, H1; simpl in H0, H1.
  destruct (eq_var_dec x a).
  generalize (proj1 H). inversion H0; inversion* H1.
  apply* (IHXs _ _ _ _ _ (proj2 H) H0 H1).
Qed.
End For_all2.

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

  Lemma binds_in : forall x (a:A) E,
    binds x a E -> In (x, a) E.
  Proof.
    unfold binds; induction E; intros. elim (binds_empty H).
    destruct a0; simpl in *.
    destruct* (x == v). inversions* H.
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

  Lemma binds_combine : forall x (c:A) Ys Ks,
    binds x c (combine Ys Ks) -> In c Ks.
  Proof.
    induction Ys; destruct Ks; simpl; intros; try (elim (binds_empty H)).
    unfold binds in H. simpl in H.
    destruct* (eq_var_dec x a). inversion* H.
  Qed.

  Section Map.
    Variable f : A -> A.

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

  Lemma list_forall_env_prop : forall Xs Vs,
    list_forall P Vs -> env_prop P (combine Xs Vs).
  Proof.
    intros; gen Xs.
    induction H; destruct Xs; intro; simpl; intros; try contradiction.
    destruct H1.
      inversions* H1.
    apply (IHlist_forall _ _ _ H1).
Qed.

End Env.

Hint Resolve in_ok_binds env_prop_single env_prop_concat.
Hint Resolve list_forall_env_prop in_or_concat.
Hint Immediate binds_in env_prop_concat_inv1 env_prop_concat_inv2.

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

Lemma remove_4 : forall y x L, y \in S.remove x L -> ~ E.eq x y.
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
  | H: x \in _ \u _ |- _ =>
    destruct (S.union_1 H); clear H; union_solve x
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
  end.

Ltac sets_solve :=
  match goal with
  | |- ?x \in _ => try union_solve x; try find_in_solve x
  | |- _ << _ =>
    let y := fresh "y" in let Hy := fresh "Hy" in
    intros y Hy; sets_solve
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

Hint Extern 1 (_ \in _) => solve [sets_solve].
Hint Extern 1 (_ << _) => solve [sets_solve].

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
  simpl in H; destruct H.
    simpl; rewrite* H. auto with sets.
  simpl. eauto with sets.
Qed.


(** Disjointness *)

Definition disjoint s1 s2 :=
  forall x, x \notin s1 \/ x \notin s2.

Lemma disjoint_union : forall A B C,
  disjoint A C -> disjoint B C -> disjoint (A \u B) C.
Proof.
  intros. intro x; destruct* (H x); destruct* (H0 x).
Qed.

Lemma disjoint_comm : forall A B,
  disjoint A B -> disjoint B A.
Proof.
  intros. intro x; destruct* (H x).
Qed.

Lemma ok_disjoint : forall (A:Set) (E F:Env.env A),
  ok (E & F) -> disjoint (dom E) (dom F).
Proof.
  induction F; simpls; intros.
    intro; right*.
  destruct a; simpl.
  inversion H.
  clear x a0 H0 H1 H3.
  intro y.
  destruct* (eq_var_dec y v).
    rewrite* e.
  destruct* (IHF H2 y).
Qed.

Lemma fresh_disjoint : forall n Xs L,
  fresh L n Xs -> disjoint L (mkset Xs).
Proof.
  induction n; destruct Xs; simpl; intros; auto*.
    intro; auto.
  destruct H.
  intro x.
  assert (fresh L n Xs). auto*.
  destruct* (IHn Xs L H1 x).
  destruct* (eq_var_dec x v).
Qed.

Lemma notin_disjoint : forall x L, x \notin L -> disjoint {{x}} L.
Proof.
  intros; intro v. destruct (x == v); try subst; auto.
Qed.

Hint Resolve notin_disjoint.

Lemma notin_disjoint_r : forall x L, x \notin L -> disjoint L {{x}}.
Proof.
  intros; apply* disjoint_comm.
Qed.

Hint Resolve notin_disjoint_r.

Lemma disjoint_notin : forall s v,
  disjoint s {{v}} -> v \notin s.
Proof.
  intros.
  destruct* (H v).
Qed.

Hint Immediate disjoint_notin.

(** Result on fresh *)

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

(** More properties of get *)

Lemma get_notin_dom : forall A x (S : Env.env A),
  x # S -> get x S = None.
Proof.
  induction S; intros. auto.
  destruct a; simpl in *.
  destruct (eq_var_dec x v).
    rewrite e in H. elim H. auto with sets.
  auto with sets.
Qed.

Lemma fresh_rev : forall x L n xs,
  fresh L n xs -> x \in L -> ~In x xs.
Proof.
  induction n; destruct xs; simpl; intros; auto.
  intros [e | i].
    elim (proj1 H); rewrite e; auto.
  elim (IHn xs); auto*.
Qed.

Lemma in_dom_combine : forall (A:Set) v Xs (Us:list A),
  v \in dom (combine Xs Us) -> In v Xs.
Proof.
  induction Xs; destruct Us; simpl; auto; intros.
    elim (in_empty H).
  destruct (proj1 (in_union _ _ _) H).
    rewrite* (proj1 (in_singleton _ _) H0).
  auto*.
Qed.

Lemma dom_combine : forall (A:Set) Xs (As:list A),
  length Xs = length As -> dom (combine Xs As) = mkset Xs.
Proof.
  induction Xs; destruct As; simpl; intros; try discriminate.
    auto.
  rewrite* IHXs.
Qed.

Lemma get_none_notin : forall (A : Set) x (S : Env.env A),
  get x S = None -> x # S.
Proof.
  induction S; intro; simpl; auto*.
  destruct* a.
  simpl in H. destruct* (eq_var_dec x v).
    discriminate.
  intro. destruct* (proj1 (in_union _ _ _) H0).
  elim n; apply (proj1 (in_singleton _ _) H1).
Qed.

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

Lemma get_none_notin_list : forall (A:Set) x (a:A) E,
  get x E = None -> ~In (x,a) E.
Proof.
  induction E; simpl; intros. auto.
  destruct a0. destruct (x == v). discriminate.
  intro. destruct H0. inversions H0. elim n; auto.
  intuition.
Qed.

Lemma ok_map0 : forall (A:Set) (f:A->A) E,
  ok E -> ok (map f E).
Proof.
  intros.
  rewrite (app_nil_end (map f E)).
  fold (nil & map f E).
  apply ok_map.
  unfold concat; rewrite* <- (app_nil_end E).
Qed.

Hint Resolve ok_map0.

Hint Unfold extends.

Lemma notin_remove_self : forall v L, v \notin S.remove v L.
Proof.
  intros. apply S.remove_1. reflexivity.
Qed.

Lemma notin_remove : forall x v L,
  v \notin L -> v \notin S.remove x L.
Proof.
  intros; intro.
  elim H; apply* S.remove_3.
Qed.

Hint Resolve notin_remove_self notin_remove.

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
  intros; apply eq_ext; intros; split; intro.
    use (S.remove_3 H).
    elim (S.remove_1 (S.singleton_1 H0) H).
  elim (in_empty H).
Qed.

Lemma fv_in_subset_inv : forall (A:Set) fv F E,
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

Lemma incl_fv_in_subset : forall (A:Set) fv (E F:env A),
  incl E F -> fv_in fv E << fv_in fv F.
Proof.
  induction E; simpl; intros. auto.
  destruct a.
  assert (In (v,a) F) by auto.
  use (fv_in_spec fv _ _ _ H0).
  simpl in *.
  forward~ (IHE F) as G.
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
