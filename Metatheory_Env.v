(***************************************************************************
* Generic Environments for Programming Language Metatheory                 *
* Brian Aydemir & Arthur Charguéraud, July 2007, Coq v8.1                  *
***************************************************************************)

Set Implicit Arguments.
Require Import Lib_Tactic List Decidable Metatheory_Var Metatheory_Fresh.

(* ********************************************************************** *)
(** * Definitions of Environments *)

Declare Scope env_scope.

Module Env.

(* ********************************************************************** *)
(** ** Structure and Basic Operations on Environments *)

Section Definitions.

Variable A : Set.
Implicit Types x : var.
Implicit Types a : A.

(** Environments is represented as an associative list. *)

Definition env := list (var * A).

(** Empty environment. *)

Definition empty : env := nil.

(** An environment containing only one binding mapping x to a. *)

Definition single x a := (x,a) :: nil.

(** Concatenation of environments E and F. *)

Definition concat (E F : env) := F ++ E.

(** Comutes the domain of the environment, i.e. the set of vars mapped. *)

Fixpoint dom (E : env) : vars :=
  match E with
  | nil => {}
  | (x, _) :: E' => {{x}} \u (dom E')
  end.

(** [map] applies a function to all the values mapped by the environment. *)

Fixpoint map (f : A -> A) (E : env) {struct E} : env :=
  match E with
  | nil => nil
  | (x, V) :: E' => (x, f V) :: map f E'
  end.

(** [get] locates a binding in an environment. *)

Fixpoint get (x : var) (E : env) {struct E} : option A :=
  match E with
  | nil => None
  | (y,a) :: E' => if eq_var_dec x y then Some a else get x E'
  end.

End Definitions.


(* ********************************************************************** *)
(** ** Notations *)

Arguments empty [A].

(** [x ~ a] is the notation for a singleton environment mapping x to a. *)

Notation "x ~ a" := (single x a)
  (at level 27, left associativity) : env_scope.

(** [E & F] is the notation for concatenation of E and F. *)

Notation "E & F" := (concat E F) 
  (at level 28, left associativity) : env_scope.

(** [x # E] to be read x fresh from E captures the fact that 
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Bind Scope env_scope with env.
Local Open Scope env_scope.


(* ********************************************************************** *)
(** ** Relations on environemnts *)

Section Relations.

Variable A : Set.

(** An environment is well-formed iff it contains no duplicate 
  bindings. *)

Inductive ok : env A -> Prop :=
  | ok_empty :
      ok empty
  | ok_push : forall E x a,
      ok E -> x # E -> ok (E & x ~ a).

(** An environment contains a binding from x to a iff the most recent
  binding on x is mapped to a *)

Definition binds x a (E : env A) := 
  get x E = Some a.

(** Proposition capturing the idea that a proposition P holds on all 
  values containted in the environment.
  Use In rather than binds for compatibility with fv_in. *)

Definition env_prop (P : A -> Prop) (E : env A) := 
  forall x a, In (x,a) E  -> P a.

(** Inclusion of an environment in another one. *)

Definition extends (E E' : env A) :=
  forall x a, binds x a E -> binds x a E'.

End Relations.


(* ********************************************************************** *)
(** * Properties of Environemnts *)

Hint Constructors ok : core.

Local Open Scope env_scope.


(* ********************************************************************** *)
(** ** Properties of Operations *)

Section OpProperties.
Variable A : Set.
Implicit Types E F : env A.
Implicit Types a b : A.

(** Concatenation with an empty environment is identity. *)

Lemma concat_empty : forall E,
  E & empty = E.
Proof. 
  auto.
Qed.

(** Concatenation is associative. *)

Lemma concat_assoc : forall E F G,
  (E & F) & G = E & (F & G).
Proof.
  induction G; simpl; congruence.
Qed.

(** Map commutes with substitution. *)

Lemma map_concat : forall f E F,
  map f (E & F) = (map f E) & (map f F).
Proof.
  induction F as [|(x,a)]; simpl; congruence.
Qed.

(** Interaction of associativity and map. *)

Lemma concat_assoc_map_push : forall f E F y V,
  (E & map f F) & y ~ (f V) = E & (map f (F & y ~ V)).
Proof.
  auto.
Qed.

(** Inversion results. *)

Lemma eq_empty_inv : forall x a E F,
  empty = E & x ~ a & F -> False.
Proof.
  induction F as [|(y,b)]; simpl; discriminate. 
Qed.

Lemma eq_push_inv : forall E x a E' x' a',
  E & x ~ a = E' & x' ~ a' -> E = E' /\ x = x' /\ a = a'.
Proof.
  simpl. intros. inversions* H.  
Qed.

(** Domain of an empty environment. *)

Lemma dom_empty :
  dom (A:=A) empty = {}.
Proof.
  auto.
Qed.

(** Domain of a singleton environment. *)

Lemma dom_single : forall x a,
  dom (x ~ a) = {{x}}.
Proof.
  simpl. intros. apply union_empty_r.
Qed.

(** Domain of a push is the head variable union the domain of the tail. *)

Lemma dom_push : forall x a E,
  dom (E & x ~ a) = {{x}} \u dom E.
Proof.
  auto.
Qed.

(** Domain of a cons is the head variable union the domain of the tail. *)

Lemma dom_cons : forall x a E,
  dom ((x,a) :: E) = {{x}} \u dom E.
Proof.
  auto.
Qed.

(** Domain of a concatenation is the union of the domains. *)

Lemma dom_concat : forall E F,
  dom (E & F) = dom E \u dom F.
Proof.
  induction F as [|(x,a)]; simpl.
  symmetry. apply union_empty_r.
  rewrite IHF. apply union_comm_assoc.
Qed.

(** Map preserves the domain. *)

Lemma dom_map : forall f E,
  dom (map f E) = dom E.
Proof.
  induction E as [|(x,a)]; simpl; congruence.
Qed.

End OpProperties.

Arguments eq_empty_inv [A x a E F].
Arguments eq_push_inv [A E x a E' x' a'].

(** Simplification tactics *)

Hint Rewrite 
  concat_empty 
  map_concat
  dom_empty dom_single dom_push dom_cons dom_concat dom_map : rew_env.
  
Hint Rewrite <- concat_assoc : rew_env.

Tactic Notation "simpl_env" :=
  autorewrite with rew_env in *.

Hint Extern 1 (_ # _) => simpl_env; notin_solve : core.

(** The [env_fix] tactic is used to convert environments
  from [(x,a)::E] to [E & x ~ a]. *)

(* Duplication in first two cases is to work around a Coq bug
   of the change tactic *)

Ltac env_fix_core :=
  let go := try env_fix_core in
  match goal with 
  | H: context [(?x,?a)::?E] |- _ =>
     (   (progress (change ((x,a)::E) with (E & x ~ a) in H))
      || (progress (unsimpl (E & x ~ a) in H))   ); go
  | |- context [(?x,?a)::?E] =>
    (   (progress (change ((x,a)::E) with (E & x ~ a)))
      || (progress (unsimpl (E & x ~ a)))  ); go
  |  H: context [@nil ((var * ?A)%type)] |- _ =>
      progress (change (@nil ((var * A)%type)) with (@empty A) in H); go
  | |- context [@nil ((var * ?A)%type)] => 
     progress (change (@nil ((var * A)%type)) with (@empty A)); go
  end.

Ltac env_fix := try env_fix_core.


(* ********************************************************************** *)
(** ** Properties of Well-formedness and Freshness *)

Section OkProperties.
Variable A : Set.
Implicit Types E F : env A.
Implicit Types a b : A.
Hint Constructors ok : core.

(** Inversion for ok on concat *)

Lemma ok_concat_inv : forall E F,
  ok (E & F) -> ok E /\ ok F.
Proof.
  induction F as [|(x,a)]; simpl; env_fix; intros Ok.
  auto*.
  inversions Ok. split. auto*. apply* ok_push. 
Qed.
  
(** Removing bindings preserves ok *)

Lemma ok_remove : forall F E G,
  ok (E & F & G) -> ok (E & G).
Proof.
  induction G as [|(y,a)]; simpl; env_fix; intros Ok.
    induction F as [|(y,a)]; simpl.
      auto.
      inversions* Ok.
    inversions* Ok. 
Qed.

(** Mapping values preserves ok *)

Lemma ok_map : forall E F (f : A -> A),
  ok (E & F) -> ok (E & map f F).
intros. induction F as [|(y,a)]; simpl; env_fix.
auto.
rewrite <- concat_assoc in H. inversions* H.
Qed.

(** A binding in the middle of an environment has a var fresh
  from all the bindings before it *)

Lemma fresh_mid : forall E F x a,
  ok (E & x ~ a & F) -> x # E.
Proof.
  induction F; simpl; introv Ok; inversions Ok; env_fix.
    auto.
    inversions H1; env_fix.
     contradictions. fold (@empty A) in H0. apply* eq_empty_inv.
     simpls*.
Qed.

End OkProperties.

(** Automation *)

Hint Resolve fresh_mid ok_map : core.

(* Hint Extern 1 (ok (?E & ?G)) =>
  match goal with H: context [E & ?F & G] |- _ =>
    apply (@ok_remove _ F) end. *)


(* ********************************************************************** *)
(** ** Properties of the binds relation *)

Section BindsProperties.
Variable A : Set.
Implicit Types E F : env A.
Implicit Types a b : A.

Hint Extern 1 (_ \notin _) => notin_solve : core.

(** Binds at head *)

Lemma binds_head : forall x a E,
  binds x a (E & x ~ a).
Proof.
  intros. unfold binds. simpl. case_var*.
Qed.

(** Binds in tail *)

Lemma binds_tail : forall x y a b E,
  x <> y -> binds x a E -> binds x a (E & y ~ b).
Proof.
  intros. unfold binds. simpl. case_var*.
Qed.

(** Binds is functional *)

Lemma binds_func : forall x a b E,
  binds x a E -> binds x b E -> a = b.
Proof.
  unfold binds. introv B1 B2.
  poses H (trans_eq (sym_eq B1) B2). 
  inversion* H.
Qed.

(** No binding in an empty environment *)

Lemma binds_empty : forall x a,
  binds x a empty -> False.
Proof.
  introv H. inversions H.
Qed.

(** No binding on x if x is fresh from the environment *)

Lemma binds_fresh : forall x a E,
  binds x a E -> x # E -> False.
Proof.
  unfold binds. induction E as [|(y,b)]; simpl; intros Has Fresh.
  contradictions.
  case_var*. notin_contradiction.
Qed.

(** Binding on x preserved by concatenation if x is fresh 
  for the extension *)

Lemma binds_concat_fresh : forall x a E F,
  binds x a E -> x # F -> binds x a (E & F).
Proof.
  unfold binds. induction F as [|(y,b)]; simpl; intros.
  auto. case_var*. notin_contradiction.
Qed.

(** Binding on x preserved by concatenation if the result 
  of the concatenation is a well-formed environment *)

Lemma binds_concat_ok : forall x a E F,
  binds x a E -> ok (E & F) -> binds x a (E & F).
Proof.
  unfolds binds. induction F as [|(y,b)]; simpl; intros Map Ok.
  auto.
  inversions Ok. case_var. 
    contradictions. apply* (@binds_fresh y a E). 
    auto.
Qed.

(** Bindings preserved by pre-catenation *)

Lemma binds_prepend : forall x a E F,
  binds x a F -> binds x a (E & F).
Proof.
  unfold binds. induction F as [|(y,b)]; simpl; intros Map.
  contradictions. case_var*.
Qed.

(** Case analysis on the belonging of a binding to a concatenation *)

Lemma binds_concat_inv : forall x a E F,
  binds x a (E & F) -> (x # F /\ binds x a E) \/ (binds x a F).
Proof.
  unfold binds. induction F as [|(y,b)]; simpl; intros Map.
  left*. 
  case_var.
    right*.
    destruct (IHF Map) as [[Fr Map2] | Map2]. left*. right*.
Qed.

(** Interaction of binds and map *)

Lemma binds_map : forall x a f E,
  binds x a E -> binds x (f a) (map f E).
Proof.
  unfold binds. induction E as [|(y,b)]; simpl; intros Map.
  contradictions. case_var*. inversions* Map.
Qed.

(** Retreive the binding on x from an environment [E & (x~a) & F] *)

Lemma binds_mid : forall x a E F,
  ok (E & x ~ a & F) -> binds x a (E & x ~ a & F).
Proof.
  unfold binds. induction F as [|(y,b)]; simpl; intros Ok.
  case_var*.
  inversions Ok. case_var.
    simpl_env. notin_contradiction.
    auto.
Qed.

(** The binding on x in the environment [E & (x~a) & F] can only
   be bound to a if that environment is well-formed *)

Lemma binds_mid_eq : forall z a b E F,
  binds z a (E & z ~ b & F) -> ok (E & z ~ b & F) -> a = b.
Proof.
  unfold binds. induction F as [|(y,c)]; simpl; intros Map Ok.
  case_var*. inversions* Map.
  inversions Ok. case_var.
    inversions Ok. simpl_env. notin_contradiction.
    auto.
Qed.

(** Inversion on a binding in an atomic environment *)

Lemma binds_single_inv : forall x y a b,
  binds x a (y ~ b) -> x = y /\ a = b.
Proof.
  unfold binds. simpl. intros. case_var.
   inversions* H.
   contradictions.
Qed.

(** Interaction between binds and the insertion of bindings.
  In theory we don't need this lemma since it would suffice
  to use the binds_cases tactics, but since weakening is a
  very common operation we provide a lemma for it. *)

Lemma binds_weaken : forall x a E F G,
  binds x a (E & G) -> ok (E & F & G) ->
  binds x a (E & F & G).
Proof. 
  unfold binds. induction G as [|(y,b)]; simpl; intros Map Ok. 
  apply* binds_concat_ok.
  inversions Ok. case_var*.
Qed.

(* Whether bindings are or not in the context is decidable *)

Lemma binds_dec : forall E x a,
  (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
  decidable (binds x a E).
Proof.
  introv Dec. remember (get x E) as B. symmetry in HeqB.
  unfold binds. destruct B as [a'|].
  destruct (Dec a a'). subst. 
    left*.
    right*. intros H. congruence.
  right*. intros H. congruence.
Qed.

End BindsProperties.

Arguments binds_concat_inv [A x a E F].

Hint Resolve binds_head binds_tail : core.


(* ********************************************************************** *)
(** ** Properties of environment inclusion *)

Section ExtendsProperties.
Variable A : Set.
Implicit Types E F : env A.

Lemma extends_self : forall E,
  extends E E.
Proof.
  introz. auto. 
Qed.

Lemma extends_push : forall E x a, 
  x # E -> extends E (E & x ~ a).
Proof.
  introz. apply* binds_tail.
  destruct (x0 == x).
    subst. contradictions. apply* binds_fresh.
    auto.
Qed.

Lemma binds_inj : forall E x a b,
  binds x a E -> binds x b E -> a = b.
Proof.
  unfold binds. intros. congruence.
Qed.

Lemma extends_binds : forall E x a,
  binds x a E -> extends E (E & x ~ a).
Proof.
  introz. unfolds binds. simpl. case_var. congruence. auto.
Qed.

End ExtendsProperties.

Hint Resolve extends_self extends_push extends_binds : core.


(* ********************************************************************** *)
(** ** Iteration of pushing bindings in the environment *)

Section IterPush.
Variable A : Set.
Implicit Types E F : env A.

Definition iter_push (xs : list var) (vs : list A) := 
  rev (combine xs vs).

Lemma iter_push_nil : forall xs,
  iter_push xs nil = nil.
Proof.
  induction xs; simpl*. 
Qed.

Lemma iter_push_cons : forall x (v : A) xs vs,
  iter_push (x::xs) (v::vs) = (x ~ v) & (iter_push xs vs).
Proof.
  auto*.
Qed.

Lemma ok_concat_iter_push : forall xs E (Us : list A),
  ok E ->
  fresh (dom E) (length xs) xs -> 
  ok (E & iter_push xs Us).
Proof.
  induction xs; simpl; intros. auto.
  destruct H0. destruct Us; simpls. auto.
  rewrite iter_push_cons. rewrite* <- concat_assoc.
Qed.  

End IterPush.

Hint Resolve ok_concat_iter_push : core.

Section Fv_in.

(* ********************************************************************** *)
(** ** Gathering free variables of the values contained in an
  environment *)

Variables (A : Set) (fv : A -> vars).

(** Computing free variables contained in an environment. *)

Fixpoint fv_in (E : env A) : vars :=
  match E with
  | nil => {}
  | (x,a)::E' => fv a \u fv_in E'
  end.

(** Specification of the above function in terms of [bind]. *)

Lemma fv_in_spec : forall E, env_prop (fun a => fv a << fv_in E) E.
Proof.
  induction E; intro; simpl; intros. elim H.
  destruct H; intro; intros.
    subst. auto with sets.
  destruct a.
  puts (IHE _ _ H).
  auto with sets.
Qed.

End Fv_in.

(* ********************************************************************** *)
(** ** Tactics *)

Opaque binds.

(** [binds_get H as EQ] produces from an hypothesis [H] of
  the form [binds x a (E & x ~ b & F)] the equality [EQ: a = b]. *)

Tactic Notation "binds_get" constr(H) "as" ident(EQ) :=
  match type of H with binds ?z ?a (?E & ?x ~ ?b & ?F) =>
    let K := fresh "K" in assert (K : ok (E & x ~ b & F)); 
    [ auto | poses EQ (@binds_mid_eq _ z a b E F H K); clear K ] end.

(** [binds_get H] expects an hypothesis [H] of the form 
  [binds x a (E & x ~ b & F)] and substitute [a] for [b] in the goal. *)

Tactic Notation "binds_get" constr(H) :=
  let EQ := fresh in binds_get H as EQ;
  try match type of EQ with 
  | ?f _ = ?f _ => inversions EQ; clear EQ
  | ?x = ?y => subst x end.

(** [binds_single H] derives from an hypothesis [H] of the form 
  [binds x a (y ~ b)] the equalities [x = y] and [a = b], then
  it substitutes [x] for [y] in the goal or deduce a contradiction
  if [x <> y] can be found in the context. *)

Ltac binds_single H :=
  match type of H with binds ?x ?a (?y ~ ?b) =>
    destruct (binds_single_inv H); 
    try discriminate; try subst y; 
    try match goal with N: ?x <> ?x |- _ =>
      contradictions; apply N; reflexivity end end.

(** [binds_case H as B1 B2] derives from an hypothesis [H] of the form 
  [binds x a (E & F)] two subcases: [B1: binds x a E] (with a freshness
  condition [x # F]) and [B2: binds x a F]. *)

Tactic Notation "binds_case" constr(H) "as" ident(B1) ident(B2) :=
   let Fr := fresh "Fr" in 
   destruct (binds_concat_inv H) as [[Fr B1] | B2].

(** [binds_case H] makes a case analysis on an hypothesis [H] of the form 
  [binds x a E] where E can be constructed using concatenation and
  singletons. It calls [binds_single] when reaching a singleton. *)

Ltac binds_cases H :=
  let go B := clear H; 
    first [ binds_single B | binds_cases B | idtac ] in
  let B1 := fresh "B" in let B2 := fresh "B" in
  binds_case H as B1 B2; simpl_env; [ go B1 | go B2 ].


(** Automation *)

Hint Resolve 
  binds_concat_fresh binds_concat_ok 
  binds_prepend binds_map : core.


(* ********************************************************************** *)
(** ** Other tactics (syntactical sugar for tactics) *)

(** Tactic to apply an induction hypothesis modulo a rewrite of 
  the associativity of the environment necessary to handle the
  inductive rules dealing with binders. [apply_ih_bind] is in
  fact just a syntactical sugar for [do_rew concat_assoc (eapply H)] 
  which in turns stands for 
  [rewrite concat_assoc; eapply H; rewrite <- concat_assoc]. *)

Tactic Notation "apply_ih_bind" constr(H) :=
  do_rew concat_assoc (eapply H).

Tactic Notation "apply_ih_bind" "*" constr(H) :=
  do_rew* concat_assoc (eapply H).

(** Similar as the above, except in the case where there
  is also a map function, so we need to use [concat_assoc_map_push]
  for rewriting. *)

Tactic Notation "apply_ih_map_bind" constr(H) :=
  do_rew concat_assoc_map_push (eapply H).

Tactic Notation "apply_ih_map_bind" "*" constr(H) :=
  do_rew* concat_assoc_map_push (eapply H).

(** [apply_empty] applies a lemma of the form "forall E:env, P E"
    in the particular case where E is empty. The tricky step is
    the simplification of "P empty" before the "apply" tactic is
    called, and this is necessary for Coq to recognize that the
    lemma indeed applies. *)

Tactic Notation "apply_empty" constr(lemma) :=
  let H := fresh in poses H (@lemma empty);
  simpl in H; eapply H; env_fix; clear H.

Tactic Notation "apply_empty" "*" constr(lemma) :=
  apply_empty lemma; auto*.


End Env.
