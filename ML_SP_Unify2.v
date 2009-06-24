(***************************************************************************
* Principality of unification for mini-ML with structural polymorphism     *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import Arith List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure Cardinal.
Require Import ML_SP_Soundness ML_SP_Eval.

Set Implicit Arguments.

Module MkUnify(Cstr:CstrIntf)(Const:CstIntf).

Module MyEval := MkEval(Cstr)(Const).
Import MyEval.
Import Sound.
Import Infra.
Import Defs.

(* Composition of substitutions *)
Definition compose S1 S2 : subs := S1 & map (typ_subst S1) S2.

(* Inclusion of substitutions. Very handy to use in proofs *)
Definition extends S S0 :=
  forall T, typ_subst S (typ_subst S0 T) = typ_subst S T.

(* Unifiers *)
Definition unifies S K' K pairs :=
  well_subst K K' S /\
  forall T1 T2, In (T1, T2) pairs -> typ_subst S T1 = typ_subst S T2.

(* Subsititions should be in normal form *)
Definition is_subst (S : subs) :=
  env_prop (fun T => disjoint (dom S) (typ_fv T)) S.

Section Moregen.
  (* Here we relate extends with the more usual notional of generality *)

  Definition moregen S0 S :=
    exists S1, forall T, typ_subst S T = typ_subst S1 (typ_subst S0 T).

  (* Extends implies more general *)
  Lemma extends_moregen : forall S S0,
    extends S S0 -> moregen S0 S.
  Proof.
    intros.
    exists* S.
  Qed.

  Lemma typ_subst_idem : forall S T,
    is_subst S -> typ_subst S (typ_subst S T) = typ_subst S T.
  Proof.
    intros.
    induction T; simpl. auto.
      case_eq (get v S); intros.
        rewrite* typ_subst_fresh.
      simpl.
      rewrite* H0.
    simpl; congruence.
  Qed.

  (* For substitutions in normal form, moregeneral implies extends *)
  Lemma moregen_extends : forall S S0,
    moregen S0 S -> is_subst S0 -> extends S S0.
  Proof.
    intros; intro.
    destruct H as [S1 Heq].
    rewrite Heq.
    rewrite* typ_subst_idem.
  Qed.

End Moregen.

Definition is_fvar t :=
  match t with
  | typ_fvar _ => true
  | _ => false
  end.

Inductive Unify :
  subs -> kenv -> list(typ*typ) -> subs -> kenv -> list(typ*typ) -> Prop :=
| Unify_eq   : forall S K t pairs, Unify S K ((t,t)::pairs) S K pairs
| Unify_var  : forall S K x t pairs,
  x \notin typ_fv t ->
  is_fvar t = false ->
  Unify S K ((typ_fvar x,t)::pairs) (compose (x ~ t) S) K pairs
| Unify_vars : forall S K x y pairs,
  x <> y ->
  Unify S K ((typ_fvar x,typ_fvar y)::pairs)
    (compose (x ~ typ_fvar y) S) 
