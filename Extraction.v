(***************************************************************************
* Code extraction for structural polymorphism                              *
* Jacques Garrigue, October 2007 - Jun 2009                                *
***************************************************************************)

Set Implicit Arguments.

Require Import List Arith Metatheory ML_SP_Domain.
Require Omega.
Import Infer2.
Import MyEval2.
Import Sound3.
Import Infer.Unify.
Import MyEval.
Import Rename.Sound.Infra.
Import Defs.
Import Rename2.Sound2.JudgInfra.
Import Judge.
Import Infer2.

Definition t :=
  trm_app
    (trm_cst (Const.matches (NoDup_nodup (5 :: nil))))
    (trm_abs (trm_bvar O)).

(* This doesn't seem to work inside Coq (some things don't get evaluated) *)
(* Eval compute in typinf' t. *)

Definition decidable (A : Set) (P : A -> Prop) :=
  forall x, {P x} + {~P x}.

Definition ok_dec : decidable (@ok sch).
  intro E; induction E; env_fix.
    auto.
  destruct a; env_fix.
  destruct IHE.
    case_eq (get v E); intros.
      right*; intro.
      elim (binds_fresh H).
      inversions* H0.
    auto.
  right*.
Defined.

Inductive type_n (n:nat) : typ -> Prop :=
  | typn_bvar : forall m, m < n -> type_n n (typ_bvar m)
  | typn_fvar : forall x, type_n n (typ_fvar x)
  | typn_arrow : forall T1 T2,
      type_n n T1 -> type_n n T2 -> type_n n (typ_arrow T1 T2).
Hint Constructors type_n : core.

Definition type_n_dec : forall n , decidable (type_n n).
  introv T; induction* T.
    destruct* (le_lt_dec n n0).
    right*; intro. inversions H. Omega.omega.
  destruct IHT1.
    destruct* IHT2.
    right*; intro. inversions* H.
  right*; intro. inversions* H.
Defined.

Lemma type_n_typ_body : forall T Xs,
  (type_n (length Xs) T <-> type (typ_open_vars T Xs)).
Proof.
  unfold typ_open_vars.
  intros; split.
    induction 1; simpl*.
  induction T; simpl*; intros.
    destruct* (le_lt_dec (length Xs) n).
    unfold typ_fvars in H.
    rewrite <- (map_length typ_fvar) in l.
    rewrite (nth_overflow _ _ l) in H. inversion H.
  inversions* H.
Qed.

Definition list_forall_dec : forall (A:Set) (P:A->Prop),
  decidable P -> decidable (list_forall P).
  introv HP l; induction l.
    left*.
  destruct* (HP a).
  right*; intro. inversion* H.
Defined.
  
Definition scheme_dec : decidable scheme.
  intros [T Ks].
  unfold scheme, typ_body; simpl.
  set (n := length Ks). clearbody n.
  destruct (type_n_dec n T).
    puts (list_forall_dec (type_n_dec n)).
    unfold All_kind_types.
    puts (list_forall_dec (fun k => H (kind_types k))).
    destruct (H0 Ks).
      left*; intuition; subst. apply* (proj1 (type_n_typ_body T Xs)).
      apply* list_forall_imp; intros. simpl in H1.
      apply* list_forall_imp; intros.
      apply* (proj1 (type_n_typ_body x0 Xs)).
    right*; intro.
    elim n0; clear -H1.
    destruct (var_freshes {} n).
    destruct* (H1 x); clear H1.
    apply* list_forall_imp; intros. simpl in H1.
    refine (list_forall_imp _ _ H1); intros.
    rewrite (fresh_length _ _ _ f).
    refine (proj2 (type_n_typ_body x1 x) H2); auto*.
  right*; intro.
  elim n0; clear -H.
  destruct (var_freshes {} n).
  destruct* (H x); clear H.
  rewrite (fresh_length _ _ _ f).
  refine (proj2 (type_n_typ_body T x) H0); auto*.
Defined.

Definition env_prop_dec : forall (A:Set) (P:A->Prop),
  decidable P -> decidable (env_prop P).
  introv HP E; induction E.
    left*; intro; intros. elim H.
  destruct a; env_fix.
  destruct* (HP a).
Defined.

Lemma env_weaker_refl : forall E, Rename2.env_weaker E E.
Proof.
  introv x; intros.
  exists (@nil kind).
  rewrite* <- app_nil_end.
Qed.

Definition typinf1 : forall E t,
  {p:kenv*typ | let (K,T) := p in K; E |Gc|= t ~: T}+
  ({env_fv E <> {}}+{forall K T, ~ K;E |Gc|= t ~: T}).
  intros.
  case_eq (S.is_empty (env_fv E)); intros.
    assert (Hempty: env_fv E = {}).
      puts (S.is_empty_2 H).
      apply eq_ext; split2*. intro Ha; elim (H0 _ Ha).
    clear H; destruct (ok_dec E).
      destruct (env_prop_dec scheme_dec E).
        case_eq (typinf' E t0); intros.
          left*; exists p. destruct p.
          apply* typinf_sound'.
        right*; right*; introv Typ.
        destruct* (Rename2.typing_remove_gc Typ {} (@env_weaker_refl E))
          as [K' [HK' Typ']].
        destruct* (typinf_principal' Hempty Typ') as [K0 [T' [TI]]].
        rewrite H in TI; discriminate.
      right*.
    right*.
  right*; left*.
  intro. rewrite H0 in H.
  puts (S.is_empty_1 (S.empty_1)).
  rewrite H1 in H; discriminate.
Defined.

Definition eval1 fenv t h := eval fenv h nil nil t nil.

(* Export and try to do this in ocaml *)
Require Import Extraction.
(* Extraction Language Haskell. *)
Set Extraction AccessOpaque.
Extraction "typinf" typinf1 eval1.
