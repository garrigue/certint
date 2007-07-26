(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Charguéraud, July 2007, Coq v8.1                                  *
***************************************************************************)

Set Implicit Arguments.
Require Import List Metatheory ML_Definitions ML_Infrastructure.


(* helper lemma to beautify *)
Lemma factorize_map : forall Z U xs Us,
   iter_push xs (List.map (Sch 0) (List.map (typ_subst Z U) Us))
 = (map (sch_subst Z U) (iter_push xs (List.map (Sch 0) Us))).
Proof.
  induction xs; simpl; intros.
  auto. destruct Us. auto. simpl.
  do 2 rewrite iter_push_cons.
  rewrite map_concat. f_equal*.
Qed.


(* ********************************************************************** *)
(** Typing schemes for expressions *)

Definition has_scheme_vars L E P t M := forall Xs, 
  fresh L (sch_arity M) Xs ->
  E ! P |= t ~: (M ^ Xs).

Definition has_scheme E P t M := forall Vs,
  types (sch_arity M) Vs -> 
  E ! P |= t ~: (M ^^ Vs).

(* ********************************************************************** *)
(** Type substitution preserves typing of patterns *)

Lemma pat_typing_typ_subst : forall Z U Us p T,
  Us \= p ~: T ->
  List.map (typ_subst Z U) Us \= p ~: typ_subst Z U T.
Proof.
  induction 1; simpl*. rewrite* map_app.
Qed.  

(* ********************************************************************** *)
(** Type substitution preserves typing of expressions *)

Lemma typing_typ_subst : forall F P Z U E t T,
  Z \notin (env_fv E) -> Z \notin (phi_fv P) -> (* factorize *)
  type U -> 
  E & F ! P |= t ~: T -> 
  E & (map (sch_subst Z U) F) ! P |= t ~: (typ_subst Z U T).
Proof.
  introv. intros Fr1 Fr2 WVs Typ. gen_eq (E & F) as G. gen F.
  induction Typ; intros F EQ; subst; simpls typ_subst.
  rewrite~ sch_subst_open. apply* typing_var.
    binds_cases H1.
      apply* binds_concat_fresh.
       rewrite* sch_subst_fresh. use (fv_in_spec sch_fv B).
      auto*.
    rewrite~ sch_subst_arity. apply* typ_subst_type_list.
  apply_fresh* typing_abs. intros y Fr.
   rewrite sch_subst_fold.   
   apply_ih_map_bind* H1.
  apply_fresh* typing_fix. intros f y Fr.
   replace (E & (map (sch_subst Z U) F) &
    f ~ Sch 0 (typ_arrow (typ_subst Z U U0) (typ_subst Z U T)) &
    y ~ Sch 0 (typ_subst Z U U0))
   with (E & map (sch_subst Z U) (F & 
    f ~ Sch 0 (typ_arrow U0 T) &
    y ~ (Sch 0 U0))); [|auto]. 
   apply* H1. 
  apply_fresh* (@typing_let (sch_subst Z U M) (L1 \u {{Z}})).
   simpl. intros Ys Fr. rewrite* <- sch_subst_open_vars.
   intros y Fr. apply_ih_map_bind* H4.
  apply_fresh* (@typing_match (typ_subst Z U T) 
                              (List.map (typ_subst Z U) Us)).
    apply* pat_typing_typ_subst.
    intros xs Fr. 
    rewrite factorize_map. rewrite concat_assoc.
     rewrite <- map_concat. apply* H1. rewrite* <- concat_assoc.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  apply* typing_loc.
   rewrite* typ_subst_fresh. 
   use (fv_in_spec typ_fv H1).
  auto*.
  auto*.
  apply* typing_set.
  apply* typing_raise.
   rewrite* <- (@typ_subst_fresh Z U typ_exn). 
  apply* typing_catch. 
   rewrite* <- (@typ_subst_fresh Z U typ_exn). 
Qed.

(* ********************************************************************** *)
(** Iterated type substitution preserves typing *)

Lemma typing_typ_substs : forall Zs Us E P t T,
  fresh (env_fv E \u phi_fv P) (length Zs) Zs -> 
  types (length Zs) Us ->
  E ! P |= t ~: T -> 
  E ! P |= t ~: (typ_substs Zs Us T).
Proof.
  induction Zs; destruct Us; simpl; introv Fr WU Tt;
   destruct Fr; inversions WU; 
   simpls; try solve [ auto | contradictions* ].
  inversions H2. inversions H1. clear H2 H1.
  apply* IHZs. apply_empty* typing_typ_subst.
Qed.

(* ********************************************************************** *)
(** Type schemes can be instanciated *)

Lemma has_scheme_from_vars : forall L E P t M,
  has_scheme_vars L E P t M ->
  has_scheme E P t M.
Proof.
  intros L E P t [n T] H Vs TV. unfold sch_open. simpls.
  pick_freshes n Xs.
  rewrite (fresh_length _ _ _ Fr) in TV, H.
  rewrite~ (@typ_substs_intro Xs Vs T).
  unfolds has_scheme_vars sch_open_vars. simpls.
  apply* typing_typ_substs.
Qed.

(* ********************************************************************** *)
(** A term that has type T has type scheme "forall(no_var).T" *)

Lemma has_scheme_from_typ : forall E P t T,
  E ! P |= t ~: T -> 
  has_scheme E P t (Sch 0 T).
Proof.
  introz. unfold sch_open. simpls.
  rewrite* <- typ_open_type.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by weakening *)

Lemma typing_weaken : forall G E F P t T,
   (E & G) ! P |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) ! P |= t ~: T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; intros G EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs. intros y Fr. 
   do_rew* concat_assoc (apply* H1).
  apply_fresh* typing_fix. intros f y Fr2.
   do_rew_2* concat_assoc (apply* H1).
  apply_fresh* (@typing_let M L1). intros y Fr.
   do_rew* concat_assoc (apply* H4).
  apply_fresh* (@typing_match T Us). intros xs Fr.
    do_rew* concat_assoc (apply* H1).
    apply* (@ok_iter_push sch (pat_arity p)). simpl_env. auto.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(* ********************************************************************** *)
(** Values are preserved by term substitution *)

Lemma value_fv : forall z u t, 
  value u -> value t -> value ([z ~> u]t).
Proof.
  introv Valu Valt. induction Valt; simpl*.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by term substitution *)

Lemma typing_trm_subst : forall F M E P t T z u, 
  E & z ~ M & F ! P |= t ~: T ->
  has_scheme E P u M -> 
  value u ->
  E & F ! P |= (trm_subst z u t) ~: T.
Proof.
  introv Typt. intros Typu Valu. 
  gen_eq (E & z ~ M & F) as G. gen F.
  induction Typt; intros G EQ; subst; simpl trm_subst.
  case_var.
    binds_get H1. apply_empty* typing_weaken.
    binds_cases H1; apply* typing_var.
  apply_fresh* typing_abs. intros y Fr.
   rewrite* subst_open_vars.
   do_rew concat_assoc (apply* H1).
  apply_fresh* typing_fix. intros f y Fr.
   rewrite* subst_open_vars.
   do_rew_2 concat_assoc (apply* H1).
  apply_fresh* (@typing_let M0 L1); try intros y Fr.
   apply* value_fv. 
   rewrite* subst_open_vars. do_rew concat_assoc (apply* H4).
  apply_fresh* (@typing_match T Us). intros xs Fr.
   rewrite* subst_open_vars.
   do_rew* concat_assoc (apply* H1).
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by iterated term substitution. *)

Lemma typing_trm_substs : forall Us E P xs ts t T,
   length xs = length ts ->
   typings E P ts Us ->
   (E & (iter_push xs (List.map (Sch 0) Us))) ! P |= t ~: T ->
   list_forall value ts ->
   E ! P |= substs xs ts t ~: T.
Proof.
  intros Us E P xs. gen Us E.
  induction xs; simpl; introv Le Typts Typt Val. auto.
  destruct ts; simpls; inversions Le.
  inversions Typts. inversions Val.
  simpl in Typt.
  rewrite iter_push_cons in Typt. 
  rewrite <- concat_assoc in Typt.
  apply* (@IHxs Us0).
  apply* typing_trm_subst.
  apply* has_scheme_from_typ.
Qed.

(* ********************************************************************** *)
(** The result of pattern matching is a list of well-typed terms. *)

Lemma typing_pattern_match : forall p t T E P ts Us,
  Some ts = pat_match p t ->
  E ! P |= t ~: T ->
  Us \= p ~: T ->
  typings E P ts Us.
Proof.
  induction p; introv H1 H2 H0; destruct t; 
   inversion H0; inversion H1; auto; subst; inversions H2; auto*.
  remember (pat_match p1 t1) as K1. 
   remember (pat_match p2 t2) as K2. 
   destruct K1 as [ts1|]; destruct K2 as [ts2|]; try discriminate.
   inversions H9. apply* typings_concat.
Qed.

(* ********************************************************************** *)
(** The result of pattern matching applied to a value is a list of values. *)

Lemma pattern_match_values : forall p t ts,
  Some ts = pat_match p t ->
  value t ->
  list_forall value ts.
Proof.
  induction p; introv EQ Val; 
   destruct t; simpl in EQ; inversion EQ; auto; inversions Val; auto*.
  remember (pat_match p1 t1) as K1. 
   remember (pat_match p2 t2) as K2. 
   destruct K1 as [ts1|]; destruct K2 as [ts2|]; try discriminate.
   inversions EQ. apply* list_forall_concat.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by an extension of store typing. 
    (This result is added to hints because we use it many times. *)

Lemma typing_stability : forall P E P' t T,
  E ! P |= t ~: T ->
  extends P P' -> 
  phi_ok P' ->
  E ! P' |= t ~: T.
Proof.
  introv Typ Ext. induction* Typ.
Qed.

Hint Resolve typing_stability.

(* ********************************************************************** *)
(** Store typing preserved by allocation of a well-typed term. *)

Lemma sto_typing_push : forall P mu l t T,
  P |== mu ->
  empty ! P |= t ~: T ->
  l # mu -> l # P ->
  (P & l ~ T) |== (mu & l ~ t).
Proof.
  unfold sto_typing. introv [PhiOk [StoOk [Dom Ext]]]. split4.
    auto.
    auto.
    intros l0 Fr. simpls. puts (Dom l0). 
      asserts* Frl0 (l0 # P). auto.
    intros l' T' Has. binds_cases Has.
      destruct (Ext _ _ B) as [t' [Hast' Typt']].
       exists* t'. 
      subst. exists* t.
Qed.   

(* ********************************************************************** *)
(** Fails always returns an exception. *)

Lemma fails_to_exception : forall E P t T e,
  fails t e -> 
  E ! P |= t ~: T -> 
  E ! P |= e ~: typ_exn.
Proof.
  introv Fail Typ. induction Typ; inversions* Fail.
  pick_freshes (sch_arity M) Xs. forward~ (H2 Xs).
Qed.

(* ********************************************************************** *)
(** Preservation: typing is preserved by reduction *)

(* A tactic to help us name nicely all the hypotheses *)
Ltac pres H t' mu' :=
  let P' := fresh "P'" in
  let Ext := fresh "Ext" in
  let Typt' := fresh "Typt'" in
  let TypSto' := fresh "TypSto'" in
  destruct~ (H (@refl_equal env empty) t' mu') 
                  as [P' [Ext [Typt' TypSto']]].  

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t' mu'. gen_eq (empty : env) as E.
  induction Typ; intros EQ t' mu' Red TypSto; subst; 
   inversions Red; env_fix.
  exists P. split3~. 
   pick_fresh x. forward~ (H3 x) as K. clear H2 H3 H4.
   rewrite~ (@substs_intro (x::nil)). simpl.
   apply_empty* typing_trm_subst.
   apply* (@has_scheme_from_vars L1).
  exists P. split3~. clear H1 IHTyp1 IHTyp2.
   forward~ (@pat_match_terms _ _ _ H13) as Wts.
   pick_freshes (pat_arity p) xs.
   rewrite~ (@substs_intro xs);
    [| rewrite~ <- (fresh_length _ _ _ Fr)].
   forward~ (H0 xs) as K. 
   rewrite (proj1 Wts) in Fr, Wts.
   apply_empty* (@typing_trm_substs Us). 
     rewrite* (fresh_length _ _ _ Fr).
     apply* typing_pattern_match.
     apply* pattern_match_values.
  exists P. split3~.
  pres IHTyp1 t1' mu'. exists* P'.
  exists P. split3~. 
   inversions Typ1. 
   pick_fresh x. forward~ (H8 x) as K. clear H8 IHTyp1 IHTyp2.
   rewrite~ (@substs_intro (x::nil)). simpl.
   apply_empty* typing_trm_subst.
   apply* has_scheme_from_typ.
  exists P. split3~. 
   inversions Typ1. 
   pick_fresh f. pick_fresh x. forward~ (H8 f x) as K. clear H8.
   rewrite~ (@substs_intro (f::x::nil)).
   apply_empty* (@typing_trm_substs ((typ_arrow S T)::S::nil)).
  exists P. split3~. inversions Typ1. inversions* H4.
  pres IHTyp1 t1' mu'. exists* P'.
  pres IHTyp2 t2' mu'. exists* P'.
  pres IHTyp1 t1' mu'. exists* P'.
  pres IHTyp2 t2' mu'. exists* P'.
  pres IHTyp t1' mu'. exists* P'.
  pres IHTyp t1' mu'. exists* P'.
  exists (P & l ~ T). puts (proj43 TypSto).
   split3~. apply* sto_typing_push. 
  pres IHTyp t1' mu'. exists* P'. 
  exists P. split3~. 
   inversions Typ. 
   destruct~ ((proj44 TypSto) l T) as [t [Hast Typt]].
   rewrite~ (binds_inj H4 Hast).
  pres IHTyp t1' mu'. exists* P'. 
  exists P. inversions Typ1. split3~.
   destruct TypSto as [PhiOk [StoOk [Dom Map]]]. split4~.
    intros. unfold binds. simpl. case_var.
      exists t2. split~. rewrite~ (binds_inj H H7).
      destruct (Map _ _ H) as [t [Has Typ]]. exists* t.  
  pres IHTyp1 t1' mu'. exists* P'.
  pres IHTyp2 t2' mu'. exists* P'.
  pres IHTyp t1' mu'. exists* P'. 
  exists* P.
  exists P. split3~.
    apply* typing_app. apply* fails_to_exception.
  pres IHTyp2 t2' mu'. exists* P'.
Qed.

(* ********************************************************************** *)
(** A value cannot be reduced (needed for the let case of progress). *)

Lemma red_value_false : forall t, value t ->
  forall t' mu mu', (t, mu) --> (t', mu') -> False.
Proof.
  induction 1; introv Red; inversions* Red.
  inversions H5. inversions H5.
Qed.

(* ********************************************************************** *)
(** Progress: typed terms are values or can reduce *)

Hint Constructors fails.

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (empty:env) as E. poses Typ' Typ.
  induction Typ; intros; subst. 
  contradictions.
  or_31*.
  or_31*.
  asserts* K (empty ! P |= (trm_let t1 t2) ~: T2).
   pick_freshes (sch_arity M) Ys.
    forward~ (@H2 Ys) as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
     or_33. exists* (t2 ^^ (t1::nil)) mu.
     or_32. exists* e.
     contradictions. apply* (red_value_false H Red1). 
  destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    or_33. remember (pat_match p t1) as K. destruct K as [ts|].
      exists* (b ^^ ts) mu.
      exists* t2 mu.
    or_32. exists* e. 
    or_33. exists* (trm_match t1' p b t2) mu'.
  destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' [mu' Red2]]]].
      inversions Typ1; inversion Val1. 
        or_33. exists* (t0 ^^ (t2::nil)) mu.
        or_33. exists* (t0 ^^ ((trm_fix t0)::t2::nil)) mu. 
        or_33. subst. inversions H. inversions Val2; inversions Typ2. 
           exists* (trm_nat (n + n0)) mu.
           inversions H6.
        or_31. inversions Val2; inversions Typ2. 
          auto*.
          inversions H4.
        or_32. exists* e.
        or_33. exists* (trm_app t1 t2') mu'.
    or_32. exists* e. 
    or_33. exists* (trm_app t1' t2) mu'.
  or_31*.
  or_31*.  
  or_31*.
  destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' [mu' Red2]]]].
      or_32. exists* e.
      or_33. exists* (trm_pair t1 t2').
    or_32. exists* e.
    or_33. exists* (trm_pair t1' t2).
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    or_32. exists* e.
    or_33. exists* (trm_inj1 t1') mu'.
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    or_32. exists* e.
    or_33. exists* (trm_inj2 t1') mu'.
  or_31*.
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    destruct (var_fresh (dom mu)) as [l Fr].
      or_33. exists* (trm_loc l) (mu & l ~ t1).
      or_32. exists* e.
    or_33. exists* (trm_ref t1') mu'. 
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    inversions Val1; inversions Typ.
      inversion H4.  
      destruct ((proj44 H0) _ _ H6) as [t' [Has' Typt']].
       or_33. exists* t' mu.
    or_32. exists* e.
    or_33. exists* (trm_get t1') mu'.
  destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' [mu' Red2]]]].
      inversions Val1; inversions Typ1.  
        inversion H4.
        destruct ((proj44 H0) _ _ H6) as [t' [Has' Typt']].
         or_33. exists* trm_unit (mu & l ~ t2).
      or_32. exists* e. 
      or_33. exists* (trm_set t1 t2') mu'. 
    or_32. exists* e.
    or_33. exists* (trm_set t1' t2) mu'.
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    or_32. exists* t1. 
    or_32. exists* e. 
    or_33. exists* (trm_raise t1') mu'. 
  destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' [mu' Red2]]]].
    or_33. exists* t2 mu. 
    or_33. exists* (trm_app t1 e) mu.
    or_33. exists* (trm_catch t1 t2') mu'. 
Qed.




