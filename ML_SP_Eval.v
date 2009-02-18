(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, January 2009                                           *
***************************************************************************)

Set Implicit Arguments.

Require Import Arith List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure.
Require Import ML_SP_Soundness.

Module MkEval(Cstr:CstrIntf)(Const:CstIntf).

Module Sound := MkSound(Cstr)(Const).
Import Sound.
Import Infra.
Import Defs.
Import Metatheory_Env.Env.

Module Mk2(Delta:DeltaIntf).

Inductive clos : Set :=
  | clos_abs : trm -> list clos -> clos
  | clos_const : Const.const -> list clos -> clos.

Definition term_n n t :=
  forall ts, list_for_n term n ts -> term (trm_inst t ts).

Inductive clos_ok : clos -> Prop :=
  | clos_ok_abs : forall t cls,
      list_forall clos_ok cls ->
      term_n (S (length cls)) t ->
      clos_ok (clos_abs t cls)
  | clos_ok_const : forall c cls,
      list_forall clos_ok cls ->
      List.length cls <= Const.arity c ->
      clos_ok (clos_const c cls).

Fixpoint clos2trm (c:clos) : trm :=
  match c with
  | clos_abs t l     => trm_inst (trm_abs t) (List.map clos2trm l)
  | clos_const cst l => const_app cst (List.map clos2trm l)
  end.

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
End Cut.

Parameter delta_red : Const.const -> list clos -> clos.

Section Eval.

Variable fenv : env clos.

Record frame : Set := Frame
  { frm_benv : list clos; frm_app : list clos; frm_trm : trm }.

Fixpoint stack2trm t0 (l : list frame) {struct l} : trm :=
  match l with
  | nil => t0
  | Frame benv args t :: rem =>
    let t1 :=
      match t0 with
      | trm_bvar _ => t
      | _ => trm_app t t0
      end
    in
    let t2 :=
      trm_inst
        (List.fold_left trm_app (List.map clos2trm args) t1)
        (List.map clos2trm benv)
    in stack2trm t2 rem
  end.
    
Inductive eval_res : Set :=
  | Result : clos -> eval_res
  | Inter  : list frame -> eval_res.

Definition res2trm res :=
  match res with
  | Result cl => clos2trm cl
  | Inter l => stack2trm trm_def l
  end.

Definition clos_def := clos_abs trm_def nil.

Definition trm2clos (benv : list clos) (fenv : env clos) t :=
  match t with
  | trm_bvar n => nth n benv clos_def
  | trm_fvar v =>
    match get v fenv with
    | None => clos_def
    | Some c => c
    end
  | trm_cst c => clos_const c nil
  | trm_abs t1 => clos_abs t1 benv
  | trm_let _ _ | trm_app _ _ => clos_def
  end.

Fixpoint eval (h:nat) (benv:list clos) (app:list clos) (t:trm)
  (stack : list frame) {struct h} : eval_res :=
  match h with
  | 0 => Inter (Frame benv app t :: stack)
  | S h =>
    let result c :=
      match stack with
      | nil => Result c
      | Frame benv' app' t :: rem => eval h benv' (c::app') t rem
      end
    in
    match t with
    | trm_let t1 t2 =>
      eval h benv nil t1 (Frame benv app (trm_abs t2) :: stack)
    | trm_app t1 t2 =>
      eval h benv nil t2 (Frame benv app t1 :: stack)
    | _ =>
    let c := trm2clos benv fenv t in
    match app with
    | nil => result c
    | c1 :: rem =>
    match c with
    | clos_abs t1 benv =>
      eval h (c1::benv) rem t1 stack
    | clos_const cst l =>
      let nargs := length l +  length app in
        let nred := S(Const.arity cst) in
        if le_lt_dec nred nargs then
        let (args, app') := cut nred (List.app l app) in
        match delta_red cst args with
        | clos_const cst' app'' =>
          eval h nil (List.app app'' app') (trm_cst cst') stack
        | clos_abs t1 benv =>
          eval h benv app' (trm_abs t1) stack
        end
      else result c
    end end end
  end.
End Eval.

Check eval.

Definition trm_S :=
  trm_abs (trm_abs (trm_abs
    (trm_app (trm_app (trm_bvar 2) (trm_bvar 0))
      (trm_app (trm_bvar 1) (trm_bvar 0))))).
Definition trm_K :=
  trm_abs (trm_abs (trm_bvar 1)).

Eval compute in eval nil 100 nil nil
  (trm_app (trm_abs (trm_bvar 0)) (trm_abs (trm_bvar 0))) nil.

Definition skk := eval nil 100 nil nil
  (trm_app (trm_app (trm_app trm_S trm_K) (trm_K)) (trm_abs (trm_bvar 13))) nil.

Eval compute in skk.
Eval compute in
  match skk with Result c => clos2trm c | _ => trm_def end.

Definition skk' := eval nil 3 nil nil
  (trm_app (trm_app (trm_app trm_S trm_K) (trm_K))
    (trm_abs (trm_abs (trm_abs (trm_bvar 2))))) nil.

Eval compute in skk'.
Eval compute in res2trm skk'.

Module Sound2 := Sound.Mk2(Delta).
Import Sound2.
Import JudgInfra.
Import Judge.

Parameter delta_red_sound : forall c cls K T,
  length cls = (S(Const.arity c)) ->
  K ; empty |(false,GcLet)|= const_app c (List.map clos2trm cls) ~: T ->
  exists t1:trm, exists t2:trm, exists tl:list trm,
    Delta.rule (length tl) t1 t2 /\ list_forall term tl /\
    const_app c (List.map clos2trm cls) = trm_inst t1 tl /\
    clos2trm (delta_red c cls) = trm_inst t2 tl.

Module Mk3(SH:SndHypIntf).

Module Sound3 := Sound2.Mk3(SH).
Import Sound3.

Lemma clos_ok_value : forall cl,
  clos_ok cl -> value (clos2trm cl).
Proof.
  unfold value.
  induction 1; simpl.
    exists 0. unfold trm_inst. simpl. constructor.
    apply (@term_abs {}). intros.
Lemma trm_inst_rec_more : forall tl t1 t n,
  term_n (S n) t ->
  trm_open_rec n t1 (trm_inst_rec (S n) tl t) = trm_inst_rec n (t1 :: tl) t.
Proof.
  induction t; intros.
  unfold trm_inst_rec.
  destruct (le_lt_dec (S n0) n).
      destruct (le_lt_dec n0 n).
      destruct n. elimtype False; omega.
      replace (S n - S n0) with (n-n0) by omega.
      rewrite <- minus_Sn_m.
      simpl.
      unfold term_n in H; simpl in H.
      assert (n0 = n - (n-n0)) by omega.
      pattern n0 at 1; rewrite H.
      clear; induction (n-n0).
        simpl.
      simpl.
      assert (n0 <= n) by omega.


  destruct n.
    apply (H0 (List.map clos2trm cls)).
    Search term.

Theorem eval_sound : forall K t T h,
  K ; empty |(true,GcAny)|= t ~: T ->
  K ; empty |(true,GcAny)|= res2trm (eval empty h nil nil t nil) ~: T.

End Mk3.
End Mk2.
End MkEval.