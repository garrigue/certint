(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, January 2009                                           *
***************************************************************************)

Set Implicit Arguments.

Require Import Arith List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure.
Require Import ML_SP_Soundness.

Section ListForall.
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

Variable Q : A -> Prop.

Lemma list_forall_apply : forall l,
  list_forall (fun x => P x -> Q x) l ->
  list_forall P l -> list_forall Q l.
Proof.
  intros; induction* H.
  inversion* H0.
Qed.
End ListForall.

Hint Resolve list_forall_apply.

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

Check clos_ind.

Section ClosInd.
Variable P : clos -> Prop.
Hypothesis Habs : forall t l, list_forall P l -> P (clos_abs t l).
Hypothesis Hconst : forall c l, list_forall P l -> P (clos_const c l).

Fixpoint clos_ind' (c : clos) : P c :=
  match c return P c with
  | clos_abs t l => Habs t (map_prop P clos_ind' l)
  | clos_const c l => Hconst c (map_prop P clos_ind' l)
  end.
End ClosInd.

Inductive closed_n : nat -> trm -> Prop :=
  | cln_fvar : forall n x, closed_n n (trm_fvar x)
  | cln_bvar : forall n m, m < n -> closed_n n (trm_bvar m)
  | cln_abs  : forall n t, closed_n (S n) t -> closed_n n (trm_abs t)
  | cln_let  : forall n t1 t2,
      closed_n n t1 -> closed_n (S n) t2 -> closed_n n (trm_let t1 t2)
  | cln_app  : forall n t1 t2,
      closed_n n t1 -> closed_n n t2 -> closed_n n (trm_app t1 t2)
  | cln_cst  : forall n c, closed_n n (trm_cst c).

Lemma trm_inst_rec_more : forall tl t1 t n,
  closed_n (S n + List.length tl) t ->
  list_forall term tl ->
  {n~>t1}trm_inst_rec (S n) tl t = trm_inst_rec n (t1 :: tl) t.
Proof.
  intros.
  remember (S n + length tl) as z.
  gen n; induction H; intros; subst; auto.
    unfold trm_inst_rec.
    destruct (le_lt_dec (S n0) m).
      destruct (le_lt_dec n0 m); try solve [elimtype False; omega].
      remember (m - S n0) as z.
      replace (m - n0) with (S z) by omega.
      assert (z < length tl) by omega.
      simpl.
      clear -H0 H1; gen z; induction H0; simpl; intros.
        elimtype False; omega.
      destruct z. rewrite* <- Infra.trm_open_rec.
      assert (z < length L) by omega.
      auto*.
    destruct (le_lt_dec n0 m).
      assert (n0 = m) by omega. subst.
      replace (m-m) with 0 by omega. simpl.
      destruct* (m === m).
    simpl. destruct* (n0 === m). subst; elimtype False; omega.
  simpl. rewrite* (IHclosed_n (S n0)).
  simpl. rewrite* (IHclosed_n1 n0). rewrite* (IHclosed_n2 (S n0)).
  simpl. rewrite* (IHclosed_n1 n0). rewrite* (IHclosed_n2 n0).
Qed.

Lemma term_trm_inst_closed : forall t tl,
  closed_n (length tl) t -> list_forall term tl -> term (trm_inst t tl).
Proof.
  unfold trm_inst; induction t; intros; inversions H; simpl; auto.
  rewrite <- minus_n_O.
  generalize (trm_bvar n).
  clear H; gen tl; induction n; intros; destruct tl; try elim (lt_n_O _ H3).
    simpl. inversion* H0.
  simpl.
  apply IHn. inversion* H0.
  apply* lt_S_n.
  apply (@term_abs {}); intros.
  unfold trm_open. rewrite* trm_inst_rec_more.
  apply* (@term_let {}); intros.
  unfold trm_open. rewrite* trm_inst_rec_more.
Qed.

Inductive clos_ok : clos -> Prop :=
  | clos_ok_abs : forall t cls,
      list_forall clos_ok cls ->
      closed_n (S (length cls)) t ->
      clos_ok (clos_abs t cls)
  | clos_ok_const : forall c cls,
      list_forall clos_ok cls ->
      List.length cls <= Const.arity c ->
      clos_ok (clos_const c cls).
Check clos_ok_ind.
Reset clos_ok_ind.

Section ClosOkInd.
Variable  P : clos -> Prop.
Hypothesis Habs : forall t cls,
  list_forall clos_ok cls ->
  closed_n (S (length cls)) t ->
  list_forall P cls -> P (clos_abs t cls).
Hypothesis Hconst : forall c cls,
  list_forall clos_ok cls ->
  length cls <= Const.arity c ->
  list_forall P cls -> P (clos_const c cls).

Lemma clos_ok_ind : forall c, clos_ok c -> P c.
Proof.
  Hint Resolve Habs Hconst.
  intros c H; induction c using clos_ind'; inversion* H.
Qed.
End ClosOkInd.

Fixpoint clos2trm (c:clos) : trm :=
  match c with
  | clos_abs t l     => trm_inst (trm_abs t) (List.map clos2trm l)
  | clos_const cst l => const_app cst (List.map clos2trm l)
  end.

Lemma clos_ok_term : forall cl,
  clos_ok cl -> term (clos2trm cl).
Proof.
  induction 1; simpl.
    apply term_trm_inst_closed.
      rewrite map_length.
      constructor; auto.
    apply* list_forall_map. intros; auto.
  unfold const_app.
  cut (term (trm_cst c)); auto.
  generalize (trm_cst c).
  clear -H H1; induction H; intros; simpl*.
  inversion* H1.
Qed.

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

Definition is_bvar t :=
  match t with trm_bvar _ => true | _ => false end.

Definition app_trm t1 t2 :=
  match t1 with
  | trm_abs t => trm_let t2 t
  | _ => trm_app t1 t2
  end.

Definition app2trm t args :=
  List.fold_left app_trm (List.map clos2trm args) t.

Fixpoint stack2trm t0 (l : list frame) {struct l} : trm :=
  match l with
  | nil => t0
  | Frame benv args t :: rem =>
    let t1 :=
      if is_bvar t0 then t else app_trm t t0
    in
    let t2 := trm_inst (app2trm t1 args) (List.map clos2trm benv)
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
  induction 1; simpl;
    assert (list_forall term (List.map clos2trm cls))
      by (clear -H; apply* list_forall_map; auto using clos_ok_term).
    exists 0. unfold trm_inst. simpl. constructor.
    apply (@term_abs {}). intros.
    unfold trm_open. rewrite* trm_inst_rec_more.
    fold (trm_inst t (trm_fvar x :: List.map clos2trm cls)).
    apply* term_trm_inst_closed. simpl. rewrite* map_length.
    rewrite map_length; simpl*.
  exists (Const.arity c - length cls). unfold const_app.
  set (t := trm_cst c).
  assert (valu (Const.arity c) t) by (unfold t; auto).
  replace (Const.arity c) with (Const.arity c - length cls + length cls)
    in H3 by omega.
  set (n := Const.arity c - length cls) in *.
  gen t n; clear H H0; induction H1; simpl in *; intros.
    rewrite <- plus_n_O in H3. auto.
  inversions H2; clear H2.
  apply* IHlist_forall.
  destruct H.
  apply* value_app.
  replace (S (n + length L)) with (n + S (length L)) by omega; auto.
Qed.

Lemma trm_inst_nil : forall t, trm_inst t nil = t.
Proof.
  unfold trm_inst; intros.
  generalize 0; induction t; intros; simpl*.
     destruct* (le_lt_dec n0 n).
     destruct* (n-n0).
    rewrite* IHt.
   rewrite IHt1; rewrite* IHt2.
  rewrite IHt1; rewrite* IHt2.
Qed.

Definition gc := (false, GcAny).

Lemma typing_app_abs_let : forall K E t1 t2 T,
  K; E |gc|= trm_app (trm_abs t2) t1 ~: T ->
  K; E |gc|= trm_let t1 t2 ~: T.
Proof.
  intros.
  inversions H; try discriminate; simpl in *.
  inversions H4; try discriminate; simpl in *.
  apply (@typing_let gc (Sch S nil) {} L).
    simpl; intros.
    destruct Xs; try elim H0.
    unfold kinds_open_vars, kinds_open, sch_open_vars; simpl.
    rewrite* typ_open_vars_nil.
  apply H8.
Qed.

Lemma term_trm_inst : forall n t tl,
  closed_n n t -> trm_inst_rec n tl t = t.
Proof.
  induction 1; simpl*; try congruence.
  destruct* (le_lt_dec n m).
  elimtype False; omega.
Qed.

Hint Constructors closed_n.

Lemma closed_n_le : forall m n t, closed_n m t -> m <= n -> closed_n n t.
Proof.
  intros until 1; revert n.
  induction H; intuition; omega.
Qed.

Lemma closed_0_1 : forall t x, closed_n 0 (t ^ x) -> closed_n 1 t.
Proof.
  intros t x.
  unfold trm_open.
  generalize 0.
  induction t; simpl; intros; auto.
     destruct* (le_lt_dec (S n0) n).
     destruct (n0 === n). elimtype False; omega.
     inversions H. elimtype False; omega.
    simpl in H; inversions* H.
   simpl in H; inversions* H.
  simpl in H; inversions* H.
Qed.

Lemma term_closed_0 : forall t, term t -> closed_n 0 t.
Proof.
  induction 1; simpl*;
    constructor; auto;
    destruct (var_fresh L);
    apply* closed_0_1.
Qed.

Definition retypable t1 t2 :=
  forall K E T, K; E |gc|= t1 ~: T -> K; E |gc|= t2 ~: T.

Lemma trm_open_comm : forall i j u v t,
  i <> j -> term u -> term v ->
  {i ~> u}({j ~> v}t) = {j ~> v}({i ~> u}t).
Proof.
  intros.
  revert i j H.
  induction t; intros; simpl*.
     destruct (j === n).
      destruct (i === n); simpl*.
        elimtype False; omega.
      destruct* (j === n).
      rewrite* <- Infra.trm_open_rec.
     simpl.
     destruct (i === n).
      rewrite* <- Infra.trm_open_rec.
     simpl.
     destruct* (j === n).
    rewrite* IHt.
   rewrite* IHt1.
   rewrite* IHt2.
  rewrite* IHt1.
  rewrite* IHt2.
Qed.

Lemma hole_retypable : forall t1 t2 C,
  term t1 -> term t2 ->
  retypable t1 t2 -> retypable (C ^^ t1) (C ^^ t2).
Proof.
  introv Ht1 Ht2 H.
  unfold trm_open.
  generalize 0.
  intros; intro; intros.
  gen_eq ({n ~> t1} C) as t.
  unfold gc in *.
  gen_eq (false, GcAny) as g.
  gen n C.
  induction H0; intros; destruct C; try discriminate; simpl in *; subst*;
    try solve [inversion* H0 | destruct (n === n0); try discriminate; subst*].
        inversions* H5.
      inversions* H4.
      apply* (@typing_abs gc L).
      intros.
      simpl in *.
      puts (H1 _ H3); clear H1.
      unfold trm_open.
      rewrite* trm_open_comm.
      apply* (H2 _ H3).
      unfold trm_open.
      rewrite* trm_open_comm.
    inversions* H5; clear H0 H2 H5.
    apply* (@typing_let gc M L1 L2); intros.
    unfold trm_open.
    rewrite* trm_open_comm.
    apply* (H3 _ H0).
    rewrite* trm_open_comm.
  inversions* H4.
Qed.

Lemma retypable_app_trm : forall t1 t2,
  retypable (trm_app t1 t2) (app_trm t1 t2).
Proof.
  intros; intro; intros.
  unfold app_trm; destruct* t1.
  apply* typing_app_abs_let.
Qed.

Ltac case_rewrite H t :=
  case_eq t; introv H; rewrite H in *; try discriminate.

Lemma app_trm_cases : forall t1,
  (forall t2, app_trm t1 t2 = trm_app t1 t2) \/ (exists t, t1 = trm_abs t).
Proof.
  intros.
  destruct t1; simpl*.
Qed.

Hint Resolve term_closed_0 clos_ok_term.

Lemma term_closed_n : forall n t,
  term t -> closed_n n t.
Proof.
  intros.
  apply* (@closed_n_le 0); omega.
Qed.

Hint Resolve term_closed_n.

Lemma trm_inst_app2trm : forall t benv args,
  list_forall clos_ok args ->
  retypable (trm_inst (app2trm t args) benv) (app2trm (trm_inst t benv) args).
Proof.
  unfold trm_inst, app2trm.
  intros.
  generalize 0; induction args using rev_ind; intros; simpl*.
    intro; auto*.
  rewrite map_app. do 2 rewrite fold_left_app; simpl.
  intro; intros.
  clear IHargs.
  gen x T; induction args using rev_ind; intros.
    simpl in *.
    assert (closed_n n (clos2trm x)) by inversions* H.
    clear H.
    destruct (app_trm_cases t).
      rewrite H in H0; simpl in H0.
      inversions H0; try discriminate.
      simpl in *.
      apply* retypable_app_trm.
      fold (trm_inst (clos2trm x) benv) in H8.
      rewrite term_trm_inst in H8; auto*.
    destruct H as [t1 Ht1].
    subst. simpl app_trm in *.
    simpl in H0.
    inversions H0; try discriminate.
    rewrite term_trm_inst in H5; auto*.
  rewrite map_app in *.
  repeat rewrite fold_left_app in *.
  simpl in *.
  destruct (app_trm_cases (app_trm
           (fold_left app_trm (List.map clos2trm args)
              (trm_inst_rec n benv t)) (clos2trm x))).
    rewrite H1; clear H1.
    destruct (app_trm_cases
      (app_trm (fold_left app_trm (List.map clos2trm args) t) (clos2trm x))).
      rewrite H1 in *; clear H1.
      simpl in H0.
      inversions H0; try discriminate; clear H0.
      apply* typing_app.
        simpl.
        apply* IHargs.
        apply* list_forall_in.
        intros; apply* (list_forall_out H).
      rewrite term_trm_inst in H7; auto*.
      assert (clos_ok x0) by apply* (list_forall_out H).
      auto.
    destruct H1.
    case_rewrite R (fold_left app_trm (List.map clos2trm args) t).
  destruct H1.
  case_rewrite R
    (fold_left app_trm (List.map clos2trm args) (trm_inst_rec n benv t)).
Qed.

(*
Lemma trm_inst_app2trm : forall t benv args,
  list_forall clos_ok args ->
  trm_inst (app2trm t args) benv = app2trm (trm_inst t benv) args.
Proof.
  unfold trm_inst, app2trm.
  induction args using rev_ind; intros; simpl*.
  rewrite map_app. do 2 rewrite fold_left_app; simpl.
  rewrite IHargs.
    destruct 
    fold (trm_inst (clos2trm x) benv).
    rewrite* term_trm_inst.
    apply term_closed_0.
    apply clos_ok_term.
    Check list_forall_out.
    apply* (list_forall_out H).
  apply list_forall_in.
  intros.
  apply* (list_forall_out H).
Qed.
*)

Inductive frame_ok : frame -> Prop :=
  frm_ok : forall benv app trm,
    list_forall clos_ok benv ->
    list_forall clos_ok app ->
    closed_n (length benv) trm ->
    frame_ok (Frame benv app trm).
Hint Constructors frame_ok.

Lemma cln_app_trm : forall n t1 t2,
  closed_n n t1 -> closed_n n t2 -> closed_n n (app_trm t1 t2).
Proof.
  intros.
  destruct (app_trm_cases t1).
    rewrite* H1.
  destruct H1.
  subst; simpl.
  inversions* H.
Qed.

Lemma closed_n_app2trm : forall n t args,
  closed_n n t ->
  list_forall clos_ok args ->
  closed_n n (app2trm t args).
Proof.
  unfold app2trm.
  intros.
  induction args using rev_ind. simpl*.
  rewrite map_app; rewrite fold_left_app. simpl.
  assert (clos_ok x) by apply* (list_forall_out H0).
  assert (list_forall clos_ok args) by
    (apply list_forall_in; intros; apply* (list_forall_out H0)).
  apply* cln_app_trm.
Qed.

Lemma retypable_stack2trm : forall t1 t2 fl,
  term t1 -> term t2 ->
  retypable t1 t2 ->
  list_forall frame_ok fl ->
  retypable (stack2trm t1 fl) (stack2trm t2 fl).
Proof.
  intros.
  gen t1 t2; induction H2; intros; simpl. auto.
  destruct x as [benv app t'].
  case_eq (is_bvar t1); intros.
    inversions H0; discriminate.
  case_eq (is_bvar t2); intros.
    inversions H1; discriminate.
  inversions H; clear H.
  apply IHlist_forall.
      apply term_trm_inst_closed.
        rewrite map_length.
        apply* closed_n_app2trm.
        apply* cln_app_trm.
      apply* list_forall_map.
    apply term_trm_inst_closed.
      rewrite map_length.
      apply* closed_n_app2trm.
      apply* cln_app_trm.
    apply* list_forall_map.
  clear IHlist_forall L H2 H4 H5.
  unfold app2trm.
  induction app using rev_ind.
    simpl.
    destruct (app_trm_cases t').
      do 2 rewrite H; clear H.
      unfold trm_inst; simpl.
      intro; intros.
      inversions H; try discriminate.
      apply* typing_app.
      rewrite* term_trm_inst.
      rewrite term_trm_inst in H12; auto.
    destruct H. subst; unfold trm_inst; simpl.
    intro; intros.
    inversions H; try discriminate.
    apply* (@typing_let gc M L1 L2).
    rewrite* term_trm_inst.
    rewrite term_trm_inst in H7; auto*.
  rewrite map_app.
  repeat rewrite fold_left_app. simpl.
  assert (Habs: forall t t' t1,
    fold_left app_trm (List.map clos2trm app) (app_trm t' t1) <> trm_abs t).
    clear.
    intros.
    induction app using rev_ind. destruct t'; discriminate.
    clear IHapp.
    rewrite map_app; rewrite fold_left_app.
    intro.
    destruct (fold_left app_trm (List.map clos2trm app) (app_trm t' t1));
     discriminate.
  destruct (app_trm_cases 
    (fold_left app_trm (List.map clos2trm app) (app_trm t' t1))).
   rewrite H; clear H.
   destruct (app_trm_cases 
     (fold_left app_trm (List.map clos2trm app) (app_trm t' t2))).
    rewrite H; clear H.
    unfold trm_inst in *; simpl.
    intro; intros.
    inversions H; try discriminate.
    assert (list_forall clos_ok app)
      by (apply list_forall_in; intros; apply* (list_forall_out H10)).
    assert (clos_ok x) by apply* (list_forall_out H10).
    apply* typing_app.
   destruct H. elim (Habs _ _ _ H).
  destruct H. elim (Habs _ _ _ H).
Qed.

Theorem eval_sound : forall h fl benv args K E t T,
  list_forall clos_ok args ->
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  list_forall frame_ok fl ->
  K ; E |gc|=
    stack2trm (app2trm (trm_inst t (List.map clos2trm benv)) args) fl ~: T ->
  K ; E |gc|= res2trm (eval nil h benv args t fl) ~: T.
Proof.
  induction h; introv; intros Hargs Hbenv Ht Hfl Typ.
    simpl*.
    refine (retypable_stack2trm _ _ _ _ Typ); auto.
  
  
    rewrite* trm_inst_app2trm.
  simpl.
  destruct t.
       destruct args as [|arg args].
        unfold app2trm in Typ; simpl in *.
        destruct fl.
         clear IHh.
         unfold trm_inst in Typ. simpl in *.
         rewrite <- minus_n_O in Typ.
         rewrite <- (map_nth clos2trm).
         destruct (le_lt_dec (length (List.map clos2trm benv)) n).
           rewrite nth_overflow in Typ; auto. inversions Typ. inversion H.
         rewrite* (nth_indep _ (clos2trm clos_def) (trm_bvar n) l).
        destruct f as [benv' app' t'].
        simpl.
        inversions Hfl; clear Hfl.
        inversions H2; clear H2.
        inversions Ht; clear Ht.
        unfold trm_inst in Typ; simpl in Typ.
        rewrite <- minus_n_O in Typ.
        poses Hlen H2.
        rewrite <- (map_length clos2trm) in H2.
        rewrite (nth_indep _ (trm_bvar n) (clos2trm clos_def) H2) in Typ.
        rewrite map_nth in Typ.
        assert (Hn: clos_ok (nth n benv clos_def)).
          apply (list_forall_out Hbenv).
          apply* nth_In.
        case_rewrite (is_bvar (clos2trm (nth n benv clos_def))) R.
          case_rewrite (clos2trm (nth n benv clos_def)) R1.
          clear -R1 Hn.
          assert (term (trm_bvar n0)).
            rewrite <- R1.
            apply* clos_ok_term.
          inversion H.
        clear R.
        replace (app2trm (app_trm t' (clos2trm (nth n benv clos_def))) app')
           with (app2trm t' (nth n benv clos_def :: app')) in Typ.
         rewrite trm_inst_app2trm in Typ; auto.
        unfold app2trm. simpl*. unfold app_trm.

Theorem eval_sound : forall h fl benv args K E t T K' E' T',
  list_forall clos_ok args ->
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  list_forall frame_ok fl ->
  K ; E |gc|= app2trm (trm_inst t (List.map clos2trm benv)) args ~: T ->
  (forall t, K ; E |gc|= t ~: T -> K'; E' |gc|= stack2trm t fl ~: T') ->
  K' ; E' |gc|= res2trm (eval nil h benv args t fl) ~: T'.
Proof.
  induction h; introv; intros Hargs Hbenv Ht Hfl Typ Env.
    simpl*.
    rewrite* trm_inst_app2trm.
  simpl.
  destruct t.
       destruct args as [|arg args].
        unfold app2trm in Typ; simpl in *.
        destruct fl.
         clear IHh.
         unfold trm_inst in Typ. simpl in *.
         apply Env. clear -Typ.
         rewrite <- minus_n_O in Typ.
         rewrite <- (map_nth clos2trm).
         destruct (le_lt_dec (length (List.map clos2trm benv)) n).
           rewrite nth_overflow in Typ; auto. inversions Typ. inversion H.
         rewrite* (nth_indep _ (clos2trm clos_def) (trm_bvar n) l).
        destruct f as [benv' app' t'].
        simpl.
        inversions Hfl; clear Hfl.
        inversions H2; clear H2.
        inversions Ht; clear Ht.
        puts (Env _ Typ).
        unfold trm_inst in H; simpl in H.
        rewrite <- minus_n_O in H.
        poses Hlen H2.
        rewrite <- (map_length clos2trm) in H2.
        rewrite (nth_indep _ (trm_bvar n) (clos2trm clos_def) H2) in H.
        rewrite map_nth in H.
        case_rewrite (is_bvar (clos2trm (nth n benv clos_def))) R.
          case_rewrite (clos2trm (nth n benv clos_def)) R1.
          clear -Hbenv Hlen R1.
          assert (term (trm_bvar n0)).
            rewrite <- R1.
            apply clos_ok_term.
            apply (list_forall_out Hbenv).
            apply* nth_In.
          inversion H.
        clear R.
        replace (app2trm (app_trm t' (clos2trm (nth n benv clos_def))) app')
           with (app2trm t' (nth n benv clos_def :: app')) in H.
         
        unfold app2trm in H.
        fold (fold_left trm_app clos2trm (nth n benv clos_def) 
        rewrite trm_inst_app2trm in H; auto.
          
        
        apply* IHh; clear IHh.
          constructor; auto.
          apply (list_forall_out Hbenv).
          apply* nth_In.
         simpl in Env.
        
             rewrite 
        

Section Eval.

Variables (K':kenv) (T':typ) (E':Defs.env) (fenv:env clos).

Hypothesis fenv_ok : forall x M,
  binds x M E' ->
  exists cl, binds x cl fenv /\
    has_scheme_vars gc {} empty empty (clos2trm cl) M.

Lemma concat_empty : forall (A:Set) (K:env A), empty & K = K.
Proof. intros; symmetry; apply (app_nil_end K). Qed.

Lemma has_scheme_from_vars' : forall t M,
  has_scheme_vars gc {} empty empty t M ->
  kenv_ok K' -> env_ok E' ->
  has_scheme gc K' E' t M.
Proof.
  clear fenv_ok.
  intros.
  apply (@has_scheme_from_vars gc (dom K')).
  intro; intros.
  replace K' with (empty & K') by apply concat_empty.
  apply typing_weaken_kinds.
    replace E' with (empty & E' & empty) by (simpl; apply concat_empty).
    apply typing_weaken.
      simpl.
      apply* H.
    simpl. rewrite* concat_empty.
  assert (fresh {} (sch_arity M) Xs) by auto.
  puts (H _ H3).
  rewrite concat_empty.
  rewrite concat_empty in H4.
  apply* kenv_ok_concat.
  rewrite* dom_kinds_open_vars.
  apply* fresh_disjoint.
Qed.

Theorem eval_sound : forall h fl xs benv K E t T,
  fresh (dom E) (length benv) xs ->
  (forall x cl, binds x cl (combine xs benv) ->
    exists M, binds x M E /\ K;E' |gc|= clos2trm cl 
  K ; E' & E |gc|= trm_inst t xs ~: T ->
  (K ; E' & E |gc|= trm_inst t xs ~: T -> K'; E' |gc|= stack2trm t fl ~: T') ->
  K' ; E' |gc|= res2trm (eval fenv h benv nil t fl) ~: T'.
Proof.
  induction h; intros.
    simpl. rewrite* trm_inst_nil.
  induction fl.
  (* fl = nil *)
  poses Typ (H0 H).
  simpl in *.
  clear H H0; inversions Typ.
  (* Var *)
  simpl.
  destruct (fenv_ok H1) as [cl [B HS]].
  rewrite B.
  destruct H2.
  apply* (has_scheme_from_vars' HS).
  (* Abs *)
  simpl. rewrite* trm_inst_nil.
  (* Let *)
  destruct (var_freshes L1 (sch_arity M)) as [Xs Fr].
  poses Typ1 (H _ Fr).
  rewrite <- (trm_inst_nil t1) in Typ1.
  refine (IHh _ _ _ _ _ _ Typ1 _); intros.
  simpl.
  rewrite trm_inst_nil in Typ1.
  assert (is_bvar t1 = false).
    assert (trm1: term t1) by auto;
    inversions* trm1.
  rewrite H2. rewrite* trm_inst_nil.
  (* App *)
  rewrite <- (trm_inst_nil t2) in H0.
  refine (IHh _ _ _ _ _ _ H0 _); intros.
  simpl.
  rewrite trm_inst_nil in H0.
  assert (is_bvar t2 = false).
    assert (trm2: term t2) by auto;
    inversions* trm2.
  Hint Resolve typing_app_abs_let.
  rewrite H2.
  inversions H; simpl; try discriminate; try rewrite* trm_inst_nil.
  (* Cst *)
  apply Typ.
  (* Gc *)
  discriminate.
  (* a :: fl *)
  simpl.
  destruct a as [benv' app' t'].
  destruct t.
  (* Var *)
  simpl.
  destruct (fenv_ok H4) as [cl [B HS]].
  apply IHfl.
  
Qed.

End Mk3.
End Mk2.
End MkEval.