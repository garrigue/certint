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

Fixpoint clos_depth (c:clos) : nat :=
  match c with
  | clos_abs _ cls => S (fold_right (fun c => Max.max (clos_depth c)) 0 cls)
  | clos_const _ cls => S (fold_right (fun c => Max.max (clos_depth c)) 0 cls)
  end.

Lemma clos_ok_ind : forall P : clos -> Prop,
       (forall (t : trm) (cls : list clos),
        list_forall clos_ok cls ->
        closed_n (S (length cls)) t ->
        list_forall P cls -> P (clos_abs t cls)) ->
       (forall (c : Const.const) (cls : list clos),
        list_forall clos_ok cls ->
        length cls <= Const.arity c ->
        list_forall P cls -> P (clos_const c cls)) ->
       forall c : clos, clos_ok c -> P c.
Proof.
  intros.
  assert (clos_depth c < S (clos_depth c)) by auto with arith.
  set (n:=S(clos_depth c)) in *. clearbody n.
  generalize dependent c.
  induction n; intros.
    elim (lt_n_O _ H2).
  inversions H1.
    apply (H _ _ H3 H4).
    simpl in H2.
    clear -IHn H2 H3.
    induction H3. auto. simpl in H2.
    constructor. apply IHlist_forall.
      puts (Max.le_max_r (clos_depth x)
              (fold_right (fun c : clos => Max.max (clos_depth c)) 0 L)).
      omega.
    apply* IHn.
    puts (Max.le_max_l (clos_depth x)
            (fold_right (fun c : clos => Max.max (clos_depth c)) 0 L)).
    omega.
  apply (H0 _ _ H3 H4).
  simpl in H2.
  clear -IHn H2 H3.
  induction H3. auto. simpl in H2.
  constructor. apply IHlist_forall.
  puts (Max.le_max_r (clos_depth x)
          (fold_right (fun c : clos => Max.max (clos_depth c)) 0 L)).
  omega.
  apply* IHn.
  puts (Max.le_max_l (clos_depth x)
          (fold_right (fun c : clos => Max.max (clos_depth c)) 0 L)).
  omega.
Qed.

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
    clear -H H1; induction H; simpl*.
    inversions H1.
    constructor; auto*.
  unfold const_app.
  assert (term (trm_cst c)) by auto.
  set (t:=trm_cst c) in *. clearbody t.
  clear H0; gen t; induction H; intros; simpl*.
  inversions H1; clear H1.
  auto*.
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

Fixpoint stack2trm t0 (l : list frame) {struct l} : trm :=
  match l with
  | nil => t0
  | Frame benv args t :: rem =>
    let t1 :=
      match t0 with
      | trm_bvar _ => t
      | _ =>
        match t with
        | trm_abs t1 => trm_let t0 t1
        | _ => trm_app t t0
        end
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
  induction 1; simpl;
    assert (list_forall term (List.map clos2trm cls))
      by (clear -H; induction H; simpl; auto using clos_ok_term).
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

Lemma typing_app_abs_let : forall K E t1 t2 T,
  K; E |(false,GcAny)|= trm_app (trm_abs t2) t1 ~: T ->
  K; E |(false,GcAny)|= trm_let t1 t2 ~: T.
Proof.
  intros.
  inversions H; try discriminate; simpl in *.
  inversions H4; try discriminate; simpl in *.
  apply (@typing_let (false,GcAny) (Sch S nil) {} L).
    simpl; intros.
    destruct Xs; try elim H0.
    unfold kinds_open_vars, kinds_open, sch_open_vars; simpl.
    rewrite* typ_open_vars_nil.
  apply H8.
Qed.

Theorem eval_sound : forall K T h fl t,
  K ; empty |(false,GcAny)|= stack2trm t fl ~: T ->
  K ; empty |(false,GcAny)|= res2trm (eval empty h nil nil t fl) ~: T.
Proof.
  induction h; intros.
    simpl. rewrite* trm_inst_nil.
  induction fl; simpl in *.
  (* fl = nil *)
  inversions H.
  (* Var *)
  elim (binds_empty H2).
  (* Abs *)
  simpl. rewrite* trm_inst_nil.
  (* Let *)
  apply IHh.
  simpl.
  destruct t1; try rewrite* trm_inst_nil.
  puts (proj43 (typing_regular H)).
  inversion H2. inversion H5.
  (* App *)
  apply IHh.
  simpl.
  Hint Resolve typing_app_abs_let.
  inversions H1; inversions H0; try discriminate; try rewrite* trm_inst_nil.
  (* Cst *)
  auto*.
  (* Gc *)
  discriminate.
  (* a :: fl *)
Qed.

End Mk3.
End Mk2.
End MkEval.