(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, January 2009                                           *
***************************************************************************)

Set Implicit Arguments.

Require Import Arith List Metatheory.
Require Import ML_SP_Definitions.
Require Import ML_SP_Soundness.

Module MkEval(Cstr:CstrIntf)(Const:CstIntf).

Module Sound := MkSound(Cstr)(Const).
Import Sound.
Import Infra.
Import Defs.
Import Metatheory_Env.Env.

Inductive clos : Set :=
  | clos_abs : trm -> list clos -> clos
  | clos_const : Const.const -> list clos -> clos.

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
  trm_open_rec n t1 (trm_inst_rec (S n) tl t) = trm_inst_rec n (t1 :: tl) t.
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
Reset clos_ok_ind.
Hint Constructors clos_ok.

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

Definition inst t benv := trm_inst t (List.map clos2trm benv).

Fixpoint stack2trm t0 (l : list frame) {struct l} : trm :=
  match l with
  | nil => t0
  | Frame benv args t :: rem =>
    let t1 := inst t benv in
    let t2 := if is_bvar t0 then t1 else app_trm t1 t0 in
    stack2trm (app2trm t2 args) rem
  end.
    
Inductive eval_res : Set :=
  | Result : nat -> clos -> eval_res
  | Inter  : list frame -> eval_res.

Definition res2trm res :=
  match res with
  | Result _ cl => clos2trm cl
  | Inter l => stack2trm trm_def l
  end.

Definition clos_def := clos_abs trm_def nil.

Lemma clos_ok_def : clos_ok clos_def.
Proof.
  unfold clos_def.
  constructor. auto.
  unfold trm_def.
  simpl.
  constructor.
  auto.
Qed.
Hint Resolve clos_ok_def.

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

Definition trm2app t :=
  match t with
  | trm_app t1 t2 => Some (t1, t2)
  | trm_let t2 t1 => Some (trm_abs t1, t2)
  | _             => None
  end.

Module Mk2(Delta:DeltaIntf).

Module Sound2 := Sound.Mk2(Delta).
Import Sound2.
Import Sound.
Import JudgInfra.
Import Judge.

Definition Gc := (false, GcAny).

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
  set (n := Const.arity c - length cls).
  exists n. unfold const_app.
  set (t := trm_cst c).
  assert (valu (Const.arity c) t) by (unfold t; auto).
  replace (Const.arity c) with (n + length cls)
    in H3 by (unfold n; omega).
  gen t n; clear H H0; induction H1; simpl in *; intros.
    rewrite <- plus_n_O in H3. auto.
  inversions H2; clear H2.
  apply* IHlist_forall.
  destruct H.
  apply* value_app.
  replace (S (n + length L)) with (n + S (length L)) by omega; auto.
Qed.
Hint Resolve clos_ok_value.

Lemma list_for_n_value : forall n cls,
  list_for_n clos_ok n cls ->
  list_for_n value n (List.map clos2trm cls).
Proof.
  split. rewrite* map_length.
  destruct H; apply* list_forall_map.
Qed.

Module Type SndHypIntf2.
  Include Type SndHypIntf.
  Parameter reduce_clos : Const.const -> list clos -> clos * list clos.
  Parameter reduce_clos_regular : forall c cls cl' cls',
    reduce_clos c cls = (cl', cls') ->
    list_forall clos_ok cls ->
    list_forall clos_ok (cl' :: cls').
  Parameter reduce_clos_sound :
    forall c cls (CLS : list_for_n clos_ok (S(Const.arity c)) cls) K E T,
      K; E |Gc|= const_app c (List.map clos2trm cls) ~: T ->
      let (cl', cls') := reduce_clos c cls in
      clos_ok cl' /\ list_forall clos_ok cls' /\
      fold_left trm_app (List.map clos2trm cls') (clos2trm cl') =
      Delta.reduce (list_for_n_value CLS).
End SndHypIntf2.

Module Mk3(SH:SndHypIntf2).

Module Sound3 := Sound2.Mk3(SH).
Import Sound3.

Section Eval.

Variable fenv : env clos.

Fixpoint eval (h:nat) (benv:list clos) (app:list clos) (t:trm)
  (stack : list frame) {struct h} : eval_res :=
  match h with
  | 0 => Inter (Frame benv app t :: stack)
  | S h =>
    let result c :=
      match stack with
      | nil => Result h c
      | Frame benv' app' t :: rem => eval h benv' (c::app') t rem
      end
    in
    match trm2app t with
    | Some (t1, t2) =>
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
          match SH.reduce_clos cst args with
          | (clos_const cst' app'', app3) =>
            eval h nil (app'' ++ app3 ++ app') (trm_cst cst') stack
          | (clos_abs t1 benv, app3) =>
            eval h benv (app3 ++ app') (trm_abs t1) stack
          end
        else result (clos_const cst (l++app))
      end
    end end
  end.
End Eval.

(*
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
*)

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

Definition is_abs t :=
  match t with trm_abs _ => true | _ => false end.

Lemma app_trm_cases : forall t1,
  (forall t2, app_trm t1 t2 = trm_app t1 t2) \/ (exists t, t1 = trm_abs t).
Proof.
  intros.
  destruct t1; simpl*.
Qed.

Lemma app_trm_false : forall t1 t2,
  is_abs t1 = false -> app_trm t1 t2 = trm_app t1 t2.
Proof.
  intros.
  destruct* (app_trm_cases t1).
  destruct H0; subst; discriminate.
Qed.

Definition retypable E t1 t2 :=
  forall K T, K; E |Gc|= t1 ~: T -> K; E |Gc|= t2 ~: T.

Lemma typing_app_abs_let : forall E t1 t2,
  retypable E (trm_app (trm_abs t2) t1) (trm_let t1 t2).
Proof.
  intros; intro; intros.
  inversions H; try discriminate; simpl in *.
  inversions H4; try discriminate; simpl in *.
  apply (@typing_let Gc (Sch S nil) {} L).
    simpl; intros.
    destruct Xs; try elim H0.
    unfold kinds_open_vars, kinds_open, sch_open_vars; simpl.
    rewrite* typ_open_vars_nil.
  apply H8.
Qed.

Lemma trm_open_comm : forall i j u v t,
  i <> j -> term u -> term v ->
  trm_open_rec i u (trm_open_rec j v t) = trm_open_rec j v (trm_open_rec i u t).
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

Lemma retypable_trm_app : forall E t1 t2,
  retypable E (trm_app t1 t2) (app_trm t1 t2).
Proof.
  intros; intro; intros.
  unfold app_trm; destruct* t1.
  apply* typing_app_abs_let.
Qed.

Hint Resolve term_closed_0 clos_ok_term.

Lemma term_closed_n : forall n t,
  term t -> closed_n n t.
Proof.
  intros.
  apply* (@closed_n_le 0); omega.
Qed.

Hint Resolve term_closed_n.

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

Lemma term_app_trm : forall t1 t2,
  term t1 -> term t2 -> term (app_trm t1 t2).
Proof.
  intros.
  destruct (app_trm_cases t1).
    rewrite* H1.
  destruct H1.
  subst; simpl.
  inversions* H.
Qed.

Lemma term_app2trm : forall t cl,
  term t -> list_forall clos_ok cl -> term (app2trm t cl).
Proof.
  unfold app2trm.
  intros.
  induction cl using rev_ind.
    simpl*.
  rewrite map_app; rewrite fold_left_app; simpl.
  puts (list_forall_out H0).
  apply* term_app_trm.
  apply IHcl.
  apply* list_forall_in.
Qed.

Hint Resolve term_app_trm term_app2trm.

Lemma retypable_app_trm : forall E t1 t2 t3 t4,
  is_abs t1 = false ->
  retypable E t1 t2 -> retypable E t3 t4 ->
  retypable E (app_trm t1 t3) (app_trm t2 t4).
Proof.
  intros.
  rewrite (app_trm_false _ _ H).
  intro; intros.
  apply* retypable_trm_app.
  inversions* H2; discriminate.
Qed.

Lemma retypable_app_trm2 : forall E t1 t2 t3,
  retypable E t2 t3 -> retypable E (app_trm t1 t2) (app_trm t1 t3).
Proof.
  intros; intro; intros.
  destruct (app_trm_cases t1).
    rewrite H1 in *. inversions* H0; try discriminate.
  destruct H1; subst; simpl in *.
  inversions* H0; try discriminate.
Qed.

Lemma is_abs_app_trm : forall t1 t2,
  is_abs (app_trm t1 t2) = false.
Proof.
  intros.
  destruct t1; simpl*.
Qed.
Hint Resolve is_abs_app_trm.

Lemma app2trm_app : forall t l1 l2,
  app2trm t (l1 ++ l2) = app2trm (app2trm t l1) l2.
Proof.
  intros; unfold app2trm.
  rewrite map_app. rewrite* fold_left_app.
Qed.

Lemma is_abs_fold_left_app_trm : forall t args,
  is_abs t = false -> is_abs (fold_left app_trm args t) = false.
Proof.
  intros; induction args using rev_ind. auto.
  rewrite fold_left_app. simpl. apply is_abs_app_trm.
Qed.

Lemma is_abs_app2trm : forall t args,
  is_abs t = false -> is_abs (app2trm t args) = false.
Proof.
  intros; unfold app2trm. apply* is_abs_fold_left_app_trm.
Qed.
Hint Resolve is_abs_app2trm.

Lemma retypable_app2trm : forall E t1 t2 args,
  is_abs t1 = false ->
  retypable E t1 t2 ->
  list_forall clos_ok args ->
  retypable E (app2trm t1 args) (app2trm t2 args).
Proof.
  intros; induction args using rev_ind. auto.
  repeat rewrite app2trm_app.
  assert (list_forall clos_ok args).
    apply list_forall_in; intros; apply* (list_forall_out H1).
  unfold app2trm at 1 3. simpl.
  apply retypable_app_trm; auto.
  intro; auto.
Qed.

Lemma term_inst_closed : forall t cl,
  closed_n (length cl) t -> list_forall clos_ok cl ->
  term (inst t cl).
Proof.
  intros.
  apply term_trm_inst_closed.
    rewrite* map_length.
  apply* list_forall_map.
Qed.
Hint Resolve term_inst_closed.

Lemma is_bvar_term : forall t, term t -> is_bvar t = false.
Proof. induction 1; simpl*. Qed.

Lemma retypable_stack2trm : forall E t1 t2 fl,
  term t1 -> is_abs t1 = false ->
  retypable E t1 t2 ->
  list_forall frame_ok fl ->
  retypable E (stack2trm t1 fl) (stack2trm t2 fl).
Proof.
  intros.
  gen t1 t2; induction H2; intros; simpl. auto.
  destruct x as [benv app t'].
  case_eq (is_bvar t1); intros.
    inversions H0; discriminate.
  inversions H; clear H.
  apply IHlist_forall; clear IHlist_forall; auto.
  apply retypable_app2trm; auto.
  intro; intros.
  rewrite is_bvar_term.
    apply* retypable_app_trm2.
  destruct (app_trm_cases (inst t' benv)).
    rewrite H5 in H.
    inversions H; try discriminate.
    use (H3 _ _ H15).
  destruct H5. rewrite H5 in H; simpl in H.
  inversions H; try discriminate.
  destruct (var_freshes L1 (sch_arity M)).
  use (H3 _ _ (H13 _ f)).
Qed.

Lemma term_fold_app : forall tl t,
  list_forall term tl -> term t -> term (fold_left trm_app tl t).
Proof.
  intros; gen t.
  induction H; intros; simpl*.
Qed.

Lemma typing_app_trm_inv : forall K E t1 t2 T,
  is_abs t1 = false ->
  K; E |Gc|= app_trm t1 t2 ~: T ->
  exists T1, K; E |Gc|= t1 ~: T1.
Proof.
  intros.
  rewrite (app_trm_false _ _ H) in H0.
  inversions* H0; try discriminate.
Qed.

Lemma typing_app2trm_inv : forall K E t1 cl T,
  K; E |Gc|= app2trm t1 cl ~: T ->
  is_abs t1 = false ->
  exists T1, K; E |Gc|= t1 ~: T1.
Proof.
  unfold app2trm.
  intros.
  gen T; induction (List.map clos2trm cl) using rev_ind; simpl; intros.
    auto*.
  rewrite fold_left_app in H.
  simpl in H.
  destruct* (typing_app_trm_inv _ _ (is_abs_fold_left_app_trm _ l H0)  H).
Qed.

Lemma is_bvar_app_trm : forall t1 t2, is_bvar (app_trm t1 t2) = false.
Proof. 
  intros; destruct (app_trm_cases t1).
    rewrite* H.
  destruct H; rewrite* H.
Qed.
Hint Resolve is_bvar_app_trm.

Lemma typing_stack2trm_inv : forall K E fl t1 T,
  K; E |Gc|= stack2trm t1 fl ~: T ->
  is_bvar t1 = false ->
  exists T1, exists K, K; E |Gc|= t1 ~: T1.
Proof.
  induction fl; simpl; intros. auto*.
  destruct a as [benv args t].
  rewrite H0 in H.
  destruct (IHfl _ _ H) as [T1 [K' Typ]].
    clear.
    unfold app2trm. induction (List.map clos2trm args) using rev_ind.
      simpl*.
    rewrite fold_left_app; simpl*.
  clear -H0 Typ.
  set (t0 := inst t benv) in *.
  destruct* (typing_app2trm_inv _ _ Typ).
  destruct (app_trm_cases t0).
    rewrite H1 in H; inversions* H; try discriminate.
  destruct H1; rewrite H1 in H.
  inversions* H; try discriminate.
  destruct (var_freshes L1 (sch_arity M)).
  auto*.
Qed.

Lemma app2trm_cases : forall t cl,
  (exists t1, exists t2, app2trm t cl = trm_app t1 t2) \/
  (exists t1, exists t2, app2trm t cl = trm_let t1 t2) \/
  app2trm t cl = t.
Proof.
  intros.
  induction cl using rev_ind. simpl*.
  rewrite app2trm_app.
  destruct (app_trm_cases (app2trm t cl)); unfold app2trm at 1 3; simpl.
    rewrite* H.
  destruct H; rewrite H. simpl*.
Qed.

Lemma app2trm_cst : forall c cl,
  app2trm (trm_cst c) cl = const_app c (List.map clos2trm cl).
Proof.
  unfold app2trm, const_app.
  induction cl using rev_ind. simpl*.
  rewrite map_app. repeat rewrite fold_left_app. simpl.
  rewrite app_trm_false. rewrite* IHcl.
  apply* is_abs_app2trm.
Qed.

Section Soundness.

Variables (E:Defs.env) (fenv:env clos).

Hypothesis E_ok : env_ok E.

Hypothesis fenv_ok : env_prop clos_ok fenv /\
  forall x M, binds x M E ->
    exists cl, binds x cl fenv /\
      has_scheme_vars Gc {} empty empty (clos2trm cl) M.

Lemma concat_empty : forall (A:Set) (K:env A), empty & K = K.
Proof. intros; symmetry; apply (app_nil_end K). Qed.

Lemma has_scheme_from_vars' : forall K t M,
  has_scheme_vars Gc {} empty empty t M ->
  kenv_ok K -> env_ok E ->
  has_scheme Gc K E t M.
Proof.
  clear fenv_ok.
  intros.
  apply (@has_scheme_from_vars Gc (dom K)).
  intro; intros.
  replace K with (empty & K) by apply concat_empty.
  apply typing_weaken_kinds.
    replace E with (empty & E & empty) by (simpl; apply concat_empty).
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

Lemma trm_inst_n : forall d benv n,
  closed_n (length benv) (trm_bvar n) ->
  trm_inst (trm_bvar n) benv = nth n benv d.
Proof.
  unfold trm_inst; simpl; intros.
  rewrite <- minus_n_O.
  inversions H.
  apply* nth_indep.
Qed.  

Lemma inst_n : forall benv n,
  closed_n (length benv) (trm_bvar n) ->
  inst (trm_bvar n) benv = clos2trm (nth n benv clos_def).
Proof.
  intros; unfold inst.
  rewrite <- map_nth.
  apply trm_inst_n.
  rewrite* map_length.
Qed.

Lemma retypable_clos : forall benv t,
  closed_n (length benv) t ->
  trm2app t = None ->
  retypable E (inst t benv) (clos2trm (trm2clos benv fenv t)).
Proof.
  introv Ht H; intro; introv Typ.
  destruct t; try discriminate; try apply Typ; clear H; simpl in *.
    rewrite inst_n in Typ; auto.
  inversions Typ; try discriminate.
  destruct (proj2 fenv_ok _ _ H2) as [cl [B Typ']].
  rewrite B.
  destruct H5.
  apply* has_scheme_from_vars'.
Qed.

Lemma retypable_app_clos : forall benv t t1,
  closed_n (length benv) t ->
  trm2app t = None ->
  retypable E (app_trm (inst t benv) t1)
    (app_trm (clos2trm (trm2clos benv fenv t)) t1).
Proof.
  intros; intro; intros.
  destruct (app_trm_cases (inst t benv)).
    rewrite H2 in H1.
    apply retypable_trm_app.
    inversions H1; try discriminate.
    apply* typing_app.
    simpl gc_lower in *.
    apply* retypable_clos.
  destruct H2.
  rewrite H2 in H1; simpl in H1.
  inversions H1; try discriminate; clear H1.
  destruct t; try discriminate.
    simpl.
    rewrite* <- inst_n.
    rewrite H2; simpl*.
  simpl.
  inversions* H2.
Qed.

Lemma clos_ok_nth : forall benv n0,
  list_forall clos_ok benv ->
  clos_ok (nth n0 benv clos_def).
Proof.
  intros.
  destruct (le_lt_dec (length benv) n0).
    rewrite* nth_overflow.
  apply (list_forall_out H).
  apply* nth_In.
Qed.
Hint Resolve clos_ok_nth.

Lemma clos_ok_trm : forall benv K t T,
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  K;E |Gc|= inst t benv ~: T ->
  trm2app t = None ->
  clos_ok (trm2clos benv fenv t).
Proof.
  intros.
  destruct t; simpl*; try discriminate.
    inversions H1; try discriminate.
    destruct (proj2 fenv_ok _ _ H6) as [cl [B Typ]].
    rewrite* B.
   inversions* H0.
  constructor; auto.
  simpl; omega.
Qed.

Lemma term_const_app : forall c cls,
  list_forall clos_ok cls ->
  term (const_app c (List.map clos2trm cls)).
Proof.
  intros.
  unfold const_app.
  cut (term (trm_cst c)).
    generalize (trm_cst c).
    induction H; simpl*.
  auto.
Qed.

Hint Resolve term_const_app.

Lemma clos2trm_const_eq : forall cl c tl,
  clos2trm cl = const_app c tl ->
  exists args, cl = clos_const c args /\ tl = List.map clos2trm args.
Proof.
  unfold const_app; intros.
  destruct cl.
    induction tl using rev_ind. discriminate.
    rewrite fold_left_app in H; discriminate.
  simpl in H.
  destruct (const_app_eq _ _ _ _ H). subst.
  exists* l.
Qed.

Inductive result_ok : eval_res -> Prop :=
  | rok_R : forall n cl, clos_ok cl -> result_ok (Result n cl)
  | rok_I : forall fl, list_forall frame_ok fl -> result_ok (Inter fl).

Hint Constructors result_ok.

Lemma clos_ok_get : forall v,
  clos_ok match get v fenv with
          | Some x => x
          | None => clos_def
          end.
Proof.
  intros.
  case_eq (get v fenv); intros.
    apply (proj1 fenv_ok _ _ (binds_in H)).
  auto.
Qed.
Hint Resolve clos_ok_get.

Lemma clos_ok_nil : forall c, clos_ok (clos_const c nil).
Proof.
  intros; constructor; auto. simpl; omega.
Qed.
Hint Resolve clos_ok_nil.

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

Hint Extern 1 (clos_ok ?x) => solve [list_forall_find clos_ok x].

Lemma trm2clos_regular : forall benv t,
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  clos_ok (trm2clos benv fenv t).
Proof.
  intros; destruct t; simpl*.
  inversions* H0.
Qed.
Hint Resolve trm2clos_regular.

Lemma eval_regular : forall h fl benv args t,
  list_forall clos_ok args ->
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  list_forall frame_ok fl ->
  result_ok (eval fenv h benv args t fl).
Proof.
  induction h; introv; intros Hargs Hbenv Ht Hfl.
    simpl*.
  simpl.
  case_eq (trm2app t); intros.
    destruct p.
    assert (closed_n (length benv) t1 /\ closed_n (length benv) t0).
      destruct t; try discriminate; simpl in H; inversions H; inversions* Ht.
    destruct H0.
    apply* IHh.
  destruct args.
    destruct fl.
      constructor. destruct t; simpl*. inversions* Ht.
    destruct f.
    inversions Hfl; clear Hfl.
    inversions H3; clear H3.
    apply* IHh.
  poses Hreg (trm2clos_regular Hbenv Ht).
  case_eq (trm2clos benv fenv t); introv R1;
    rewrite R1 in Hreg; inversions* Hreg; clear Hreg.
  case_eq (length l + length (c::args)); introv R2.
    destruct fl.
      constructor. constructor; auto.
      rewrite app_length; rewrite R2; auto with arith.
    destruct f.
    inversions Hfl; clear Hfl.
    inversions H5; clear H5.
    apply* IHh.
    constructor; auto.
    constructor; auto.
    rewrite app_length; rewrite R2; auto with arith.
  destruct (le_lt_dec (Const.arity c0) n); simpl.
    case_eq (l ++ c :: args); introv R3.
      destruct l; discriminate.
    case_eq (cut (Const.arity c0) l1); introv R4.
    case_eq (SH.reduce_clos c0 (c1 :: l2)); introv R5.
    assert (list_forall clos_ok (c1::l2++l3)).
      puts (le_n_S _ _ l0).
      rewrite <- R2 in H0.
      rewrite <- app_length in H0.
      rewrite R3 in H0.
      simpl in H0.
      puts (le_S_n _ _ H0).
      destruct (cut_ok _ H1 R4).
      subst l1.
      rewrite* <- R3.
    forward~ (SH.reduce_clos_regular R5) as Hreg.
    inversions Hreg; clear Hreg.
    inversions H6; apply* IHh.
    apply* list_forall_app.
  rewrite <- app_length in R2.
  destruct fl.
    constructor.
    constructor; auto.
    omega.
  destruct f.
  inversions Hfl; clear Hfl.
  inversions H5; clear H5.
  apply* IHh.
  constructor; auto.
  constructor; auto.
  omega.
Qed.
    
Theorem eval_sound_rec : forall h fl benv args K t T,
  list_forall clos_ok args ->
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  list_forall frame_ok fl ->
  K ; E |Gc|=
    stack2trm (app2trm (inst t benv) args) fl ~: T ->
  K ; E |Gc|= res2trm (eval fenv h benv args t fl) ~: T.
Proof.
  induction h; introv; intros Hargs Hbenv Ht Hfl Typ.
    simpl*.
  simpl.
  case_eq (trm2app t); intros.
    destruct p as [t1 t2].
    assert (closed_n (length benv) t1 /\ closed_n (length benv) t2)
      by (destruct t; try discriminate; inversions H; inversions* Ht).
    apply* IHh.
    unfold app2trm; simpl.
    destruct H0.
    rewrite* is_bvar_term.
    destruct t; try discriminate; inversions H.
      apply Typ.
    refine (retypable_stack2trm _ _ _ _ Typ); auto.
    apply* retypable_app2trm.
    apply retypable_trm_app.
  destruct args as [|arg args].
    destruct fl; simpl in *.
      refine (retypable_clos _ Ht H Typ).
    destruct f as [benv' app' t'].
    unfold app2trm at 2 3 in Typ; simpl in Typ.
    rewrite is_bvar_term in Typ; auto.
    inversions Hfl; clear Hfl.
    inversions H3; clear H3.
    apply* IHh; clear IHh.
    refine (retypable_stack2trm _ _ _ _ Typ); auto.
    unfold app2trm; simpl.
    apply* retypable_app2trm.
    apply retypable_app_trm2.
    apply (retypable_clos _ Ht H).
  poses Hl (trm2clos_regular Hbenv Ht).
  case_eq (trm2clos benv fenv t); introv R1; rewrite R1 in Hl.
    inversions Hargs; clear Hargs.
    inversions Hl.
    apply* IHh; clear IHh.
    refine (retypable_stack2trm _ _ _ _ Typ); auto.
      unfold app2trm; simpl.
      apply* is_abs_app2trm.
    unfold app2trm; simpl.
    apply* retypable_app2trm.
    intro; intros.
    clear Typ.
    poses Typ (retypable_app_clos _ _ Ht H H0); clear H0.
    rewrite R1 in Typ.
    simpl in Typ.
    unfold inst, trm_inst; simpl.
    rewrite <- trm_inst_rec_more;
      [|rewrite* map_length | apply* list_forall_map].
    set (t1 := trm_inst_rec 1 (List.map clos2trm l) t0) in *.
    clear H fl Hfl; inversions Typ; try discriminate.
    destruct (var_fresh (L2 \u trm_fv t1)).
    clear Typ; forward~ (H9 x) as Typ; clear H9; simpl gc_raise in Typ.
    fold (trm_open t1 (clos2trm arg)).
    rewrite* (@trm_subst_intro x).
    replace E with (E & empty) by simpl*.
    apply* typing_trm_subst.
    simpl*.
  simpl length.
  rewrite <- plus_n_Sm.
  case_eq (is_abs (inst t benv)); intros.
    elimtype False.
    destruct t; try discriminate.
    simpl in R1.
    rewrite inst_n in H0; auto.
    rewrite R1 in H0.
    clear -H0.
    simpl in H0. unfold const_app in H0.
    induction (List.map clos2trm l) using rev_ind. discriminate.
    rewrite fold_left_app in H0. discriminate.
  assert (Typ': K; E |Gc|= stack2trm
    (app2trm (clos2trm (trm2clos benv fenv t)) (arg :: args)) fl ~:  T).
    refine (retypable_stack2trm _ _ _ _ Typ); auto.
    unfold app2trm in *; simpl in *.
    clear Typ; intro; introv Typ.
    refine (retypable_app2trm _ _ _ Typ); auto.
      apply* retypable_app_clos.
    inversions* Hargs.
  clear Typ; rewrite R1 in Typ'; simpl in Typ'.
  destruct (le_lt_dec (Const.arity c) (length l + length args)).
    simpl.
    case_eq (l ++ arg :: args); intros. destruct l; discriminate.
    case_eq (cut (Const.arity c) l1); intros.
    assert (Const.arity c <= length l1).
      clear -l0 H1.
      puts (f_equal (@length clos) H1).
      rewrite app_length in H.
      simpl in H.
      omega.
    destruct (cut_ok _ H5 H2).
    subst.
    assert (Hok: list_forall clos_ok (c0 :: l2 ++ l3)).
      rewrite <- H1.
      inversions* Hl.
    assert (Hok2: list_forall clos_ok (c0 :: l2)) by auto.
    assert (Hok3: list_forall clos_ok l3) by auto.
    poses Hred (@SH.reduce_clos_sound c (c0 :: l2)
      (conj (f_equal S (sym_equal H6)) Hok2)).
    case_rewrite R (SH.reduce_clos c (c0 :: l2)).
    replace (app2trm (const_app c (List.map clos2trm l)) (arg :: args))
      with (app2trm (const_app c (List.map clos2trm (c0 :: l2))) l3)
        in Typ'.
      assert (K; E |Gc|=
        stack2trm (app2trm (clos2trm c1) (l1 ++ l3)) fl ~: T).
        assert (Habs: forall l, is_abs (const_app c l) = false).
          clear; intros; destruct (const_app_inv c l) as [eq|[t1[t2 eq]]];
            rewrite* eq.
        rewrite app2trm_app.
        refine (retypable_stack2trm _ _ _ _ Typ'); auto.
        apply* retypable_app2trm.
        intro; intros.
        assert (Typ: K0; E |Gc|=
          fold_left trm_app (List.map clos2trm l1) (clos2trm c1) ~: T0).
          rewrite (proj33 (Hred _ _ _ H7)).
          apply* SH.delta_typed.
        clear -Typ.
        unfold app2trm.
        gen T0; induction l1 using rev_ind; simpl; intros. auto.
        rewrite map_app in *; rewrite fold_left_app in *; simpl in *.
        apply retypable_trm_app.
        inversions* Typ; discriminate.
      destruct (typing_stack2trm_inv _ _ Typ') as [T' [K' Typ'']].
        apply* is_bvar_term.
      destruct (typing_app2trm_inv _ _ Typ'') as [T'' Typ3].
        unfold const_app. clear.
        cut (is_abs (trm_cst c) = false); auto.
        generalize (trm_cst c); induction (List.map clos2trm (c0::l2));
          intros; simpl*.
      destruct (Hred _ _ _ Typ3) as [Hcl' [Hl' _]].
      destruct c1; inversions Hcl'; apply* IHh; clear IHh;
        repeat apply* list_forall_app.
      unfold inst; rewrite trm_inst_nil.
      rewrite app2trm_app.
      rewrite* app2trm_cst.
    do 2 rewrite <- app2trm_cst.
    do 2 rewrite <- app2trm_app.
    rewrite H1. simpl*.
  simpl.
  destruct fl.
    simpl in *.
    rewrite <- app2trm_cst.
    rewrite app2trm_app.
    rewrite* app2trm_cst.
  destruct f as [benv' app' t'].
  inversions Hfl; clear Hfl.
  inversions H6; clear H6.
  apply* IHh; clear IHh.
    constructor; auto.
    inversions Hl.
    constructor; auto.
    rewrite app_length. simpl; omega.
  simpl in Typ'.
  case_rewrite R
    (is_bvar (app2trm (const_app c (List.map clos2trm l)) (arg :: args))).
    unfold app2trm in R.
    clear -R; induction args using rev_ind; simpl in R.
      rewrite is_bvar_app_trm in R. discriminate.
    rewrite map_app in R; rewrite fold_left_app in R; simpl in R.
    rewrite is_bvar_app_trm in R. discriminate.
  simpl in Typ'.
  rewrite <- app2trm_cst in Typ'.
  rewrite <- app2trm_app in Typ'.
  unfold app2trm in Typ'.
  unfold app2trm; simpl.
  rewrite <- app2trm_cst.
  apply Typ'.
Qed.

Theorem eval_sound : forall h K t T,
  K ; E |Gc|= t ~: T ->
  K ; E |Gc|= res2trm (eval fenv h nil nil t nil) ~: T.
Proof.
  intros.
  apply* eval_sound_rec.
  unfold app2trm; simpl.
  unfold inst; rewrite* trm_inst_nil.
Qed.

Definition eval_restart h fl res :=
  match res with
  | Inter nil => Inter fl
  | Inter (Frame benv args t :: fl') =>
    eval fenv h benv args t (fl' ++ fl)
  | Result h' c =>
      match fl with
      | nil => Result (h'+h) c
      | Frame benv' app' t :: rem => eval fenv (h'+h) benv' (c::app') t rem
      end
  end.

Lemma eval_restart_ok : forall h' fl' h benv args t fl,
  eval_restart h' fl' (eval fenv h benv args t fl) =
  eval fenv (h+h') benv args t (fl++fl').
Proof.
  induction h; simpl; intros. auto.
  destruct (trm2app t).
    destruct p. apply* IHh.
  destruct args.
    destruct* fl.
    destruct f.
    simpl*.
  destruct* (trm2clos benv fenv t).
  destruct (length l + length (c::args)).
    destruct* fl. destruct f. simpl*.
  destruct (le_lt_dec (Const.arity c0) n); simpl.
    destruct (l ++ c :: args).
      destruct (SH.reduce_clos c0 nil).
      destruct* c1.
    destruct (cut (Const.arity c0) l1).
    destruct (SH.reduce_clos c0 (c1 :: l2)).
    destruct* c2.
  destruct* fl.
  destruct f. simpl*.
Qed.
    
Lemma eval_restart_ok' : forall h' fl' h benv args t,
  eval_restart h' fl' (eval fenv h benv args t nil) =
  eval fenv (h+h') benv args t fl'.
Proof.
  intros.
  apply* eval_restart_ok.
Qed.

Lemma eval_restart_step : forall h c,
  eval_restart 1 nil (Result h c) = Result (S h) c.
Proof.
  intros; simpl. rewrite plus_comm; reflexivity.
Qed.

Require Import Relations.

Fixpoint untyped (t:trm) : trm :=
  match t with
  | trm_let t1 t2 => trm_app (trm_abs (untyped t2)) (untyped t1)
  | _ => t
  end.

Definition app_trm' t1 t2 :=
  match t1 with
  | trm_abs t => t ^^ t2
  | _ => trm_app t1 t2
  end.

Definition app2trm' t args :=
  List.fold_left trm_app (List.map clos2trm args) t.

Fixpoint stack2trm' t0 (l : list frame) {struct l} : trm :=
  match l with
  | nil => t0
  | Frame benv args t :: rem =>
    let t1 := inst t benv in
    let t2 := if is_bvar t0 then t1 else trm_app t1 t0 in
    stack2trm' (app2trm' t2 args) rem
  end.

Definition res2trm' res :=
  match res with
  | Result _ cl => clos2trm cl
  | Inter l => stack2trm' trm_def l
  end.

Lemma stack2trm'_app : forall l1 l2 t,
  stack2trm' t (l1 ++ l2) = stack2trm' (stack2trm' t l1) l2.
Proof.
  induction l1; intros. simpl*.
  simpl. destruct a.
  destruct (is_bvar t); rewrite* IHl1.
Qed.

Definition is_app t := match t with trm_app _ _ => true | _ => false end.
Lemma trm_inst_inv_app : forall benv t t1 t2,
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  trm_app (trm_abs t1) t2 = inst t benv ->
  is_app t = true.
Proof.
  introv Hbenv Ht H.
  destruct t; try discriminate; auto.
  rewrite inst_n in H; auto.
  puts (clos_ok_nth n Hbenv).
  set (cl := nth n benv clos_def) in *. clearbody cl.
  inversions H0. discriminate.
  simpl in H.
  clear -H. elimtype False.
  induction (List.map clos2trm cls) using rev_ind. discriminate.
  unfold const_app in H. rewrite fold_left_app in H.
  inversions H.
  clear -H1.
  induction l using rev_ind. discriminate.
  rewrite fold_left_app in H1; discriminate.
Qed.

Lemma inst_clos2trm : forall t n benv,
  t = inst (trm_bvar n) benv ->
  t = clos2trm (nth n benv clos_def) \/ t = trm_bvar n.
Proof.
  intros.
  unfold inst, trm_inst in H. simpl in H. rewrite <- minus_n_O in H.
  destruct (le_lt_dec (length (List.map clos2trm benv)) n).
    right. rewrite nth_overflow in H; auto.
  rewrite <- (map_nth clos2trm).
  left.
  rewrite (nth_indep _ _ (trm_bvar n) l). auto.
Qed.

Lemma eval_cst_args : forall c benv args t,
  length args <= Const.arity c ->
  eval fenv 1 benv nil t nil = Result 0 (clos_const c nil) ->
  eval fenv 1 benv args t nil = Result 0 (clos_const c args).
Proof.
  simpl; intros.
  destruct (trm2app t).
    destruct p. discriminate.
  destruct* args.
  inversions H0.
  rewrite H2. simpl.
  destruct* (le_lt_dec (Const.arity c) (length args)).
  elimtype False; simpl in *; omega.
Qed.

Lemma value_arity : forall n c l,
  valu n (const_app c l) ->
  Const.arity c = length l + n.
Proof.
  intros.
  unfold const_app in H.
  gen n; induction l using rev_ind; simpl; intros.
    inversions* H.
  rewrite fold_left_app in H. simpl in H.
  inversions H.
  puts (IHl _ H3).
  rewrite app_length. simpl. omega.
Qed.

Lemma eval_value : forall benv t,
  value (inst t benv) ->
  exists h, exists cl, eval fenv h benv nil t nil = Result 0 cl
    /\ clos2trm cl = inst t benv.
Proof.
  intros benv t [n Val].
  assert (Hlen: length (@nil clos) <= n) by (simpl; omega).
  revert Hlen.
  remember (inst t benv) as t1.
  replace t1 with (fold_left trm_app (List.map clos2trm nil) t1) by reflexivity.
  generalize (@nil clos).
  gen t; induction Val; intros.
      destruct t; try discriminate; exists 1; simpl;
        destruct l; simpl in Hlen; try solve [elimtype False; omega];
          esplit; split*.
      simpl.
      destruct (inst_clos2trm _ _ Heqt1). congruence. discriminate.
    exists 1; exists (clos_const c l).
    split*.
    apply* eval_cst_args.
    simpl.
    destruct t; try discriminate; simpl.
      destruct (inst_clos2trm _ _ Heqt1); try discriminate.
      destruct (nth n benv clos_def); try discriminate.
      destruct (clos2trm_const_eq _ c nil (sym_equal H)) as [cl [eq1 eq2]].
      inversions eq1.
      destruct* cl; discriminate.
    inversions* Heqt1.
  destruct t; try discriminate.
    destruct (inst_clos2trm _ _ Heqt1); try discriminate.
    exists 1; simpl.
    destruct l. esplit; split*.
    destruct (nth n0 benv clos_def); try discriminate.
    simpl.
    rewrite <- plus_n_Sm.
    destruct (le_lt_dec (Const.arity c0) (length l0 + length l)).
      elimtype False.
      puts (value_app Val1 Val2).
      rewrite H in H0. simpl in *.
      puts (value_arity _ _ H0).
      rewrite map_length in H1.
      omega.
    simpl.
    esplit; split*.
    simpl. unfold const_app. rewrite map_app; rewrite fold_left_app. simpl.
    rewrite* H.
  unfold trm_inst in Heqt1; simpl in Heqt1.
  inversions Heqt1; clear Heqt1.
  destruct* (IHVal2 t4 (refl_equal _) nil) as [h2 [cl2 [Eq2 Eq2']]];
    clear IHVal2.
    simpl; omega.
  destruct* (IHVal1 t3 (refl_equal _) (cl2::l)) as [h1 [cl1 [Eq1 Eq1']]];
    clear IHVal1.
    simpl; omega.
  exists (S h2+h1).
  simpl.
  rewrite <- eval_restart_ok'.
  rewrite Eq2.
  simpl.
  rewrite Eq1.
  esplit; split*.
  rewrite Eq1'. simpl. rewrite* Eq2'.
Qed.

Lemma value_const_app : forall c tl,
  list_forall value tl ->
  length tl <= Const.arity c ->
  value (const_app c tl).
Proof.
  intros.
  exists (Const.arity c - length tl).
  induction tl using rev_ind. simpl. rewrite <- minus_n_O.
    apply value_cst.
  rewrite app_length. simpl.
  unfold const_app; rewrite fold_left_app.
  assert (value x) by apply* (list_forall_out H).
  destruct H1.
  apply* value_app.
  rewrite app_length in H0; simpl in H0.
  replace (S (Const.arity c - (length tl +1))) with (Const.arity c - length tl)
    by omega.
  apply* IHtl.
  omega.
Qed.

Definition check_const_app t :=
  match t with
  | trm_cst _ | trm_app _ _ => true
  | _ => false
  end.
Lemma is_const_app : forall c tl, check_const_app (const_app c tl) = true.

Proof.
  intros.
  unfold const_app.
  destruct tl using rev_ind. auto.
  rewrite* fold_left_app.
Qed.

Lemma eval_const : forall benv c t tl args,
  inst t benv = const_app c tl ->
  value (inst t benv) ->
  list_forall value tl ->
  exists cls1, exists cls2, exists t1, exists h,
    trm2clos benv fenv t1 = clos_const c cls1 /\ trm_fv t1 = {} /\
    eval fenv h benv args t nil = Inter (Frame benv (cls2 ++ args) t1 :: nil)
    /\ List.map clos2trm (cls1 ++ cls2) = tl.
Proof.
  introv HI Val Htl.
  gen_eq (inst t benv) as t'.
  gen args t tl.
  destruct Val as [n Val].
  induction Val; simpl; intros.
      puts (is_const_app c tl).
      rewrite <- HI in H1; discriminate.
    destruct t; try discriminate.
      destruct (inst_clos2trm _ _ H); try discriminate.
      case_rewrite R1 (nth n benv clos_def).
      rewrite H0 in HI.
      simpl in HI.
      destruct (const_app_eq _ _ _ _ HI); subst; clear HI.
      simpl in H0.
      destruct (const_app_inv c (List.map clos2trm l)).
        rewrite H1 in *. inversions H0.
        esplit; exists (@nil clos); exists (trm_bvar n); exists 0; split*.
        split*. destruct* l. discriminate.
      destruct H1 as [t1 [t2 eq]].
      rewrite eq in H0; discriminate.
    inversions H; clear H.
    destruct (const_app_inv c tl).
      rewrite H in HI; inversions HI.
      exists (@nil clos); exists (@nil clos); esplit;
        exists 0; split; try split*; simpl*.
    destruct H as [t1 [t2 eq]].
    rewrite eq in HI; discriminate.
  clear IHVal2.
  destruct t; try discriminate.
    destruct (inst_clos2trm _ _ H); try discriminate.
    case_rewrite R1 (nth n0 benv clos_def).
    rewrite H0 in HI. simpl in HI.
    destruct (const_app_eq _ _ _ _ HI). subst.
    exists l; exists (@nil clos); exists (trm_bvar n0); exists 0; split*.
    split. simpl*.
    rewrite* <- app_nil_end.
  assert (value t2) by (esplit; auto*).
  unfold trm_inst in H; simpl in H. inversions H; clear H.
  destruct (eval_value _ _ H0) as [h2 [cl2 [eq2 eq2']]].
  induction tl using rev_ind; try discriminate.
  clear IHtl.
  unfold const_app in HI; rewrite fold_left_app in HI.
  simpl in HI; inversions HI; clear HI.
  destruct* (IHVal1 (cl2::args) t3 tl)
    as [cls1 [cls2 [t1 [h1 [eq1 [fv1 [eq1' eq1'']]]]]]].
  exists cls1. exists (cls2 ++ cl2 :: nil).
  exists t1; exists (S h2 + h1).
  split*.
  split; simpl*.
  rewrite <- eval_restart_ok'.
  rewrite eq2. simpl.
  rewrite app_ass.
  split*.
  rewrite <- app_ass.
  rewrite map_app.
  rewrite eq1''.
  simpl. rewrite* eq2'.
Qed.

Lemma app_eq_inv : forall (A:Set) (l3 l4 l1 l2 : list A),
  length l1 = length l2 ->
  l1 ++ l3 = l2 ++ l4 ->
  l1 = l2 /\ l3 = l4.
Proof.
  induction l1; destruct l2; intros; try discriminate. simpl in H0; auto.
  simpl in H0; inversions H0.
  simpl in H; inversions H.
  destruct* (IHl1 l2).
  subst*.
Qed.

Lemma closed_n_inst_rec : forall l t m,
  closed_n m (trm_inst_rec m l t) -> closed_n (m + length l) t.
Proof.
  unfold trm_inst. induction t; simpl; intros; auto.
     constructor.
     destruct (le_lt_dec m n); try omega.
     destruct (le_lt_dec (m + length l) n); try omega.
     rewrite nth_overflow in H; try omega.
     inversions H. omega.
    constructor.
    apply (IHt (S m)).
    inversions* H.
   inversions H.
   constructor; auto.
   apply* (IHt2 (S m)).
  inversions* H.
Qed.

Lemma closed_n_inst : forall l t,
  closed_n 0 (inst t l) -> closed_n (length l) t.
Proof.
  intros.
  rewrite <- (map_length clos2trm).
  refine (closed_n_inst_rec _ _ H).
Qed.
Hint Immediate closed_n_inst.

Section Forall2.
Variables A B : Set.
Variable P : A -> B -> Prop.

Inductive list_forall2 : list A -> list B -> Prop :=
  | list_forall2_nil : list_forall2 nil nil
  | list_forall2_cons : forall a b la lb,
      P a b ->
      list_forall2 la lb ->
      list_forall2 (a::la) (b::lb).

Hint Constructors list_forall2.

Lemma list_forall2_sound : forall la lb,
  list_forall2 la lb -> For_all2 P la lb.
Proof.
  induction 1; simpl*.
Qed.

Lemma list_forall2_complete : forall la lb,
  For_all2 P la lb -> list_forall2 la lb.
Proof.
  induction la; intros; destruct lb; try contradiction; auto.
  simpl in H; destruct* H.
Qed.

Lemma list_forall2_app : forall l1 l2 l3 l4,
  list_forall2 l1 l3 -> list_forall2 l2 l4 ->
  list_forall2 (l1 ++ l2) (l3 ++ l4).
Proof.
  intros until 1.
  revert l2 l4.
  induction H; simpl*.
Qed.

Lemma list_forall2_app_inv : forall l2 l4 l1 l3,
  list_forall2 (l1 ++ l2) (l3 ++ l4) ->
  length l1 = length l3 ->
  list_forall2 l1 l3 /\ list_forall2 l2 l4.
Proof.
  induction l1; intros; destruct l3; try discriminate; simpl in *.
    auto.
  inversions H.
  destruct* (IHl1 l3).
Qed.

Lemma list_forall2_length : forall l1 l2,
  list_forall2 l1 l2 -> length l1 = length l2.
Proof.
  induction 1; simpl*.
Qed.
End Forall2.

Hint Constructors list_forall2.
Hint Resolve list_forall2_sound list_forall2_app list_forall2_length.
Hint Immediate list_forall2_complete.

Inductive equiv_clos : clos -> clos -> Prop :=
  | Equiv_clos_abs : forall t benv t' benv',
      inst (trm_abs t) benv = inst (trm_abs t') benv' ->
      equiv_clos (clos_abs t benv) (clos_abs t' benv')
  | Equiv_clos_const : forall c args args',
      list_forall2 equiv_clos args args' ->
      equiv_clos (clos_const c args) (clos_const c args').
Hint Constructors equiv_clos.

Lemma equiv_cl : forall cl1 cl2,
  equiv_clos cl1 cl2 -> clos2trm cl1 = clos2trm cl2.
Proof.
  induction cl1 using clos_ind'; intros; inversions H0; simpl*.
  apply f_equal.
  clear -H H4.
  gen args'; induction H; intros; inversions H4; simpl*.
  rewrite* (IHlist_forall lb).
  rewrite* (H0 b).
Qed.
Hint Resolve equiv_cl.

Lemma equiv_cls : forall cls1 cls2,
  list_forall2 equiv_clos cls1 cls2 ->
  List.map clos2trm cls1 = List.map clos2trm cls2.
Proof.
  induction 1; simpl; intros; auto*.
  apply* f_equal2.
Qed.

Definition equiv_frame f1 f2 :=
  inst (frm_trm f1) (frm_benv f1) = inst (frm_trm f2) (frm_benv f2) /\
  list_forall2 equiv_clos (frm_app f1) (frm_app f2).

(*
Lemma app2trm'_equiv : forall args args' t,
  list_forall2 equiv_clos args args' ->
  app2trm' t args = app2trm' t args'.
Proof.
  intros; revert t; induction H; intros; auto.
  unfold app2trm'; simpl.
  rewrite H.
  apply* IHlist_forall2.
Qed.

Lemma stack2trm'_equiv : forall fl fl' t,
  term t ->
  list_forall frame_ok fl ->
  list_forall2 equiv_frame fl fl' ->
  stack2trm' t fl = stack2trm' t fl'.
Proof.
  introv Ht Hfl Eqfl; gen fl' t.
  induction Hfl; intros; inversions Eqfl; clear Eqfl. auto.
  simpl.
  rewrite* is_bvar_term.
  destruct x; destruct b.
  inversions H2; clear H2.
  simpl in H0,H1.
  rewrite* (IHHfl lb).
    rewrite <- H0.
    apply* f_equal2.
    apply* app2trm'_equiv.
  inversions H; clear H.
  apply* term_fold_app.
  apply* list_forall_map.
  Search term.
Qed.
*)

Parameter reduce_clos_ext : forall c args args',
  list_forall2 equiv_clos args args' ->
  let (cl,arg) := SH.reduce_clos c args in
  let (cl',arg') := SH.reduce_clos c args' in
  equiv_clos cl cl' /\ list_forall2 equiv_clos arg arg'.

Lemma const_app_app : forall c l l',
  const_app c (l++l') = fold_left trm_app l' (const_app c l).
Proof.
  intros. unfold const_app. apply fold_left_app.
Qed.

Lemma list_forall2_refl : forall (A:Set) (P:A->A->Prop),
  (forall x, P x x) ->
  forall l, list_forall2 P l l.
Proof.
  induction l; simpl*.
Qed.
Hint Resolve list_forall2_refl.

Lemma equiv_clos_refl : forall cl, equiv_clos cl cl.
Proof.
  induction cl using clos_ind'; constructor; auto.
  induction H; auto.
Qed.
Hint Resolve equiv_clos_refl.

Lemma equiv_cl_nth : forall n cls1 cls2,
  list_forall2 equiv_clos cls1 cls2 ->
  equiv_clos (nth n cls1 clos_def) (nth n cls2 clos_def).
Proof.
  intros; revert n; induction H; intros. simpl*.
  destruct n; simpl*.
Qed.

(*
Lemma res2trm'_equiv : forall t benv args fl t' benv' args' fl',
  inst t benv = inst t' benv' ->
  list_forall2 equiv_clos args args' ->
  list_forall2 equiv_frame fl fl' ->
  closed_n (length benv) t ->
  list_forall clos_ok args ->
  list_forall clos_ok benv ->
  list_forall frame_ok fl ->
  stack2trm' (app2trm' (inst t benv) args) fl =
  stack2trm' (app2trm' (inst t' benv') args') fl'.
Proof.
  introv Eqt Eqargs Eqfl. intros Ht Hargs Hbenv Hfl.
  rewrite <- Eqt.
  rewrite (@stack2trm'_equiv fl fl'); auto.
    apply f_equal2; auto.
    apply* app2trm'_equiv.
  apply* term_fold_app.
  apply* list_forall_map.
Qed.
*)

Lemma equiv_trm_abs : forall a b t t0 l l0,
  inst (trm_abs t) l = inst (trm_abs t0) l0 ->
  equiv_clos a b ->
  closed_n (1+length l) t ->
  closed_n (1+length l0) t0 ->
  list_forall clos_ok l ->
  list_forall clos_ok l0 ->
  inst t (a :: l) = inst t0 (b :: l0).
Proof.
  unfold inst, trm_inst; simpl; intros.
  rewrite (equiv_cl H0).
  rewrite* <- trm_inst_rec_more.
  rewrite* <- trm_inst_rec_more.
  inversions* H.
  rewrite* map_length.
  apply* list_forall_map.
  rewrite* map_length.
  apply* list_forall_map.
Qed.
Hint Resolve equiv_trm_abs.

Inductive eval_cont : clos -> list frame -> eval_res -> Prop :=
  | Eval_nil : forall cl,
      eval_cont cl nil (Result 0 cl)
  | Eval_Frame : forall cl benv args t fl,
      eval_cont cl (Frame benv args t :: fl)
                    (Inter (Frame benv (cl::args) t :: fl)).
Hint Constructors eval_cont.

Lemma eval_cont_ok : forall cl fl,
  eval_cont cl fl (eval_restart 0 fl (Result 0 cl)).
Proof.
  intros; simpl.
  destruct fl. auto.
  destruct f; auto.
Qed.

Definition reduce_clos c args args' :=
  match SH.reduce_clos c args with
  | (clos_const c' args'', args3) =>
    Frame nil (args''++args3++args') (trm_cst c')
  | (clos_abs t1 benv, args3) =>
    Frame benv (args3++args') (trm_abs t1)
  end.

Inductive eval_spec : eval_res -> eval_res -> Prop :=
  | Eval_trmapp : forall benv args t t1 t2 fl,
      trm2app t = Some (t1, t2) ->
      eval_spec (Inter (Frame benv args t :: fl))
        (Inter (Frame benv nil t2 :: Frame benv args t1 :: fl))
  | Eval_clos : forall benv args t fl r,
      trm2app t = None ->
      eval_cont (trm2clos benv fenv t) fl r ->
      eval_spec (Inter (Frame benv args t :: fl)) r
  | Eval_abs : forall benv args t t1 benv' cl fl,
      trm2clos benv fenv t = clos_abs t1 benv' ->
      eval_spec (Inter (Frame benv (cl::args) t :: fl))
        (Inter (Frame (cl::benv') args t1 :: fl))
  | Eval_const : forall benv args t c cls1 cls2 cls3 fl,
      cls1 ++ args = cls2 ++ cls3 ->
      length cls2 = S(Const.arity c) ->
      eval_spec (Inter (Frame benv args t :: fl))
        (Inter (reduce_clos c cls2 cls3 :: fl))
  | Eval_const' : forall benv args t c cls1 fl r,
      length (cls1 ++ args) <= Const.arity c ->
      eval_cont (clos_const c (cls1++args)) fl r ->
      eval_spec (Inter (Frame benv args t :: fl)) r
  | Eval_stop : forall n cl,
      eval_spec (Result n cl) (Result (S n) cl)
  | Eval_error : eval_spec (Inter nil) (Inter nil).

Hint Constructors eval_cont eval_spec.

Lemma eval_spec_ok : forall r, eval_spec r (eval_restart 1 nil r).
Proof.
  intros.
  destruct r; simpl.
    rewrite plus_comm; simpl*.
  destruct l as [|[benv args t] fl]. auto.
  rewrite <- app_nil_end.
  case_eq (trm2app t); introv R1.
    destruct* p.
  destruct args.
    apply* Eval_clos.
    destruct* fl.
    destruct* f.
  case_eq (trm2clos benv fenv t); introv R2.
    auto.
  case_eq (length l + length (c::args)); introv R3.
    destruct l; discriminate.
  destruct (le_lt_dec (Const.arity c0) n); simpl.
    case_eq (l++c::args); introv R4.
      destruct l; discriminate.
    case_eq (cut (Const.arity c0) l1); introv R5.
    assert (Const.arity c0 <= length l1). 
      puts (f_equal (@length _) R4).
      simpl in H. rewrite app_length in H. omega.
    destruct (cut_ok _ H R5).
    subst.
    replace (c1::l2++l3) with ((c1::l2)++l3) in R4 by reflexivity.
    puts (Eval_const benv (c::args) t _ _ _ fl R4 (f_equal S H0)).
    unfold reduce_clos in H1.
    case_rewrite R6 (SH.reduce_clos c0 (c1::l2)).
    destruct* c2.
  apply* Eval_const'.
    unfold lt in l0.
    rewrite <- R3 in l0.
    rewrite* app_length.
  destruct* fl.
  destruct* f.
Qed.

Inductive equiv_result : eval_res -> eval_res -> Prop :=
  | Equiv_result : forall n cl1 cl2,
      equiv_clos cl1 cl2 ->
      equiv_result (Result n cl1) (Result n cl2)
  | Equiv_inter  : forall fl1 fl2,
      list_forall2 equiv_frame fl1 fl2 ->
      equiv_result (Inter fl1) (Inter fl2).
Hint Constructors equiv_result.

Lemma eval_restart_ok'' : forall h' h benv args t fl,
  eval_restart h' nil (eval fenv h benv args t fl) =
  eval fenv (h+h') benv args t fl.
Proof.
  intros.
  rewrite eval_restart_ok. rewrite* <- app_nil_end.
Qed.

Lemma clos2trm_equiv : forall cl1 cl2,
  clos2trm cl1 = clos2trm cl2 ->
  equiv_clos cl1 cl2.
Proof.
  induction cl1 using clos_ind'; destruct cl2; simpl; intros.
        constructor; auto.
      puts (is_const_app c (List.map clos2trm l0)).
      rewrite <- H0 in H1; discriminate.
    puts (is_const_app c (List.map clos2trm l)).
    rewrite H0 in H1; discriminate.
  destruct (const_app_eq _ _ _ _ H0).
  subst c0; constructor.
  clear -H H2.
  gen l0; induction H; intros; destruct l0; try discriminate. auto.
  inversions H2.
  auto*.
Qed.
Hint Immediate clos2trm_equiv.

Hint Extern 1 (equiv_result _ _) => solve [constructor; simpl; auto].
Hint Extern 1 (list_forall2 _ _ _) => solve [constructor; simpl; auto].
Hint Extern 1 (equiv_clos _ _) => solve [constructor; simpl; auto].
Hint Extern 1 (equiv_frame _ _) => solve [constructor; simpl; auto].

(*
Lemma eval_bisim_app : forall t tl t' benv benv' args args' la lb,
  inst (fold_left trm_app tl t) benv = inst t' benv' ->
  list_forall2 equiv_clos args args' ->
  list_forall2 equiv_frame la lb ->
  list_forall frame_ok la ->
  list_forall frame_ok lb ->
  list_forall clos_ok benv ->
  list_forall clos_ok args ->
  list_forall (closed_n (length benv)) (t::tl) ->
  list_forall clos_ok benv' ->
  list_forall clos_ok args' ->
  closed_n (length benv') t' ->
  exists h1, exists h2,
    equiv_result
      (eval_restart h1 nil (Inter (Frame benv args (trm_bvar n) :: la)))
      (eval_restart (h2+1) nil (Inter (Frame benv' args' t' :: lb))).
Proof.
  introv Eqt Eqargs Eqfl Hfl Hfl'.
  intros Hbenv Hargs Ht Hbenv' Hargs' Ht'.
*)

Definition eq2 := eq.

Lemma eval_bisim_bvar : forall n t' benv benv' args args' la lb,
  inst (trm_bvar n) benv = inst t' benv' ->
  list_forall2 equiv_clos args args' ->
  list_forall2 equiv_frame la lb ->
  list_forall frame_ok la ->
  list_forall frame_ok lb ->
  list_forall clos_ok benv ->
  list_forall clos_ok args ->
  closed_n (length benv) (trm_bvar n) ->
  list_forall clos_ok benv' ->
  list_forall clos_ok args' ->
  closed_n (length benv') t' ->
  exists h1, exists h2,
    equiv_result
      (eval_restart (h1+1) nil (Inter (Frame benv args (trm_bvar n) :: la)))
      (eval_restart (h2+1) nil (Inter (Frame benv' args' t' :: lb))).
Proof.
  introv Eqt Eqargs Eqfl Hfl Hfl'.
  intros Hbenv Hargs Ht Hbenv' Hargs' Ht'.
  destruct (inst_clos2trm _ _ (sym_equal Eqt)).
    case_rewrite R1 (nth n benv clos_def); simpl in H.
      poses Hn (clos_ok_nth n Hbenv); rewrite R1 in Hn.
      destruct t'; try discriminate.
        destruct (inst_clos2trm _ _ (sym_equal H)); try discriminate.
        case_rewrite R2 (nth n0 benv' clos_def).
          poses Hn0 (clos_ok_nth n0 Hbenv'); rewrite R2 in Hn0.
          exists 0; exists 0.
          simpl.
          rewrite R1; rewrite R2.
          inversions Eqargs; clear Eqargs.
            do 2 rewrite <- app_nil_end.
            inversions *Eqfl; clear Eqfl.
            destruct a; destruct b.
            simpl.
            destruct H1. simpl in H1, H3.
            constructor; simpl.
            inversions Hfl; inversions Hfl'; clear Hfl Hfl'.
            inversions H7; inversions* H9.
          remember (a::l) as benv1.
          remember (b::l0) as benv2.
          simpl in *.
          inversions Hargs; inversions Hargs'; clear Hargs Hargs'.
          inversions Hn.
          repeat rewrite <- app_nil_end.
          inversions* Hn0.
        simpl in H0.
        puts (is_const_app c (List.map clos2trm l0)).
        rewrite <- H0 in H1; discriminate.
      inversions H.
      exists 0; exists 0; simpl.
      rewrite R1.
      repeat rewrite <- app_nil_end.
      inversions Eqargs; clear Eqargs.
        inversions* Eqfl; clear Eqfl.
        destruct a; destruct b; simpl.
        inversions H0; clear H0.
        simpl in *. auto.
      inversions Hn.
      inversions* Ht'.
    simpl.
    repeat rewrite <- app_nil_end.
    puts (clos_ok_nth n Hbenv).
    rewrite R1 in H0.
    destruct (eval_const _ _ _ args' H)
      as [cls1 [cls2 [t1 [h [Eq1 [Fv1 [Eq' Eql]]]]]]].
        rewrite* H.
        apply (clos_ok_value H0).
      inversions H0.
      apply* list_forall_map.
    exists 0; exists h.
    do 2 rewrite <- eval_restart_ok'.
    rewrite Eq'.
    simpl.
    rewrite R1; rewrite Eq1.
    assert (equiv_clos (clos_const c (l++args))
                    (clos_const c (cls1 ++ cls2 ++ args'))).
      constructor.
      rewrite <- app_ass.
      apply* list_forall2_app.
      clear -Eql.
      gen l; induction (cls1++cls2) as [|cl cls]; intros;
             destruct l; try discriminate; auto.
      simpl in Eql; inversions Eql.
      use (sym_equal H0).
    case_eq (trm2app t1); introv R2.
      destruct t1; try discriminate.
    case_eq (cls2 ++ args'); introv R3.
      inversions Eqargs; clear Eqargs; try (destruct cls2; discriminate).
      repeat rewrite <- app_nil_end in *.
      inversions* Eqfl; clear Eqfl; rewrite <- app_nil_end in H1; auto.
      destruct a; destruct b; destruct H2; simpl in *; auto.
    case_eq (length cls1 + length (c0 :: l0)); introv R4.
      destruct cls1; discriminate.
    inversions Eqargs; clear Eqargs.
      repeat rewrite <- app_nil_end in *.
      destruct (le_lt_dec (Const.arity c) n0); simpl.
        elimtype False.
        inversions H0.
        rewrite <- app_length in R4.
        puts (f_equal (@length _) Eql).
        repeat rewrite map_length in H2.
        omega.
      inversions* Eqfl; clear Eqfl.
      destruct a; destruct b; destruct H2; simpl in *; auto.
    case_eq (length l + length (a :: la0)); introv R5.
      destruct l; discriminate.
    assert (n1 = n0).
      rewrite <- R3 in R4.
      rewrite app_length in R4.
      puts (f_equal (@length _) Eql).
      autorewrite with list in H4. simpl in *.
      assert (length la0 = length lb0).
      clear -H3; induction H3; simpl*.
      omega.
    subst.
    destruct (le_lt_dec (Const.arity c) n0); simpl.
      case_eq (l ++ a :: la0); introv R6. destruct l; discriminate.
      case_eq (cls1 ++ c0 :: l0); introv R7. destruct cls1; discriminate.
      case_eq (cut (Const.arity c) l2); introv R8.
      case_eq (cut (Const.arity c) l3); introv R9.
      assert (Const.arity c <= length l2).
        puts (f_equal (@length _) R6).
        rewrite app_length in H4. simpl in *; omega.
      assert (Const.arity c <= length l3).
        puts (f_equal (@length _) R7).
        rewrite app_length in H5. simpl in *; omega.
      destruct (cut_ok _ H4 R8).
      destruct (cut_ok _ H5 R9).
      subst.
      assert (list_forall2 equiv_clos (c1 :: l4 ++ l5) (c2 :: l6 ++ l7)).
        rewrite <- R7; rewrite <- R6.
        rewrite <- R3.
        inversions* H1.
      inversions H7; clear H7.
      destruct (list_forall2_app_inv _ _ _ _ H14). congruence.
      puts (reduce_clos_ext c (list_forall2_cons _ _ H12 H7)).
      destruct (SH.reduce_clos c (c1::l4)).
      destruct (SH.reduce_clos c (c2::l6)).
      destruct H10.
      inversions* H10.
    rewrite <- R3.
    inversions* Eqfl; clear Eqfl.
    destruct a0; destruct b0; destruct H4.
    simpl in *; auto.
  assert (term (trm_bvar n)). rewrite* <- H.
  inversion H0.
Qed.

Lemma equiv_clos_sym : forall cl1 cl2,
  equiv_clos cl1 cl2 -> equiv_clos cl2 cl1.
Proof.
  induction cl1 using clos_ind'; destruct cl2; intros; try inversions* H0.
  constructor.
  clear -H H2. gen l0; induction H; intros; inversions H2; auto.
Qed.
Hint Immediate equiv_clos_sym.

Lemma equiv_cls_sym : forall cl1 cl2,
  list_forall2 equiv_clos cl1 cl2 -> list_forall2 equiv_clos cl2 cl1.
Proof.
  induction 1; auto.
Qed.
Hint Immediate equiv_cls_sym.

Lemma equiv_frame_sym : forall f1 f2,
  equiv_frame f1 f2 -> equiv_frame f2 f1.
Proof.
  intros [benv1 args1 t1] [benv2 args2 t2] [Ht Hargs]; split; simpl in *; auto.
Qed.
Hint Immediate equiv_frame_sym.

Lemma equiv_fl_sym : forall f1 f2,
  list_forall2 equiv_frame f1 f2 -> list_forall2 equiv_frame f2 f1.
Proof.
  induction 1; auto.
Qed.
Hint Immediate equiv_fl_sym.

Lemma equiv_result_sym : forall r1 r2,
  equiv_result r1 r2 -> equiv_result r2 r1.
Proof.
  induction 1; constructor; auto.
Qed.
Hint Immediate equiv_result_sym.

Lemma eval_bisim_sym : forall r1 r2,
  (exists h1, exists h2,
    equiv_result (eval_restart (h1+1) nil r1) (eval_restart (h2+1) nil r2)) ->
  exists h2, exists h1,
    equiv_result (eval_restart (h2+1) nil r2) (eval_restart (h1+1) nil r1).
Proof.
  intros r1 r2 [h1 [h2 Eqr]].
  exists h2; exists* h1.
Qed.

Lemma eval_bisim : forall h0 args benv t fl args' benv' t' fl',
  list_forall clos_ok args ->
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  list_forall frame_ok fl ->
  list_forall clos_ok args' ->
  list_forall clos_ok benv' ->
  closed_n (length benv') t' ->
  list_forall frame_ok fl' ->
  list_forall2 equiv_clos args args' ->
  inst t benv = inst t' benv' ->
  list_forall2 equiv_frame fl fl' ->
  exists h, exists h', h0 <= h /\ h0 <= h' /\
    equiv_result (eval fenv h benv args t fl) (eval fenv h' benv' args' t' fl').
Proof.
  induction h0; intros.
    exists 0; exists 0; split*; split*.
    simpl*.
  destruct* (IHh0 args benv t fl args' benv' t' fl')
    as [h [h' [Hh [Hh' Eqr]]]].
  poses Hr (eval_regular h H H0 H1 H2).
  poses Hr' (eval_regular h' H3 H4 H5 H6).
  case_rewrite R1 (eval fenv h benv args t fl);
    case_rewrite R2 (eval fenv h' benv' args' t' fl');
    inversions Eqr; clear Eqr.
    exists (h+1); exists (h'+1). split. omega. split. omega.
    do 2 rewrite <- eval_restart_ok''.
    rewrite R1; rewrite R2; simpl*.
  cut (exists h1, exists h2,
    equiv_result (eval_restart (h1+1) nil (Inter l))
                 (eval_restart (h2+1) nil (Inter l0))).
    rewrite <- R1; rewrite <- R2.
    intros [h1 [h2 Eqr]].
    exists (h + (h1+1)); exists (h'+(h2+1)). split. omega. split. omega.
    do 2 rewrite eval_restart_ok'' in Eqr.
    auto.
  clear -fenv_ok Hr Hr' H12.
  inversions H12; clear H12.
    exists 0; exists 0; simpl*.
  rename H0 into Eqfl.
  destruct a as [benv args t]; destruct b as [benv' args' t'].
  destruct H as [Eqt Eqargs]. simpl in Eqt, Eqargs.
  inversions Hr; inversions Hr'; clear Hr Hr'.
  inversions H0; inversions H1; clear H0 H1.
  inversions H4; inversions H6; clear H4 H6.
  destruct t; try apply* eval_bisim_bvar; destruct t'; try discriminate;
    try solve [apply eval_bisim_sym; apply* eval_bisim_bvar];
    exists 0; exists 0; inversions Eqt;
    simpl; repeat rewrite <- app_nil_end.
      inversions Eqargs; clear Eqargs.
        inversions* Eqfl; clear Eqfl.
        destruct a; destruct b; destruct H; simpl in *; auto.
      set (t := trm2clos benv fenv (trm_fvar v0)). simpl in t. fold t.
      assert (clos_ok t).
        subst t.
        case_eq (get v0 fenv); intros; auto*.
      destruct* t.
        inversions* H1.
      simpl.
      rewrite <- (list_forall2_length H0).
      case_eq (length l + S (length la0)); introv R0.
        inversions* Eqfl; clear Eqfl.
        destruct a0; destruct b0; destruct H4; simpl in *; auto.
      destruct (le_lt_dec (Const.arity c) n); simpl.
        case_eq (l++a::la0); introv R1. destruct l; discriminate.
        case_eq (l++b::lb0); introv R2. destruct l; discriminate.
        case_eq (cut (Const.arity c) l1); introv R3.
        case_eq (cut (Const.arity c) l2); introv R4.
        assert (Const.arity c <= length l1).
          puts (f_equal (@length _) R1).
          rewrite app_length in H4. simpl in *; omega.
        assert (Const.arity c <= length l2).
          puts (f_equal (@length _) R2).
          puts (list_forall2_length H0).
          rewrite app_length in H6. simpl in *; omega.
        destruct (cut_ok _ H4 R3).
        destruct (cut_ok _ H6 R4).
        subst.
        assert (list_forall2 equiv_clos (c0 :: l3 ++ l4) (c1 :: l5 ++ l6)).
          rewrite <- R2; rewrite <- R1.
          inversions* H1.
        inversions H13; clear H13.
        destruct (list_forall2_app_inv _ _ _ _ H20). congruence.
        puts (reduce_clos_ext c (list_forall2_cons _ _ H18 H13)).
        destruct (SH.reduce_clos c (c0::l3)).
        destruct (SH.reduce_clos c (c1::l5)).
        destruct H16.
        inversions* H16.
      inversions* Eqfl; clear Eqfl.
      destruct a0; destruct b0; destruct H4.
      simpl in *; auto.
     inversions Eqargs; clear Eqargs.
       inversions* Eqfl; clear Eqfl.
       destruct a; destruct b; destruct H; simpl in *; auto.
     inversions H8; inversions* H11.
    assert (inst (trm_abs t2) benv = inst (trm_abs t'2) benv').
      unfold inst, trm_inst; simpl; apply* f_equal.
    inversions Eqargs; clear Eqargs.
      inversions* Eqfl; clear Eqfl.
    inversions H8; inversions* H11.
   inversions Eqargs; clear Eqargs.
     inversions* Eqfl; clear Eqfl.
   inversions H8; inversions* H11.
  inversions Eqargs; clear Eqargs.
    inversions* Eqfl; clear Eqfl.
    destruct a; destruct b; destruct H; simpl in *; auto.
  simpl.
  rewrite <- (list_forall2_length H0).
  destruct (le_lt_dec (Const.arity c0) (length la0)); simpl.
    case_eq (cut (Const.arity c0) la0); introv R3.
    case_eq (cut (Const.arity c0) lb0); introv R4.
    destruct (cut_ok _ l R3).
    rewrite (list_forall2_length H0) in l.
    destruct (cut_ok _ l R4).
    subst.
    destruct (list_forall2_app_inv _ _ _ _ H0). congruence.
    puts (reduce_clos_ext c0 (list_forall2_cons _ _ H H4)).
    destruct (SH.reduce_clos c0 (a::l0)).
    destruct (SH.reduce_clos c0 (b::l2)).
    destruct H13.
    inversions* H13.
  inversions* Eqfl; clear Eqfl.
  destruct a0; destruct b0; destruct H1; simpl in *; auto.
Qed.

Lemma eval_complete_rec : forall args benv t fl args' benv' t' fl' K T,
  list_forall clos_ok args ->
  list_forall clos_ok benv ->
  list_forall frame_ok fl ->
  list_forall clos_ok args' ->
  list_forall clos_ok benv' ->
  list_forall frame_ok fl' ->
  list_forall2 equiv_clos args args' ->
  list_forall2 equiv_frame fl fl' ->
  K ; E |Gc|= stack2trm (app2trm (inst t benv) args) fl ~: T ->
  inst t benv --> inst t' benv' ->
  exists h, exists h',
    equiv_result (eval fenv h benv args t fl) (eval fenv h' benv' args' t' fl').
Proof.
  introv Hargs Hbenv Hfl.
  intros Hargs' Hbenv' Hfl' Eqargs Eqfl Typ Red.
  destruct (red_regular Red).
  poses Ht (closed_n_inst _ _ (term_closed_0 H)).
  poses Ht' (closed_n_inst _ _ (term_closed_0 H0)).
  clear H H0.
  gen_eq (inst t benv) as t1; gen_eq (inst t' benv') as t1'.
  gen args benv fl K T. gen t t' args' benv' fl'.
  induction Red; intros.
       poses Happ (trm_inst_inv_app Hbenv Ht H2).
       destruct t; try discriminate; clear Happ.
       unfold trm_inst in H2; simpl in H2.
       inversions H2; clear H2.
       destruct (eval_value _ _ H0) as [h4 [cl4 [eq4 eq4']]].
       exists (S h4 + 1).
       simpl.
       rewrite <- eval_restart_ok'. rewrite eq4.
       unfold eval_restart.
       exists 0; simpl.
       destruct t3; try discriminate; simpl.
         destruct (inst_clos2trm _ _ H4).
           case_rewrite R1 (nth n benv clos_def).
             repeat (constructor; auto).
             simpl.
             rewrite <- H1.
             inversions H2.
             unfold trm_open.
             unfold trm_inst in H2.
             puts (clos_ok_nth n Hbenv).
             rewrite R1 in H3.
             inversions H3.
             rewrite* trm_inst_rec_more.
                 unfold inst, trm_inst. simpl.
                 rewrite* eq4'.
               rewrite* map_length.
             apply* list_forall_map.
           simpl in H2.
           elimtype False.
           puts (is_const_app c (List.map clos2trm l)).
           rewrite <- H2 in H3; discriminate.
         discriminate.
       repeat (constructor; simpl*).
       rewrite <- H1.
       unfold inst, trm_inst.
       simpl in *.
       rewrite* <- trm_inst_rec_more.
           inversions H4.
           unfold trm_open.
           rewrite* eq4'.
         inversions Ht.
         inversions H6.
         rewrite* map_length.
       apply* list_forall_map.
      destruct t; try discriminate.
        destruct (inst_clos2trm _ _ H2).
          puts (clos_ok_nth n Hbenv).
          set (cl := nth n benv clos_def) in *; clearbody cl.
          inversions H4; try discriminate.
          simpl in H3. unfold const_app in H3.
          clear -H3; induction (List.map clos2trm cls) using rev_ind.
            discriminate.
          rewrite fold_left_app in H3; discriminate.
        discriminate.
      inversions H2; clear H2.
      destruct (eval_value _ _ H0) as [h4 [cl4 [eq4 eq4']]].
      exists (S h4 + 1); exists 0; simpl.
      rewrite <- eval_restart_ok'. rewrite eq4.
      simpl.
      repeat (constructor; simpl*).
      rewrite <- H1.
      unfold trm_open.
      rewrite* trm_inst_rec_more.
          unfold inst, trm_inst; simpl.
          rewrite* eq4'.
        inversions Ht.
        rewrite* map_length.
      apply* list_forall_map.
     generalize vl. intros [Hlen Htl].
     induction tl using rev_ind. discriminate.
     clear IHtl.
     poses Hc H0.
     rewrite const_app_app in Hc. simpl in Hc.
     destruct t; try discriminate.
       destruct (inst_clos2trm _ _ Hc); try discriminate.
       puts (clos_ok_nth n Hbenv).
       inversions H2. rewrite <- H3 in H1; discriminate.
       rewrite <- H3 in H1; simpl in H1.
       rewrite Hc in H1; rewrite <- H0 in H1.
       destruct (const_app_eq _ _ _ _ (sym_equal H1)).
       subst.
       rewrite <- (map_length clos2trm) in H5.
       rewrite H7 in H5.
       elimtype False; omega.
     assert (value x) by apply* (list_forall_out Htl).
     inversions Hc; clear H0 Hc.
     destruct (eval_value _ _ H1) as [h4 [cl4 [eq4 eq4']]].
     assert (value (const_app c tl)).
       apply* value_const_app.
       clear -Hlen.
       rewrite app_length in Hlen. simpl in *; omega.
     rewrite H3 in H0.
     destruct (eval_value _ _ H0) as [h1 [cl1 [eq1 eq1']]].
     destruct* (eval_const _ _ _ (cl4::args) (sym_equal H3) H0)
       as [cls1 [cls2 [t1' [h2 [Eq1 [Vt1' [Eq1' Eq1'']]]]]]].
     assert (E1: eval fenv (S h4 + h2) benv args (trm_app t1 t2) nil =
              Inter (Frame benv (cls2 ++ cl4 :: args) t1' :: nil)).
       simpl. rewrite <- eval_restart_ok'. rewrite* eq4.
     remember (eval fenv ((S h4 + h2)+1) benv args (trm_app t1 t2) fl) as e.
     poses E' Heqe.
     (* exists ((S h4 + h2)+S h). *)
     rewrite <- eval_restart_ok' in E'. rewrite E1 in E'.
     simpl in E'.
     case_rewrite R1 (trm2app t1').
       destruct t1'; try discriminate.
     case_rewrite R2 (cls2 ++ cl4 :: args).
       destruct cls2; discriminate.
     rewrite Eq1 in E'.
     rewrite <- R2 in E'; simpl in E'.
     case_rewrite R3 (cls1 ++ cls2 ++ cl4 :: args).
       destruct cls1; destruct cls2; discriminate.
     puts (f_equal (@length clos) R3).
     rewrite app_length in H2; rewrite H2 in E'; clear H2. simpl in E'.
     destruct (le_lt_dec (Const.arity c) (length l0)).
       simpl in E'.
       case_rewrite R4 (cut (Const.arity c) l0).
       case_rewrite R5 (SH.reduce_clos c (c1 :: l2)).
       destruct (typing_stack2trm_inv _ _ Typ) as [T' [K' Typ']].
         apply* is_bvar_term.
         apply* term_app2trm.
         rewrite const_app_app. simpl.
         constructor; auto.
         apply value_regular.
         rewrite* H3.
       destruct (typing_app2trm_inv _ _ Typ') as [T'' Typ''].
         unfold const_app. rewrite fold_left_app. auto.
       destruct (cut_ok _ l1 R4). subst l0.
       assert (length (cls1 ++ cls2 ++ cl4 :: nil) = length (c1::l2)).
         clear -H2 Hlen Eq1''.
         rewrite <- app_ass.
         rewrite app_length; simpl.
         rewrite <- (map_length clos2trm).
         rewrite Eq1''.
         rewrite H2.
         rewrite app_length in Hlen.
         rewrite* Hlen.
       destruct* (app_eq_inv args l3 _ _ H4).
         repeat rewrite app_ass. simpl*.
       subst l3.
       rewrite <- H5 in R5.
       assert (CLS: list_for_n clos_ok (S(Const.arity c))
                      (cls1 ++ cls2 ++ cl4::nil)).
         rewrite <- H2; split*.
         clear Typ Typ''.
         assert (closed_n (length benv) (trm_app t1 t2)) by auto.
         puts (eval_regular (S h4 + h2) Hargs Hbenv H6
                  (@list_forall_nil _ frame_ok)).
         rewrite E1 in H7. rewrite <- R2 in *.
         clear -Eq1 H7 fenv_ok.
         inversions H7; clear H7.
         inversions H0; clear H0.
         inversions H3; clear H3.
         assert (clos_ok (clos_const c cls1)).
           rewrite <- Eq1.
           destruct t1'; try discriminate; simpl.
               apply* clos_ok_nth.
             case_eq (get v fenv); intros; auto.
             apply (proj1 fenv_ok _ _ (binds_in H)).
           constructor. auto. simpl; omega.
         inversions* H.
         apply list_forall_in; intros.
         destruct (in_app_or _ _ _ H0). apply* (list_forall_out H3).
         destruct (in_app_or _ _ _ H1); apply* (list_forall_out H5).
       forward~ (SH.reduce_clos_sound CLS).
         rewrite <- app_ass. rewrite map_app. rewrite Eq1''.
         simpl. rewrite eq4'.
         apply Typ''.
       rewrite R5.
       generalize (list_for_n_value CLS).
       rewrite <- app_ass.
       rewrite map_app. rewrite Eq1''.
       simpl List.map. rewrite eq4'.
       intros Hcls [Ok5 [Ok4 Eqred]].
       rewrite (ProofIrrelevance.proof_irrelevance _ vl Hcls) in H.
       puts (trans_equal Eqred H); clear H Eqred Typ Typ' Typ''.
       destruct c2.
         clear -Eqargs Eqfl Ok5 Ok4 H6 Hbenv' Ht' Heqe E'.
         poses E2 (f_equal (eval_restart 1 nil) E').
         simpl in E2. rewrite <- app_nil_end in E2.
         remember (eval fenv 0 benv' args' t' fl') as e'.
         poses E3 Heqe'. simpl in E3.
         gen args args' t'; induction l4 using rev_ind; intros.
           destruct t'; try discriminate.
             simpl in E3.
             exists h. subst; simpl.
             destruct (inst_clos2trm _ _ H6); try discriminate.
             inversions Eqargs; clear Eqargs.
               inversions* Eqfl; clear Eqfl.
               destruct a; destruct b; destruct H0; simpl in *; auto.
             case_rewrite R1 (nth n benv' clos_def).
               inversions H.
               repeat (constructor; simpl*).
               inversions Ok5.
               puts (clos_ok_nth n Hbenv').
               rewrite R1 in H2.
               inversions* H2.
             elimtype False.
             puts (is_const_app c (List.map clos2trm l)).
             simpl in H; rewrite <- H in H2; discriminate.
           exists h; subst. simpl.
           inversions Eqargs; clear Eqargs.
             inversions* Eqfl; clear Eqfl.
             destruct a; destruct b; destruct H; simpl in *; auto.
           repeat (constructor; simpl*).
           inversions Ok5.
           inversions* Ht'.
         rewrite map_app in H6; rewrite fold_left_app in H6; simpl in H6.
         destruct t'; try discriminate.
           clear IHl4. elimtype False.
           destruct (inst_clos2trm _ _ H6); try discriminate.
           case_rewrite R1 (nth n benv' clos_def).
           simpl in H. unfold const_app in H.
           induction l using rev_ind. discriminate.
           rewrite map_app in H; rewrite fold_left_app in H.
           inversions H. clear -H1.
           gen l4; induction l using rev_ind; destruct l4 using rev_ind;
             repeat (rewrite map_app; rewrite fold_left_app);
             simpl; intros; try discriminate.
           inversions H1; clear H1.
           elim (IHl _ H0).
         inversions H6.
         assert (clos_ok x) by auto.
         assert (list_forall clos_ok l4) by auto.
         clear Ok4.
         puts (clos_ok_value H). rewrite H1 in H3.
         destruct (eval_value _ _ H3) as [h1 [cl [eq1 eq2]]].
         puts (clos2trm_equiv _ _ (trans_equal H1 (sym_equal eq2))).
         inversions Ht'.
         destruct* (IHl4 H2 _ _ (list_forall2_cons _ _ H4 Eqargs) t'1).
         exists (S h + x0). rewrite <-eval_restart_ok'.
         remember 1 as h.
         simpl.
         replace x0 with (x0+0) by omega.
         rewrite <- eval_restart_ok'.
         
         inversions Eqargs; clear Eqargs.
           inversions* Eqfl; clear Eqfl.
               destruct a; destruct b; destruct H0; simpl in *; auto.
             case_rewrite R1 (nth n benv' clos_def).
             inversions H.
             repeat (constructor; simpl*).
             inversions Ok5.
             puts (clos_ok_nth n Hbenv').
             rewrite R1 in H2.
             inversions* H2.
       inversions H6; clear H6.
       destruct (IHl4 (x::args) 
         
           simpl.
         assert (exists h', 
         simpl in H6.
         subst h.

 repeat (constructor; simpl; auto).
           rewrite <- H. refine (trans_equal _ Eqred). simpl.
       unfold trm_inst in Eqred.
       rewrite <- Eqred.
       destruct c2; simpl.
         unfold app2trm'. rewrite map_app. rewrite* fold_left_app.
       rewrite trm_inst_nil.
       unfold app2trm'. do 2 rewrite map_app.
       do 2 rewrite fold_left_app. auto.
     elimtype False.
     puts Hlen.
     rewrite <- Eq1'' in H2.
     rewrite app_length in H2.
     rewrite map_length in H2; simpl in H2.
     puts (f_equal (@length clos) R3).
     rewrite <- app_ass in H4.
     rewrite app_length in H4. simpl in H4.
     omega.
    destruct t; try discriminate.
      destruct (inst_clos2trm _ _ H1).
        destruct (nth n benv clos_def). discriminate.
        simpl in H2. puts (is_const_app c (List.map clos2trm l)).
        rewrite <- H2 in H3; discriminate.
      discriminate.
    destruct (typing_stack2trm_inv _ _ Typ) as [T' [K' Typ']].
      apply* is_bvar_term.
    destruct (typing_app2trm_inv _ _ Typ') as [T'' Typ'']. auto.
    inversions Typ''; try discriminate.
    destruct (var_freshes L1 (sch_arity M)) as [Xs Fr].
    unfold trm_inst in H1; inversion H1; clear H1.
    inversions Ht.
    destruct t'; try discriminate.
      destruct (inst_clos2trm _ _ H0).
        destruct (nth n benv' clos_def). discriminate.
        simpl in H1. puts (is_const_app c (List.map clos2trm l)).
        rewrite <- H1 in H2; discriminate.
      discriminate.
    unfold trm_inst in H0; inversions H0; clear H0.
    assert (list_forall frame_ok (Frame benv args (trm_abs t4) :: fl)) by auto.
    assert (Ht'2: closed_n (S (length benv')) t'2).
      rewrite <- (map_length clos2trm).
      apply (@closed_n_inst (List.map clos2trm benv') t'2 1).
      rewrite <- H3.
      assert (clos_ok (clos_abs t4 benv)) by auto.
      puts (term_closed_0 (clos_ok_term H1)).
      simpl in H2. unfold trm_inst in H2. inversions* H2.
    assert (list_forall frame_ok (Frame benv' args' (trm_abs t'2) :: fl'))
      by auto.
    forward~ (IHRed t3 t'1 nil (list_forall_nil clos_ok) benv' Hbenv' _ H1
               _ (list_forall_nil clos_ok) I _ Hbenv H7 Eqbenv _ H0).
       split*. split*. simpl. unfold equiv_trm, trm_inst; simpl. rewrite* H3.
       simpl*. rewrite* (equiv_cls _ _ Eqbenv).
      simpl.
      rewrite* is_bvar_term.
    intros [h3 [h3' eq3]].
    exists (S h3); exists (S h3'). simpl*.
   destruct t; try discriminate.
     destruct (inst_clos2trm _ _ H1); try discriminate.
     elim (@value_irreducible t1 t1'); auto.
     clear -H2 Hbenv.
     destruct (clos_ok_value (clos_ok_nth n Hbenv)).
     rewrite <- H2 in H.
     inversions H. esplit; auto*.
    destruct (typing_stack2trm_inv _ _ Typ) as [T' [K' Typ']].
      apply* is_bvar_term.
    destruct (typing_app2trm_inv _ _ Typ') as [T'' Typ'']. auto.
    inversions Typ''; try discriminate.
    unfold trm_inst in H1; inversion H1; clear H1.
    inversions Ht.
    destruct t'; try discriminate.
      destruct (inst_clos2trm _ _ H0); try discriminate.
      (*
      puts (clos_ok_nth n Hbenv).
      puts (clos_ok_value H2).
      rewrite <- H1 in H3.
      case_rewrite R1 (nth n benv clos_def).
      rewrite H0 in *.
      simpl in H1.
      destruct (eval_const _ _ _ args H1 H3)
        as [cls1 [cls2 [t1 [h [Eq1 [Fv1 [Eq2 Eq3]]]]]]].
        inversions H2. apply* list_forall_map. intros; apply* clos_ok_value.
      *)
      puts (clos_ok_nth n Hbenv').
      case_rewrite R1 (nth n benv' clos_def).
      destruct l using rev_ind. discriminate. clear IHl.
      destruct (eval_value _ _ H) as [h4 [cl4 [Eq4 Eq4c]]].
      (* rewrite (trm_inst_equiv benv benv') in H.
      destruct (eval_value _ _ H) as [h4' [cl4' [Eq4' Eq4c']]]. *)
      simpl in H1; rewrite map_app in H1; rewrite const_app_app in H1.
      simpl in H1; inversions H1; clear H1.
      assert (Hcl4: clos_ok cl4).
        assert (result_ok (Result 0 cl4)).
        rewrite <- Eq4.
        apply* eval_regular.
        inversions* H1.
      clear Typ' Typ''.
      assert (list_forall clos_ok (cl4::args)) by auto.
      assert (Hx: clos_ok x) by inversions* H2.
      assert (list_forall clos_ok (x::args')) by auto.
      assert (For_all2 equiv_clos (cl4::args) (x::args')).
        simpl. split*. unfold equiv_clos. rewrite Eq4c. rewrite* <- H5.
      forward~ (IHRed t3 (const_app c (List.map clos2trm l)) (x::args') H3
        benv' Hbenv' _ Hfl' _ H1 H4 _ Hbenv H7 Eqbenv _ Hfl); clear IHRed.
        eapply retypable_stack2trm; try apply Typ; auto.
        unfold app2trm; simpl.
        apply retypable_app2trm; auto.
        rewrite Eq4c.
        apply retypable_trm_app; auto.
        symmetry; apply term_trm_inst.
        puts (clos_ok_term H2).
        simpl in H10; unfold const_app in H10.
        rewrite map_app in H10; rewrite fold_left_app in H10; simpl in H10.
        inversions* H10.
      intros [h3 [h3' eq3]].
      exists (Datatypes.S h4 + h3); exists h3'. simpl.
      rewrite <- eval_restart_ok'. rewrite Eq4. simpl.
      rewrite eq3.
      assert (exists h', res2trm'
        (eval fenv h3' benv' (x :: args') (const_app c (List.map clos2trm l))
          fl') = res2trm' (eval fenv h' benv' args' (trm_bvar n) fl')).
        set (l' := x :: nil) in *.
        replace (x::args') with (l'++args') by reflexivity.
        assert (const_app c (List.map clos2trm (l++l')) =
                trm_inst (trm_bvar n) (List.map clos2trm benv')).
          unfold l'; rewrite map_app; rewrite const_app_app; simpl.
          rewrite* <- H5.
        clearbody l'; clear - H2 R1 Eqbenv Hbenv' H10.
        set (l'' := l') in R1.
        assert (Eql: For_all2 equiv_clos l' l'').
          unfold equiv_clos, equiv_trm, l''; clear; induction l'; simpl*.
        clearbody l''.
        gen h3' l' l''; induction l using rev_ind; intros.
          unfold const_app.
          simpl in *.
          exists h3'.
          destruct h3'. simpl.
            rewrite <- H10.
            unfold app2trm'; rewrite map_app; rewrite fold_left_app.
            reflexivity.
          simpl.
          rewrite R1.
          destruct l'; destruct l''; try contradiction.
            destruct args'; simpl*.
          simpl.
          destruct (le_lt_dec (Const.arity c) (length (l'++args'))); simpl.
            destruct args'.
              elimtype False.
              inversions H2. simpl in H3; rewrite <- app_nil_end in l.
              omega.
            rewrite app_length in l.
            destruct (le_lt_dec (Const.arity c)(length l''+ length(c2::args')));
              try solve [elimtype False; omega].
            simpl.
            case_eq (cut (Const.arity c) (l'++c2::args')); introv R2.
            case_eq (cut (Const.arity c) (l''++c2::args')); introv R3.
            rewrite <- app_length in l,l0.
            destruct (cut_ok _ l R2).
            destruct (cut_ok _ l0 R3).
            assert (For_all2 equiv_clos (l1 ++ l2) (l3 ++ l4)).
              rewrite <- H0. rewrite <- H3.
              simpl in Eql; destruct Eql.
              apply* For_all2_app.
            destruct (For_all2_app_inv _ _ _ _ _ H4). congruence.
            simpl in Eql; destruct Eql.
            puts (reduce_clos_ext c (c0 :: l1) (c1 :: l3) (conj H7 H5)).
            destruct (SH.reduce_clos c (c0 :: l1)).
            destruct (SH.reduce_clos c (c1 :: l3)).
            simpl in H9; destruct H9.
            unfold equiv_clos in H9.
            destruct c3. simpl in H9.
              destruct c4; simpl in H9.
                
              
  
            reflexivity.
          destruct args'.
            rewrite <- app_nil_end. auto.
          rewrite app_length in l.
          destruct (le_lt_dec (Const.arity c) (length l'+ length(c1::args')));
            try solve [elimtype False; omega].
          simpl. reflexivity.
        destruct h3'.
          exists 0; simpl.
          rewrite <- H10.
          simpl.
          unfold app2trm'; rewrite map_app.
          rewrite fold_left_app.
          unfold trm_inst; rewrite* term_trm_inst.
            rewrite (map_app _ (l++x::nil)). rewrite* const_app_app.
          puts (term_closed_0 (clos_ok_term H2)). simpl in H.
          rewrite map_app in H.
          rewrite const_app_app in H.
          revert H; generalize (const_app c (List.map clos2trm (l++x::nil))).
          generalize (List.map clos2trm l').
          clear; intros; induction l using rev_ind. auto.
          rewrite fold_left_app in H. simpl in H.
          inversions* H.
        rewrite app_ass in *. simpl in * |-.
        rewrite map_app in *.
        rewrite const_app_app in *.
        simpl fold_left.
        simpl.
        inversions H2.
        assert (Hx: clos_ok x) by auto.
        destruct (eval_value benv' (clos2trm x)) as [h [cl [eq1 eq2]]].
          unfold trm_inst.
          rewrite* term_trm_inst.
          apply* clos_ok_value.
        destruct (le_lt_dec h h3').
          replace h3' with (h + (h3'-h)) by omega.
          rewrite <- eval_restart_ok'.
          rewrite eq1.
          simpl.
          replace (cl::l'++args') with ((cl::l')++args') by reflexivity.
          assert (clos_ok cl).
            assert (result_ok (Result 0 cl)).
              rewrite <- eq1.
              apply* eval_regular.
            inversions* H.
          apply* IHl.
            constructor; auto. clear -H H1.
              apply list_forall_in; intros. destruct* (in_app_or _ _ _ H0).
                apply* (list_forall_out H1).
              simpl in H2; destruct H2. subst*.
              apply* (list_forall_out H1).
            rewrite app_length in *; simpl in *. auto.
          


        destruct IHh3' as [h' Eq].
        exists (S h').
        destruct l using rev_ind.
          simpl in * |-. unfold const_app; simpl fold_left.
          simpl.
          SearchAbout term.
        unfold app2trm'; simpl.
        unfold trm_inst in Eq4c; rewrite <- Eq4c.
        unfold trm_inst. rewrite* term_trm_inst .
        
      assert (
      destruct h3'. simpl.
        unfold trm_inst at 2.
        rewrite* <- (trm_inst_equiv benv benv'); auto.
        unfold trm_inst in H0; rewrite <- H0.
        unfold app2trm'; simpl.
        unfold trm_inst in Eq4c; rewrite <- Eq4c.
        unfold trm_inst. rewrite* term_trm_inst .
      simpl.
        rewrite <- H0.
      assert (list_forall frame_ok (Frame benv' args' (trm_abs t'2) :: fl'))
      by auto.
      
      discriminate.
    unfold trm_inst in H0; inversions H0; clear H0.
    assert (list_forall frame_ok (Frame benv args (trm_abs t4) :: fl)) by auto.
    assert (Ht'2: closed_n (S (length benv')) t'2).
      rewrite <- (map_length clos2trm).
      apply (@closed_n_inst (List.map clos2trm benv') t'2 1).
      rewrite <- (equiv_cls _ _ Eqbenv).
      rewrite <- H3.
      assert (clos_ok (clos_abs t4 benv)) by auto.
      puts (term_closed_0 (clos_ok_term H1)).
      simpl in H2. unfold trm_inst in H2. inversions* H2.
    assert (list_forall frame_ok (Frame benv' args' (trm_abs t'2) :: fl'))
      by auto.
    forward~ (IHRed t3 t'1 nil (list_forall_nil clos_ok) benv' Hbenv' _ H1
               _ (list_forall_nil clos_ok) I _ Hbenv H7 Eqbenv _ H0).
       split*. split*. simpl. unfold equiv_trm, trm_inst; simpl. rewrite* H3.
       simpl*.
      simpl.
      rewrite* is_bvar_term.
    intros [h3 [h3' eq3]].
    exists (S h3); exists (S h3'). simpl*.
   

Theorem eval_complete : forall K t t' T,
  K ; E |Gc|= t ~: T ->
  clos_refl_trans _ red t t' ->
  value t' ->
  exists h,
    eval fenv h nil nil t nil = Result c /\
    untyped t' = untyped (clos2trm cl).


End Soundness.

End Mk3.
End Mk2.
End MkEval.