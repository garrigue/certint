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
    let t1 := trm_inst t (List.map clos2trm benv) in
    let t2 := if is_bvar t0 then t1 else app_trm t1 t0 in
    stack2trm (app2trm t2 args) rem
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

Definition trm2app t :=
  match t with
  | trm_app t1 t2 => Some (t1, t2)
  | trm_let t2 t1 => Some (trm_abs t1, t2)
  | _             => None
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
          match delta_red cst args with
          | clos_const cst' app'' =>
            eval h nil (List.app app'' app') (trm_cst cst') stack
          | clos_abs t1 benv =>
            eval h benv app' (trm_abs t1) stack
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

Module Sound2 := Sound.Mk2(Delta).
Import Sound2.
Import Sound.
Import JudgInfra.
Import Judge.

Definition gc := (false, GcAny).

Parameter delta_red_sound : forall c cls,
  list_for_n clos_ok (S(Const.arity c)) cls ->
  exists t1:trm, exists t2:trm, exists tl:list trm,
    forall K E T,
      K ; E |gc|= const_app c (List.map clos2trm cls) ~: T ->
      Delta.rule (length tl) t1 t2 /\ list_forall term tl /\
      const_app c (List.map clos2trm cls) = trm_inst t1 tl /\
      clos2trm (delta_red c cls) = trm_inst t2 tl /\
      clos_ok (delta_red c cls).

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
  forall K T, K; E |gc|= t1 ~: T -> K; E |gc|= t2 ~: T.

Lemma typing_app_abs_let : forall E t1 t2,
  retypable E (trm_app (trm_abs t2) t1) (trm_let t1 t2).
Proof.
  intros; intro; intros.
  inversions H; try discriminate; simpl in *.
  inversions H4; try discriminate; simpl in *.
  apply (@typing_let gc (Sch S nil) {} L).
    simpl; intros.
    destruct Xs; try elim H0.
    unfold kinds_open_vars, kinds_open, sch_open_vars; simpl.
    rewrite* typ_open_vars_nil.
  apply H8.
Qed.

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

Lemma term_trm_inst_closed' : forall t cl,
  closed_n (length cl) t -> list_forall clos_ok cl ->
  term (trm_inst t (List.map clos2trm cl)).
Proof.
  intros.
  apply term_trm_inst_closed.
    rewrite* map_length.
  apply* list_forall_map.
Qed.
Hint Resolve term_trm_inst_closed'.

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
  destruct (app_trm_cases (trm_inst t' (List.map clos2trm benv))).
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
  K; E |gc|= app_trm t1 t2 ~: T ->
  exists T1, K; E |gc|= t1 ~: T1.
Proof.
  intros.
  rewrite (app_trm_false _ _ H) in H0.
  inversions* H0; try discriminate.
Qed.

Lemma typing_app2trm_inv : forall K E t1 cl T,
  K; E |gc|= app2trm t1 cl ~: T ->
  is_abs t1 = false ->
  exists T1, K; E |gc|= t1 ~: T1.
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
  K; E |gc|= stack2trm t1 fl ~: T ->
  is_bvar t1 = false ->
  exists T1, exists K, K; E |gc|= t1 ~: T1.
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
  set (t0 := trm_inst t (List.map clos2trm benv)) in *.
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

Section Eval.

Variables (E:Defs.env) (fenv:env clos).

Hypothesis E_ok : env_ok E.

Hypothesis fenv_ok : forall x M,
  binds x M E ->
  exists cl, binds x cl fenv /\ clos_ok cl /\
    has_scheme_vars gc {} empty empty (clos2trm cl) M.

Lemma concat_empty : forall (A:Set) (K:env A), empty & K = K.
Proof. intros; symmetry; apply (app_nil_end K). Qed.

Lemma has_scheme_from_vars' : forall K t M,
  has_scheme_vars gc {} empty empty t M ->
  kenv_ok K -> env_ok E ->
  has_scheme gc K E t M.
Proof.
  clear fenv_ok.
  intros.
  apply (@has_scheme_from_vars gc (dom K)).
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

Lemma retypable_clos : forall benv t,
  closed_n (length benv) t ->
  trm2app t = None ->
  retypable E (trm_inst t (List.map clos2trm benv))
    (clos2trm (trm2clos benv fenv t)).
Proof.
  introv Ht H; intro; introv Typ.
  destruct t; try discriminate; try apply Typ; clear H; simpl in *.
    rewrite (trm_inst_n (clos2trm clos_def)) in Typ.
      rewrite map_nth in Typ; auto.
    rewrite* map_length.
  inversions Typ; try discriminate.
  destruct (fenv_ok H2) as [cl [B [_ Typ']]].
  rewrite B.
  destruct H5.
  apply* has_scheme_from_vars'.
Qed.

Lemma retypable_app_clos : forall benv t t1,
  closed_n (length benv) t ->
  trm2app t = None ->
  retypable E (app_trm (trm_inst t (List.map clos2trm benv)) t1)
    (app_trm (clos2trm (trm2clos benv fenv t)) t1).
Proof.
  intros; intro; intros.
  destruct (app_trm_cases (trm_inst t (List.map clos2trm benv))).
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
    rewrite <- (map_nth clos2trm).
    rewrite <- trm_inst_n.
      rewrite H2; simpl*.
    rewrite* map_length.
  simpl.
  unfold trm_inst in H2; simpl in H2; inversions* H2.
Qed.

Lemma clos_ok_trm : forall benv K t T,
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  K;E |gc|= trm_inst t (List.map clos2trm benv) ~: T ->
  trm2app t = None ->
  clos_ok (trm2clos benv fenv t).
Proof.
  intros.
  destruct t; simpl; try discriminate.
     apply (list_forall_out H).
     inversions H0; apply* nth_In.
    inversions H1; try discriminate.
    destruct (fenv_ok H6) as [cl [B [Hcl Typ]]].
    rewrite* B.
   inversions H0.
   constructor; auto.
  constructor; auto.
  simpl; omega.
Qed.

Theorem eval_sound_rec : forall h fl benv args K t T,
  list_forall clos_ok args ->
  list_forall clos_ok benv ->
  closed_n (length benv) t ->
  list_forall frame_ok fl ->
  K ; E |gc|=
    stack2trm (app2trm (trm_inst t (List.map clos2trm benv)) args) fl ~: T ->
  K ; E |gc|= res2trm (eval fenv h benv args t fl) ~: T.
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
    unfold trm_inst; simpl.
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
      constructor; auto.
      destruct t; try discriminate; simpl.
         apply (list_forall_out Hbenv).
         inversion Ht; apply* nth_In.
        unfold trm_inst at 2 in Typ. simpl in Typ.
        assert (exists V, binds v V E).
         destruct (typing_stack2trm_inv _ _ Typ) as [T' [K' Typ']].
          apply* is_bvar_term.
         destruct (typing_app2trm_inv _ _ Typ') as [T1 Typ1]. auto.
         destruct (app_trm_cases (trm_inst t' (List.map clos2trm benv'))).
          rewrite H0 in Typ1.
          inversions Typ1; try discriminate.
          inversions* H11; try discriminate.
         destruct H0. rewrite H0 in Typ1.
         inversions Typ1; try discriminate.
         destruct (var_freshes L1 (sch_arity M)).
         poses Typv (H9 _ f).
         inversions* Typv; try discriminate.
        destruct H0.
        destruct (fenv_ok H0) as [cl [B [Cok' _]]].
        rewrite* B.
       inversions Ht.
       constructor; auto.
      constructor; auto. simpl; omega.
    refine (retypable_stack2trm _ _ _ _ Typ); auto.
    unfold app2trm; simpl.
    apply* retypable_app2trm.
    apply retypable_app_trm2.
    apply (retypable_clos _ Ht H).
  case_eq (trm2clos benv fenv t); intros.
    inversions Hargs; clear Hargs.
    assert (Hl: clos_ok (clos_abs t0 l)).
      rewrite <- H0.
      destruct t; try discriminate; simpl.
        apply (list_forall_out Hbenv).
        inversions Ht; apply* nth_In.
       assert (exists V, binds v V E).
        destruct (typing_stack2trm_inv _ _ Typ) as [T' [K' Typ']].
         apply* is_bvar_term.
        destruct (typing_app2trm_inv _ _ Typ') as [T1 Typ1]. auto.
        unfold trm_inst in Typ1; simpl in Typ1.
        inversions* Typ1; try discriminate.
       destruct H1.
       destruct (fenv_ok H1) as [cl [B [Cok' _]]].
       rewrite* B.
      inversions Ht.
      constructor; auto.
    inversions Hl.
    apply* IHh; clear IHh.
    refine (retypable_stack2trm _ _ _ _ Typ); auto.
      unfold app2trm; simpl.
      apply* is_abs_app2trm.
    unfold app2trm; simpl.
    apply* retypable_app2trm.
    intro; intros.
    clear Typ.
    poses Typ (retypable_app_clos _ _ Ht H H1); clear H1.
    rewrite H0 in Typ.
    simpl in Typ.
    unfold trm_inst.
    rewrite <- trm_inst_rec_more;
      [|rewrite* map_length | apply* list_forall_map].
    set (t1 := trm_inst_rec 1 (List.map clos2trm l) t0) in *.
    clear H fl Hfl; inversions Typ; try discriminate.
    destruct (var_fresh (L2 \u trm_fv t1)).
    clear Typ; forward~ (H10 x) as Typ; clear H10; simpl gc_raise in Typ.
    fold (trm_open t1 (clos2trm arg)).
    rewrite* (@trm_subst_intro x).
    replace E with (E & empty) by simpl*.
    apply* typing_trm_subst.
    simpl*.
  simpl length.
  rewrite <- plus_n_Sm.
  case_eq (is_abs (trm_inst t (List.map clos2trm benv))); intros.
    elimtype False.
    destruct t; try discriminate.
    simpl in H0.
    rewrite (trm_inst_n (clos2trm clos_def)) in H1; try rewrite* map_length.
    rewrite map_nth in H1. rewrite H0 in H1.
    clear -H1.
    simpl in H1. unfold const_app in H1.
    induction (List.map clos2trm l) using rev_ind. discriminate.
    rewrite fold_left_app in H1. discriminate.
  assert (Hc: clos_ok (clos_const c l)).
    rewrite <- H0.
    destruct (typing_stack2trm_inv _ _ Typ).
      apply* is_bvar_term.
    destruct H2.
    destruct* (typing_app2trm_inv _ _ H2).
    apply* clos_ok_trm.
  assert (Typ': K; E |gc|= stack2trm
    (app2trm (clos2trm (trm2clos benv fenv t)) (arg :: args)) fl ~:  T).
    refine (retypable_stack2trm _ _ _ _ Typ); auto.
    unfold app2trm in *; simpl in *.
    clear Typ; intro; introv Typ.
    refine (retypable_app2trm _ _ _ Typ); auto.
      apply* retypable_app_clos.
    inversions* Hargs.
  clear Typ; rewrite H0 in Typ'; simpl in Typ'.
  destruct (le_lt_dec (Const.arity c) (length l + length args)).
    simpl.
    case_eq (l ++ arg :: args); intros. destruct l; discriminate.
    case_eq (cut (Const.arity c) l1); intros.
    assert (Const.arity c <= length l1).
      clear -l0 H2.
      puts (f_equal (@length clos) H2).
      rewrite app_length in H.
      simpl in H.
      omega.
    destruct (cut_ok _ H4 H3).
    subst.
    assert (Hok: list_forall clos_ok (c0 :: l2 ++ l3)).
      rewrite <- H2.
      apply list_forall_in.
      intros.
      destruct (in_app_or _ _ _ H6).
        inversions Hc.
        apply* (list_forall_out H10).
      apply* (list_forall_out Hargs).
    assert (Hok2: list_forall clos_ok (c0 :: l2)).
      apply list_forall_in; intros; apply* (list_forall_out Hok).
    assert (Hok3: list_forall clos_ok l3).
      apply list_forall_in; intros; apply* (list_forall_out Hok).
    destruct (@delta_red_sound c (c0 :: l2))
      as [t1 [t2 [tl Hd]]].
      split*. simpl; rewrite* H5.
    replace (app2trm (const_app c (List.map clos2trm l)) (arg :: args))
      with (app2trm (const_app c (List.map clos2trm (c0 :: l2))) l3)
        in Typ'.
      assert (K; E |gc|=
        stack2trm (app2trm (clos2trm (delta_red c (c0 :: l2))) l3) fl ~: T).
        assert (Habs: forall l, is_abs (const_app c l) = false).
          clear; unfold const_app.
          induction l using rev_ind. simpl*.
          rewrite fold_left_app. simpl*.
        refine (retypable_stack2trm _ _ _ _ Typ'); auto.
          apply* term_app2trm.
          unfold const_app. apply* term_fold_app.
          apply* (@list_forall_map _ clos_ok _ term clos2trm).
        apply* retypable_app2trm.
        intro; intros.
        destruct (Hd _ _ _ H6) as [Hr [Htl [Ht1 [Ht2 _]]]]; clear Typ' Hd.
        rewrite Ht1 in H6.
        rewrite Ht2.
        apply* SH.delta_typed. split*.
      assert (clos_ok (delta_red c (c0 :: l2))).
        clear -Typ' Hd.
        set (args := List.map clos2trm (c0 :: l2)) in *.
        destruct (typing_stack2trm_inv _ _ Typ').
          destruct (app2trm_cases (const_app c args) l3).
            destruct H as [t1' [t2' Happ]]. rewrite* Happ.
          destruct H.
            destruct H as [t1' [t2' Happ]]. rewrite* Happ.
          rewrite H. unfold const_app.
          clear. induction args using rev_ind. simpl*.
          rewrite fold_left_app. simpl*.
        destruct H.
        destruct (typing_app2trm_inv _ _ H).
          clear. unfold const_app; induction args using rev_ind. simpl*.
          rewrite fold_left_app; simpl*.
        destruct* (Hd _ _ _ H0).
      case_rewrite R (delta_red c (c0 :: l2));
        inversions H7; apply* IHh; clear IHh.
        apply* list_forall_app.
      simpl in *.
      rewrite trm_inst_nil.
      rewrite app2trm_app.
      rewrite* app2trm_cst.
    do 2 rewrite <- app2trm_cst.
    do 2 rewrite <- app2trm_app.
    rewrite H2. simpl*.
  simpl.
  destruct fl.
    simpl in *.
    rewrite <- app2trm_cst.
    rewrite app2trm_app.
    rewrite* app2trm_cst.
  destruct f as [benv' app' t'].
  inversions Hfl; clear Hfl.
  inversions H5; clear H5.
  apply* IHh; clear IHh.
    constructor; auto.
    constructor.
      apply* list_forall_app.
      inversions* Hc.
    rewrite app_length; simpl; omega.
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
  K ; E |gc|= t ~: T ->
  K ; E |gc|= res2trm (eval fenv h nil nil t nil) ~: T.
Proof.
  intros.
  apply* eval_sound_rec.
  unfold app2trm; simpl.
  rewrite* trm_inst_nil.
Qed.

End Eval.

End Mk3.
End Mk2.
End MkEval.