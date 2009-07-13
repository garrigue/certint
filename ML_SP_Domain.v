(***************************************************************************
* Preservation and Progress for mini-ML with structural polymorphism       *
* Jacques Garrigue, May 2008                                               *
***************************************************************************)

Set Implicit Arguments.
Require Import Lib_FinSet Metatheory List ListSet Arith.
Require Import ML_SP_Eval.
(* Require Import ML_SP_Inference. *)

Section ListSet.
  Variable A : Type.
  Hypothesis eq_dec : forall x y:A, sumbool (x = y) (x <> y).

  Definition set_incl : forall (s1 s2 : list A),
    sumbool (incl s1 s2) (~incl s1 s2).
    intros.
    induction s1. left; intros x Hx. elim Hx.
    case_eq (set_mem eq_dec a s2); intros.
      destruct IHs1.
        left; intros x Hx. simpl in Hx; destruct Hx.
        subst; apply* set_mem_correct1. apply* i.
      right. intro. elim n. intros x Hx. apply* H0.
    right. intro; elim (set_mem_complete1 eq_dec _ _ H).
    apply* H0.
  Defined.
End ListSet.

Module Cstr.
  Record cstr_impl : Set := C {
    cstr_low  : list var;
    cstr_high : option (list var) }.
  Definition cstr := cstr_impl.
  Definition valid c :=
    match cstr_high c with
    | None => True
    | Some h => incl (cstr_low c) h
    end.
  Definition entails c1 c2 :=
    incl (cstr_low c2) (cstr_low c1) /\
    match cstr_high c2 with
    | None => True
    | Some h2 =>
      match cstr_high c1 with
      | None => False
      | Some h1 => incl h1 h2
      end
     end.
  Lemma entails_refl : forall c, entails c c.
  Proof.
    intros.
    split. apply incl_refl.
    destruct* (cstr_high c).
  Qed.
    
  Lemma entails_trans : forall c1 c2 c3,
    entails c1 c2 -> entails c2 c3 -> entails c1 c3.
  Proof.
    introv. intros [CL1 CH1] [CL2 CH2].
    split. apply* incl_tran.
    clear CL1 CL2.
    destruct* (cstr_high c3).
    destruct* (cstr_high c2).
    destruct* (cstr_high c1).
  Qed.

  Definition unique c v := set_mem E.eq_dec v (cstr_low c).

  Definition lub c1 c2 :=
    C (set_union eq_var_dec (cstr_low c1) (cstr_low c2))
    (match cstr_high c1, cstr_high c2 with
     | None, h => h
     | h, None => h
     | Some s1, Some s2 => Some (set_inter eq_var_dec s1 s2)
     end).

  Hint Resolve incl_tran.
  Lemma entails_lub : forall c1 c2 c,
    (entails c c1 /\ entails c c2) <-> entails c (lub c1 c2).
  Proof.
    unfold entails, lub; simpl; split; intros.
      intuition.
        intros x Hx; destruct* (set_union_elim _ _ _ _ Hx).
      case_rewrite R1 (cstr_high c1);
      case_rewrite R2 (cstr_high c2);
      try case_rewrite R3 (cstr_high c); intuition.
      intros x Hx; apply set_inter_intro. apply* H2. apply* H3.
    destruct H.
    split; split;
      try (intros x Hx; apply H;
           solve [ apply* set_union_intro2 | apply* set_union_intro1 ]);
      case_rewrite R1 (cstr_high c1);
      case_rewrite R2 (cstr_high c2);
      try case_rewrite R3 (cstr_high c); intuition;
      intros x Hx; destruct* (set_inter_elim _ _ _ _ (H0 _ Hx)).
  Qed.

  Definition valid_dec : forall c, sumbool (valid c) (~valid c).
    intros.
    unfold valid.
    case_eq (cstr_high c); intros.
      destruct* (set_incl eq_var_dec (cstr_low c) l).
    auto.
  Defined.

  Lemma entails_unique : forall c1 c2 v,
    entails c1 c2 -> unique c2 v = true -> unique c1 v = true.
  Proof.
    unfold entails, unique.
    intros.
    destruct H.
    apply set_mem_correct2.
    apply H.
    apply* set_mem_correct1.
  Qed.

  Lemma entails_valid : forall c1 c2,
    entails c1 c2 -> valid c1 -> valid c2.
  Proof.
    unfold entails, valid.
    intros. destruct H.
    case_rewrite R1 (cstr_high c1); case_rewrite R2 (cstr_high c2);
    auto*.
  Qed.
End Cstr.

Section NoDup.
  Fixpoint nodup (l:list var) :=
    match l with
    | nil => nil
    | v :: l' =>
      if In_dec eq_var_dec v l' then nodup l' else v :: nodup l'
    end.
  Lemma nodup_elts : forall a l, In a l <-> In a (nodup l).
  Proof.
    induction l; split*; simpl; intro; destruct IHl.
      destruct H. subst.
        destruct* (In_dec eq_var_dec a l).
      destruct* (In_dec eq_var_dec a0 l).
    destruct* (In_dec eq_var_dec a0 l).
    simpl in H; destruct* H.
  Qed.
  Lemma NoDup_nodup : forall l, NoDup (nodup l).
  Proof.
    induction l; simpl. constructor.
    destruct* (In_dec eq_var_dec a l).
    constructor; auto.
    intro Ha. elim n. apply (proj2 (nodup_elts _ _) Ha).
  Qed.
End NoDup.

Module Const.
  Inductive ops : Set :=
    | tag     : var -> ops
    | matches : forall (l:list var), NoDup l -> ops.
  Definition const := ops.
  Definition arity op :=
    match op with
    | tag _     => 1
    | matches l _ => length l
    end.
End Const.

(* Module Infer := MkInfer(Cstr)(Const).
Import Infer.
Import Unify.MyEval. *)
Module MyEval := MkEval(Cstr)(Const).
Import MyEval.
Import Rename.Sound.Infra.
Import Defs.

Module Delta.
  Definition matches_arg n := typ_arrow (typ_bvar n) (typ_bvar 1).
  Lemma valid_tag : forall t, Cstr.valid (Cstr.C (t::nil) None).
    intros. compute. auto.
  Qed.
  Lemma coherent_tag : forall t,
    coherent (Cstr.C (t::nil) None) ((t, typ_bvar 0) :: nil).
  Proof.
    intros t x; intros.
    destruct H0; destruct H1; try contradiction.
    inversions H0. inversions* H1.
  Qed.
  Lemma valid_matches : forall l, Cstr.valid (Cstr.C nil (Some l)).
  Proof.
    intros; unfold Cstr.valid; simpl.
    intros x Hx; elim Hx.
  Qed.
  Lemma coherent_matches : forall l,
    NoDup l ->
    coherent (Cstr.C nil (Some l))
      (combine l (map typ_bvar (seq 2 (length l)))).
  Proof.
    intros; intro; intros.
    clear H0; revert H1 H2; generalize 2.
    induction H; simpl; intros. elim H1.
    destruct H1. inversions H1.
      destruct H2. inversions* H2.
      elim (H (in_combine_l _ _ _ _ H2)).
    destruct H2. inversions H2.
      elim (H (in_combine_l _ _ _ _ H1)).
    apply* (IHNoDup (S n)).
  Qed.
  Definition type (op:Const.const) :=
    match op with
    | Const.tag t =>
      Sch (typ_arrow (typ_bvar 0) (typ_bvar 1))
        (None :: Some (Kind (valid_tag t) (@coherent_tag t)) :: nil)
    | Const.matches l ND =>
      Sch (fold_right typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 1))
             (map matches_arg (seq 2 (length l))))
        (Some (Kind (@valid_matches l) (coherent_matches ND)) ::
         map (fun _ => None) (seq 0 (S (length l))))
    end.

  Definition trm_default := trm_abs trm_def.

  Definition reduce c tl (vl:list_for_n value (S(Const.arity c)) tl) :=
    match c with
    | Const.tag _ => trm_default
    | Const.matches l nd =>
      match nth (length l) tl trm_def with
      | trm_app (trm_cst (Const.tag t)) t1 =>
        match index eq_var_dec 0 t l with
        | Some i => trm_app (nth i tl trm_def) t1
        | None => trm_default
        end
      | _ => trm_default
      end
    end.

  Lemma value_term : forall e,
    value e -> term e.
  Proof.
    intros. destruct H. induction H; auto.
  Qed.

  Lemma term_default : term trm_default.
  Proof.
    unfold trm_default, trm_def.
    apply (@term_abs {}).
    intros. unfold trm_open; simpl. auto.
  Qed.
  Hint Resolve term_default.

  Lemma term : forall c tl vl,
    term (@reduce c tl vl).
  Proof.
    intros.
    case vl; clear vl; intros.
    destruct c; simpl in *. auto.
    assert (length l0 < S (length l0)) by auto.
    rewrite e in H.
    case_eq (nth (length l0) tl trm_def); intros; auto.
    destruct* t.
    destruct* c.
    case_eq (index eq_var_dec 0 v l0); intros; auto.
    apply term_app.
      destruct (index_ok eq_var_dec var_default _ _ H1).
      apply value_term.
      apply* (list_forall_out l).
      apply* nth_In. omega.
    assert (term (nth (length l0) tl trm_def)).
      apply value_term.
      apply* (list_forall_out l).
      apply* nth_In.
    rewrite H0 in H2.
    inversion* H2.
  Qed.

  Lemma closed : forall c, sch_fv (Delta.type c) = {}.
  Proof.
    intros.
    induction c; unfold sch_fv; simpl. unfold kind_fv; simpl.
      repeat rewrite union_empty_l. auto.
    pose (x := 1). assert (x = 1) by auto.
    unfold kind_fv_list, kind_fv; simpl. pattern 1 at -1. rewrite <- H.
    generalize x; clear.
    induction l; simpl in *; intros;
      repeat rewrite union_empty_l.
      auto.
    use (IHl (S x)); clear IHl. rewrite union_empty_l in H. auto.
  Qed.

  Lemma type_nth_typ_vars : forall n Xs,
    n < length Xs -> Defs.type (nth n (typ_fvars Xs) typ_def).
  Proof.
    induction n; destruct Xs; simpl; intros; try (elimtype False; omega).
      auto.
    apply IHn; omega.
  Qed.

  Lemma scheme : forall c, scheme (Delta.type c).
  Proof.
    intros. intro; intros.
    destruct c; simpl in *.
      do 3 (destruct Xs; try discriminate).
      unfold typ_open_vars; simpl.
      split*.
      unfold All_kind_types.
      repeat (constructor; simpl*).
    rewrite map_length in H.
    rewrite seq_length in H.
    split.
      do 2 (destruct Xs; try discriminate).
      inversion H; clear H.
      unfold typ_open_vars.
      replace Xs with (nil ++ Xs) by simpl*.
      set (Xs0 := nil(A:=var)).
      replace 2 with (S (S (length Xs0))) by simpl*.
      gen Xs; generalize Xs0; induction n; simpl; intros. auto.
      destruct Xs; try discriminate.
      constructor.
        unfold typ_fvars.
        rewrite map_app.
        rewrite app_nth2.
          rewrite map_length.
          replace (length Xs1 - length Xs1) with 0 by omega.
          simpl*.
        rewrite map_length; omega.
      replace (v1 :: Xs) with ((v1 :: nil) ++ Xs) by simpl*.
      rewrite <- app_ass.
      simpl in IHn.
      replace (S (length Xs1)) with (length (Xs1 ++ v1 :: nil))
        by (rewrite app_length; simpl; omega).
      apply* IHn.
    unfold All_kind_types.
    repeat (constructor; auto).
      induction (seq 1 (length l)); simpl; try constructor; simpl*.
    simpl.
    assert (length Xs >= 2 + length l) by omega.
    clear H; revert H0.
    unfold typ_open_vars.
    generalize 2; induction n; simpl; intros. auto.
    constructor. apply IHn. omega.
    apply type_nth_typ_vars. omega.
  Qed.
End Delta.

(* Module Infer2 := Infer.Mk2(Delta).
Import Infer2.MyEval2. *)
Module MyEval2 := Mk2(Delta).
Import MyEval2.
Import Rename2.Sound2.
Import JudgInfra.
Import Judge.

Module SndHyp.
  Lemma fold_arrow_eq : forall T1 TL1 T2 TL2 Us,
    typ_open (fold_right typ_arrow T1 TL1) Us = fold_right typ_arrow T2 TL2 ->
    length TL1 = length TL2 ->
    typ_open T1 Us = T2 /\
    For_all2 (fun U1 U2 => typ_open U1 Us = U2) TL1 TL2.
  Proof.
    induction TL1; intros; destruct* TL2; simpl in *; try discriminate; auto.
    inversions H.
    destruct* (IHTL1 T2 TL2 Us).
  Qed.

  Lemma gc_lower_false : forall gc, gc_lower (false, gc) = (false, gc).
  Proof. destruct gc; simpl*. Qed.

  Lemma fold_app_inv : forall K E gc t tl T,
    K ; E |(false,gc)|= fold_left trm_app tl t ~: T ->
    exists TL,
      K ; E |(false,gc)|= t ~: fold_right typ_arrow T TL /\
      For_all2 (typing (false,gc) K E) tl TL.
  Proof.
    induction tl using rev_ind; simpl; intros.
      exists* (nil(A:=typ)).
    rewrite fold_left_app in *; simpl in *.
    inversions H; try discriminate. rewrite gc_lower_false in *.
    destruct (IHtl (typ_arrow S T) H4).
    exists (x0 ++ S :: nil).
    rewrite fold_right_app; simpl.
    split*.
  Qed.

  Lemma map_nth : forall (A B:Set) d1 d2 (f:A->B) k l,
    k < length l -> nth k (map f l) d1 = f (nth k l d2).
  Proof.
    induction k; intros; destruct l; simpl in *; auto; try elim (lt_n_O _ H).
    apply IHk.
    apply* lt_S_n.
  Qed.

  Hint Rewrite combine_length combine_nth : list.

  Lemma tag_is_const : forall v vl K E gc T TL,
    S (Const.arity (Const.tag v)) = length vl ->
    K; E |(false,gc)|= trm_cst (Const.tag v) ~:
      fold_right typ_arrow T TL ->
    For_all2 (typing (false,gc) K E) vl TL -> False.
  Proof.
    introv Hv TypC TypA.
    inversions TypC; try discriminate. clear TypC H4.
    destruct* vl; try destruct* vl; try destruct* vl; try discriminate.
    destruct TL; destruct* TypA.
    destruct TL; destruct* H2.
    destruct TL; destruct* H3.
    unfold sch_open in H0.
    simpl in H0.
    inversions H0. clear H0.
    destruct H5 as [_ WK]. simpl in WK.
    destruct* Us. destruct* Us. destruct* Us.
    destruct WK as [_ [WK _]].
    inversions WK.
    discriminate.
  Qed.

  Lemma matches_not_value : forall K E gc i x TL t,
    K;E |(false,gc)|= t ~: fold_right typ_arrow (typ_fvar x) TL ->
    valu (length TL + i) t ->
    length TL <= 1.
  Proof.
    intros.
    gen_eq (length TL + i) as j.
    gen TL; induction H0; intros; subst; try discriminate.
        omega.
      destruct c; simpl in *.
        omega.
      inversions H; clear H; try discriminate.
      unfold sch_open in H2; simpl in *.
      rewrite H1 in H2.
      simpl in H2.
      clear -H2.
      elimtype False.
      revert H2; generalize 2; induction TL; simpl; intros.
        destruct i; discriminate.
      inversions* H2.
    inversions H; clear H; try discriminate.
    rewrite gc_lower_false in *.
    forward~ (IHvalu1 (S::TL)) as IH.
    simpl in IH. omega.
  Qed.

  Lemma value_fvar_is_const : forall K E gc t x,
    K; E |(false,gc)|= t ~: typ_fvar x ->
    value t ->
    exists v, exists t2, t = trm_app (trm_cst (Const.tag v)) t2.
  Proof.
    intros.
    destruct H0 as [i vi].
    inversions vi; clear vi.
        inversion H; discriminate.
      destruct c; inversions H; try discriminate.
      unfold sch_open in *; simpl in *.
      clear -H1.
      destruct (length l); discriminate.
    inversions H; clear H; try discriminate.
    rewrite gc_lower_false in *.
    inversions H0; clear H0.
      destruct c; inversions H6; clear H6; try discriminate.
        esplit; esplit; reflexivity.
      simpl in H2.
      unfold sch_open in *; simpl in *.
      rewrite H2 in H0. simpl in H0.
      inversions H0.
      destruct i; discriminate.
    inversions H6; clear H6; try discriminate. rewrite gc_lower_false in *.
    puts (matches_not_value i x (S0 :: S :: nil) H7 H).
    elimtype False. simpl in H0. omega.
  Qed.

  Lemma fold_right_app_end : forall T1 T2 TL,
    fold_right typ_arrow (typ_arrow T1 T2) TL =
    fold_right typ_arrow T2 (TL ++ T1 :: nil).
  Proof.
    intros; rewrite* fold_right_app.
  Qed.
    
  Lemma in_matches_types : forall i l T1 T2 Us,
    i < length l ->
    In (nth i l var_default, nth i Us typ_def)
    (List.map
      (fun XT : var * typ => (fst XT, typ_open (snd XT) (T1 :: T2 :: Us)))
      (combine l (map typ_bvar (seq 2 (length l))))).
  Proof.
    intros.
    remember (0 + i) as m.
    pattern i at 2.
    replace i with (0+i) by reflexivity. rewrite <- Heqm.
    gen i; generalize 0; induction l; intros.
    simpl in H; elimtype False; omega.
    destruct i; simpl.
      replace m with n; auto. omega.
    right.
    apply (IHl (S n) i). simpl in H. omega.
    omega.
  Qed.

  Lemma delta_typed : forall c tl vl K E gc T,
    K ; E |(false,gc)|= const_app c tl ~: T ->
    K ; E |(false,gc)|= @Delta.reduce c tl vl ~: T.
  Proof.
    intros.
    destruct (fold_app_inv _ _ H) as [TL [Typ0 TypA]]; clear H.
    destruct c.
      elim (tag_is_const _ _ _ (proj1 vl) Typ0 TypA).
    inversions Typ0; try discriminate. clear Typ0.
    unfold sch_open in H0. simpl in H0.
    rewrite fold_right_app_end in H0.
    poses Hlen (proj1 vl). simpl in Hlen.
    destruct (fold_arrow_eq _ _ _ _ _ H0) as [HT HA]; clear H0.
      generalize (For_all2_length _ _ _ TypA).
      autorewrite with list. simpl. intros; omega.
    forward~ (For_all2_nth _ trm_def typ_def _ TL TypA (n:=length l)) as Typn.
      rewrite* <- Hlen.
    forward~ (For_all2_nth _ typ_def typ_def _ TL HA (n:=length l)) as Eqn.
      autorewrite with list. simpl*. omega.
    rewrite app_nth2 in Eqn; [|rewrite map_length; rewrite* seq_length].
    autorewrite with list in Eqn.
    rewrite <- minus_n_n in Eqn.
    simpl in Eqn.
    destruct H5 as [_ WUs]. simpl in WUs.
    do 2 destruct* Us.
    simpl in Eqn.
    destruct WUs as [Wt _].
    inversions Wt; clear Wt.
    rewrite <- H5 in *; clear H5.
    destruct (value_fvar_is_const Typn) as [v [t2 Hv]].
      apply* (list_forall_out (proj2 vl)). apply* nth_In. omega.
    simpl.
    rewrite Hv in *; clear Hv.
    inversions Typn; clear Typn; try discriminate.
    rewrite gc_lower_false in *.
    inversions H7; clear H7; try discriminate.
    destruct H12.
    destruct H as [H _]. simpl in H.
    do 3 (destruct Us0; try discriminate). clear H.
    simpl in *.
    destruct H2 as [_ [Ht1 _]].
    subst t1.
    inversions Ht1; clear Ht1.
    puts (binds_func H6 H0).
    inversions H; clear H H6 H10 H11.
    destruct H7; destruct H3.
    destruct H; destruct H3.
    destruct k' as [[kcl kch] kv kr kh]; simpl in *.
    destruct* kch.
    assert (Hvt: In (v,t) kr) by auto*. clear H6 H2.
    unfold Cstr.valid in kv; simpl in kv.
    assert (Hvl: In v l) by auto*.
    case_eq (index eq_var_dec 0 v l); introv R2;
      try elim (index_none_notin _ _ _ _ R2 Hvl).
    destruct (index_ok _ var_default _ _ R2).
    assert (Hvn: In (v, nth n0 Us typ_def) kr).
      rewrite <- H6. apply H5. apply* in_matches_types.
    clear H5 H6.
    forward~ (For_all2_nth _ trm_def typ_def _ TL TypA (n:=n0)) as Typv.
      omega.
    forward~ (For_all2_nth _ typ_def typ_def _ TL HA (n:=n0)) as Eqv.
      rewrite (For_all2_length _ _ _ HA).
      rewrite <- (For_all2_length _ _ _ TypA).
      omega.
    rewrite <- Eqv in Typv; clear Eqv.
    rewrite app_nth1 in Typv; [|rewrite map_length; rewrite* seq_length].
    rewrite (map_nth _ 0) in Typv; [|rewrite* seq_length].
    rewrite seq_nth in Typv; auto.
    simpl in Typv.
    assert (nth n0 Us typ_def = t).
      apply (kh v); trivial.
      unfold Cstr.unique.
      apply set_mem_correct2. simpl. unfold set_In. auto*.
    rewrite H5 in Typv.
    apply* typing_app; rewrite gc_lower_false; auto*.
  Qed.

  Definition reduce_clos c (cl : list clos) :=
    match c with
    | Const.tag _ => (clos_def, nil)
    | Const.matches l nd =>
      match nth (length l) cl clos_def with
      | clos_const (Const.tag t) (cl1 :: nil) =>
        match index eq_var_dec 0 t l with
        | Some i => (nth i cl clos_def, cl1 :: nil)
        | None => (clos_def, nil)
        end
      | _ => (clos_def, nil)
      end
    end.

  Lemma reduce_clos_sound :
    forall c cls (CLS : list_for_n clos_ok (S(Const.arity c)) cls) K E T,
      K; E |Gc|= const_app c (List.map clos2trm cls) ~: T ->
      let (cl', cls') := reduce_clos c cls in
      clos_ok cl' /\ list_forall clos_ok cls' /\
      fold_left trm_app (List.map clos2trm cls') (clos2trm cl') =
      Delta.reduce c (list_for_n_value CLS).
  Proof.
    intros.
    clear H. (* Simpler to prove it independently of typability *)
    unfold Delta.reduce.
    destruct c. simpl*.
    poses Hlen (proj1 CLS). simpl in Hlen.
    rewrite (map_nth _ clos_def); try omega.
    unfold reduce_clos.
    case_eq (nth (length l) cls clos_def); introv R1; simpl*.
    unfold const_app.
    destruct l0; simpl. destruct* c.
    destruct l0 using rev_ind; simpl.
      destruct* c.
      case_eq (index eq_var_dec 0 v l); introv R2; simpl*.
      destruct (index_ok _ var_default _ _ R2).
      rewrite (map_nth _ clos_def); try omega.
      intros.
      split. 
        apply (list_forall_out (proj2 CLS)).
        apply* nth_In.
        omega.
      assert (Htag: clos_ok (nth (length l) cls clos_def)).
        apply (list_forall_out (proj2 CLS)).
        apply* nth_In. omega.
      rewrite R1 in Htag.
      inversion* Htag.
    clear IHl0.
    rewrite map_app; rewrite fold_left_app; simpl.
    destruct l0 using rev_ind; simpl.
      destruct* c.
    clear IHl0.
    rewrite map_app; rewrite fold_left_app; simpl.
    destruct l0; destruct c; simpl*.
  Qed.

  Lemma reduce_clos_regular : forall c cls cl' cls',
    reduce_clos c cls = (cl', cls') ->
    list_forall clos_ok cls ->
    list_forall clos_ok (cl' :: cls').
  Proof.
    destruct c; simpl; intros.
      inversions* H.
    puts (clos_ok_nth (length l) H0).
    destruct (nth (length l) cls clos_def); inversions H1.
      inversions* H.
    destruct c.
      destruct l0.
        inversions* H.
      destruct l0.
        destruct (index eq_var_dec 0 v l).
          puts (clos_ok_nth n0 H0).
          inversions* H.
        inversions* H.
      inversions* H.
    inversions* H.
  Qed.

  Lemma reduce_clos_ext : forall c args args',
    list_forall2 equiv_clos args args' ->
    let (cl,arg) := reduce_clos c args in
    let (cl',arg') := reduce_clos c args' in
    equiv_clos cl cl' /\ list_forall2 equiv_clos arg arg'.
  Proof.
    destruct c; simpl; intros. split*.
    puts (equiv_cl_nth (length l) H).
    inversions* H0.
    destruct c.
      inversions H3. auto.
      inversions H5.
        destruct (index eq_var_dec 0 v l).
          split*.
          apply* equiv_cl_nth.
        auto.
      auto.
    auto.
  Qed.
End SndHyp.

(* Module Sound3 := Infer2.MyEval2.Mk3(SndHyp). *)
Module Sound3 := MyEval2.Mk3(SndHyp).

