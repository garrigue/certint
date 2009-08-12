(***************************************************************************
* Preservation and Progress for mini-ML with structural polymorphism       *
* Jacques Garrigue, May 2008                                               *
***************************************************************************)

Set Implicit Arguments.
Require Import Lib_FinSet Metatheory List ListSet Arith.
(* Require Import ML_SP_Inference_wf. *)
Require Import ML_SP_Eval.

Section ListSet.
  Variable A : Type.
  Hypothesis eq_dec : forall x y:A, {x = y} + {x <> y}.

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
  Definition attr := nat.
  Definition eq_dec := eq_nat_dec.
  Inductive ksort := Ksum | Kprod | Kbot.
  Record cstr_impl : Set := C {
    cstr_sort : ksort;
    cstr_low  : list nat;
    cstr_high : option (list nat) }.
  Definition cstr := cstr_impl.
  Definition valid c :=
    cstr_sort c <> Kbot /\
    match cstr_high c with
    | None => True
    | Some h => incl (cstr_low c) h
    end.
  Definition le_sort s1 s2 :=
    s1 = Kbot \/ s1 = s2.
  Definition entails c1 c2 :=
    le_sort (cstr_sort c1) (cstr_sort c2) /\
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
    split. right*.
    split. apply incl_refl.
    destruct* (cstr_high c).
  Qed.
    
  Lemma entails_trans : forall c1 c2 c3,
    entails c1 c2 -> entails c2 c3 -> entails c1 c3.
  Proof.
    introv. intros [CS1 [CL1 CH1]] [CS2 [CL2 CH2]].
    split.
      unfold le_sort.
      destruct* CS1.
      rewrite H. destruct* CS2.
    split. apply* incl_tran.
    clear CL1 CL2.
    destruct* (cstr_high c3).
    destruct* (cstr_high c2).
    destruct* (cstr_high c1).
  Qed.

  Definition unique c v := set_mem eq_nat_dec v (cstr_low c).

  Definition sort_lub s1 s2 :=
    match s1, s2 with
    | Ksum, Ksum => Ksum
    | Kprod, Kprod => Kprod
    | _, _ => Kbot
    end.

  Definition lub c1 c2 :=
    C (sort_lub (cstr_sort c1) (cstr_sort c2))
    (set_union eq_nat_dec (cstr_low c1) (cstr_low c2))
    (match cstr_high c1, cstr_high c2 with
     | None, h => h
     | h, None => h
     | Some s1, Some s2 => Some (set_inter eq_nat_dec s1 s2)
     end).

  Lemma ksort_dec : forall s, {s=Kbot} + {s<>Kbot}.
    intro; destruct* s; right; intro; discriminate.
  Qed.

  Hint Resolve incl_tran.
  Lemma entails_lub : forall c1 c2 c,
    (entails c c1 /\ entails c c2) <-> entails c (lub c1 c2).
  Proof.
    unfold entails, lub; simpl; split; intros.
      intuition.
          destruct (ksort_dec (cstr_sort c)).
            rewrite e; left*.
          destruct* H.
          destruct* H0.
          rewrite <- H, <- H0.
          right; destruct* (cstr_sort c).
        intros x Hx; destruct* (set_union_elim _ _ _ _ Hx).
      case_rewrite R1 (cstr_high c1);
      case_rewrite R2 (cstr_high c2);
      try case_rewrite R3 (cstr_high c); intuition.
      intros x Hx; apply set_inter_intro. apply* H4. apply* H5.
    destruct H as [HS [HL HH]].
    split; split; try split;
      try (intros x Hx; apply HL;
           solve [ apply* set_union_intro2 | apply* set_union_intro1 ]);
      try solve [
        case_rewrite R1 (cstr_high c1);
        case_rewrite R2 (cstr_high c2);
        try case_rewrite R3 (cstr_high c); intuition;
        intros x Hx; destruct* (set_inter_elim _ _ _ _ (HH _ Hx))];
      clear -HS; destruct HS; try solve [left*];
      rewrite H;
      unfold le_sort; destruct (cstr_sort c1); destruct* (cstr_sort c2).
  Qed.

  Definition valid_dec : forall c, sumbool (valid c) (~valid c).
    intros.
    unfold valid.
    destruct* (ksort_dec (cstr_sort c)).
    case_eq (cstr_high c); intros.
      destruct (set_incl eq_nat_dec (cstr_low c) l). left*.
      right*.
    auto.
  Defined.

  Lemma entails_unique : forall c1 c2 v,
    entails c1 c2 -> unique c2 v = true -> unique c1 v = true.
  Proof.
    unfold entails, unique.
    intros.
    destruct H as [_ [H _]].
    apply set_mem_correct2.
    apply H.
    apply* set_mem_correct1.
  Qed.

  Lemma entails_valid : forall c1 c2,
    entails c1 c2 -> valid c1 -> valid c2.
  Proof.
    unfold entails, valid.
    intros.
    destruct H as [HS [HL HH]]; destruct H0.
    destruct* HS.
    rewrite <- H1. split*.
    case_rewrite R1 (cstr_high c1); case_rewrite R2 (cstr_high c2);
    auto*.
  Qed.
End Cstr.

Section NoDup.
  Fixpoint nodup (l:list nat) :=
    match l with
    | nil => nil
    | v :: l' =>
      if In_dec eq_nat_dec v l' then nodup l' else v :: nodup l'
    end.
  Lemma nodup_elts : forall a l, In a l <-> In a (nodup l).
  Proof.
    induction l; split*; simpl; intro; destruct IHl.
      destruct H. subst.
        destruct* (In_dec eq_nat_dec a l).
      destruct* (In_dec eq_nat_dec a0 l).
    destruct* (In_dec eq_nat_dec a0 l).
    simpl in H; destruct* H.
  Qed.
  Lemma NoDup_nodup : forall l, NoDup (nodup l).
  Proof.
    induction l; simpl. constructor.
    destruct* (In_dec eq_nat_dec a l).
    constructor; auto.
    intro Ha. elim n. apply (proj2 (nodup_elts _ _) Ha).
  Qed.
End NoDup.

Module Const.
  Inductive ops : Set :=
    | tag     : Cstr.attr -> ops
    | matches : forall (l:list Cstr.attr), NoDup l -> ops
    | record  : forall (l:list Cstr.attr), NoDup l -> ops
    | sub     : Cstr.attr -> ops
    | recf    : ops.
  Definition const := ops.
  Definition arity op :=
    match op with
    | tag _       => 1
    | matches l _ => length l
    | record l _  => length l
    | sub _       => 0
    | recf        => 1
    end.
End Const.

(*
Module Infer := MkInfer(Cstr)(Const).
Import Infer.
Import Unify.MyEval. *)
Module MyEval := MkEval(Cstr)(Const).
Import MyEval.
Import Rename.Sound.Infra.
Import Defs.

Lemma list_snd_combine : forall (A B:Set) (l1:list A) (l2:list B),
  length l1 = length l2 ->
  list_snd (combine l1 l2) = l2.
Proof.
  induction l1; destruct l2; intros; try discriminate. reflexivity.
  inversions H.
  simpl. rewrite* (IHl1 l2).
Qed.

Module Delta.
  Definition matches_arg n := typ_arrow (typ_bvar n) (typ_bvar 1).

  Lemma valid_tag : forall s t,
    s <> Cstr.Kbot -> Cstr.valid (Cstr.C s (t::nil) None).
  Proof.
    intros. split*. compute. auto.
  Qed.

  Lemma ksum : Cstr.Ksum <> Cstr.Kbot.
    intro; discriminate.
  Qed.

  Lemma kprod : Cstr.Kprod <> Cstr.Kbot.
    intro; discriminate.
  Qed.

  Lemma coherent_tag : forall s t,
    coherent (Cstr.C s (t::nil) None) ((t, typ_bvar 0) :: nil).
  Proof.
    intros s t x; intros.
    destruct H0; destruct H1; try contradiction.
    inversions H0. inversions* H1.
  Qed.

  Lemma valid_matches : forall s l,
    s <> Cstr.Kbot -> Cstr.valid (Cstr.C s nil (Some l)).
  Proof.
    intros; split*. simpl*.
  Qed.

  Lemma coherent_matches : forall s n l,
    NoDup l ->
    coherent (Cstr.C s nil (Some l))
      (combine l (map typ_bvar (seq n (length l)))).
  Proof.
    intros; intro; intros.
    clear H0; revert H1 H2; gen n.
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
        (None :: Some (Kind (valid_tag t ksum) (@coherent_tag _ t)) :: nil)
    | Const.matches l ND =>
      Sch (fold_right typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 1))
             (map matches_arg (seq 2 (length l))))
        (Some (Kind (@valid_matches _ l ksum) (coherent_matches 2 ND)) ::
         map (fun _ => None) (seq 0 (S (length l))))
    | Const.record l ND =>
      Sch (fold_right typ_arrow (typ_bvar 0) (map typ_bvar (seq 1 (length l))))
        (Some (Kind (@valid_matches _ l kprod) (coherent_matches 1 ND)) ::
         map (fun _ => None) (seq 0 (length l)))
    | Const.sub f =>
      Sch (typ_arrow (typ_bvar 1) (typ_bvar 0))
        (None :: Some (Kind (valid_tag f kprod) (@coherent_tag _ f)) :: nil)
    | Const.recf =>
      let T := typ_arrow (typ_bvar 0) (typ_bvar 0) in
      Sch (typ_arrow (typ_arrow T T) T) (None :: nil)
    end.

  Definition trm_default := trm_abs trm_def.

  Fixpoint record_args (t : trm) tl {struct t} : list nat * list trm :=
    match t with
    | trm_app t1 t2 => record_args t1 (t2 :: tl)
    | trm_cst (Const.record l _) => (l, tl)
    | _ => (nil, nil)
    end.

  Definition reduce c tl (vl:list_for_n value (S(Const.arity c)) tl) :=
    match c with
    | Const.tag _ => trm_default
    | Const.matches l nd =>
      match nth (length l) tl trm_def with
      | trm_app (trm_cst (Const.tag t)) t1 =>
        match index eq_nat_dec 0 t l with
        | Some i => trm_app (nth i tl trm_def) t1
        | None => trm_default
        end
      | _ => trm_default
      end
    | Const.record _ _ => trm_default
    | Const.sub f =>
      match tl with
      | nil    => trm_default
      | t :: _ =>
        let (l, fl) := record_args t nil in
        match index eq_nat_dec 0 f l with
        | Some i => nth i fl trm_default
        | None => trm_default
        end
      end
    | Const.recf =>
      match tl with
      | f :: a :: _ => trm_app (trm_app f (trm_app (trm_cst Const.recf) f)) a
      | _ => trm_default
      end
    end.

  Lemma term_default : term trm_default.
  Proof.
    unfold trm_default, trm_def.
    apply (@term_abs {}).
    intros. unfold trm_open; simpl. auto.
  Qed.
  Hint Resolve term_default.


  Lemma value_term : forall e,
    value e -> term e.
  Proof.
    intros. destruct H. induction H; auto.
  Qed.
  Hint Resolve value_term.

  Lemma term : forall c tl vl,
    term (@reduce c tl vl).
  Proof.
    intros.
    case vl; clear vl; intros.
    destruct c; simpl in *; auto.
    (* matches *)
    assert (length l0 < S (length l0)) by auto.
    rewrite e in H.
    case_eq (nth (length l0) tl trm_def); intros; auto.
    destruct* t.
    destruct* c.
    case_eq (index eq_nat_dec 0 a l0); intros; auto.
    apply term_app.
      destruct (index_ok _ 0 _ _ H1).
      apply value_term.
      apply* (list_forall_out l).
      apply* nth_In.
      unfold Cstr.attr in *; omega.
    assert (term (nth (length l0) tl trm_def)).
      apply value_term.
      apply* (list_forall_out l).
      apply* nth_In.
    rewrite H0 in H2.
    inversion* H2.
    (* sub *)
    destruct* tl.
    case_eq (record_args t nil); intros.
    assert (list_forall value l1).
      inversions l.
      clear -H H3.
      assert (list_forall value nil) by auto.
      revert H H0. generalize (@nil trm).
      destruct H3.
      induction H; simpl; intros; try solve [inversions* H0].
        destruct c; inversions* H.
      apply* (IHvalu1 _ H1).
      constructor; auto.
      exists* n2.
    clear -H0.
    destruct* (index eq_nat_dec 0 a l0).
    gen n; induction H0; simpl; intros; auto; destruct* n.
    (* recf *)
    inversions* l; clear l.
    inversions* H; clear H.
  Qed.

  Lemma closed : forall c, sch_fv (Delta.type c) = {}.
  Proof.
    intros.
    induction c; unfold sch_fv; simpl.
    (* tag *)
    unfold kind_fv; simpl.
    repeat rewrite union_empty_l. auto.
    (* matches *)
    set (x := 1). unfold x at 1.
    unfold kind_fv_list, kind_fv; simpl.
    generalize x; clear.
    induction l; simpl in *; intros;
      repeat rewrite union_empty_l.
      auto.
    use (IHl (S x)); clear IHl. rewrite union_empty_l in H. auto.
    (* record *)
    set (x := 0). unfold x at 1.
    unfold kind_fv_list, kind_fv; simpl.
    generalize x; clear.
    induction l; simpl in *; intros;
      repeat rewrite union_empty_l.
      auto.
    use (IHl (S x)).
    (* sub *)
    unfold kind_fv; simpl.
    repeat rewrite union_empty_l. auto.
    (* recf *)
    simpl.
    repeat rewrite union_empty_l. auto.
  Qed.

  Lemma type_nth_typ_vars : forall n Xs,
    n < length Xs -> Defs.type (nth n (typ_fvars Xs) typ_def).
  Proof.
    induction n; destruct Xs; simpl; intros; try (elimtype False; omega).
      auto.
    apply IHn; omega.
  Qed.

  Hint Extern 1 (Defs.type (nth _ (typ_fvars _) typ_def)) =>
    solve [apply type_nth_typ_vars; omega].

  Lemma scheme : forall c, scheme (Delta.type c).
  Proof.
    intros. intro; intros.
    unfold typ_open_vars.
    destruct c; simpl in *.
    (* tag *)
    do 3 (destruct Xs; try discriminate).
    simpl.
    split*.
    unfold All_kind_types.
    repeat (constructor; simpl*).
    (* matches *)
    rewrite map_length, seq_length in H.
    split.
      do 2 (destruct Xs; try discriminate).
      inversion H; clear H.
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
    generalize 2; induction n; simpl; intros. auto.
    constructor. apply* IHn. omega.
    simpl*.
    (* record *)
    rewrite map_length, seq_length in H.
    assert (1 + length l = length Xs) by omega. clear H.
    split.
      assert (0 < 1) by omega.
      revert H0 H.
      generalize 1 Xs. clear.
      induction (length l); simpl; intros. auto.
      constructor. auto.
      apply* IHn.
    repeat (constructor; auto).
      clear; generalize 0; induction (length l); simpl*.
    unfold All_kind_types. simpl.
    rewrite list_snd_combine by (rewrite map_length, seq_length; auto).
    revert H0; generalize 1.
    unfold Cstr.attr in *.
    clear; induction (length l); simpl; intros. auto.
    constructor. apply* IHn.
    simpl*.
    (* sub *)
    split. simpl*.
    repeat (constructor; auto).
    unfold All_kind_types. simpl.
    repeat (constructor; auto). simpl*.
    (* recf *)
    repeat (constructor; simpl*).
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
    list_forall2 (fun U1 U2 => typ_open U1 Us = U2) TL1 TL2.
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
      list_forall2 (typing (false,gc) K E) tl TL.
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
    list_forall2 (typing (false,gc) K E) vl TL -> False.
  Proof.
    introv Hv TypC TypA.
    inversions TypC; try discriminate. clear TypC H4.
    destruct* vl; try destruct* vl; try destruct* vl; try discriminate.
    inversions TypA; clear TypA.
    inversions H6; clear H6.
    inversions H8; clear H8.
    unfold sch_open in H0.
    simpl in H0.
    inversions H0. clear H0.
    destruct H5 as [_ WK]. simpl in WK.
    inversions WK; clear WK.
    inversions H7; clear H7.
    inversions H5; clear H5.
    discriminate.
  Qed.

  Lemma typing_value_inv : forall gc K E t T n,
    K;E |(false,gc)|= t ~: T -> valu n t ->
    (exists t1, t = trm_abs t1) \/
    (exists c, exists vl, t = const_app c vl /\
      n <= Const.arity c /\ list_for_n value (Const.arity c - n) vl).
  Proof.
    intros.
    gen K E T. induction H0; intros.
        left. esplit; reflexivity.
      right; exists c; exists (@nil trm).
      split*.
      rewrite <- minus_n_n. split*. split*.
    clear IHvalu2.
    inversions H; clear H; try discriminate.
    rewrite gc_lower_false in *.
    destruct (IHvalu1 _ _ _ H4); clear IHvalu1.
      destruct H. subst. inversion H0_.
    destruct H as [c [vl [HE [HC HV]]]].
    subst.
    right; exists c; exists (vl ++ t2 :: nil).
    rewrite const_app_app. split*.
    split. omega.
    destruct HV. split*.
    assert (value t2) by exists* n2.
    apply* list_forall_app.
  Qed.

  Lemma value_fvar_is_const : forall K E gc t x k,
    K; E |(false,gc)|= t ~: typ_fvar x ->
    binds x (Some k) K ->
    Cstr.cstr_sort (kind_cstr k) = Cstr.Ksum ->
    value t ->
    exists v, exists t2, t = trm_app (trm_cst (Const.tag v)) t2.
  Proof.
    introv Typ B HS HV.
    destruct HV as [i vi].
    destruct (typing_value_inv Typ vi).
      destruct H. subst. inversions Typ. discriminate.
    destruct H as [c [vl [HE [HA Hvl]]]].
    subst.
    destruct (fold_app_inv _ _ Typ) as [TL [Typ0 TypA]]; clear Typ.
    inversions Typ0; clear Typ0; try discriminate.
    unfold sch_open in H0. destruct H5. clear H.
    destruct c; simpl in *.
        destruct  Hvl.
        destruct i.
        inversions TypA; clear TypA; try discriminate.
        inversions H6; clear H6; try discriminate.
        esplit; esplit; reflexivity.
        inversions TypA; try discriminate.
       case_eq (cut (length TL) (map Delta.matches_arg (seq 2 (length l))));
         introv R1.
       assert (length TL <= length (map Delta.matches_arg (seq 2 (length l)))).
         rewrite map_length, seq_length.
         rewrite <- (list_forall2_length TypA). rewrite <- (proj1 Hvl).
         omega.
       destruct (cut_ok _ H R1). clear H. rewrite H5 in H0.
       rewrite fold_right_app in H0.
       destruct* (fold_arrow_eq _ _ _ _ _ H0).
       destruct l1; discriminate.
      case_eq (cut (length TL) (map typ_bvar (seq 1 (length l))));
        introv R1.
      assert (length TL <= length (map typ_bvar (seq 1 (length l)))).
        rewrite map_length, seq_length.
        rewrite <- (list_forall2_length TypA). rewrite <- (proj1 Hvl).
        omega.
      destruct (cut_ok _ H R1). clear H. rewrite H5 in H0.
      rewrite fold_right_app in H0.
      destruct* (fold_arrow_eq _ _ _ _ _ H0).
      destruct l1; try discriminate.
      simpl in H.
      inversions H2; clear H2. simpl in H; subst.
      inversions H9; clear H9.
      puts (binds_func H8 B). inversions H; clear H H8.
      destruct H10. clear -H HS.
      simpl in H.
      destruct H. destruct H; rewrite H in HS; discriminate.
     destruct Hvl.
     inversions TypA; try discriminate.
    destruct Hvl.
    inversions TypA; clear TypA; try discriminate.
    inversions H0; clear H0.
    inversions H6; clear H6; try discriminate.
    destruct i; discriminate.
  Qed.

  Lemma value_prod_is_record : forall K E gc t x k,
    K; E |(false,gc)|= t ~: typ_fvar x ->
    binds x (Some k) K ->
    Cstr.cstr_sort (kind_cstr k) = Cstr.Kprod ->
    value t ->
    exists l, exists nd:NoDup l, exists tl,
      t = const_app (Const.record nd) tl /\ length tl = length l.
  Proof.
    introv Typ B HS HV.
    destruct HV as [i vi].
    destruct (typing_value_inv Typ vi).
      destruct H. subst. inversions Typ. discriminate.
    destruct H as [c [vl [HE [HA Hvl]]]].
    subst.
    destruct (fold_app_inv _ _ Typ) as [TL [Typ0 TypA]]; clear Typ.
    inversions Typ0; clear Typ0; try discriminate.
    unfold sch_open in H0. destruct H5. clear H.
    destruct c; simpl in *.
        destruct TL; try discriminate.
        inversions H0; clear H0.
        inversions H2; clear H2.
        inversions H7; clear H7.
        simpl in H5.
        inversions H2; clear H2.
        destruct TL; try discriminate.
        inversions H9; clear H9.
        puts (binds_func H0 B). inversions H; clear H H0.
        destruct H7. clear -H HS.
        simpl in H.
        destruct H. destruct H; rewrite H in HS; discriminate.
       case_eq (cut (length TL) (map Delta.matches_arg (seq 2 (length l))));
         introv R1.
       assert (length TL <= length (map Delta.matches_arg (seq 2 (length l)))).
         rewrite map_length, seq_length.
         rewrite <- (list_forall2_length TypA). rewrite <- (proj1 Hvl).
         omega.
       destruct (cut_ok _ H R1). clear H. rewrite H5 in H0.
       rewrite fold_right_app in H0.
       destruct* (fold_arrow_eq _ _ _ _ _ H0).
       destruct l1; discriminate.
      case_eq (cut (length TL) (map typ_bvar (seq 1 (length l))));
        introv R1.
      assert (length TL <= length (map typ_bvar (seq 1 (length l)))).
        rewrite map_length, seq_length.
        rewrite <- (list_forall2_length TypA). rewrite <- (proj1 Hvl).
        omega.
      destruct (cut_ok _ H R1). clear H. rewrite H5 in H0.
      rewrite fold_right_app in H0.
      destruct* (fold_arrow_eq _ _ _ _ _ H0).
      destruct l1; try discriminate.
      simpl in H. rewrite <- app_nil_end in H5.
      exists l. exists n. exists vl.
      split*. subst. length_hyps. rewrite seq_length in *. omega.
     destruct Hvl.
     inversions TypA; try discriminate.
    destruct Hvl.
    inversions TypA; clear TypA; try discriminate.
    inversions H0; clear H0.
    inversions H6; clear H6; try discriminate.
    destruct i; discriminate.
  Qed.

  Lemma fold_right_app_end : forall T1 T2 TL,
    fold_right typ_arrow (typ_arrow T1 T2) TL =
    fold_right typ_arrow T2 (TL ++ T1 :: nil).
  Proof.
    intros; rewrite* fold_right_app.
  Qed.
    
  Lemma in_matches_types : forall i l TL Us,
    i < length l ->
    In (nth i l 0, nth i Us typ_def)
    (map_snd (fun T => typ_open T (TL ++ Us))
      (combine l (map typ_bvar (seq (length TL) (length l))))).
  Proof.
    intros.
    remember (0 + i) as m.
    pattern i at 2.
    replace i with (0+i) by reflexivity. rewrite <- Heqm.
    generalize 0 at 1. intro d.
    replace (length TL) with (0 + length TL) by auto.
    gen i; generalize 0; induction l; intros.
    simpl in H; elimtype False; omega.
    destruct i; simpl.
      replace m with n; auto. rewrite app_nth2.
      replace (n + length TL - length TL) with n by omega.
      auto.  omega. omega.
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
    (* tag *)
    elim (tag_is_const _ (proj1 vl) Typ0 TypA).
    (* matches *)
    inversions Typ0; try discriminate. clear Typ0.
    unfold sch_open in H0. simpl in H0.
    rewrite fold_right_app_end in H0.
    poses Hlen (proj1 vl). simpl in Hlen.
    destruct (fold_arrow_eq _ _ _ _ _ H0) as [HT HA]; clear H0.
      generalize (list_forall2_length TypA).
      autorewrite with list. simpl. intros; omega.
    forward~ (list_forall2_nth trm_def typ_def TypA (n:=length l)) as Typn.
      rewrite* <- Hlen.
    forward~ (list_forall2_nth typ_def typ_def HA (n:=length l)) as Eqn.
      autorewrite with list. simpl*. omega.
    rewrite app_nth2 in Eqn; [|rewrite map_length; rewrite* seq_length].
    autorewrite with list in Eqn.
    rewrite <- minus_n_n in Eqn.
    simpl in Eqn.
    destruct H5 as [_ WUs]. simpl in WUs.
    inversions WUs; clear WUs.
    inversions H5; clear H5.
    simpl in Eqn.
    inversions H2; clear H2.
    rewrite <- H8 in *; clear H8.
    destruct (value_fvar_is_const Typn H0) as [v [t2 Hv]].
        destruct H6 as [[H _] _]. simpl in H. destruct* H.
        clear -H. destruct k'.
        elimtype False. simpl in H.
        destruct kind_valid0. elim (H0 H).
      apply* (list_forall_out (proj2 vl)). apply* nth_In. omega.
    simpl.
    rewrite Hv in *; clear Hv.
    inversions Typn; clear Typn; try discriminate.
    rewrite gc_lower_false in *.
    inversions H9; clear H9; try discriminate.
    destruct H14.
    destruct H as [H _]. simpl in H.
    do 3 (destruct Us; try discriminate). clear H.
    simpl in *.
    inversions H2; clear H2.
    inversions H15; clear H15. clear H14.
    inversions H8; clear H8.
    puts (binds_func H9 H0).
    inversions H; clear H H9 H12 H13.
    destruct H6; destruct H14.
    destruct H; destruct H5. destruct H9.
    destruct k' as [[ks kcl kch] kv kr kh]; simpl in *.
    destruct* kch.
    assert (Hvt: In (v,t) kr) by auto*. clear H6 H12.
    unfold Cstr.valid in kv; simpl in kv.
    assert (Hvl: In v l).
      apply (proj2 H8). apply* (proj2 kv).
    case_eq (index eq_nat_dec 0 v l); introv R2;
      try elim (index_none_notin _ _ _ _ R2 Hvl).
    destruct (index_ok _ 0 _ _ R2).
    assert (Hvn: In (v, nth n0 lb0 typ_def) kr).
      rewrite <- H12. apply H2.
      pose (TL1 := typ_fvar x :: b0 :: nil).
      replace (typ_fvar x :: b0 :: lb0) with (TL1 ++ lb0) by auto.
      replace 2 with (length TL1) by auto.
      apply* in_matches_types.
    forward~ (list_forall2_nth trm_def typ_def TypA (n:=n0)) as Typv.
      unfold Cstr.attr in *; omega.
    forward~ (list_forall2_nth typ_def typ_def HA (n:=n0)) as Eqv.
      rewrite (list_forall2_length HA).
      rewrite <- (list_forall2_length TypA).
      unfold Cstr.attr in *; omega.
    rewrite <- Eqv in Typv; clear Eqv.
    rewrite app_nth1 in Typv; [|rewrite map_length; rewrite* seq_length].
    rewrite (map_nth _ 0) in Typv; [|rewrite* seq_length].
    rewrite seq_nth in Typv; auto.
    simpl in Typv.
    assert (nth n0 lb0 typ_def = t).
      apply (kh v); trivial.
      unfold Cstr.unique.
      apply set_mem_correct2. simpl. unfold set_In. auto*.
    rewrite H13 in Typv.
    apply* typing_app; rewrite gc_lower_false; auto*.
    (* record *)
    elimtype False.
    inversions Typ0; try discriminate.
    puts (proj1 vl).
    simpl in H.
    unfold sch_open in H0. simpl in H0.
    destruct TL using rev_ind. inversion TypA. subst; discriminate.
    clear IHTL. rewrite fold_right_app in H0.
    puts (fold_arrow_eq _ _ _ _ _ H0).
    rewrite map_length, seq_length in H2.
    puts (list_forall2_length TypA). rewrite app_length in H3; simpl in H3.
    destruct H2. omega.
    destruct H5.
    simpl in H7. inversions H7; clear H7.
    inversions H10; clear H10. discriminate.
    (* sub *)
    inversions Typ0; clear Typ0; try discriminate.
    puts (proj1 vl). simpl in H.
    do 2 (destruct tl; try discriminate).
    inversions TypA; clear TypA.
    inversions H8; clear H8.
    unfold sch_open  in H0; simpl in H0.
    destruct H5.
    inversions H3; clear H3.
    inversions H10; clear H10.
    inversions H11; clear H11. simpl in *.
    inversions H0; clear H0 H8.
    destruct vl. clear H H0.
    inversions H3; clear H3.
    clear H5.
    inversions H7; clear H7.
    case_eq (Delta.record_args t nil); introv R1.
    destruct* (value_prod_is_record H6 H0) as [l' [nd [vl [HE HL]]]].
      destruct H5 as [[H _] _]. simpl in H. destruct* H.
      clear -H. destruct k'.
      elimtype False. simpl in H.
      destruct kind_valid0. elim (H0 H).
    subst.
    assert (l' = l /\ l0 = vl).
      clear -HL R1.
      set (vl0 := @nil trm) in *.
      assert (l' = l /\ l0 = vl ++ vl0).
        assert (length vl + length vl0 = length l').
          simpl. omega.
        clear HL; clearbody vl0.
        gen vl0; induction vl using rev_ind; simpl; intros.
          inversions* R1.
        rewrite const_app_app in R1.
        rewrite app_length in *; simpl in *.
        destruct (IHvl _ R1). simpl*.
        subst.
        rewrite app_ass. simpl*.
      subst vl0. rewrite <- app_nil_end in H. auto.
    destruct H. subst.
    destruct (fold_app_inv _ _ H6) as [TL [Typ0 TypA]]; clear H6.
    inversions Typ0; clear Typ0; try discriminate.
    unfold sch_open in H3; simpl in H3.
    destruct (fold_arrow_eq _ _ _ _ _ H3).
      rewrite map_length, seq_length. auto.
    destruct H11 as [_ WS].
    simpl in WS.
    inversions WS; clear WS.
    simpl in H; subst.
    inversions H12; clear H12.
    puts (binds_func H13 H0).
    inversions H; clear H H13.
    clear R1.
    puts (proj33 (proj1 H15)).
    puts (proj32 (proj1 H5)).
    destruct k' as [[ks kl km] kv kr kh]. simpl in *.
    destruct* km.
    puts (proj2 kv). simpl in H11.
    assert (In a l) by auto.
    case_eq (index eq_nat_dec 0 a l); introv R1;
      [|elim (index_none_notin _ _ _ _ R1 H12)].
    destruct (index_ok _ 0  _ _ R1).
    forward~ (list_forall2_nth Delta.trm_default typ_def TypA (n:=n)) as Typ.
      rewrite* HL.
    rewrite (kh a T (nth n TL typ_def)). auto.
        unfold Cstr.unique. simpl. apply* set_mem_correct2. apply* H9.
      apply (proj2 H5).
      simpl*.
    assert (Hvn: In (a, nth n lb typ_def) kr).
      apply (proj2 H15).
      simpl.
      pose (TL1 := typ_fvar x :: nil).
      replace (typ_fvar x :: lb) with (TL1 ++ lb) by auto.
      replace 1 with (length TL1) by auto.
      rewrite <- H16.
      apply* in_matches_types.
    forward~ (list_forall2_nth typ_def typ_def H7 (n:=n)) as Eqv.
      rewrite map_length, seq_length; auto.
    rewrite <- Eqv.
    rewrite (map_nth _ 0).
      rewrite* seq_nth.
    rewrite* seq_length.
    (* recf *)
    puts (proj1 vl).
    inversions TypA; clear TypA; try discriminate.
    inversions H1; clear H1; try discriminate.
    inversions H3; clear H3; try discriminate.
    simpl in *.
    inversions Typ0; try discriminate.
    eapply typing_app; rewrite* gc_lower_false.
    eapply typing_app; rewrite* gc_lower_false.
    

  Definition reduce_clos c (cl : list clos) :=
    match c with
    | Const.tag _ => (clos_def, nil)
    | Const.matches l nd =>
      match nth (length l) cl clos_def with
      | clos_const (Const.tag t) (cl1 :: nil) =>
        match index eq_nat_dec 0 t l with
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
      case_eq (index eq_nat_dec 0 a l); introv R2; simpl*.
      destruct (index_ok _ 0 _ _ R2).
      unfold Cstr.attr in *.
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
        destruct (index eq_nat_dec 0 a l).
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
        destruct (index eq_nat_dec 0 a l).
          split*.
          apply* equiv_cl_nth.
        auto.
      auto.
    auto.
  Qed.
End SndHyp.

Module Sound3 := Infer2.MyEval2.Mk3(SndHyp).
(* Module Sound3 := MyEval2.Mk3(SndHyp). *)
