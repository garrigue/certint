(***************************************************************************
* Preservation and Progress for mini-ML with structural polymorphism       *
* Jacques Garrigue, May 2008                                               *
***************************************************************************)

Set Implicit Arguments.
Require Import Lib_FinSet Metatheory List ListSet Arith.
Require Import ML_SP_Infrastructure ML_SP_Soundness ML_SP_Eval.
(* Require Import ML_SP_Unify ML_SP_Rename ML_SP_Inference. *)

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
Import Rename.Unify.MyEval.Sound.Infra. *)
Module MyEval := MkEval(Cstr)(Const).
Import MyEval.
Import Sound.Infra.
Import Defs.

Inductive closed_n : nat -> trm -> Prop :=
  | cln_fvar : forall n x, closed_n n (trm_fvar x)
  | cln_bvar : forall n m, m < n -> closed_n n (trm_bvar m)
  | cln_app  : forall n t1 t2,
      closed_n n t1 -> closed_n n t2 -> closed_n n (trm_app t1 t2)
  | cln_cst  : forall n c, closed_n n (trm_cst c).

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
Qed.

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
  Definition matches_lhs l (ND:NoDup l) k :=
    trm_app
      (const_app (Const.matches ND) (map trm_bvar (seq 1 (length l))))
      (trm_app (trm_cst (Const.tag (nth k l var_default)))
        (trm_bvar 0)).
  Definition matches_rhs k :=
    trm_app (trm_bvar (S k)) (trm_bvar 0).
  Definition rule n t1 t2 :=
    exists l, exists ND:NoDup l, exists k,
      n = S (length l) /\ k < length l /\
      t1 = matches_lhs ND k /\ t2 = matches_rhs k.

  Hint Constructors closed_n.
  Lemma closed_n_fold_app : forall n m k t,
    m + k <= n -> closed_n n t ->
    closed_n n (fold_left trm_app (map trm_bvar (seq k m)) t).
  Proof.
    induction m; simpl; intros.
      auto.
    apply IHm. omega.
    apply* cln_app.
    apply cln_bvar. omega.
  Qed.
  Lemma term : forall n t1 t2 tl,
    rule n t1 t2 ->
    list_for_n term n tl ->
    term (trm_inst t1 tl) /\ term (trm_inst t2 tl).
  Proof.
    intros.
    destruct H as [l [ND [k [N [K [T1 T2]]]]]].
    subst.
    destruct H0.
    split; apply* term_trm_inst_closed.
      unfold matches_lhs.
      apply cln_app.
      unfold const_app.
      apply* closed_n_fold_app. destruct H0; omega.
      apply* cln_app.
      apply cln_bvar. destruct H0; omega.
    unfold matches_rhs.
    apply cln_app; apply cln_bvar; omega.
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

(* Module Infer2 := Mk2(Delta).
Import Infer2.Rename2.MyEval2. *)
Module MyEval2 := Mk2(Delta).
Import MyEval2.
Import Sound2.
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
    split*. apply* For_all2_app.
    simpl. split*.
  Qed.

  Lemma map_nth : forall (A B:Set) d1 d2 (f:A->B) k l,
    k < length l -> nth k (map f l) d1 = f (nth k l d2).
  Proof.
    induction k; intros; destruct l; simpl in *; auto; try elim (lt_n_O _ H).
    apply IHk.
    apply* lt_S_n.
  Qed.

  Lemma nth_In_eq : forall (A:Set) n l l' (d:A),
    n < length l -> n < length l' ->
    nth n l d = nth n l' d -> In (nth n l d) l'.
  Proof.
    intros. rewrite H1. apply* nth_In.
  Qed.

  Lemma nth_map : forall (A:Set) d1 (B:Set) (f:A->B) d2 n l,
    n < length l -> nth n (map f l) d2 = f (nth n l d1).
  Proof.
    induction n; intros; destruct l; try elim (lt_n_O _ H); simpl in *.
      auto.
    apply IHn. apply* lt_S_n.
  Qed.

  Require Import Min.

  Hint Rewrite combine_length combine_nth : list.

  Lemma get_kind_for_matches : forall k l (ND:NoDup l) t K E gc Us,
    k < length l ->
    proper_instance K (sch_kinds (Delta.type (Const.matches ND))) Us ->
    K; E |(false,gc)|= trm_app (trm_cst (Const.tag (nth k l var_default)))
                    t ~: nth 0 Us typ_def ->
    K; E |(false,gc)|= t ~: nth (S (S k)) Us typ_def.
  Proof.
    introv Hk PI Typ.
    destruct PI as [[Arity _] WK].
    simpl in Arity. autorewrite with list in Arity.
    simpl in WK.
    destruct* Us. destruct* Us. simpl in *.
    inversion Arity as [Ary]; clear Arity.
    destruct WK as [WK _].
    inversions WK. clear WK.
    destruct H2 as [_ HE]. simpl in *.
    inversions Typ; try discriminate. clear Typ.
    rewrite gc_lower_false in *.
    inversions H4; try discriminate. clear H4 H8.
    destruct H9 as [_ WK'].
    destruct* Us0. discriminate.
    simpl in WK'. destruct WK' as [_ WK].
    destruct* Us0.
    destruct* Us0.
    destruct WK as [WK _].
    inversions WK. clear WK; simpl in *.
    inversions H2; clear H2.
    use (binds_func H0 H1). inversion H; clear H H1; subst k'0.
    destruct H4; simpl in *.
    destruct k' as [kc kv kr kh]; simpl in *.
    rewrite (kh (nth k l var_default) t0 (nth k Us typ_def)) in H6; auto.
      unfold Cstr.unique.
      destruct H as [Hlow _]. simpl in Hlow.
      apply set_mem_correct2.
      apply* Hlow.
    apply HE.
    clear HE t0 H6 H7 H H1.
    rewrite* <- combine_nth.
    apply* nth_In_eq.
        rewrite combine_length.
        rewrite* min_l.
        rewrite* Ary.
      autorewrite with list.
      rewrite* min_l.
    rewrite* (nth_map (var_default, typ_def));
      autorewrite with list; simpl; autorewrite with list; auto.
      rewrite (nth_map 0).
        rewrite* seq_nth.
      rewrite* seq_length.
    rewrite* min_l.
  Qed.

  Lemma delta_typed : forall n t1 t2 tl K E gc T,
    Delta.rule n t1 t2 ->
    list_for_n term n tl ->
    K ; E |(false,gc)|= trm_inst t1 tl ~: T ->
    K ; E |(false,gc)|= trm_inst t2 tl ~: T.
  Proof.
    intros.
    clear H0.
    destruct H as [l [ND [k [HN [HK [T1 T2]]]]]].
    subst.
    inversions H1; try discriminate; clear H1.
    rewrite gc_lower_false in *.
    rewrite trm_inst_app in H4.
    unfold const_app in H4.
    destruct (fold_app_inv _ _ H4) as [TL [Typ0 TypA]]; clear H4.
    unfold trm_inst; simpl.
    inversions Typ0; try discriminate. clear Typ0 H1 H4.
    unfold sch_open in H0. simpl in H0.
    destruct (fold_arrow_eq _ _ _ _ _ H0); clear H0.
      generalize (For_all2_length _ _ _ TypA).
      autorewrite with list. auto.
    generalize (For_all2_nth _ trm_def typ_def _ TL TypA (n:=k)); clear TypA.
    autorewrite with list; intro TypA.
    generalize (For_all2_nth _ typ_def typ_def _ TL H1 (n:=k)); clear H1.
    autorewrite with list; intro EQ.
    rewrite <- EQ in TypA; auto; clear EQ TL.
    rewrite (map_nth trm_def trm_def) in TypA.
     rewrite (map_nth trm_def 0) in TypA.
      rewrite seq_nth in TypA; auto.
      rewrite (map_nth typ_def 0) in TypA.
       rewrite seq_nth in TypA; auto.
       simpl in TypA, H.
       inversions H; clear H.
       eapply typing_app; rewrite* gc_lower_false.
       apply* get_kind_for_matches.
      rewrite* seq_length.
     rewrite* seq_length.
    autorewrite with list; auto.
  Qed.

  Fixpoint typ_arity (T:typ) : nat :=
    match T with
    | typ_arrow T1 T2 => S (typ_arity T2)
    | _ => 0
    end.

  Lemma fold_arrow_open : forall T TL Us,
    typ_open (fold_right typ_arrow T TL) Us =
    fold_right typ_arrow (typ_open T Us) (map (fun T:typ => typ_open T Us) TL).
  Proof.
    induction TL; simpl; intros; auto.
    rewrite* IHTL.
  Qed.

  Lemma typ_arity_fold_arrow : forall T TL,
    typ_arity (fold_right typ_arrow T TL) = length TL + typ_arity T.
  Proof.
    induction TL; simpl; auto.
  Qed.

  Lemma value_is_tag : forall K gc v n T,
    K; empty |(false,gc)|= v ~: T ->
    valu n v ->
    typ_arity T <= n ->
    exists l, exists tl, v = const_app (Const.tag l) tl.
  Proof.
    induction v; introv Typv Hv TA; inversions Hv; inversions Typv;
      try discriminate.
      simpl in TA. elim (le_Sn_O _ TA).
      clear IHv2.
      rewrite gc_lower_false in *.
      destruct* (IHv1 (Datatypes.S n) _ H5) as [l [tl EQ]].
        simpl. apply* le_n_S.
      exists l. exists (tl ++ v2 :: nil).
      rewrite EQ.
      unfold const_app; rewrite fold_left_app. auto.
    destruct c.
      exists v. exists (nil (A:=trm)). auto.
    elim (le_not_lt _ _ TA). clear.
    unfold sch_open; simpl.
    rewrite fold_arrow_open.
    rewrite typ_arity_fold_arrow.
    autorewrite with list.
    simpl. omega.
  Qed.

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

  Lemma seq_in : forall k n m, In k (seq m n) -> m <= k < m+n.
  Proof.
    induction n; intros. elim H.
    simpl in H; destruct H.
      rewrite H. omega.
    destruct* (IHn (S m)).
    omega.
  Qed.

  Lemma map_inst_bvar : forall t l,
    l = map (trm_inst_rec 0 (t :: l)) (map trm_bvar (seq 1 (length l))).
  Proof.
    induction l; simpl; auto.
    apply (f_equal (cons a)).
    rewrite <- seq_shift.
    pattern l at 1. rewrite IHl.
    clear.
    rewrite map_map.
    rewrite map_map.
    rewrite map_map.
    apply list_map_ext.
    intros.
    simpl.
    rewrite <- minus_n_O.
    destruct (seq_in _ _ _ H).
    destruct x.
      elim (le_Sn_O _ H0).
    apply nth_indep. omega.
  Qed.

  Lemma typing_tag_inv : forall K E gc l tl x,
    K; E |(false,gc)|= const_app (Const.tag l) tl ~: typ_fvar x ->
    exists t, exists T, exists k,
      tl = t :: nil /\  K; E |(false,gc)|= t ~: T /\ binds x (Some k) K
      /\ exists M, entails k (@Kind _ (Delta.valid_tag l) ((l, T) :: nil) M).
  Proof.
    introv Typv.
    unfold const_app in Typv.
    destruct* (fold_app_inv _ _ Typv) as [TL [Typc Typa]]; clear Typv.
    inversions Typc; try discriminate. clear Typc H1 H4.
    destruct H5 as [_ WK].
    unfold sch_open in H0; simpl in H0.
    destruct TL as [|T TL]. discriminate.
    destruct tl. elim Typa.
    exists t. exists T.
    simpl in H0; inversions H0; clear H0.
    simpl in WK.
    destruct* Us. destruct* Us. destruct* Us.
    destruct WK as [_ [WK _]].
    inversions WK; clear WK.
    exists k'.
    destruct TL; try discriminate.
    simpl in H2; inversion H2; subst x0; clear H2.
    simpl in Typa.
    destruct Typa.
    destruct tl; try elim H1.
    intuition.
    unfold ckind_map in H3.
    destruct (ckind_map_spec
               (fun T : typ => typ_open T (t0 :: typ_fvar x :: nil))
               (Kind (Delta.valid_tag l) (Delta.coherent_tag (t:=l)))).
    destruct x0 as [kc kv kr kh]; simpl in *.
    destruct a; subst.
    exists* kh.
  Qed.

  Lemma const_arity_ok0 : forall c vl K gc T,
    S(Const.arity c) = length vl ->
    K ; empty |(false,gc)|= const_app c vl ~: T ->
    exists l, exists ND : NoDup l, exists Us, exists v, exists vl',
      vl = rev (v :: vl') /\ c = Const.matches ND /\ length l = length vl' /\
      proper_instance K (sch_kinds (Delta.type (Const.matches ND))) Us /\
      K; empty |(false,gc)|= v ~: nth 0 Us typ_def.
  Proof.
    intros.
    unfold const_app in H0.
    use (fold_app_inv _ _ H0).
    clear H0; destruct H1 as [TL [TypC TypA]].
    destruct c.
      elim (tag_is_const _ _ _ H TypC TypA).
    exists l. exists n.
    inversions TypC; try discriminate. clear TypC H5.
    exists Us.
    simpl in H.
    unfold sch_open in H1; simpl in H1.
    rewrite <- (rev_involutive TL) in *.
    destruct (rev TL) as [|T' TL'].
      destruct vl. discriminate.
      elim TypA.
    rewrite <- (rev_involutive vl) in *.
    destruct (rev vl) as [|v vl'].
      discriminate.
    exists v. exists vl'.
    rewrite rev_length in H. simpl in H; inversion* H.
    intuition.
    use (For_all2_rev _ _ _ TypA); clear TypA.
    autorewrite with list in H0.
    simpl in H0; destruct H0 as [Typv TypA].
    rewrite cons_append in H1.
    rewrite distr_rev in H1.
    rewrite fold_right_app in H1. simpl in H1.
    destruct (fold_arrow_eq _ _ _ _ _ H1); clear H1.
      autorewrite with list.
      rewrite H3. apply* For_all2_length.
    simpl in H0. inversions* H0.
  Qed.

  Lemma const_arity_ok : forall c vl K gc T,
    list_for_n value (S(Const.arity c)) vl ->
    K ; empty |(false,gc)|= const_app c vl ~: T ->
    exists n:nat, exists t1:trm, exists t2:trm, exists tl:list trm,
      Delta.rule n t1 t2 /\ list_for_n term n tl /\
      const_app c vl = trm_inst t1 tl.
  Proof.
    intros.
    destruct (const_arity_ok0 _ _ (proj1 H) H0) as
      [l [ND [Us [v [vl' [Evl [Ec [Hvl' [PI Typv]]]]]]]]]; clear H0.
    subst.
    exists (S (length l)).
    destruct PI as [_ WK].
    destruct Us; simpl in Typv.
      assert (type typ_def). auto.
      inversion H0.
    destruct H as [_ Val].
    use (list_forall_rev Val); clear Val.
    rewrite rev_involutive in H.
    inversions H; clear H.
    destruct H3 as [vn Hv].
    use (proj1 WK). inversions H; clear H WK.
    destruct* (value_is_tag (n:=vn) Typv) as [l' [tl' EQ]].
      auto with arith.
    clear vn Hv.
    subst.
    destruct (typing_tag_inv _ _ Typv) as
      [t [T' [k [EQ [Typa [Bk Ek]]]]]]; clear Typv.
    use (binds_func H1 Bk). inversion H; subst; clear H H1.
    destruct H4 as [[_ High] _].
    destruct Ek as [M [[Low _] _]].
    destruct k as [[kl kh] kv kr kch]; simpl in *.
    destruct* kh as [kh|].
    unfold Cstr.valid in kv. simpl in kv.
    assert (In l' l) by auto.
    clear High Low kl kh kv kr kch Bk x Us.
    destruct (exists_nth var_default _ _ H) as [n [Hlen EQ]].
    clear H; subst l'.
    exists (Delta.matches_lhs ND n).
    exists (Delta.matches_rhs n).
    exists (t :: rev vl').
    split3.
      unfold Delta.rule. exists l; exists ND; exists n. auto.
      split*. simpl. rewrite rev_length. rewrite* Hvl'.
      constructor; auto.
      apply* list_forall_rev.
      apply (list_forall_imp _ value_regular H2).
    unfold Delta.matches_lhs.
    unfold trm_inst.
    simpl; rewrite trm_inst_app.
    unfold const_app.
    rewrite fold_left_app.
    simpl.
    rewrite Hvl'.
    rewrite <- (rev_length vl').
    rewrite <- (map_inst_bvar t (rev vl')).
    auto.
  Qed.
    
  Lemma delta_arity : forall n t1 t2,
    Delta.rule n t1 t2 ->
    exists c, exists pl, t1 = const_app c pl /\ length pl = S(Const.arity c).
  Proof.
    intros.
    destruct H as [tl [ND [k [L1 [L2 [LHS RHS]]]]]].
    unfold Delta.matches_lhs in LHS.
    exists (Const.matches ND).
    exists (map trm_bvar (seq 1 (length tl)) ++
            trm_app (trm_cst (Const.tag (nth k tl var_default))) (trm_bvar 0)
            :: nil).
    split.
      rewrite LHS.
      unfold const_app.
      rewrite fold_left_app.
      simpl. auto.
    simpl.
    autorewrite with list.
    simpl.
    rewrite plus_comm.
    auto.
  Qed.
 
  Definition get_tag cl :=
    match cl with
    | clos_const (Const.tag t) (cl1 :: nil) => Some (t, cl1)
    | _ => None
    end.

  Definition delta_red c (cl : list clos) :=
    match c with
    | Const.tag _ => (clos_def, nil)
    | Const.matches l nd =>
      match get_tag (nth (length l) cl clos_def) with
      | Some (t, cl1) =>
        match index eq_var_dec 0 t l with
        | Some i => (nth i cl clos_def, cl1 :: nil)
        | None => (clos_def, nil)
        end
      | None => (clos_def, nil)
      end
    end.

  Lemma delta_red_sound : forall c cls,
    list_for_n clos_ok (S(Const.arity c)) cls ->
    exists t1:trm, exists t2:trm, exists tl:list trm,
    forall K E T,
      K ; E |Gc|= const_app c (List.map clos2trm cls) ~: T ->
      let (cl', cls') := delta_red c cls in
      Delta.rule (length tl) t1 t2 /\ list_forall term tl /\
      const_app c (List.map clos2trm cls) = trm_inst t1 tl /\
      app2trm (clos2trm cl') cls' = trm_inst t2 tl /\
      clos_ok cl' /\ list_forall clos_ok cls'.
  Proof.
    intros.
    destruct c.
      exists trm_def; exists trm_def; exists (@nil trm).
      intros.
      unfold const_app in H0.
      puts (fold_app_inv _ _ H0).
      clear H0; destruct H1 as [TL [TypC TypA]].
      destruct H. rewrite <- (map_length clos2trm) in H.
      elim (tag_is_const _ _ _ H TypC TypA).
    unfold delta_red.
    case_eq (get_tag (nth (length l) cls clos_def)); introv R.
      destruct p.
      case_eq (index eq_var_dec 0 v l); introv R1.
        rename n0 into i.
        exists (Delta.matches_lhs n i).
        exists (Delta.matches_rhs i).
        case_eq (cut (length l) cls); introv R2.
        exists (map clos2trm (c :: l0)).
        intros.
        destruct H as [Hl Hcls].
        assert (Hl': length l <= length cls).
          simpl in Hl. rewrite <- Hl. omega.
        destruct (cut_ok _ Hl' R2) as [Hl0 Hcut].
        destruct l1.
          elimtype False; subst. simpl in *.
          rewrite app_length in Hl; rewrite Hl0 in Hl.
          simpl in Hl; omega.
        destruct l1.
        split.
          rewrite map_length.
          unfold Delta.rule.
          simpl. exists l. exists n. exists i.
          destruct (index_ok _ v v l R1).
          rewrite* Hl0.
        split.
          apply* (@list_forall_map _ clos_ok _ term clos2trm).
            intros; apply* clos_ok_term.
          rewrite Hcut in Hcls.
          constructor.
            apply list_forall_in; intros; apply* (list_forall_out Hcls).
          case_rewrite R3 (nth (length l) cls clos_def).
          case_rewrite R4 c1.
          case_rewrite R5 l1.
          subst; simpl in R.
          inversions R; clear R.
          destruct l2; try discriminate.
          inversions H1; clear H1.
          assert (clos_ok (clos_const (Const.tag v) (c :: nil))).
            rewrite <- R3.
            apply (list_forall_out Hcls).
            simpl in Hl. apply nth_In. omega.
          inversions H. inversions* H3.
        split.
          unfold Delta.matches_lhs, trm_inst; simpl.
          rewrite trm_inst_app.
          rewrite Hcut.
          unfold const_app; rewrite map_app; rewrite fold_left_app.
          simpl; apply f_equal2.
            apply* (f_equal2 (fold_left trm_app)).
            rewrite <- Hl0.
            clear.
            rewrite <- (map_length clos2trm l0).
            apply map_inst_bvar.
            unfold get_tag in R.
            case_rewrite R3 (nth (length l) cls clos_def).
            rewrite Hcut in R3.
            rewrite app_nth2 in R3.
            rewrite Hl0 in R3.
            rewrite <- minus_n_n in R3. simpl in R3.
            subst; simpl.
            case_rewrite R4 c1.
            case_rewrite R5 l1.
            inversions R.
            destruct (index_ok _ var_default _ _ R1).
            destruct l2; try discriminate.
            rewrite H2; clear H2.
            inversions H1.
            reflexivity.
          
End SndHyp.

Module Sound3 := Infer2.Rename2.MyEval2.Mk3(SndHyp).

