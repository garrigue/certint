(* $Id$ *)

Set Implicit Arguments.
Require Import Lib_FinSet Metatheory List Arith
  ML_SP_Soundness.

Module Cstr.
  Record cstr_impl : Set := C {
    cstr_low  : vars;
    cstr_high : option vars }.
  Definition cstr := cstr_impl.
  Definition valid c :=
    match cstr_high c with
    | None => True
    | Some h => cstr_low c << h
    end.
  Definition entails c1 c2 :=
    cstr_low c2 << cstr_low c1 /\
    match cstr_high c2 with
    | None => True
    | Some h2 =>
      match cstr_high c1 with
      | None => False
      | Some h1 => h1 << h2
      end
     end.
  Lemma entails_refl : forall c, entails c c.
  Proof.
    intros.
    split. apply subset_refl.
    destruct* (cstr_high c). apply subset_refl.
  Qed.
    
  Lemma entails_trans : forall c1 c2 c3,
    entails c1 c2 -> entails c2 c3 -> entails c1 c3.
  Proof.
    introv. intros [CL1 CH1] [CL2 CH2].
    split. apply* subset_trans.
    clear CL1 CL2.
    destruct* (cstr_high c3).
    destruct* (cstr_high c2).
    destruct* (cstr_high c1).
    apply* subset_trans.
  Qed.
  Definition unique c v := v \in cstr_low c.
  Hint Resolve entails_refl.
End Cstr.

Module Const.
  Inductive ops : Set :=
    | tag     : var -> ops
    | matches : list var -> ops.
  Definition const := ops.
  Definition arity op :=
    match op with
    | tag _     => 1
    | matches l => length l
    end.
End Const.

Module Soundness := MkSound(Cstr)(Const).
Import Soundness.
Import Infra.
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
  clear H; gen tl; induction n; intros; destruct tl; try elim (lt_n_O _ H3).
    simpl. inversion* H0.
  simpl.
  apply IHn. inversion* H0.
  apply* lt_S_n.
Qed.

Module Delta.
  Definition matches_arg n := typ_arrow (typ_bvar n) (typ_bvar 1).
  Definition type op :=
    match op with
    | Const.tag t =>
        Sch (typ_arrow (typ_bvar 0) (typ_bvar 1))
            (None ::
             Some (Kind (Cstr.C {{t}} None) ((t,typ_bvar 0)::nil)) :: nil)
    | Const.matches l =>
        Sch (fold_right typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 1))
                 (map matches_arg (seq 2 (length l))))
            (Some (Kind (Cstr.C {} (Some (mkset l)))
                   (combine l (map typ_bvar (seq 2 (length l))))) ::
             map (fun _ => None) (seq 0 (S (length l))))
    end.
  Definition matches_lhs l k :=
    trm_app
      (const_app (Const.matches l) (map trm_bvar (seq 1 (length l))))
      (trm_app (trm_cst (Const.tag (nth k l var_default)))
        (trm_bvar 0)).
  Definition matches_rhs k :=
    trm_app (trm_bvar (S k)) (trm_bvar 0).
  Definition rule n t1 t2 :=
    exists l, exists k,
      n = S (length l) /\ k < length l /\
      t1 = matches_lhs l k /\ t2 = matches_rhs k.

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
    destruct H as [l [k [N [K [T1 T2]]]]].
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
End Delta.

Module Sound2 := Mk2(Delta).
Import Sound2.
Import JudgInfra.
Import Judge.

Module SndHyp.
  Lemma const_closed : forall c, sch_fv (Delta.type c) = {}.
  Proof.
    intros.
    induction c; unfold sch_fv; simpl.
      rewrite union_empty_l. rewrite* union_empty_l.
    assert (exists x, x=1). exists 1. auto.
    destruct H. pattern 1 at -1. rewrite <- H.
    generalize x.
    induction l; simpl; intros; rewrite union_empty_l; rewrite* union_empty_l.
    rewrite union_empty_l. apply IHl.
  Qed.

  Section For_all2.
  Variables (A B:Set) (P:A->B->Prop).

  Lemma For_all2_app : forall u1 u2 v1 v2,
    For_all2 P u1 u2 -> For_all2 P v1 v2 ->
    For_all2 P (app u1 v1) (app u2 v2).
  Proof.
    induction u1; intros; destruct* u2; try elim H.
    simpl; intros.
    split*.
  Qed.

  Lemma For_all2_nth : forall d1 d2 n l1 l2,
    For_all2 P l1 l2 -> n < length l1 ->
    P (nth n l1 d1) (nth n l2 d2).
  Proof.
    induction n; intros; destruct* l1; try elim (lt_n_O _ H0);
      destruct l2; try elim H; simpl; intros; auto.
    apply* IHn. apply* lt_S_n.
  Qed.

  Lemma For_all2_length : forall l1 l2,
    For_all2 P l1 l2 -> length l1 = length l2.
  Proof.
    induction l1; intros; destruct* l2; try elim H.
    intros; simpl. rewrite* (IHl1 l2).
  Qed.

  Lemma For_all2_rev : forall l1 l2,
    For_all2 P l1 l2 ->  For_all2 P (rev l1) (rev l2).
  Proof.
    induction l1; intros; destruct l2; simpl in *; auto; try elim H.
    clear H; intros.
    apply* For_all2_app.
    simpl. auto.
  Qed.
  End For_all2.

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

  Lemma fold_app_inv : forall K E t tl T,
    K ; E |= fold_left trm_app tl t ~: T ->
    exists TL,
      K ; E |= t ~: fold_right typ_arrow T TL /\
      For_all2 (typing K E) tl TL.
  Proof.
    intros K E t tl.
    rewrite <- (rev_involutive tl).
    induction (rev tl); clear tl; simpl; intros.
      exists (nil(A:=typ)). auto.
    rewrite fold_left_app in *; simpl in *.
    inversions H.
    destruct (IHl (typ_arrow S T) H4).
    exists (x ++ S :: nil).
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

  Lemma get_kind_for_matches : forall k l t K E Us,
    k < length l ->
    proper_instance K (Delta.type (Const.matches l)) Us ->
    K; E |= trm_app (trm_cst (Const.tag (nth k l var_default)))
                    t ~: nth 0 Us typ_def ->
    K; E |= t ~: nth (S (S k)) Us typ_def.
  Proof.
    introv Hk PI Typ.
    destruct PI as [[Arity _] [_ WK]].
    unfold sch_arity in Arity.
    simpl in Arity. autorewrite with list in Arity.
    simpl in WK.
    destruct* Us. destruct* Us. simpl in *.
    inversion Arity as [Ary]; clear Arity.
    destruct WK as [WK _].
    inversions WK. clear WK.
    destruct H2 as [_ HE]. simpl in *.
    inversions Typ. clear Typ.
    inversions H4. clear H4 H8.
    destruct H9 as [_ [_ WK']].
    destruct* Us0. simpl in H2. discriminate.
    simpl in WK'. destruct WK' as [_ WK].
    destruct* Us0.
    destruct* Us0.
    destruct WK as [WK _].
    inversions WK. clear WK; simpl in *.
    inversions H2; clear H2.
    use (binds_func H0 H1). inversion H; clear H H1; subst k'0.
    simpl in H4; destruct H4.
    use (proj2 H7 x (Some k') H0). simpl in H2.
    rewrite (proj2 H2 (nth k l var_default) t0 (nth k Us typ_def)) in H6;
      clear H2; auto.
      unfold Cstr.unique.
      destruct H as [Hlow _]. simpl in Hlow.
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

  Lemma delta_typed : forall n t1 t2 tl K E T,
    Delta.rule n t1 t2 ->
    list_for_n term n tl ->
    K ; E |= trm_inst t1 tl ~: T ->
    K ; E |= trm_inst t2 tl ~: T.
  Proof.
    intros.
    clear H0.
    destruct H as [l [k [HN [HK [T1 T2]]]]].
    subst.
    inversions H1; clear H1.
    rewrite trm_inst_app in H4.
    unfold const_app in H4.
    destruct (fold_app_inv _ _ H4) as [TL [Typ0 TypA]]; clear H4.
    unfold trm_inst; simpl.
    inversions Typ0. clear Typ0 H1 H4.
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
       apply* typing_app.
       apply* get_kind_for_matches.
      rewrite* seq_length.
     rewrite* seq_length.
    autorewrite with list; auto.
  Qed.

  Lemma cons_append : forall (A:Set) (a:A) l, a :: l = (a :: nil) ++ l.
  Proof. auto.
  Qed.

  Lemma list_forall_rev : forall (A:Set) (P:A->Prop) l,
    list_forall P l -> list_forall P (rev l).
  Proof.
    induction l; simpl; intros; auto.
    inversions H.
    apply* list_forall_concat.
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

  Lemma value_is_tag : forall K v n T,
    K; empty |= v ~: T ->
    valu n v ->
    typ_arity T <= n ->
    exists l, exists tl, v = const_app (Const.tag l) tl.
  Proof.
    induction v; introv Typv Hv TA; inversions Hv; inversions Typv.
      simpl in TA. elim (le_Sn_O _ TA).
      clear IHv2.
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

  Lemma tag_is_const : forall v vl K T TL,
    S (Const.arity (Const.tag v)) = length vl ->
    K; empty |= trm_cst (Const.tag v) ~: fold_right typ_arrow T TL ->
    For_all2 (typing K empty) vl TL -> False.
  Proof.
    introv Hv TypC TypA.
    inversions TypC. clear TypC H4.
    destruct* vl; try destruct* vl; try destruct* vl; try discriminate.
    destruct TL; destruct* TypA.
    destruct TL; destruct* H2.
    destruct TL; destruct* H3.
    unfold sch_open in H0.
    simpl in H0.
    inversions H0. clear H0.
    destruct H5 as [_ [_ WK]]. simpl in WK.
    destruct* Us. destruct* Us. destruct* Us.
    destruct WK as [_ [WK _]].
    inversions WK.
    discriminate.
  Qed.

  Lemma mkset_in : forall x Xs,
    x \in mkset Xs -> In x Xs.
  Proof.
    induction Xs; intros.
      elim (in_empty H).
    simpl in *.
    destruct* (proj1 (in_union _ _ _) H).
    left. rewrite* (proj1 (in_singleton _ _) H0).
  Qed.

  Lemma exists_nth : forall (A:Set) (d:A) x Xs,
    In x Xs -> exists n, n < length Xs /\ x = nth n Xs d.
  Proof.
    induction Xs; intros. elim H.
    simpl in H; destruct* H.
      exists 0; rewrite H; simpl; split*. apply lt_O_Sn.
    destruct* IHXs as [n [Hlen EQ]].
    exists (S n). simpl; split*.
    apply* lt_n_S.
  Qed.

  Lemma list_forall_imp : forall (A:Set) (P Q:A->Prop) l,
    (forall x, P x -> Q x) -> list_forall P l -> list_forall Q l.
  Proof.
    induction l; intros; auto.
    inversions H0.
    constructor; auto.
  Qed.

  Lemma seq_in : forall k n m, In k (seq m n) -> m <= k < m+n.
  Proof.
    induction n; intros. elim H.
    simpl in H; destruct H.
      rewrite H. omega.
    destruct* (IHn (S m)).
    omega.
  Qed.

  Lemma map_ext' : forall (A B:Set) (f g:A->B) l,
    (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof.
    induction l; intros; auto.
    simpl.
    rewrite* (H a).
    rewrite* IHl.
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
    apply map_ext'.
    intros.
    simpl.
    rewrite <- minus_n_O.
    destruct* x.
    destruct (seq_in _ _ _ H).
    elim (le_Sn_O _ H0).
  Qed.

  Lemma typing_tag_inv : forall K l tl x,
    K; empty |= const_app (Const.tag l) tl ~: typ_fvar x ->
    exists t, exists T, exists k,
      tl = t :: nil /\  K; empty |= t ~: T /\ binds x (Some k) K /\
      entails k (Kind (Cstr.C {{l}} None) ((l, T) :: nil)).
  Proof.
    introv Typv.
    unfold const_app in Typv.
    destruct* (fold_app_inv _ _ Typv) as [TL [Typc Typa]]; clear Typv.
    inversions Typc. clear Typc H1 H4.
    destruct H5 as [_ [_ WK]].
    unfold sch_open in H0; simpl in H0.
    destruct TL as [|T TL]. discriminate.
    destruct tl. elim Typa.
    exists t. exists T.
    simpl in H0; inversions H0; clear H0.
    simpl in WK.
    destruct* Us. destruct* Us. destruct* Us.
    destruct WK as [_ [WK _]]. simpl in WK.
    inversions WK; clear WK.
    exists k'.
    destruct TL; try discriminate.
    simpl in H2; inversion H2; subst x0; clear H2.
    simpl in Typa.
    destruct Typa.
    destruct tl; try elim H1.
    intuition.
  Qed.

  Lemma const_arity_ok0 : forall c vl K T,
    S(Const.arity c) = length vl ->
    K ; empty |= const_app c vl ~: T ->
    exists l, exists Us, exists v, exists vl',
      vl = rev (v :: vl') /\ c = Const.matches l /\ length l = length vl' /\
      proper_instance K (Delta.type (Const.matches l)) Us /\
      K; empty |= v ~: nth 0 Us typ_def.
  Proof.
    intros.
    unfold const_app in H0.
    use (fold_app_inv _ _ H0).
    clear H0; destruct H1 as [TL [TypC TypA]].
    destruct c.
      elim (tag_is_const _ _ _ H TypC TypA).
    exists l.
    inversions TypC. clear TypC H5.
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

  Lemma const_arity_ok : forall c vl K T,
    list_for_n value (S(Const.arity c)) vl ->
    K ; empty |= const_app c vl ~: T ->
    exists n:nat, exists t1:trm, exists t2:trm, exists tl:list trm,
      Delta.rule n t1 t2 /\ list_for_n term n tl /\
      const_app c vl = trm_inst t1 tl.
  Proof.
    intros.
    destruct (const_arity_ok0 _ _ (proj1 H) H0) as
      [l [Us [v [vl' [Evl [Ec [Hvl' [PI Typv]]]]]]]]; clear H0.
    subst.
    exists (S (length l)).
    destruct PI as [_ [_ WK]].
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
    destruct Ek as [[Low _] _].
    destruct k as [[kl kh] kr]; simpl in *.
    destruct* kh as [kh|].
    use (proj2 (proj41 (typing_regular Typa)) _ _ Bk).
    simpl in H; destruct H.
    unfold Cstr.valid in H. simpl in H.
    use (subset_trans Low (subset_trans H High) (in_same l')).
    clear H High Low kl kh kr Bk H0 x Us.
    use (mkset_in _ H1); clear H1.
    destruct (exists_nth var_default _ _ H) as [n [Hlen EQ]].
    clear H; subst l'.
    exists (Delta.matches_lhs l n).
    exists (Delta.matches_rhs n).
    exists (t :: rev vl').
    split3.
      unfold Delta.rule. exists l; exists n. auto.
      split*. simpl. rewrite rev_length. rewrite* Hvl'.
      constructor; auto.
      apply* list_forall_rev.
      apply (list_forall_imp _ value_regular H2).
    unfold Delta.matches_lhs.
    simpl.
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
    destruct H as [tl [k [L1 [L2 [LHS RHS]]]]].
    unfold Delta.matches_lhs in LHS.
    exists (Const.matches tl).
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
End SndHyp.

Module Sound3 := Mk3(SndHyp).

