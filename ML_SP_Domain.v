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

  Lemma closed : forall c, sch_fv (Delta.type c) = {}.
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

  Lemma For_all2_app' : forall v1 v2 u1 u2,
    For_all2 P (app u1 v1) (app u2 v2) ->
    length u1 = length u2 ->
    For_all2 P u1 u2 /\ For_all2 P v1 v2.
  Proof.
    induction u1; intros; destruct* u2; try discriminate.
      simpl in *. auto.
    simpl in *.
    destruct H.
    inversion H0; clear H0.
    destruct* (IHu1 u2).
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

  Lemma kenv_ok_concat_inv : forall K K',
    kenv_ok (K & K') -> kenv_ok K /\ kenv_ok K'.
  Proof.
    intros; destruct H.
    destruct (ok_concat_inv _ _ H).
    split; split*; intros x a B; apply* (H0 x).
  Qed.

  Lemma kenv_ok_open_fresh : forall K Ks Xs,
    kenv_ok K ->
    kenv_ok (kinds_open_vars Ks Xs) -> 
    fresh (dom K) (length Ks) Xs ->
    kenv_ok (K & kinds_open_vars Ks Xs).
  Proof.
    intros.
    split*.
      unfold kinds_open_vars.
      apply* disjoint_ok.
      rewrite mkset_dom. apply disjoint_comm.
      apply* (fresh_disjoint (length Ks)).
      unfold kinds_open. rewrite map_length.
      rewrite* (fresh_length _ _ _ H1).
    intros x a B.
    binds_cases B.
      apply* (proj2 H x).
    apply* (proj2 H0 x).
  Qed.

  Lemma typing_app_inv : forall K E t1 t2 T,
    K; E |= trm_app t1 t2 ~: T ->
    forall E' t' T',
    (forall K' U,
      K & K'; E |= t1 ~: typ_arrow U T ->
      K & K'; E |= t2 ~: U ->
      K & K'; E' |= t' ~: T') ->
    K; E' |= t' ~: T'.
  Proof.
    introv Typ.
    gen_eq (trm_app t1 t2) as t0.
    induction Typ; intros; try discriminate.
      inversions H. use (H0 (empty(A:=kind)) S).
    apply* (typing_gc Ks L).
    intros. apply* H0.
    intro. rewrite concat_assoc.
    apply* H2.
  Qed.

  Lemma trm_fv_open : forall t' t n,
    trm_fv (trm_open_rec n t' t) << trm_fv t \u trm_fv t'.
  Proof.
    induction t; simpl; intros; intros x Hx; auto*.
    destruct (n0 === n). rewrite* union_empty_l.
      elim (in_empty Hx).
    apply* S.union_2.
    apply* (IHt (S n)).
    destruct (S.union_1 Hx).
      destruct* (S.union_1 (IHt1 n x H)); auto with sets.
      destruct* (S.union_1 (IHt2 (S n) x H)); auto with sets.
    destruct (S.union_1 Hx).
      destruct* (S.union_1 (IHt1 n x H)); auto with sets.
      destruct* (S.union_1 (IHt2 n x H)); auto with sets.
    elim (in_empty Hx).
  Qed.

  Lemma typing_strengthen : forall y s t K E E' T,
    K ; E & y ~ s & E' |= t ~: T ->
    y \notin trm_fv t ->
    K ; E & E' |= t ~: T.
  Proof.
    introv Typ. gen_eq (E & y ~ s & E') as E0. gen E E'.
    induction Typ; intros; subst; auto*.
      binds_cases H1.
        apply* typing_var.
        simpl in H4. elim H4. apply* (proj2 (in_singleton x x)).
        apply* typing_var.
      apply* typing_abs.
        intros.
        rewrite concat_assoc.
        apply* H1.
    intro.
    destruct (S.union_1 (trm_fv_open _ _ _ H4)).
      elim (H3 H5).
      use (proj42 (typing_regular (H0 _ H2))).
      use (ok_remove _ _ _ H6); clear H6.
      inversions H7.
      elim H11.
      rewrite* (proj1 (in_singleton _ _) H5).
      simpl. auto with sets.
    apply* typing_let.
      intros. apply* H0. simpl in H4. auto*.
      intros. rewrite concat_assoc. apply* H2.
    intro.
    destruct (S.union_1 (trm_fv_open _ _ _ H5)).
      elim H4. simpl. auto with sets.
      use (proj42 (typing_regular (H1 _ H3))).
      use (ok_remove _ _ _ H7); clear H7.
      inversions H8.
      elim H12; simpl.
      rewrite (proj1 (in_singleton _ _) H6). auto with sets.
    simpl in H0.
    apply* typing_app.
  Qed.

  Lemma typing_var_inv : forall K E x T,
    K ; E |= trm_fvar x ~: T ->
    exists M, binds x M E /\
      exists Us, T = sch_open M Us /\
        exists K', kenv_ok (K & K') /\ proper_instance (K & K') M Us.
  Proof.
    introv Typ; gen_eq (trm_fvar x) as t.
    induction Typ; intros; subst; try discriminate.
      inversions H3. exists M; intuition.
      exists Us; intuition.
      exists (empty(A:=kind)). simpl*.
    pick_freshes (length Ks) Xs.
    destruct* (H0 Xs) as [M [B [Us [HT [K' [Kok PI]]]]]].
    exists M; intuition.
    exists Us; intuition.
    rewrite concat_assoc in *.
    exists* (kinds_open_vars Ks Xs & K').
  Qed.

  Lemma typing_strengthen' : forall K E t T E',
    K ; E |= t ~: T ->
    ok E' ->
    trm_fv t << dom E' ->
    extends E' E ->
    K ; E' |= t ~: T.
  Proof.
    introv Typ. gen E'.
    induction Typ; intros.
    apply* typing_var.
      simpl in H4.
      case_eq (get x E'); intros.
        rewrite (binds_func (H5 x _ H6) H1) in H6. auto.
      elim (get_none_notin _ H6).
      apply H4. auto with sets.
    apply_fresh* typing_abs as y.
      apply* H1.
        intros x Hx.
        use (trm_fv_open _ _ _ Hx).
        rewrite dom_concat.
        simpl in *.
        destruct (S.union_1 H5); auto with sets.
      intros x M B.
      binds_cases B.
        apply* binds_concat_ok.
        forward~ (H0 y) as Hy.
      apply* binds_prepend.
    apply_fresh* (typing_let (M:=M) (L1 \u dom K)) as y.
      intros.
      apply* H0.
      intros x Hx; apply H4.
      simpl; auto with sets.
      apply* H2.
      intros x Hx.
      simpl in *.
      destruct (S.union_1 (trm_fv_open _ _ _ Hx)); auto with sets.
      intros x M' B.
      binds_cases B.
        apply* binds_concat_ok.
        forward~ (H1 y) as Hy.
      apply* binds_prepend.
    apply* typing_app.
      apply* IHTyp1.
      intros x Hx; apply H0. simpl; auto with sets.
      apply* IHTyp2.
      intros x Hx; apply H0. simpl; auto with sets.
    apply* typing_cst.
    apply* typing_gc.
  Qed.

  Lemma trm_open_comm : forall u v t i j,
    term u -> term v -> i <> j ->
    {j ~> v}({i ~> u}t) = {i ~> u}({j ~> v}t).
  Proof.
    induction t; intros; simpl; auto.
    destruct (i === n); simpl; destruct* (j === n).
      elim H1; rewrite* e.
      simpl. destruct* (i === n). rewrite* <- Infra.trm_open_rec.
      rewrite* <- Infra.trm_open_rec.
    simpl. destruct* (i === n).
    rewrite* IHt.
    rewrite* IHt1. rewrite* IHt2.
    rewrite* IHt1. rewrite* IHt2.
  Qed.

(*
  Lemma typing_rename : forall K E t1 x T1 T,
    x \notin (dom E \u trm_fv t1) ->
    K ; E & x ~ T1 |= t1 ^ x ~: T ->
    forall y,
      y \notin (dom E \u trm_fv t1 \u {{x}}) ->
      K ; E & y ~ T1 |= t1 ^ y ~: T.
  Proof.
    intros.
    replace (E & y ~ T1) with (E & y ~ T1 & nil) by simpl*.
    replace (t1 ^ y) with (trm_subst x (trm_fvar y) (t1 ^ x)).
      apply* (typing_trm_subst nil (M:=T1)).
      rewrite concat_assoc. simpl (x ~ T1 & nil).
      apply* typing_weaken.
      destruct (ok_concat_inv _ _ (proj42 (typing_regular H0))).
      apply* disjoint_ok.
        simpl; intro.
        case_eq (S.mem x0 ({{y}} \u dom E)); intros.
          right; intro.
          destruct (S.union_1 H5).
            use (proj1 (in_singleton _ _) H6); subst; clear H5 H6.
            destruct (S.union_1 (S.mem_2 H4)).
              use (proj1 (in_singleton _ _) H5); subst; clear H5.
              elim H1; auto with sets.
            elim H; auto with sets.
          elim (in_empty H6).
        left; intro.
        rewrite (S.mem_1 H5) in H4. discriminate.
      exists (dom K \u fv_in kind_fv K \u env_fv E \u typ_fv (sch_type T1)).
      intros Xs Fr.
      unfold sch_open_vars, typ_open_vars.
      fold (sch_open T1 (typ_fvars Xs)).
      apply* typing_var.
        split.
          unfold kinds_open_vars, kinds_open.
          apply* disjoint_ok. apply* ok_combine_fresh.
          rewrite mkset_dom.
          apply disjoint_comm.
          apply* (fresh_disjoint (sch_arity T1)).
          rewrite map_length. rewrite <- (fresh_length _ _ _ Fr).
          reflexivity.
        (* impossible... *)
  
  Lemma typing_abs_inv : forall K E t1 U T,
    K ; E |= trm_abs t1 ~: typ_arrow U T ->
    forall x, x \notin (dom E \u trm_fv t1) ->
      K ; (E & x ~ Sch U nil) |= (t1 ^ x) ~: T.
  Proof.
    intros.
    gen_eq (trm_abs t1) as t; gen_eq (typ_arrow U T) as T0; gen x.
    induction H; intros; try discriminate.
      inversions H3; inversions H4; clear H3 H4.
      destruct (var_fresh (dom E \u trm_fv t1 \u L)) as [y Fr].
      exists* L.
    subst.
    pick_freshes (length Ks) Xs.
    destruct* (H0 Xs) as [L' R].
    exists L'.
    intros; apply (typing_gc Ks L).
    intros.
    destruct* (H0 Xs0) as [L'' R']; clear H0 R Fr.
    apply* R'.
*)    

  Lemma fv_in_concat : forall (A : Set) (fv : A -> vars) E F,
    fv_in fv (E & F) = fv_in fv F \u fv_in fv E.
  Proof.
    induction F; simpl.
      rewrite* union_empty_l.
    destruct a. rewrite IHF. rewrite* union_assoc.
  Qed.

  Lemma fv_in_combine : forall Xs Ks,
    length Xs = length Ks ->
    fv_in kind_fv (combine Xs Ks) = kind_fv_list Ks.
  Proof.
    induction Xs; intros; destruct Ks; try discriminate; simpl in *.
      auto.
    rewrite* IHXs.
  Qed.

  Lemma notin_typ_open : forall x T Us,
    x \notin typ_fv T -> x \notin typ_fv_list Us ->
    x \notin typ_fv (typ_open T Us).
  Proof.
    induction T; simpl; intros; auto.
      gen n; induction Us; simpl in *; intros; destruct* n.
    apply* notin_union_l.
  Qed.

  Lemma notin_kinds_open : forall x Ks Us,
    x \notin kind_fv_list Ks ->
    x \notin typ_fv_list Us ->
    x \notin kind_fv_list (kinds_open Ks Us).
  Proof.
    induction Ks; simpl; intros.
      auto.
    apply* notin_union_l.
    unfold kind_open, kind_fv in *.
    destruct a as [[kc kr]|]; simpl in *.
      induction kr; simpl. auto.
      destruct a; simpl in *.
      apply* notin_union_l.
      apply* notin_typ_open.
      auto*.
  Qed.

  Lemma notin_dec : forall x E, x \in E \/ x \notin E.
    intros.
    case_eq (S.mem x E); intros.
      use (S.mem_2 H).
    right; intro.
    rewrite (S.mem_1 H0) in H. discriminate.
  Qed.

  Lemma typ_fv_list_fvars : forall Xs,
    typ_fv_list (typ_fvars Xs) = mkset Xs.
  Proof.
    induction Xs; simpl; auto.
    rewrite* IHXs.
  Qed.

  Lemma disjoint_fresh : forall n Xs L' L,
    fresh L n Xs ->
    disjoint (mkset Xs) L' ->
    fresh L' n Xs.
  Proof.
    induction n; intros; destruct Xs; use (fresh_length _ _ _ H);
      try discriminate.
    simpl in *.
    split. elim (H0 v); intro; auto. elim H2; auto with sets.
    apply* IHn.
    intro.
    destruct (x == v). subst.
      elim (fresh_disjoint _ _ _ (proj2 H) v); intro; auto.
      elim (H0 v); intro; auto.
    elim (H0 x); intro; auto.
  Qed.

  Lemma typing_gc_rename : forall Xs Ks K E t T L,
    L = dom K \u fv_in kind_fv K \u kind_fv_list Ks \u env_fv E \u typ_fv T ->
    fresh L (length Ks) Xs ->
    K & kinds_open_vars Ks Xs; E |= t ~: T ->
    forall Xs',
      fresh (L \u mkset Xs) (length Ks) Xs' ->
      K & kinds_open_vars Ks Xs'; E |= t ~: T.
  Proof.
    intros.
    rewrite <- (typ_subst_fresh (combine Xs (typ_fvars Xs')) T).
    assert (disjoint (mkset Xs) (mkset Xs')).
      intro.
      destruct (notin_dec x (mkset Xs')).
        left; intro. destruct (fresh_union_r _ _ _ _ H2).
        use (fresh_disjoint _ _ _ H6 x).
      auto.
    apply* typing_typ_substs.
      use (fresh_disjoint _ _ _ H0). rewrite H in H4.
      rewrite mkset_dom.
      intro x; destruct (H4 x). left*.
      elim (H3 x); intro; auto.
      right.
      rewrite fv_in_concat. rewrite dom_concat.
      repeat apply* notin_union_l.
        unfold kinds_open_vars.
        rewrite fv_in_combine.
        apply* notin_kinds_open.
        rewrite* typ_fv_list_fvars.
        unfold kinds_open; autorewrite with list.
        rewrite* (fresh_length _ _ _ H2).
      unfold kinds_open_vars, kinds_open.
      rewrite* mkset_dom. rewrite map_length. rewrite* (fresh_length _ _ _ H2).
      unfold typ_fvars; rewrite map_length. rewrite <- (fresh_length _ _ _ H2).
      rewrite* (fresh_length _ _ _ H0).
      clear; gen Xs; induction Xs'; destruct Xs; simpl; intro; intros;
        try elim (binds_empty H).
        unfold binds in H; simpl in H.
        destruct (x == v). inversion* H.
        apply* (IHXs' Xs x).
      apply well_subst_open_vars.
      rewrite fv_in_concat.
      apply* fresh_union_l.
      apply* disjoint_fresh.
      intro.
      destruct (notin_dec x (mkset Xs)).
      elim (H3 x); intro; auto.
      right. unfold kinds_open_vars.
      rewrite fv_in_combine.
      apply* notin_kinds_open.

      

  Lemma typing_abs_inv0 : forall K E t1 U T,
    K ; E |= trm_abs t1 ~: typ_arrow U T ->
    exists L, exists K',
    forall x, x \notin L ->
      K & K'; (E & x ~ Sch U nil) |= (t1 ^ x) ~: T.
  Proof.
    intros.
    gen_eq (trm_abs t1) as t; gen_eq (typ_arrow U T) as T0.
    induction H; intros; try discriminate.
     exists L. exists (empty(A:=kind)).
     inversions H2; inversions H3. simpl*.
    pick_freshes (length Ks) Xs.
    destruct* (H0 Xs) as [L' [K' R]]; clear H0.
    exists L'; exists (kinds_open_vars Ks Xs & K').
    rewrite* <- concat_assoc.
  Qed.

  Lemma typing_let_inv0 : forall K E t1 t2 T,
    K ; E |= trm_let t1 t2 ~: T ->
    exists M, exists K',
      (exists L1, forall Xs, fresh L1 (sch_arity M) Xs ->
        K & K' & kinds_open_vars (sch_kinds M) Xs; E |= t1 ~: (M ^ Xs)) /\
      (exists L2, forall x, x \notin L2 ->
        K & K' ; (E & x ~ M) |= (t2 ^ x) ~: T).
  Proof.
    intros.
    gen_eq (trm_let t1 t2) as t.
    induction H; intros; try discriminate.
     exists M. exists (empty(A:=kind)).
     inversions H3. simpl*.
    subst.
    pick_freshes (length Ks) Xs.
    destruct* (H0 Xs) as [M [K' R]]; clear H0.
    exists M; exists (kinds_open_vars Ks Xs & K').
    repeat rewrite* <- concat_assoc.
  Qed.

  Lemma binds_dom : forall (A:Set) x (a:A) E,
    binds x a E -> x \in dom E.
  Proof.
    induction E; intros.
      discriminate.
    destruct a0.
    unfold binds in H. simpl in H.
    simpl. destruct (x == v); auto with sets.
    rewrite e; auto with sets.
  Qed.

  Lemma trm_fv_open2 : forall u t i,
    trm_fv t << trm_fv ({i ~> u}t).
  Proof.
    induction t; intros; intros y Hy; simpl; auto with sets.
    elim (in_empty Hy).
    apply* IHt.
    simpl in Hy; unfold S.Subset in *; destruct (S.union_1 Hy); auto with sets.
    simpl in Hy; unfold S.Subset in *; destruct (S.union_1 Hy); auto with sets.
  Qed.

  Lemma typing_fv : forall K E t T,
    K ; E |= t ~: T -> trm_fv t << dom E.
  Proof.
    induction 1; simpl; intros y Hy.
    rewrite (proj1 (in_singleton _ _) Hy). apply* binds_dom.
    pick_fresh x.
    forward~ (H1 x) as Hx.
    simpl in Hx.
    assert (y \in {{x}} \u dom E).
      apply Hx. unfold trm_open; apply* trm_fv_open2.
    destruct* (S.union_1 H2).
    elim Fr. rewrite (proj1 (in_singleton _ _) H3).
    repeat (apply S.union_2; try (apply* S.union_3; fail)).
    pick_fresh x.
    pick_freshes (sch_arity M) Xs.
    forward~ (H0 Xs) as Ht1; clear H0.
    forward~ (H2 x) as Ht2; clear H2.
    destruct (S.union_1 Hy).
      apply* Ht1.
    simpl in Ht2.
    assert (y \in {{x}} \u dom E).
      apply Ht2. unfold trm_open; apply* trm_fv_open2.
    destruct* (S.union_1 H2).
    elim Fr. rewrite (proj1 (in_singleton _ _) H3).
    repeat (apply S.union_2; try (apply* S.union_3; fail)).
    destruct (S.union_1 Hy). apply* IHtyping1. apply* IHtyping2.
    elim (in_empty Hy).
    pick_freshes (length Ks) Xs.
    apply* (H0 Xs).
  Qed.    

  Lemma typing_var_inv' : forall K E x T t E',
    K; E |= trm_fvar x ~: T ->
    (forall K' M Us,
      kenv_ok (K & K') ->
      binds x M E ->
      proper_instance (K & K') M Us ->
      K & K'; E' |= t ~: sch_open M Us) ->
    K; E' |= t ~: T.
  Proof.
    introv Typ.
    gen_eq (trm_fvar x) as t0. gen E'.
    induction Typ; intros; try discriminate.
      inversions H3. use (H4 (empty(A:=kind)) M).
    apply* (typing_gc Ks L).
    intros. apply* H0.
    intro. rewrite concat_assoc.
    apply* H2.
  Qed.

  Lemma typing_abs_inv : forall K E t1 U T,
    K ; E |= trm_abs t1 ~: typ_arrow U T ->
    (forall x, t1 ^ x = t1) ->
    K ; E |= t1 ~: T.
  Proof.
    introv Typ; gen_eq (trm_abs t1) as t; gen_eq (typ_arrow U T) as T0.
    induction Typ; intros; subst; try discriminate.
      inversions H2; inversions H3; clear H2 H3.
      destruct (var_fresh (L \u trm_fv t1)) as [x Hx].
      replace E with (E & empty) by simpl*.
      apply* typing_strengthen.
        simpl; simpl in H0. rewrite* <- (H4 x).
        auto*.
    apply* typing_gc.
  Qed.

  Lemma fold_app_inv : forall E t tl K T,
    K ; E |= fold_left trm_app tl t ~: T ->
    forall E' t' T',
    (forall K' TL,
      K & K'; E |= t ~: fold_right typ_arrow T TL ->
      For_all2 (typing (K & K') E) tl TL ->
      K & K'; E' |= t' ~: T') ->
    K ; E' |= t' ~: T'.
  Proof.
    induction tl using rev_ind; simpl; intros.
      use (H0 empty nil).
    rewrite fold_left_app in *; simpl in *.
    apply* (typing_app_inv H).
    intros.
    apply* IHtl; clear IHtl.
    intros.
    rewrite* concat_assoc.
    apply* (H0 (K' & K'0) (TL ++ U :: nil)); clear H0.
      rewrite fold_right_app; simpl.
      rewrite* <- concat_assoc.
      rewrite* <- concat_assoc.
    apply* For_all2_app.
    split*. apply* typing_weaken_kinds'. simpl*.
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

  Lemma For_all2_imp : forall (A B:Set) (P P' : A -> B -> Prop) l1 l2,
    For_all2 P l1 l2 ->
    (forall x y, In (x,y) (combine l1 l2) -> P x y -> P' x y) ->
    For_all2 P' l1 l2.
  Proof.
    induction l1; destruct l2; simpl; intros; auto.
    split*.
  Qed.

  Lemma typing_cst_inv' : forall K E c T,
    K; E |= trm_cst c ~: T ->
    forall E' t T',
    (forall K' Us,
      kenv_ok (K & K') ->
      proper_instance (K & K') (Delta.type c) Us ->
      T = sch_open (Delta.type c) Us ->
      K & K'; E' |= t ~: T') ->
    K; E' |= t ~: T'.
  Proof.
    introv Typ.
    gen_eq (trm_cst c) as t0.
    induction Typ; intros; try discriminate.
      inversions H2. use (H3 (empty(A:=kind)) Us).
    apply* (typing_gc Ks L).
    intros. apply* H0.
    intro. rewrite concat_assoc.
    apply* H2.
  Qed.

  Lemma typing_cst_inv : forall K E c T,
    K; E |= trm_cst c ~: T ->
    exists K', exists Us,
      kenv_ok (K & K') /\
      proper_instance (K & K') (Delta.type c) Us /\
      T = sch_open (Delta.type c) Us.
  Proof.
    introv Typ; gen_eq (trm_cst c) as t.
    induction Typ; intros; try discriminate.
      inversions H2. exists (empty(A:=kind)); exists* Us.
    subst.
    pick_freshes (length Ks) Xs.
    destruct* (H0 Xs) as [K' R]; clear H0.
    exists (kinds_open_vars Ks Xs & K'). rewrite* <- concat_assoc.
  Qed.

(*
  Lemma get_kind_for_matches : forall k l t K E Us,
    k < length l ->
    proper_instance K (Delta.type (Const.matches l)) Us ->
    K ; E |= trm_app (trm_cst (Const.tag (nth k l var_default)))
                    t ~: nth 0 Us typ_def ->
    K ; E |= t ~: nth (S (S k)) Us typ_def.
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
    destruct (typing_app_inv Typ) as [U [K' [Typ1 Typ2]]]. clear Typ.
    destruct (typing_cst_inv Typ1) as [Us' [K'' [WK [Eq Kok]]]].
    destruct WK as [_ [_ WK']].
    destruct* Us'. discriminate.
    simpl in WK'. destruct WK' as [_ WK].
    destruct* Us'.
    destruct* Us'.
    destruct WK as [WK _].
    inversions WK. clear WK; simpl in *.
    unfold sch_open in Eq. simpl in Eq.
    inversions Eq; clear Eq.
    use (binds_concat_ok K' H0 (proj1 (proj1 (typing_regular Typ2)))).
    use (binds_concat_ok K'' H (proj1 Kok)).
    use (binds_func H2 H1). inversion H4; clear H H1 H4; subst k'0.
    simpl in H3; destruct H3.
    use (proj2 Kok x0 (Some k') H2). simpl in H3.
    exists K'.
    rewrite (proj2 (proj2 H3) (nth k l var_default) t0 (nth k Us typ_def))
      in Typ2; auto.
      unfold Cstr.unique.
      destruct H as [Hlow _]. simpl in Hlow.
      apply* Hlow.
    apply HE.
    clear HE t0 Typ1 Typ2 H H1.
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
*)

  Lemma cut_list : forall (A:Set) k (l:list A),
    k < length l ->
    exists l1, exists a, exists l2, l = l1 ++ a :: l2 /\ length l1 = k.
  Proof.
    induction k; intros.
      destruct l. elim (lt_n_O _ H).
      exists (nil(A:=A)). exists a. exists* l.
    destruct l. elim (lt_n_O _ H).
    destruct* (IHk l) as [l1 [b [l2 [E1 E2]]]].
      apply (lt_S_n _ _ H).
    exists (a::l1). exists b. exists* l2.
    simpl; rewrite E1; rewrite* E2.
  Qed.

  Lemma seq_app : forall n m k,
    seq k (m + n) = seq k m ++ seq (m+k) n.
  Proof.
    induction m; simpl; intros. auto.
    rewrite IHm. rewrite <- plus_Snm_nSm. simpl*.
  Qed.

  Lemma app_nth3 : forall (A:Set) (d:A) l1 a l2,
    nth (length l1) (l1 ++ a :: l2) d = a.
  Proof.
    intros. rewrite* app_nth2. rewrite <- minus_n_n. simpl*.
  Qed.

  Lemma combine_app : forall (A B:Set) (u2:list A) (v2:list B) u1 v1,
    length u1 = length v1 ->
    combine (u1 ++ u2) (v1 ++ v2) = combine u1 v1 ++ combine u2 v2.
  Proof.
    induction u1; destruct v1; simpl; intros; try discriminate.
      auto.
    inversion H; rewrite* IHu1.
  Qed.

  Lemma delta_typed : forall n t1 t2 tl K E T,
    Delta.rule n t1 t2 ->
    list_for_n term n tl ->
    K ; E |= trm_inst t1 tl ~: T ->
    K ; E |= trm_inst t2 tl ~: T.
  Proof.
    intros.
    destruct H as [l [k [HN [HK [T1 T2]]]]].
    subst.
    unfold Delta.matches_lhs, trm_inst in H1. simpl in H1.
    rewrite trm_inst_app in H1.
    apply* typing_app_inv; clear H1.
    intros.
    unfold const_app in H.
    apply* fold_app_inv; clear H.
    intros.
    unfold Delta.matches_rhs, trm_inst.
    destruct tl.
      destruct H0; discriminate.
    simpl in *.
    rewrite <- seq_shift in H2.
    repeat rewrite map_map in H2.
    simpl in H2.
    destruct* (cut_list _ HK) as [l1 [v [l2 [El El']]]]. subst l.
    destruct* (cut_list tl (k:=k)) as [tl1 [f [tl2 [Etl Etl']]]].
      clear -HK H0.
      destruct H0. simpl in H; inversion* H.
    destruct* (cut_list TL (k:=k)) as [TL1 [V [TL2 [ETL ETL']]]].
      rewrite* <- (For_all2_length _ _ _ H2).
      rewrite map_length. rewrite* seq_length.
    rewrite <- El' in H1. rewrite app_nth3 in H1.
    rewrite Etl. rewrite <- Etl'. rewrite app_nth3.
    subst; simpl in *.
    apply* (typing_cst_inv' H); clear H.
    intros.
    unfold sch_open, sch_arity in H4; simpl in H4.
    destruct (fold_arrow_eq _ _ _ _ _ (sym_equal H4)); clear H4.
      rewrite map_length; rewrite seq_length.
      rewrite <- (For_all2_length _ _ _ H2).
      autorewrite with list. auto.
    unfold sch_open, sch_arity in H5; simpl in H5.
    inversions H5; clear H5.
    use (proj1 (proj1 H3)).
    unfold sch_arity in H4; simpl in H4.
    do 2 (destruct Us; try discriminate).
    rewrite map_length in H4; rewrite seq_length in H4. simpl in H4.
    inversions H4; clear H4.
    repeat rewrite <- seq_shift in H6. repeat rewrite map_map in H6.
    rewrite app_length in H6. rewrite seq_app in H6.
    rewrite map_app in H6.
    destruct (For_all2_app' _ _ _ _ _ H6) as [_ HA]; clear H6.
      ssimpl_list. symmetry. trivial.
    simpl in HA; destruct HA as [Hv _].
    simpl.
    use (proj1 (proj1 H3)).
    unfold sch_arity in H4; simpl in H4.
    autorewrite with list in H4.
    inversion H4; clear H4.
    destruct (cut_list (k:=length l1) Us) as [Us1 [U [Us2 [EUs EUs']]]].
      omega.
    rewrite EUs in Hv. rewrite plus_0_r in Hv.
    rewrite <- EUs' in Hv; rewrite app_nth3 in Hv.
    simpl in H1.
    rewrite app_length in H2. rewrite seq_app in H2. rewrite map_app in H2.
    destruct (For_all2_app' _ _ _ _ _ H2) as [_ HA]; clear H2.
      ssimpl_list. symmetry. trivial.
    simpl in HA; destruct HA as [Hf _].
    rewrite <- Etl' in Hf. rewrite plus_0_r in Hf. rewrite app_nth3 in Hf.
    subst.
    apply* typing_app. apply* typing_weaken_kinds'.
    rewrite concat_assoc in H.
    use (typing_weaken_kinds' _ H H1); clear H1.
    rewrite <- concat_assoc in H2.
    apply* (typing_app_inv H2); clear H2.
    intros.
    apply* (typing_cst_inv' H1); clear H1.
    intros.
    unfold sch_open, sch_arity in H5; simpl in H5.
    inversions H5; clear H5.
    use (proj1 (proj1 H4)).
    unfold sch_arity in H5; simpl in H5.
    do 3 (destruct Us; try discriminate). clear H5.
    simpl in H2.
    use (proj2 (proj2 H3)). simpl in H5.
    use (proj2 (proj2 H4)). simpl in H8.
    use (proj1 (proj2 H8)); clear H8.
    use (proj1 H5); clear H5.
    inversions H9; clear H9.
    inversions H8; clear H8.
    use (binds_concat_ok (K'2 & K'3) H13).
    rewrite <- concat_assoc in H5.
    use (binds_func (H5 (proj1 H1)) H10); clear H5 H13.
    inversions H8; clear H8.
    use (proj2 H1 _ _ H10). simpl in H5.
    assert (Cstr.unique (kind_cstr k') v).
      destruct H12 as [[Hlow _] _]. simpl in Hlow.
      apply (Hlow v). auto with sets.
    rewrite* (proj2 (proj2 H5) v U t0).
      apply* typing_weaken_kinds'.
      apply* (proj2 H14).
      clear -EUs'.
      simpl.
      rewrite app_length; rewrite seq_app; repeat rewrite map_app. 
      rewrite combine_app.
      rewrite map_app.
      apply in_or_app. right.
      simpl. left.
      rewrite plus_comm. simpl. rewrite <- EUs'. rewrite* app_nth3.
      ssimpl_list. auto.
    apply* (proj2 H12 (v, t0)).
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
    introv Typ; gen n.
    induction Typ; introv Hv TA; try (inversions Hv; fail).
    inversions Hv.
    elim (le_Sn_O _ TA).
    inversions Hv.
    clear IHTyp2.
      destruct* (IHTyp1 (Datatypes.S n) H2) as [l [tl EQ]].
        simpl. apply* le_n_S.
      exists l. exists (tl ++ t2 :: nil).
      rewrite EQ.
      unfold const_app; rewrite fold_left_app. auto.
    destruct c.
      exists v. exists (nil (A:=trm)). auto.
    inversions Hv.
    elim (le_not_lt _ _ TA). clear.
    unfold sch_open; simpl.
    rewrite fold_arrow_open.
    rewrite typ_arity_fold_arrow.
    autorewrite with list.
    simpl. omega.
    pick_freshes (length Ks) Xs.
    apply* (H0 Xs).
  Qed.

  Lemma tag_is_const : forall v vl K T TL,
    S (Const.arity (Const.tag v)) = length vl ->
    K; empty |= trm_cst (Const.tag v) ~: fold_right typ_arrow T TL ->
    For_all2 (typing K empty) vl TL -> False.
  Proof.
    introv Hv TypC TypA.
    gen_eq (trm_cst (Const.tag v)) as t.
    gen_eq (fold_right typ_arrow T TL) as T0.
    induction TypC; intros; subst; try discriminate.
      inversions H3; clear H3.
      do 3 (destruct vl; try discriminate).
      destruct TL; destruct* TypA.
      destruct TL; destruct* H4.
      destruct TL; destruct* H5.
      unfold sch_open in H2; simpl in H2.
      inversions H2; clear H2.
      destruct H1 as [_ [_ WK]]. simpl in WK.
      do 3 destruct* Us.
      destruct WK as [_ [WK _]].
      inversions WK.
      discriminate.
    pick_freshes (length Ks) Xs.
    forward~ (H Xs) as Typ.
    apply* (H0 Xs); clear H0 H.
    apply* For_all2_imp.
    intros. apply* typing_weaken_kinds'. apply (proj1 (typing_regular Typ)).
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

  Lemma fold_app_inv' : forall E t tl K T,
    K ; E |= fold_left trm_app tl t ~: T ->
    exists K', exists TL,
      K & K'; E |= t ~: fold_right typ_arrow T TL /\
      For_all2 (typing (K & K') E) tl TL.
  Proof.
    induction tl using rev_ind; simpl; intros.
      exists (empty(A:=kind)). exists (nil(A:=typ)). simpl*.
    rewrite fold_left_app in *. simpl in *.
    gen_eq (trm_app (fold_left trm_app tl t) x) as t0.
    induction H; intros; subst; try discriminate.
      inversions H1; clear H1.
      destruct (IHtl _ _ H) as [K' [TL [Typ FA]]]; clear IHtl.
      exists K'; exists (TL ++ S :: nil).
      rewrite fold_right_app. simpl.
      split*.
      apply* For_all2_app. simpl; split*.
      apply* typing_weaken_kinds'.
    pick_freshes (length Ks) Xs.
    destruct* (H0 Xs) as [K' R]; clear H0.
    exists* (kinds_open_vars Ks Xs & K'). rewrite* <- concat_assoc.
  Qed.

  Lemma typing_tag_inv : forall K l tl x,
    K; empty |= const_app (Const.tag l) tl ~: typ_fvar x ->
    exists t, exists T, exists k, exists K',
      tl = t :: nil /\  K & K'; empty |= t ~: T /\
      binds x (Some k) (K & K') /\
      entails k (Kind (Cstr.C {{l}} None) ((l, T) :: nil)).
  Proof.
    introv Typv.
    destruct* (fold_app_inv' _ _ Typv) as [K' [TL [Typ FA]]].
    destruct* (typing_cst_inv Typ) as [K'' [Us [Kok [[_ [_ WK]] E]]]].
    unfold sch_open in E; simpl in E.
    destruct TL as [|T TL]. discriminate.
    simpl in E; inversions E; clear E.
    destruct tl. elim FA.
    simpl in WK. do 3 destruct* Us.
    simpl in *.
    exists t. exists t0.
    destruct WK as [_ [Ht1 _]].
    inversions Ht1; clear Ht1.
    exists k'; exists (K' & K''); rewrite <- concat_assoc.
    destruct TL; try discriminate.
    destruct FA.
    destruct tl; try (elim H1).
    simpl in H4; inversions H4; clear H4.
    intuition.
    apply* typing_weaken_kinds'.
  Qed.

  Lemma const_arity_ok0 : forall c vl K T,
    S(Const.arity c) = length vl ->
    K ; empty |= const_app c vl ~: T ->
    exists l, exists Us, exists v, exists vl',
      vl = vl' ++ v :: nil /\ c = Const.matches l /\ length l = length vl' /\
      exists K',
        proper_instance (K & K') (Delta.type (Const.matches l)) Us /\
        K & K'; empty |= v ~: nth 0 Us typ_def.
  Proof.
    intros.
    unfold const_app in H0.
    destruct* (fold_app_inv' _ _ H0) as [K' [TL [TypC TypA]]]; clear H0.
    destruct c.
      elim (tag_is_const _ _ _ H TypC TypA).
    exists l.
    destruct* (typing_cst_inv TypC) as [K'' [Us [Kok [PI E]]]]; clear TypC.
    exists Us.
    simpl in H.
    unfold sch_open in E; simpl in E.
    induction vl using rev_ind. discriminate. clear IHvl.
    induction TL using rev_ind.
      destruct vl; elim TypA.
    clear IHTL.
    exists x. exists vl.
    assert (length l = length vl).
      rewrite app_length in H. rewrite plus_comm in H. simpl in H.
      inversion* H.
    clear H; intuition.
    assert (length vl = length TL).
      generalize (For_all2_length _ _ _ TypA); intro.
      repeat (rewrite app_length in H; rewrite plus_comm in H; simpl in H).
      inversions* H.
    destruct* (For_all2_app' _ _ _ _ _ TypA).
    exists (K' & K''). rewrite <- concat_assoc.
    split*.
    simpl in H2. destruct H2 as [Typx _].
    rewrite fold_right_app in E. simpl in E.
    destruct (fold_arrow_eq _ _ _ _ _ (sym_equal E)); clear E.
      simpl_list. rewrite* H0.
    simpl in H2. inversions H2.
    apply* typing_weaken_kinds'.
  Qed.

  Lemma const_arity_ok : forall c vl K T,
    list_for_n value (S(Const.arity c)) vl ->
    K ; empty |= const_app c vl ~: T ->
    exists n, exists t1, exists t2, exists tl,
      Delta.rule n t1 t2 /\ list_for_n term n tl /\
      const_app c vl = trm_inst t1 tl.
  Proof.
    intros.
    destruct (const_arity_ok0 _ _ (proj1 H) H0) as
      [l [Us [v [vl' [Evl [Ec [Hvl' [K' [PI Typv]]]]]]]]]; clear H0.
    subst.
    exists (S (length l)).
    destruct PI as [_ [_ WK]].
    destruct Us; simpl in Typv.
      assert (type typ_def). auto.
      inversion H0.
    destruct H as [_ Val].
    use (list_forall_rev Val); clear Val.
    rewrite distr_rev in H. simpl in H.
    inversions H; clear H.
    destruct H3 as [vn Hv].
    use (proj1 WK). inversions H; clear H WK.
    destruct* (value_is_tag (n:=vn) Typv) as [l' [tl' EQ]].
      auto with arith.
    clear vn Hv.
    subst.
    destruct (typing_tag_inv _ _ Typv) as
      [t [T' [k [K'' [EQ [Typa [Bk Ek]]]]]]]; clear Typv.
    forward (binds_concat_ok K'' H1) as Bk'.
      apply (proj1 (proj1 (typing_regular Typa))).
    use (binds_func Bk' Bk). inversion H; subst; clear H H1 Bk'.
    destruct H4 as [[_ High] _].
    destruct Ek as [[Low _] _].
    destruct k as [[kl kh] kr]; simpl in *.
    destruct* kh as [kh|].
    use (proj2 (proj1 (typing_regular Typa)) _ _ Bk).
    simpl in H.
    unfold Cstr.valid in H. simpl in H.
    use (subset_trans Low (subset_trans (proj1 (proj2 H)) High) (in_same l')).
    clear H High Low kl kh kr Bk x Us.
    use (mkset_in _ H0); clear H0.
    destruct (exists_nth var_default _ _ H) as [n [Hlen EQ]].
    clear H; subst l'.
    exists (Delta.matches_lhs l n).
    exists (Delta.matches_rhs n).
    exists (t :: vl').
    split3.
      unfold Delta.rule. exists l; exists n. auto.
      split*. simpl. rewrite* Hvl'.
      constructor; auto.
      rewrite <- rev_involutive.
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
    rewrite <- (map_inst_bvar t vl').
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

