(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure Cardinal.
(* Require Import ML_SP_Soundness. *)

Set Implicit Arguments.

Module MkInfer(Cstr:CstrIntf)(Const:CstIntf).

Module Infra := MkInfra(Cstr)(Const).
Import Infra.
Import Defs.

Definition compose S1 S2 := map (typ_subst S1) S2 & S1.

Parameter unique : Cstr.cstr -> list var.
Parameter unique_ok : forall c l, In l (unique c) <-> Cstr.unique c l.
Parameter cstr_lub : Cstr.cstr -> Cstr.cstr -> Cstr.cstr.
Parameter cstr_lub_ok : forall c1 c2 c,
  (Cstr.entails c c1 /\ Cstr.entails c c2) <-> Cstr.entails c (cstr_lub c1 c2).

Fixpoint unify_kind_rel (kr kr':list(var*typ)) (un:list var)
  (pairs:list(typ*typ)) {struct kr} :=
  match kr with
  | nil => (kr', pairs)
  | (l,T)::krem =>
    if In_dec eq_var_dec l un then
      match get l kr' with
      | None => unify_kind_rel krem ((l,T)::kr') un pairs
      | Some T' => unify_kind_rel krem kr' un ((T,T')::pairs)
      end
    else unify_kind_rel krem ((l,T)::kr') un pairs
  end.

Fixpoint remove_env (A:Set) (E:Env.env A) (x:var) {struct E} : Env.env A :=
  match E with
  | nil => nil
  | (y,a)::E' =>
    if x == y then E' else (y,a) :: remove_env E' x
  end.

Definition unify_kinds (k1 k2:kind) :=
  match k1, k2 with
  | None, _ => (k2, nil)
  | Some _, None => (k1, nil)
  | Some (Kind kc1 kr1), Some (Kind kc2 kr2) =>
    let kc := cstr_lub kc1 kc2 in
    let (kr, pairs) := unify_kind_rel (kr1 ++ kr2) nil (unique kc) nil in
    (Some (Kind kc kr), pairs)
  end.

Definition unify_vars (K:kenv) (x y:var) :=
  match get x K, get y K with
  | Some k1, Some k2 =>
    let (k, pairs) := unify_kinds k1 k2 in
    Some (remove_env (remove_env K x) y & y ~ k, pairs)
  | _, _ => None
  end.

Definition unify_nv (unify : kenv -> subs -> option (kenv * subs)) K S x T :=
  if S.mem x (typ_fv T) then None else
    match get x K with
    | Some None => unify (remove_env K x) (compose (x ~ T) S)
    | _ => None
    end.

Fixpoint unify (h:nat) (pairs:list (typ*typ)) (K:kenv) (S:subs) {struct h}
  : option (kenv * subs) :=
  match h with 0 => None
  | S h' =>
    match pairs with
    | nil => Some (K,S)
    | (T1,T2) :: pairs' =>
      match typ_subst S T1, typ_subst S T2 with
      | typ_bvar n, typ_bvar m =>
        if n === m then unify h' pairs' K S else None
      | typ_fvar x, typ_fvar y =>
        if x == y then unify h' pairs' K S else
        match unify_vars (map (kind_subst S) K) x y with
        | Some (K', pairs) =>
          unify h' (pairs ++ pairs') K' (compose (x ~ typ_fvar y) S)
        | None => None
        end
      | typ_fvar x, T =>
        unify_nv (unify h' pairs') K S x T 
      | T, typ_fvar x =>
        unify_nv (unify h' pairs') K S x T 
       | typ_arrow T11 T12, typ_arrow T21 T22 =>
        unify h' ((T11,T21)::(T12,T22)::pairs') K S
      | _, _ =>
        None
      end
    end
  end.

Lemma mem_3 : forall v L, S.mem v L = false -> v \notin L.
Proof.
  intros. intro.
  rewrite (S.mem_1 H0) in H.
  discriminate.
Qed.

Hint Resolve mem_3.

Lemma notin_disjoint : forall x L, x \notin L -> disjoint {{x}} L.
Proof.
  intros; intro v. destruct (x == v); try subst; auto.
Qed.

Hint Resolve notin_disjoint.

Lemma binds_map_inv : forall (A:Set) (f:A->A) S x y,
  binds x y (map f S) -> exists z, f z = y /\ binds x z S.
Proof.
  unfold binds.
  induction S; simpl; intros. discriminate.
  destruct a.
  simpl in H.
  destruct (x == v).
  inversions H.
    exists* a.
  apply* IHS.
Qed.

Lemma typ_subst_compose : forall S1 S2 T,
  disjoint (dom S1) (dom S2) ->
  typ_subst (compose S1 S2) T =
  typ_subst S1 (typ_subst S2 T).
Proof.
  induction T; simpl; intros; auto.
    unfold compose.
    simpl; case_eq (get v S1); intros.
      rewrite* (binds_prepend (map (typ_subst S1) S2) H0).
      case_eq (get v S2); intros.
        destruct (H v). elim (binds_fresh H0 H2).
        elim (binds_fresh H1 H2).
      simpl; rewrite* H0.
    case_eq (get v S2); intros.
      rewrite* (binds_concat_fresh S1 (binds_map (typ_subst S1) H1)).
      destruct* (H v). elim (binds_fresh H1 H2).
    simpl; rewrite H0.
    case_eq (get v (map (typ_subst S1) S2 & S1)); intros; auto.
    destruct (binds_concat_inv H2).
      destruct H3. destruct (binds_map_inv _ _ H4).
      destruct H5; rewrite H6 in H1; discriminate.
    rewrite H3 in H0; discriminate.
  rewrite* IHT1.
  rewrite* IHT2.
Qed.

Lemma binds_typ_subst : forall x T S,
  binds x T S -> typ_subst S (typ_fvar x) = T.
Proof.
  intros. simpl. rewrite* H.
Qed.

Definition is_subst S := env_prop (fun T => disjoint (dom S) (typ_fv T)) S.

Lemma disjoint_subst : forall x T L T',
  disjoint (L \u {{x}}) (typ_fv T) ->
  disjoint L (typ_fv T') ->
  disjoint (L \u {{x}}) (typ_fv (typ_subst (x ~ T) T')).
Proof.
  induction T'; simpl; intros.
      intro; auto.
    destruct (v == x).
      subst.
      disjoint_solve.
    simpl.
    assert (disjoint {{v}} {{x}}); disjoint_solve.
    destruct* (v0 == v).
    destruct* (v0 == x).
    subst. elim (n e0).
  assert (disjoint L (typ_fv T'1)) by disjoint_solve.
  assert (disjoint L (typ_fv T'2)) by disjoint_solve.
  use (IHT'1 H H1).
  use (IHT'2 H H2).
  disjoint_solve.
Qed.

Lemma add_binding_is_subst : forall S x T,
  is_subst S ->
  disjoint (dom S \u {{x}}) (typ_fv T) ->
  is_subst (compose (x ~ T) S).
Proof.
  intros.
  unfold compose.
  intro; intros.
  binds_cases H1.
    destruct (binds_map_inv _ _ B) as [b [F B']].
    subst.
    use (H _ _ B').
    simpl in *.
    apply* disjoint_subst.
  destruct (binds_single_inv B0); subst.
  auto.
Qed.

Ltac case_rewrite t H :=
  case_eq t; introv H; rewrite H in *; try discriminate.

Lemma typ_subst_disjoint : forall S T,
  is_subst S -> disjoint (dom S) (typ_fv (typ_subst S T)).
Proof.
  intros; induction T; simpl in *.
      intro; auto.
    case_eq (get v S); intros.
    use (H _ _ H0).
    use (get_none_notin _ H0).
    simpl; intro x; destruct* (x == v).
  disjoint_solve.
Qed.

Lemma binds_add_binding : forall S T0 T1 v x T,
  is_subst S ->
  typ_subst S T0 = typ_fvar v ->
  binds x (typ_subst S T) S ->
  binds x (typ_subst (compose (v ~ T1) S) T) (compose (v ~ T1) S).
Proof.
  intros.
  use (typ_subst_disjoint T0 H).
    rewrite H0 in H2. simpl in H2.
  rewrite typ_subst_compose.
    unfold compose.
    apply binds_concat_fresh.
      apply* binds_map.
    simpl. rewrite union_empty_r; intro.
    rewrite (S.singleton_1 H3) in H2.
    destruct* (H2 x).
    elim (binds_fresh H1 H4).
  simpl; disjoint_solve.
Qed.

Lemma unify_keep_nv : forall h pairs K K' T S S' t t0 v,
  (forall K S,
    unify h pairs K S = Some (K', S') ->
    is_subst S ->
    is_subst S' /\
    (forall (x : var) (T : typ),
      binds x (typ_subst S T) S -> binds x (typ_subst S' T) S')) ->
  is_subst S ->
  typ_subst S t = typ_fvar v ->
  typ_subst S t0 = T ->
  unify_nv (unify h pairs) K S v T = Some (K', S') ->
  is_subst S' /\
  (forall (x : var) (T : typ),
    binds x (typ_subst S T) S -> binds x (typ_subst S' T) S').
Proof.
  intros until v. intros IHh HS R1 R2 H.
  unfold unify_nv in H; simpl in H.
  case_rewrite (S.mem v (typ_fv T)) R3.
  fold kind in *.
  destruct (get v K); try discriminate.
  destruct k. discriminate.
  destruct (IHh _ _ H); clear IHh.
    apply* add_binding_is_subst.
    simpl.
    use (typ_subst_disjoint t0 HS). rewrite R2 in H0.
    disjoint_solve.
    destruct* (v0 == v). subst*.
  split*.
  intros; apply H1.
  apply* binds_add_binding.
Qed.

Lemma unify_keep : forall h pairs K S K' S',
  unify h pairs K S = Some (K', S') ->
  is_subst S ->
  is_subst S' /\
  forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'.
Proof.
  induction h; simpl; intros. discriminate.
  destruct pairs.
    inversions H.
    auto.
  destruct p.
  case_rewrite (typ_subst S t) R1; case_rewrite (typ_subst S t0) R2.
        destruct (n === n0).
          apply* (IHh _ _ _ _ _ H).
        discriminate.
       apply* (@unify_keep_nv h pairs K K' (typ_bvar n)).
       intros. apply* IHh.
      apply* (@unify_keep_nv h pairs K K' (typ_bvar n)).
      intros. apply* IHh.
     destruct (v == v0).
       destruct* (IHh _ _ _ _ _ H).
     unfold unify_vars in H.
     remember (map (kind_subst S) K) as K0.
     destruct (get v K0); try discriminate.
     destruct (get v0 K0); try discriminate.
     destruct (unify_kinds k k0).
     destruct (IHh _ _ _ _ _ H); clear IHh.
       apply* add_binding_is_subst.
       simpl.
       use (typ_subst_disjoint t0 H0). rewrite R2 in H1. simpl in H1.
       assert (disjoint {{v}} {{v0}}) by auto.
       disjoint_solve.
     split*.
     intros; apply H2.
     apply* binds_add_binding.
    apply* (@unify_keep_nv h pairs K K' (typ_arrow t1 t2)).
    intros. apply* IHh.
   apply* (@unify_keep_nv h pairs K K' (typ_arrow t1 t2)).
   intros. apply* IHh.
  destruct* (IHh _ _ _ _ _ H); clear IHh.
Qed.

Lemma typ_subst_idem : forall S T,
  is_subst S -> typ_subst S (typ_subst S T) = typ_subst S T.
Proof.
  intros.
  induction T; simpl. auto.
    case_eq (get v S); intros.
      rewrite* typ_subst_fresh.
      apply (H _ _ H0).
    simpl.
    rewrite* H0.
  simpl; congruence.
Qed.

Lemma binds_subst_idem : forall x T S,
  binds x T S -> is_subst S -> binds x (typ_subst S T) S.
Proof.
  intros.
  use (binds_typ_subst H).
  use (f_equal (typ_subst S) H1).
  rewrite typ_subst_idem in H2; auto.
  congruence.
Qed.

Lemma typ_subst_extend : forall h pairs K S K' S' T,
  is_subst S ->
  unify h pairs K S = Some (K', S') ->
  typ_subst S' (typ_subst S T) = typ_subst S' T.
Proof.
  intros.
  destruct* (unify_keep _ _ _ H0).
  clear H0.
  induction T; intros. simpl*.
    remember (typ_subst S (typ_fvar v)) as T'.
    use (f_equal (typ_subst S) HeqT').
    rewrite typ_subst_idem in H0; auto.
    simpl in H0.
    case_rewrite (get v S) R.
      subst.
      use (H2 _ _ R).
      rewrite* (binds_typ_subst H0).
    simpl in HeqT'. rewrite R in HeqT'. subst*.
  simpl. congruence.
Qed.

Lemma unify_types_nv : forall S T1 T2 v T h' pairs' h pairs K K' S',
  typ_subst S T1 = typ_fvar v ->
  typ_subst S T2 = T ->
  unify h' pairs' K S = Some (K', S') ->
  unify_nv (unify h pairs) K S v T = Some (K', S') ->
  is_subst S ->
  typ_subst S' T1 = typ_subst S' T2.
Proof.
  intros.
  unfold unify_nv in H2.
  case_rewrite (S.mem v (typ_fv T)) R.
  assert (is_subst (compose (v ~ T) S)).
    apply* add_binding_is_subst.
    use (typ_subst_disjoint T2 H3).
    rewrite H0 in H4.
    use (notin_disjoint (mem_3 R)).
    disjoint_solve.
  rewrite <- (typ_subst_extend _ _ _ T1 H3 H1).
  rewrite H.
  fold kind in *.
  case_rewrite (get v K) R1. destruct k. discriminate.
  rewrite <- (typ_subst_extend _ _ _ (typ_fvar v) H4 H2).
  rewrite <- (typ_subst_extend _ _ _ T2 H3 H1).
  apply (f_equal (typ_subst S')).
  simpl. destruct* (v==v).
Qed.

Lemma typ_subst_res_fresh : forall S T v,
  is_subst S -> typ_subst S T = typ_fvar v -> v # S.
Proof.
  intros.
  use (typ_subst_disjoint T H).
  rewrite H0 in H1.
  simpl in H1. destruct* (H1 v).
Qed.

Theorem unify_types : forall h pairs K S K' S',
  unify h pairs K S = Some (K',S') ->
  is_subst S ->
  forall T1 T2,
    In (T1,T2) pairs -> typ_subst S' T1 = typ_subst S' T2.
Proof.
  induction h; intros. discriminate.
  poses H' H.
  simpl in H.
  destruct pairs.
    elim H1.
  simpl in H1; destruct H1.
    subst.
    case_rewrite (typ_subst S T1) R1; case_rewrite (typ_subst S T2) R2;
      try case_rewrite (S.mem v (typ_fv (typ_bvar n))) R3;
      try case_rewrite (S.mem v (typ_fv (typ_arrow t t0))) R3.
          destruct (n === n0).
            subst.
            rewrite <- (typ_subst_extend _ _ _ T1 H0 H').
            rewrite <- (typ_subst_extend _ _ _ T2 H0 H').
            congruence.
          discriminate.
         symmetry.
         apply* (unify_types_nv _ _ _ _ _ _ _ R2 R1 H' H).
        apply* (unify_types_nv _ _ _ _ _ _ _ R1 R2 H' H).
       destruct (v == v0).
         subst.
         rewrite <- (typ_subst_extend _ _ _ T1 H0 H').
         rewrite <- (typ_subst_extend _ _ _ T2 H0 H').
         congruence.
       unfold unify_vars in H.
       remember (map (kind_subst S) K) as K0.
       case_rewrite (get v K0) R3.
       case_rewrite (get v0 K0) R4.
       destruct (unify_kinds k k0).
       assert (IS: is_subst (compose (v ~ typ_fvar v0) S)).
         apply* add_binding_is_subst.
         use (typ_subst_disjoint T2 H0).
         rewrite R2 in H1.
         disjoint_solve. simpl. destruct* (v1 == v). subst*.
       rewrite <- (typ_subst_extend _ _ _ T1 IS H).
       rewrite <- (typ_subst_extend _ _ _ T2 IS H).
       use (typ_subst_disjoint T1 H0). rewrite  R1 in H1; simpl in H1.
       repeat rewrite* typ_subst_compose; try (simpl; disjoint_solve).
       rewrite R1; rewrite R2. simpl.
       destruct* (v == v). destruct* (v0 == v).
      apply* (unify_types_nv _ _ _ _ _ _ _ R1 R2 H' H).
     symmetry.
     apply* (unify_types_nv _ _ _ _ _ _ _ R2 R1 H' H).
    rewrite <- (typ_subst_extend _ _ _ T1 H0 H').
    rewrite <- (typ_subst_extend _ _ _ T2 H0 H').
    rewrite R1; rewrite R2.
    simpl.
    rewrite* (IHh _ _ _ _ _ H H0 t t1).
    rewrite* (IHh _ _ _ _ _ H H0 t0 t2).
  destruct p.
  case_rewrite (typ_subst S t) R1; case_rewrite (typ_subst S t0) R2;
    unfold unify_nv in H;
    try case_rewrite (S.mem v (typ_fv (typ_bvar n))) R3;
    try case_rewrite (S.mem v (typ_fv (typ_arrow t1 t2))) R3;
    fold kind in *;
    try (case_rewrite (get v K) R4; destruct k; try discriminate);
    try apply* (IHh _ _ _ _ _ H);
    try apply* add_binding_is_subst.
       destruct (n === n0). subst. apply* (IHh _ _ _ _ _ H).
       discriminate.
      simpl; intro; auto.
     simpl; intro; auto.
    destruct (v == v0).
      subst.
      apply* (IHh _ _ _ _ _ H).
    unfold unify_vars in H.
    remember (map (kind_subst S) K) as K0.
    case_rewrite (get v K0) R3.
    case_rewrite (get v0 K0) R4.
    destruct (unify_kinds k k0).
    apply* (IHh _ _ _ _ _ H).
      apply* add_binding_is_subst.
      use (typ_subst_disjoint t0 H0).
      rewrite R2 in H2.
      disjoint_solve.
      simpl; destruct* (v1 == v). subst*.
    apply* in_or_app.
   use (typ_subst_disjoint t0 H0).
   rewrite R2 in H2.
   use (notin_disjoint (mem_3 R3)).
   disjoint_solve.
  use (typ_subst_disjoint t H0).
  rewrite R1 in H2.
  use (notin_disjoint (mem_3 R3)).
  disjoint_solve.
Qed.

Definition well_subst K K' S :=
  forall Z k,
    binds Z k K ->
    well_kinded K' (kind_subst S k) (typ_subst S (typ_fvar Z)).

Lemma well_kinded_subst: forall S K K' k T,
  well_subst K K' S ->
  well_kinded K k T ->
  well_kinded K' (kind_subst S k) (typ_subst S T).
Proof.
  intros.
  induction H0.
    constructor.
  generalize (H x _ H0); intro HW.
  inversions HW.
  simpl typ_subst.
  case_eq (get x S); intros; rewrite H2 in H3.
    subst.
    simpl. apply* wk_kind.
    apply* entails_trans.
    apply* kind_subst_entails.
  simpl.
  inversions H3.
  apply* wk_kind.
  apply* entails_trans.
  apply* kind_subst_entails.
Qed.

Section Accum.
  Variables A B : Set.
  Variables (f : A -> B) (op : B->B->B) (unit : B).

  Fixpoint accum (l:list A) {struct l} : B :=
    match l with
    | nil => unit
    | a::rem => op (f a) (accum rem)
    end.
End Accum.

Fixpoint all_types S (pairs:list(typ*typ)) {struct pairs} : list typ :=
  match pairs with
  | nil => nil
  | p::rem =>
      typ_subst S (fst p) :: typ_subst S (snd p) :: all_types S rem
  end.

Definition all_fv S pairs :=
  accum typ_fv S.union {} (all_types S pairs).
Check all_fv.

Lemma kind_subst_idem : forall S k,
  is_subst S -> kind_subst S (kind_subst S k) = kind_subst S k.
Proof.
  intros.
  destruct k as [[kc kr]|].
    simpl.
    apply (f_equal (fun kr => Some (Kind kc kr))).
    induction kr; simpl. auto.
    rewrite IHkr.
    rewrite* typ_subst_idem.
  auto.
Qed.

Lemma remove_notin : forall v L,
  v \notin L -> S.remove v L = L.
Proof.
  intros.
  apply eq_ext; intro; split; intro. eauto with sets.
  apply* S.remove_2.
  intro Hv; rewrite Hv in H; auto.
Qed.

Lemma remove_single : forall v, S.remove v {{v}} = {}.
Proof.
  intros; apply eq_ext; intros; split; intro.
    use (S.remove_3 H).
    elim (S.remove_1 (S.singleton_1 H0) H).
  elim (in_empty H).
Qed.

Lemma dom_remove_env : forall (A:Set) v (K:Env.env A),
  ok K ->
 dom (remove_env K v) = S.remove v (dom K).
Proof.
  induction K; simpl; intros.
    apply eq_ext; intros; split; intro. elim (in_empty H0).
    apply* S.remove_3.
  destruct a.
  inversions H.
  destruct (v == v0).
    subst v0.
    rewrite remove_union.
    rewrite remove_single. rewrite* remove_notin. rewrite* union_empty_l.
  simpl.
  rewrite remove_union.
  rewrite* IHK.
  assert (v \notin {{v0}}) by auto.
  rewrite* (remove_notin H0).
Qed.

Ltac union_solve x :=
  match goal with
  | H: x \in _ |- _ =>
    destruct (S.union_1 H); clear H; auto with sets; try union_solve x
  end.

Lemma ok_remove_env : forall (A:Set) v (E:Env.env A),
  ok E -> ok (remove_env E v).
Proof.
  induction E; simpl; intros. auto.
  destruct a.
  inversions H.
  destruct* (v == v0).
  apply* ok_cons.
  clear -H4.
  induction E; simpl. simpl in H4. auto.
  destruct a.
  simpl in H4.
  destruct* (v == v1).
  simpl. 
  apply* notin_union_l.
Qed.

Hint Resolve ok_remove_env.

Lemma typ_fv_decr : forall v T S T1,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  typ_fv (typ_subst (compose (v ~ T) S) T1) <<
  S.remove v (typ_fv T \u typ_fv (typ_subst S T1)).
Proof.
  intros.
  rewrite* typ_subst_compose.
  induction (typ_subst S T1); simpl in *; intros x Hx.
      elim (in_empty Hx).
    destruct (v0 == v).
      subst.
      apply* S.remove_2.
        intro Hv; rewrite <- Hv in Hx. destruct* (H0 v).
        elim H1; auto with sets.
      auto with sets.
    apply* S.remove_2.
      intro Hv; rewrite <- Hv in Hx.
      revert Hx; simpl*.
    simpl in Hx; auto with sets.
  destruct (S.union_1 Hx); [use (IHt1 _ H1) | use (IHt2 _ H1)];
    apply* remove_subset;
    intros y Hy; destruct (S.union_1 Hy); auto with sets.
  simpl. intro x; destruct* (x == v).
Qed.

Lemma kind_fv_decr : forall v T S k,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  kind_fv (kind_subst (compose (v ~ T) S) k) <<
  S.remove v (typ_fv T \u kind_fv (kind_subst S k)).
Proof.
  intros.
  unfold kind_fv.
  destruct k as [[kc kr]|]; simpl.
    induction kr; simpl; intros x Hx. elim (in_empty Hx).
    destruct (S.union_1 Hx); clear Hx.
      rewrite union_assoc.
      rewrite remove_union.
      use (typ_fv_decr _ _ _ H H0 H1). auto with sets.
    rewrite union_assoc.
    rewrite (union_comm (typ_fv T)).
    rewrite <- union_assoc.
    rewrite remove_union.
    apply S.union_3. apply* IHkr.
  intros x Hx; elim (in_empty Hx).
Qed.

Lemma fv_in_decr : forall (A:Set) v T S (E:Env.env A) fv (sub:subs -> A -> A),
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  (forall a,
    fv (sub (compose (v ~ T) S) a) << S.remove v (typ_fv T \u fv (sub S a))) ->
  fv_in fv (map (sub (compose (v ~ T) S)) E) <<
  S.remove v (typ_fv T \u fv_in fv (map (sub S) E)).
Proof.
  intros.
  induction E; intros x Hx; simpl in *. elim (in_empty Hx).
  destruct a.
  simpl in *.
  destruct (S.union_1 Hx); clear Hx.
    rewrite union_assoc.
    rewrite remove_union.
    apply S.union_2.
    apply* (H1 a).
  rewrite union_comm.
  rewrite <- union_assoc.
  rewrite remove_union.
  apply S.union_3.
  rewrite union_comm.
  apply* IHE.
Qed.

Lemma all_fv_decr : forall v T S pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  all_fv (compose (v ~ T) S) pairs <<
  S.remove v (all_fv S ((typ_fvar v, T) :: pairs)).
Proof.
  unfold all_fv.
  induction pairs; intros.
    simpl. intros x Hx. elim (in_empty Hx).
  simpl.
  intros x Hx.
  rewrite* get_notin_dom.
  destruct (S.union_1 Hx).
    use (typ_fv_decr _ _ _ H H0 H1).
    apply* remove_subset.
    intros y Hy.
    destruct (S.union_1 Hy).
      rewrite <- (@typ_subst_fresh S T) in H3; auto with sets.
      disjoint_solve.
    auto with sets.
  destruct (S.union_1 H1); clear Hx H1.
    use (typ_fv_decr _ _ _ H H0 H2).
    apply* remove_subset.
    intros y Hy.
    destruct (S.union_1 Hy).
      rewrite <- (@typ_subst_fresh S T) in H3; auto with sets.
      disjoint_solve.
    auto with sets.
  use (IHpairs H H0 _ H2).
  apply* remove_subset.
  simpl.
  rewrite* get_notin_dom.
  intros y Hy.
  clear H1 H2.
  simpl in Hy.
  destruct (S.union_1 Hy). auto with sets.
  destruct (S.union_1 H1); auto with sets.
Qed.

Definition id := Env.empty (A:=typ).

Lemma typ_subst_id : forall T, typ_subst id T = T.
Proof.
  intro.
  apply typ_subst_fresh.
  simpl. intro; auto.
Qed.

Lemma is_subst_id : is_subst id.
Proof.
  unfold id, is_subst. intro; intros. elim (binds_empty H).
Qed.

Definition really_all_fv S K pairs :=
  fv_in kind_fv (map (kind_subst S) K) \u all_fv S pairs.

Lemma really_all_fv_decr : forall S K t t0 pairs v T,
  really_all_fv S K ((t, t0) :: pairs) \u fv_in typ_fv S << dom K ->
  typ_subst S t = typ_fvar v ->
  typ_subst S t0 = T ->
  is_subst S ->
  ok K ->
  S.mem v (typ_fv T) = false ->
  really_all_fv (compose (v ~ T) S) (remove_env K v) pairs \u
  fv_in typ_fv (compose (v ~ T) S) << S.remove v (dom K).
Proof.
  intros until T. intros Hra R1 R2 HS HK R3.
  unfold really_all_fv in *.
  intros x Hx.
  apply* remove_subset.
  clear Hra.
  assert (v # S) by apply* typ_subst_res_fresh.
  assert (disjoint (typ_fv T) ({{v}} \u dom S)).
    use (typ_subst_disjoint t0 HS). rewrite R2 in H0.
    disjoint_solve.
    destruct* (v0 == v); subst*.
  destruct (S.union_1 Hx); clear Hx.
    rewrite remove_union; apply S.union_2.
    destruct (S.union_1 H1); clear H1.
      unfold all_fv; simpl. rewrite R2.
      rewrite (union_comm (typ_fv (typ_subst S t))).
      do 2 rewrite union_assoc. do 2 (rewrite remove_union; apply S.union_2).
      rewrite union_comm.
      refine (fv_in_decr _ _ _ _ _ _ _ _ _); auto.
      intros; apply* kind_fv_decr.
      clear -H2; induction K; simpl in *. auto.
      destruct a; simpl.
      destruct (v == v0); simpl in H2.
        auto with sets.
      destruct (S.union_1 H2); auto with sets.
    rewrite remove_union; apply S.union_3.
    unfold all_fv; simpl.
    rewrite <- (typ_subst_idem t HS).
    rewrite <- (typ_subst_idem t0 HS).
    rewrite R1; rewrite R2.
    apply (all_fv_decr _ _ _ H H0 H2).
  unfold all_fv; simpl. rewrite R2.
  rewrite (union_comm (typ_fv T)).
  do 3 rewrite <- union_assoc.
  do 3 (rewrite remove_union; apply S.union_3).
  unfold compose in H1.
  simpl in H1.
  destruct (S.union_1 H1).
    rewrite remove_union.
    rewrite remove_notin. auto with sets.
    destruct* (H0 v).
  replace S with (map (typ_subst id) S).
    replace (v~T) with (compose (v~T) id) in H2.
      assert (v # id) by (unfold id; auto).
      assert (disjoint (typ_fv T) ({{v}} \u dom id))
        by (simpl; disjoint_solve).
      refine (fv_in_decr _ _ _ _ _ _ _ _ _); auto.
      intros; apply* typ_fv_decr.
    reflexivity.
  clear; induction S; simpl; auto.
  destruct a; simpl; rewrite typ_subst_id; rewrite* IHS.
Qed.

Lemma really_all_fv_comm : forall S K t t0 pairs,
  really_all_fv S K ((t,t0)::pairs) = really_all_fv S K ((t0,t)::pairs).
Proof.
  intros.
  unfold really_all_fv, all_fv; simpl.
  rewrite (union_assoc (typ_fv (typ_subst S t))).
  rewrite (union_comm (typ_fv (typ_subst S t))).
  rewrite* <- (union_assoc (typ_fv (typ_subst S t0))).
Qed.

Lemma binds_remove_env : forall (A:Set) v K x (a:A),
  binds x a K -> x <> v -> binds x a (remove_env K v).
Proof.
  unfold binds; induction K; simpl; intros. auto.
  destruct a; simpl in *.
  destruct (x == v0).
    destruct (v == v0). subst. elim H0; auto.
    simpl. destruct* (x == v0).
  destruct* (v == v0).
  simpl. destruct* (x == v0).
Qed.

Lemma kind_subst_combine : forall S S1 S2 k,
  (forall T, typ_subst S1 (typ_subst S2 T) = typ_subst S T) ->
  kind_subst S1 (kind_subst S2 k) = kind_subst S k.
Proof.
  intros.
  destruct k as [[kc kr]|].
    simpl.
    apply (f_equal (fun kr => Some (Kind kc kr))).
    induction kr. auto.
    simpl. rewrite IHkr. rewrite* H.
  auto.
Qed.

Definition unify_kinds_spec pairs K S K' S' :=
  is_subst S -> ok K ->
  disjoint (dom S) (dom K) ->
  really_all_fv S K pairs \u fv_in typ_fv S << dom K ->
  ok K' /\ disjoint (dom S') (dom K') /\
  fv_in kind_fv (map (kind_subst S') K') \u fv_in typ_fv S' << dom K' /\
  well_subst (map (kind_subst S) K) (map (kind_subst S') K') S'.

Lemma unify_kinds_nv : forall h pairs K S v T K' S' h' pairs' t t0,
  unify_nv (unify h pairs) K S v T = Some (K', S') ->
  typ_subst S t = typ_fvar v ->
  typ_subst S t0 = T ->
  unify h' pairs' K S = Some (K',S') ->
  (forall pairs K S,
    unify h pairs K S = Some (K',S') -> unify_kinds_spec pairs K S K' S') ->
  unify_kinds_spec ((t,t0)::pairs) K S K' S'.
Proof.
  unfold unify_nv.
  intros until 1.
  intros R1 R2 H' IHh HS Hk Dis Hra.
  case_rewrite (S.mem v (typ_fv T)) R3.
  case_rewrite (get v K) R4.
  destruct o. discriminate.
  assert (His : is_subst (compose (v ~ T) S)).
    apply* add_binding_is_subst.
    use (typ_subst_disjoint t0 HS).
    rewrite R2 in H0.
    use (notin_disjoint (mem_3 R3)).
    disjoint_solve.
  destruct* (IHh _ _ _ H); clear IHh.
      rewrite* dom_remove_env.
      unfold compose. simpl.
      rewrite dom_map.
      intro x; destruct (v == x).
        right; apply* S.remove_1.
      destruct* (Dis x). right; intro. elim H0; apply* S.remove_3.
    rewrite* dom_remove_env.
    apply* really_all_fv_decr.
  intuition.
  intro; intros.
  unfold well_subst in H4.
  destruct (binds_map_inv _ _ H3) as [k0 [Hk0 B]].
  destruct (Z == v).
    subst. fold kind in R4. rewrite B in R4.
    inversions R4. simpl. apply wk_any.
  use (binds_map (kind_subst (compose (v ~ T) S)) (binds_remove_env B n)).
  use (H4 _ _ H5).
  rewrite (@kind_subst_combine S') in H6.
    rewrite <- (@kind_subst_combine S' S' S) in H6.
      rewrite Hk0 in H6. auto.
    intro; apply* typ_subst_extend.
  intro; apply* typ_subst_extend.
Qed.

Lemma in_all_fv : forall S t t0 l,
  In (t,t0) l ->
  typ_fv (typ_subst S t) \u typ_fv (typ_subst S t0) << all_fv S l.
Proof.
  induction l; simpl; intros H x Hx. elim H.
  unfold all_fv; simpl.
  destruct H.
    subst; simpl.
    rewrite union_assoc; auto with sets.
  rewrite union_assoc; apply S.union_3; apply* IHl.
Qed.

Lemma in_typ_fv : forall t l,
  In t l -> typ_fv t << typ_fv_list l.
Proof.
  induction l; simpl; intros H x Hx. elim H.
  destruct H.
    subst; simpl.
    auto with sets.
  apply S.union_3; apply* IHl.
Qed.

Lemma unify_kinds_fv : forall k k0 k1 l S,
  unify_kinds k k0 = (k1, l) ->
  kind_fv (kind_subst S k1) \u all_fv S l <<
  kind_fv (kind_subst S k) \u kind_fv (kind_subst S k0).
Proof.
  unfold unify_kinds; intros.
  destruct k as [[kc kr]|].
    destruct k0 as [[kc0 kr0]|].
      case_rewrite
        (unify_kind_rel (kr ++ kr0) nil (unique (cstr_lub kc kc0)) nil) R1.
      inversions H; clear H. simpl.
      unfold kind_fv; simpl.
      repeat rewrite map_map; simpl.
      rewrite <- fv_list_map. rewrite <- map_app.
      set (pairs := nil(A:=typ*typ)) in *.
      set (kr' := nil(A:=var*typ)) in *.
      intros x Hx.
      rewrite <- union_empty_r.
      replace {} with
        (typ_fv_list (List.map (fun x : var * typ => typ_subst S (snd x)) kr'))
        by reflexivity.
      rewrite <- union_empty_r.
      replace {} with (all_fv S pairs) by reflexivity.
      clearbody pairs kr'.
      gen pairs kr'; induction (kr ++ kr0); simpl; intros.
        inversions R1; intuition.
        rewrite <- union_assoc; auto with sets.
      destruct a; simpl.
      destruct (In_dec eq_var_dec v (unique (cstr_lub kc kc0))).
        case_rewrite (get v kr') R2; poses Hsub (IHl1 _ _ R1).
          rewrite <- union_assoc in Hsub.
          destruct (S.union_1 Hsub); clear Hsub; auto with sets.
          destruct (S.union_1 H); clear H; auto with sets.
          unfold all_fv in H0; simpl in H0.
          destruct (S.union_1 H0); clear H0; auto with sets.
          destruct (S.union_1 H); clear H; auto with sets.
Lemma get_in : forall (A:Set) x (a:A) E,
  binds x a E -> In (x, a) E.
Proof.
  unfold binds; induction E; intros. elim (binds_empty H).
  destruct a0; simpl in *.
  destruct* (x == v). inversions* H.
Qed.
          use (get_in R2).
          use (in_map (fun x : var * typ => typ_subst S (snd x)) _ _ H).
          use (in_typ_fv _ _ H1 H0).
          auto with sets.
        simpl in Hsub. union_solve x.
      poses Hsub (IHl1 _ _ R1); clear IHl1 Hx.
      simpl in Hsub.
      union_solve x.
    inversions H.
    unfold kind_fv, all_fv; simpl.
    apply subset_refl.
  inversions H.
  unfold kind_fv, all_fv; simpl.
  rewrite union_comm; apply subset_refl.
Qed.

Definition kind_entails k k' :=
  match k', k with
  | None, _ => True
  | Some c', Some c => entails c c'
  |  Some c', None => False
  end.

Lemma unify_kind_rel_keep : forall kr kr' un pairs k' l,
  unify_kind_rel kr kr' un pairs = (k', l) ->
  incl kr' k' /\ incl pairs l.
Proof.
  induction kr; simpl; intros. inversions H. split*.
  destruct a.
  destruct (In_dec eq_var_dec v un).
    case_rewrite (get v kr') R1; destruct* (IHkr _ _ _ _ _ H).
  destruct* (IHkr _ _ _ _ _ H).
Qed.

Lemma well_subst_unify_kinds : forall k k0 k1 l S,
  unify_kinds k k0 = (k1, l) ->
  (forall T1 T2, In (T1, T2) l -> typ_subst S T1 = typ_subst S T2) ->
  kind_entails (kind_subst S k1) (kind_subst S k) /\
  kind_entails (kind_subst S k1) (kind_subst S k0).
Proof.
  unfold unify_kinds, kind_entails.
  intros.
  destruct k as [[kc kr]|]; destruct k0 as [[kc0 kr0]|]; simpl.
     case_rewrite
       (unify_kind_rel (kr ++ kr0) nil (unique (cstr_lub kc kc0)) nil) R1.
     inversions H; clear H.
     simpl.
     assert (incl
       (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT)))
         (kr ++ kr0))
       (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT))) l0)).
       clear -H0 R1.
       set (pairs := nil(A:=typ*typ)) in R1.
       set (kr' := nil(A:=var*typ)) in R1.
       clearbody pairs kr'.
       intros T HT.
       destruct T; gen kr' pairs; induction (kr++kr0); simpl; intros. elim HT.
       destruct a.
       destruct (In_dec eq_var_dec v0 (unique (cstr_lub kc kc0)));
         try case_rewrite (get v0 kr') R2; simpl in HT; destruct HT;
         try solve [apply* IHl1]; inversions H; clear H;
         destruct (unify_kind_rel_keep _ _ _ _ R1).
           use (H _ (get_in R2)); clear H.
           assert (In (t0,t1) l) by auto.
           use (H0 _ _ H).
           rewrite H3.
           refine (in_map _ _ _ H2).
         assert (In (v,t0) l0) by auto.
         refine (in_map _ _ _ H2).
       assert (In (v,t0) l0) by auto.
       refine (in_map _ _ _ H2).
     destruct (proj2 (cstr_lub_ok kc kc0 _) (Cstr.entails_refl _)).
     split; split*; simpl; intros; apply H; rewrite map_app; apply* in_or_app.
    split*.
    inversions H; clear H.
    simpl. apply entails_refl.
   split*.
   inversions H; clear H.
   simpl. apply entails_refl.
  auto.
Qed.

Lemma all_fv_app : forall S l1 l2,
  all_fv S (l1 ++ l2) = all_fv S l1 \u all_fv S l2.
Proof.
  intros.
  unfold all_fv.
  induction l1; simpl. rewrite* union_empty_l.
  rewrite IHl1.
  repeat rewrite union_assoc. auto.
Qed.

Lemma map_remove_env : forall (A:Set) x f (E:Env.env A),
  map f (remove_env E x) = remove_env (map f E) x.
Proof.
  induction E; simpl in *. auto.
  destruct a; simpl.
  destruct (x == v); simpl*.
  rewrite* IHE.
Qed.

Lemma map_map_env : forall (A:Set) f f1 f2 (E:Env.env A),
  (forall x, f x = f1 (f2 x)) -> map f E = map f1 (map f2 E).
Proof.
  intros; induction E; simpl. auto.
  destruct a; simpl.
  rewrite H.
  rewrite* IHE.
Qed.

Lemma fv_in_remove_env : forall (A:Set) (fv:A->vars) x E,
  fv_in fv (remove_env E x) << fv_in fv E.
Proof.
  induction E; simpl. apply subset_refl.
  destruct a; simpl.
  destruct (x == v); simpl; intros y Hy; auto with sets.
  destruct (S.union_1 Hy). auto with sets.
  use (IHE _ H). auto with sets.
Qed.

Lemma well_subst_unify : forall k k0 k1 l v v0 S K SK S' K' h pairs h' pairs',
  unify h (l ++ pairs) (remove_env (remove_env SK v) v0 & v0 ~ k1)
    (compose (v ~ typ_fvar v0) S) = Some (K', S') ->
  unify h' pairs' K S = Some (K', S') ->
  unify_kinds k k0 = (k1, l) ->
  SK = map (kind_subst S) K ->
  binds v k SK ->
  binds v0 k0 SK ->
  is_subst S ->
  is_subst (compose (v ~ typ_fvar v0) S) ->
  v # S ->
  v <> v0 ->
  well_subst
    (map (kind_subst (compose (v ~ typ_fvar v0) S))
      (remove_env (remove_env SK v) v0 & v0 ~ k1))
    (map (kind_subst S') K') S' ->
  well_subst SK (map (kind_subst S') K') S'.
Proof.
  intros until 1; intros H' HU HeqSK B1 B2 HS HS1 Hv n WS x; intros.
  unfold well_subst in WS.
  use (fun T => typ_subst_extend _ _ _ T HS1 H).
  use (unify_types _ _ _ H HS1).
  destruct (x == v0).
    subst.
    rewrite (binds_func H0 B2) in *; clear H0.
    assert (well_kinded (map (kind_subst S') K') (kind_subst S' k1)
               (typ_subst S' (typ_fvar v0))).
      rewrite <- (kind_subst_combine S' S' (compose (v ~ typ_fvar v0) S)).
      apply WS. apply binds_map. apply binds_head. auto.
    use (proj1 (unify_keep _ _ _ H HS1)).
    use (unify_types _ _ _ H HS1).
    assert (forall T1 T2 : typ, In (T1, T2) l ->
               typ_subst S' T1 = typ_subst S' T2).
      intros. apply H4. apply* in_or_app.
    destruct (well_subst_unify_kinds _ _ S' HU H5).
    clear H4 H5 H6.
    inversions H0.
      rewrite <- H6 in H7.
      unfold kind_entails in H7; simpl in H7.
      case_rewrite (kind_subst S' k0) R4. elim H7.
      apply wk_any.
    simpl; rewrite <- H5.
    rewrite <- H4 in H7.
    unfold kind_entails in H7; simpl in H7.
    case_rewrite (kind_subst S' k0) R4.
      apply* wk_kind. apply* entails_trans.
    apply wk_any.
  destruct (x == v).
    subst.
    rewrite (binds_func H0 B1) in *; clear H0.
    use (proj1 (unify_keep _ _ _ H HS1)).
    assert (well_kinded (map (kind_subst S') K') (kind_subst S' k1)
               (typ_subst S' (typ_fvar v))).
      rewrite <- (kind_subst_combine S' S' (compose (v ~ typ_fvar v0) S)).
      rewrite <- (typ_subst_extend _ _ _ (typ_fvar v) HS1 H).
      destruct (binds_map_inv _ _ B1).
      rewrite* typ_subst_compose.
      rewrite* (typ_subst_fresh S).
      simpl. destruct* (v == v).
      simpl. intro y; destruct* (y == v).
      simpl. intro y; destruct* (y == v).
      intros. apply* typ_subst_extend.
    use (unify_types _ _ _ H HS1).
    assert (forall T1 T2 : typ, In (T1, T2) l ->
               typ_subst S' T1 = typ_subst S' T2).
      intros. apply H4. apply* in_or_app.
    destruct (well_subst_unify_kinds _ _ S' HU H5).
    clear H4 H5 H7.
    inversions H3.
      rewrite <- H7 in H6.
      unfold kind_entails in H6; simpl in H6.
      case_rewrite (kind_subst S' k) R4. elim H6.
      apply wk_any.
    simpl; rewrite <- H5.
    rewrite <- H4 in H6.
    unfold kind_entails in H6; simpl in H6.
    case_rewrite (kind_subst S' k) R4.
      apply* wk_kind. apply* entails_trans.
    apply wk_any.
  subst.
  assert (x # v0 ~ k1) by simpl*.
  use (binds_map (kind_subst (compose (v ~ typ_fvar v0) S))
          (binds_concat_fresh _ (binds_remove_env (binds_remove_env H0 n1) n0)
            H3)).
  use (WS _ _ H4).
  rewrite (@kind_subst_combine S') in H5. auto.
  intro; apply* typ_subst_extend.
Qed.

Lemma unify_kinds_vars :
  forall h pairs K S v v0 K' S' h' pairs' t t0 k k0 k1 l SK,
  unify h (l ++ pairs) (remove_env (remove_env SK v) v0 & v0 ~ k1)
    (compose (v ~ typ_fvar v0) S) = Some (K', S') ->
  typ_subst S t = typ_fvar v ->
  typ_subst S t0 = typ_fvar v0 ->
  v <> v0 ->
  SK = map (kind_subst S) K ->
  binds v k SK ->
  binds v0 k0 SK ->
  unify_kinds k k0 = (k1, l) ->
  unify h' pairs' K S = Some (K',S') ->
  (forall pairs K S,
    unify h pairs K S = Some (K',S') -> unify_kinds_spec pairs K S K' S') ->
  unify_kinds_spec ((t,t0)::pairs) K S K' S'.
Proof.
  intros until SK.
  intros H R1 R2 n HeqSK R3 R4 R5 H' IHh HS HK Dis Hra.
  assert (His: is_subst (compose (v ~ typ_fvar v0) S)).
    apply* add_binding_is_subst.
    use (typ_subst_disjoint t0 HS).
    rewrite R2 in H0.
    simpl in *.
    intro x. destruct* (x == v0). subst v0; destruct* (H0 x).
  assert (HSK: ok SK).
    rewrite (app_nil_end SK).
    fold (nil & SK).
    rewrite HeqSK. apply ok_map.
    unfold concat; rewrite* <- (app_nil_end K).
  destruct* (IHh _ _ _ H); clear IHh.
        constructor. repeat apply ok_remove_env. auto.
        rewrite dom_remove_env.
          apply S.remove_1. reflexivity.
        apply* ok_remove_env.
      simpl.
      rewrite dom_map.
      repeat rewrite* dom_remove_env.
      disjoint_solve.
        destruct* (v1 == v).
        subst; right.
        apply* notin_union_l.
        intro.
        use (S.remove_3 H1).
        elim (S.remove_1 (refl_equal v) H2).
      destruct* (v1 == v0).
        subst; left.
        use (typ_subst_res_fresh _ HS R2).
      right; apply* notin_union_l.
      intro.
      use (S.remove_3 (S.remove_3 H1)).
      rewrite HeqSK in H2.
      rewrite dom_map in H2. auto.
    assert (S.mem v (typ_fv (typ_fvar v0)) = false).
      simpl. case_eq (S.mem v {{v0}}); intros; auto.
      pose (S.mem_2 H0).
      elim n; rewrite* (S.singleton_1 i).
    poses Hsub (really_all_fv_decr Hra R1 R2 HS HK H0).
    intros x Hx.
    unfold really_all_fv in Hx.
    rewrite all_fv_app in Hx.
    simpl in Hx.
    repeat rewrite union_assoc in Hx.
    simpl.
    rewrite* dom_remove_env.
    destruct (x == v0). subst; auto with sets.
    rewrite* dom_remove_env.
    rewrite HeqSK; rewrite dom_map.
    assert (v # S) by apply* typ_subst_res_fresh.
    assert (disjoint (typ_fv (typ_fvar v0)) ({{v}} \u dom S)).
      simpl; intro y; destruct* (y == v0); subst.
      use (typ_subst_res_fresh _ HS R2).
    assert (forall y k,
              binds y k SK ->
              x \in kind_fv (kind_subst (compose (v ~ typ_fvar v0) S) k) ->
              x \in {{v0}} \u S.remove v0 (S.remove v (dom K))).
      clear Hx; intros.
      use (kind_fv_decr _ _ _ H1 H2 H4).
      simpl in H5; rewrite remove_union in H5.
      destruct (S.union_1 H5); clear H4 H5.
        apply S.union_2; apply* S.remove_3.
      apply S.union_3; apply* S.remove_2.
      apply S.remove_2. intro Hv; elim (S.remove_1 Hv H6).
      apply Hra.
      unfold really_all_fv.
      repeat apply S.union_2.
      use (S.remove_3 H6).
      rewrite <- HeqSK.
      apply (fv_in_spec kind_fv H3).
      rewrite HeqSK in H3.
      destruct (binds_map_inv _ _ H3) as [k' [E B]].
      subst.
      rewrite kind_subst_idem in H4; auto.
    union_solve x.
            poses Hfv (unify_kinds_fv _ _ _ R5 (S.union_2 _ H4)); clear H4.
            destruct (S.union_1 Hfv); clear Hfv. apply* (H3 _ _ R3 H4).
            apply* H3.
          apply S.union_3.
          apply S.remove_2. intro Hx; elim n0; rewrite* Hx.
          apply Hsub.
          apply S.union_2.
          clear H H' Hsub Hra; unfold really_all_fv in *.
          apply S.union_2.
          subst.
          repeat rewrite map_remove_env in *.
          rewrite <- (map_map_env (kind_subst (compose (v ~ typ_fvar v0) S)))
            in H4.
            apply (fv_in_remove_env _ _ _ H4).
          intro.
          rewrite (kind_subst_combine (compose (v ~ typ_fvar v0) S)). auto.
          intro.
          assert (disjoint (dom (v ~ typ_fvar v0)) (dom S)).
            simpl. use (typ_subst_res_fresh _ HS R1).
            intro y; destruct* (y == v).
          repeat rewrite* typ_subst_compose. rewrite* typ_subst_idem.
        poses Hfv (unify_kinds_fv _ _ _ R5 (S.union_3 _ H5)).
        destruct (S.union_1 Hfv); clear Hfv. apply* (H3 _ _ R3 H4).
        apply* H3.
      unfold really_all_fv in Hsub.
      apply S.union_3.
      apply S.remove_2. intro Hx; elim n0; rewrite* Hx.
      apply Hsub; clear H H' Hra Hsub.
      auto with sets.
    unfold really_all_fv in Hsub.
    apply S.union_3.
    apply S.remove_2. intro Hx; elim n0; rewrite* Hx.
    apply Hsub; clear H H' Hra Hsub.
    unfold compose. simpl.
    auto with sets.
  intuition.
  subst; apply* well_subst_unify.
  apply* typ_subst_res_fresh.
Qed.

Theorem unify_kinds_ok : forall h pairs K S K' S',
  unify h pairs K S = Some (K',S') ->
  unify_kinds_spec pairs K S K' S'.
Proof.
  induction h; intros; intros HS Hk Dis Hra. discriminate.
  poses H' H.
  simpl in H.
  destruct pairs.
    inversions H.
    intuition.
      intros x Hx; apply Hra.
      unfold really_all_fv.
      destruct (S.union_1 Hx); auto with sets.
    intro; intros.
    destruct (binds_map_inv _ _ H0) as [k0 [HE B]].
    subst.
    rewrite* typ_subst_fresh.
      rewrite* kind_subst_idem.
      destruct k0.
        simpl in *. apply* wk_kind.
        split; simpl*.
      apply wk_any.
    case_eq (S.mem Z (dom K')); intros.
      use (S.mem_2 H1).
      destruct* (Dis Z).
      intro. destruct* (x == Z). simpl*.
    elim (binds_fresh B (mem_3 H1)).
  destruct p.
  case_rewrite (typ_subst S t) R1; case_rewrite (typ_subst S t0) R2.
        destruct (n === n0).
          apply* (IHh _ _ _ _ _ H).
          intros x Hx; apply Hra.
          clear -Hx.
          unfold really_all_fv, all_fv in *; simpl.
          union_solve x.
        discriminate.
       rewrite really_all_fv_comm in Hra.
       refine (unify_kinds_nv h _ _ H R2 R1 H' _ _ _ _ _); auto.
      refine (unify_kinds_nv h _ _ H R1 R2 H' _ _ _ _ _); auto.
      destruct (v == v0).
        subst.
        apply* (IHh _ _ _ _ _ H).
        intros x Hx; apply Hra.
        clear -Hx.
        unfold really_all_fv, all_fv in *; simpl.
        union_solve x.
      unfold unify_vars in H.
      remember (map (kind_subst S) K) as SK.
      case_rewrite (get v SK) R3.
      case_rewrite (get v0 SK) R4.
      case_rewrite (unify_kinds k k0) R5.
      subst; refine (unify_kinds_vars _ _ _ H R1 R2 n _ R3 R4 R5 H' _ _ _ _ _);
        auto.
     refine (unify_kinds_nv h _ _ H R1 R2 H' _ _ _ _ _); auto.
    rewrite really_all_fv_comm in Hra.
    refine (unify_kinds_nv h _ _ H R2 R1 H' _ _ _ _ _); auto.
  destruct* (IHh _ _ _ _ _ H HS).
  clear -Hra R1 R2 HS.
  unfold really_all_fv, all_fv in *; simpl in *.
  intros x Hx; apply Hra; clear Hra.
  rewrite <- (typ_subst_idem t HS).
  rewrite <- (typ_subst_idem t0 HS).
  rewrite R1; rewrite R2.
  simpl.
  repeat rewrite <- union_assoc in *.
  union_solve x.
Qed.
       
Lemma typ_subst_map_idem : forall S,
  is_subst S -> ok S -> map (typ_subst S) S = S.
Proof.
  intros.
  remember S as S0.
  pattern S0 at 1.
  rewrite HeqS0.
  assert (env_prop (fun T => typ_subst S T = T) S0).
    intro; intros.
    rewrite <- HeqS0.
    rewrite <- (binds_typ_subst H1).
    apply* typ_subst_idem.
  clear HeqS0 H.
  induction S0. auto.
  inversions H0.
  simpl. rewrite (H1 x a0).
    rewrite* IHS0.
    intro; intros.
    apply (H1 x0 a).
    unfold binds. simpl.
    destruct* (x0 == x).
    subst. elim (binds_fresh H H4).
  unfold binds; simpl.
  destruct* (x == x).
Qed.

Lemma fv_in_subset_inv : forall (A:Set) fv F E,
  fv_in fv E << F <-> forall x (a:A), In (x,a) E -> fv a << F.
Proof.
  induction E; intros; split; intros. elim H0.
      simpl. intros x Hx; elim (in_empty Hx).
    simpl in *; destruct H0.
      subst.
      destruct* (proj1 (subset_union_l (fv a0) (fv_in fv E) F)).
    destruct a.
    destruct* (proj1 (subset_union_l (fv a) (fv_in fv E) F)).
  simpl in *.
  destruct a.
  apply* (proj2 (subset_union_l (fv a) (fv_in fv E) F)).
Qed.

Lemma typ_subst_prebind : forall v T S T1,
  typ_subst S T = typ_subst S (typ_fvar v) ->
  typ_subst S (typ_subst (v~T) T1) = typ_subst S T1.
Proof.
  induction T1; intros.
      simpl*.
    simpl. destruct (v0 == v).
      subst*.
    reflexivity.
  simpl.
  rewrite* IHT1_1. rewrite* IHT1_2.
Qed.

Definition mgu_spec pairs S0 S S' :=
  is_subst S0 ->
  (forall T1 T2, In (T1,T2) pairs ->
    typ_subst S' (typ_subst S0 T1) = typ_subst S' (typ_subst S0 T2)) ->
  forall T1 T2,
    typ_subst S T1 = typ_subst S T2 ->
    typ_subst S' (typ_subst S0 T1) = typ_subst S' (typ_subst S0 T2).

Lemma unify_mgu_step : forall S0 pairs S S' h t t0 v T,
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  unify pairs (compose (v ~ T) S0) h = Some S ->
  S.mem v (typ_fv T) = false ->
  (forall S0, unify pairs S0 h = Some S -> mgu_spec pairs S0 S S') ->
  mgu_spec ((t,t0)::pairs) S0 S S'.
Proof.
  intros until T.
  intros R1 R2 HU R3 IHh HS0 Heq.
  intros.
  assert (BS': typ_subst S' T = typ_subst S' (typ_fvar v)).
    assert (In (t, t0) ((t,t0)::pairs)) by simpl*.
    use (Heq _ _ H0); clear H0.
    rewrite R1 in H1; rewrite R2 in H1.
    auto.
  assert (Hv: v # S0) by apply* typ_subst_res_fresh.
  assert (typ_subst S' (typ_subst (compose (v ~ T) S0) T1) =
          typ_subst S' (typ_subst (compose (v ~ T) S0) T2)).
    apply* IHh.
      apply* add_binding_is_subst.
      assert (disjoint {{v}} (typ_fv T)).
        intro x; destruct* (x == v); subst.
        right; intro. rewrite (S.mem_1 H0) in R3. discriminate.
      use (typ_subst_disjoint t0 HS0).
      rewrite R2 in H1.
      disjoint_solve.
    intros.
    repeat rewrite* typ_subst_add_binding.
    assert (In (T0, T3) ((t,t0)::pairs)) by simpl*.
      use (Heq _ _ H1); clear H1.
    repeat rewrite* typ_subst_prebind.
  do 2 rewrite typ_subst_add_binding in H0; auto.
  do 2 rewrite typ_subst_prebind in H0; auto.
Qed.

Lemma unify_mgu0 : forall h pairs S0 S S',
  unify pairs S0 h = Some S -> mgu_spec pairs S0 S S'.
Proof.
  induction h; intros; intro; intros. discriminate.
  simpl in H.
  destruct pairs.
    inversions H; clear H.
    rewrite* H2.
  destruct p.
  case_rewrite (typ_subst S0 t) R1; case_rewrite (typ_subst S0 t0) R2;
    try case_rewrite (S.mem v (typ_fv (typ_bvar n))) R3;
    try case_rewrite (S.mem v (typ_fv (typ_arrow t1 t2))) R3.
        destruct* (n === n0). unfold mgu_spec in IHh; auto*.
        discriminate.
       apply* (unify_mgu_step (S':=S') _ R2 R1 H).
       simpl; intros.
       destruct H3.
         inversions H3; symmetry; apply* H1.
       apply* H1.
      apply* (unify_mgu_step (S':=S') _ R1 R2 H).
     destruct (v == v0).
       subst v0.
       unfold mgu_spec in IHh; auto*.
     apply* (unify_mgu_step (S':=S') _ R1 R2 H).
     simpl. case_eq (S.mem v {{v0}}); intro; auto.
     elim n; rewrite* (S.singleton_1 (S.mem_2 H3)).
    apply* (unify_mgu_step (S':=S') _ R1 R2 H).
   apply* (unify_mgu_step (S':=S') _ R2 R1 H).
   simpl; intros.
   destruct H3.
     inversions H3; symmetry; apply* H1.
   apply* H1.
  apply* (IHh _ _ _ S' H).
  simpl; intros.
  assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
  pose (H1 _ _ H4).
  rewrite <- (typ_subst_idem t H0) in e.
  rewrite <- (typ_subst_idem t0 H0) in e.
  rewrite R1 in e; rewrite R2 in e; simpl in e.
  inversions e.
  destruct H3. inversions* H3.
  destruct* H3. inversions* H3.
Qed.

Theorem unify_mgu : forall h S S' T1 T2,
  unify ((T1,T2)::nil) id h = Some S ->
  typ_subst S' T1 = typ_subst S' T2 ->
  forall T3 T4,
    typ_subst S T3 = typ_subst S T4 ->
    typ_subst S' T3 = typ_subst S' T4.
Proof.
  intros.
  rewrite <- (typ_subst_id T3).
  rewrite <- (typ_subst_id T4).
  apply* (unify_mgu0 _ _ S' H is_subst_id).
  simpl; intros.
  destruct* H2.
  inversions H2.
  repeat rewrite typ_subst_id.
  auto.
Qed.

Fixpoint typ_size (T : typ) : nat :=
  match T with
  | typ_arrow T1 T2 => S (typ_size T1 + typ_size T2)
  | _ => 1
  end.

Definition all_size S pairs :=
  accum typ_size plus 0 (all_types S pairs).

Fixpoint pow2exp (m n:nat) {struct n} :=
  match n with
  | 0 => m
  | S n' => pow2exp (m*m) n'
  end.

Lemma pow2exp_min : forall n m, m <= pow2exp m n.
Proof.
  induction n; intros; simpl. omega.
  use (IHn (m*m)).
  destruct m; simpl in *. auto.
  set (m*S m) in *. omega.
Qed.

Require Import Arith Omega.

Lemma pow2exp_lt_le : forall m n s t,
  s < t -> m <= n -> pow2exp s m < pow2exp t n.
Proof.
  induction m; destruct n; simpl; intros; try omega.
    use (pow2exp_min n (t*t)).
    assert (s < t * t).
      destruct t; try omega.
      simpl. set (t*S t). omega.
    omega.
  apply IHm.
    eapply le_lt_trans; try apply* mult_lt_compat_r.
      apply mult_le_compat_l. omega.
    omega.
  omega.
Qed.

Definition size_pairs S pairs :=
  pow2exp (all_size S pairs) (S.cardinal (all_fv S pairs)).

Lemma size_pairs_grows : forall S p pairs,
  size_pairs S pairs < size_pairs S (p :: pairs).
Proof.
  intros.
  unfold size_pairs.
  unfold all_fv, all_size.
  simpl.
  rewrite union_assoc.
  rewrite cardinal_union.
  apply pow2exp_lt_le.
    destruct (typ_subst S (fst p)); simpl; omega.
  omega.
Qed.

Lemma cardinal_decr : forall v T S pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  S.cardinal (all_fv (compose (v ~ T) S) pairs) <
  S.cardinal (all_fv S ((typ_fvar v, T) :: pairs)).
Proof.
  intros.
  use (all_fv_decr T S pairs H H0).
  use (le_lt_n_Sm _ _ (cardinal_subset H1)).
  rewrite cardinal_remove in H2. auto.
  unfold all_fv.
  simpl. rewrite* get_notin_dom.
  simpl; auto with sets.
Qed.

Lemma typ_subst_decr : forall v T S T1,
  v # S ->
  typ_size (typ_subst (compose (v ~ T) S) T1) <=
  typ_size T * typ_size (typ_subst S T1).
Proof.
  intros.
  rewrite* typ_subst_add_binding.
  induction (typ_subst S T1); simpl. destruct T; simpl; omega.
    destruct (v0 == v). omega.
    destruct T; simpl; omega.
  assert (0 < typ_size T).
    destruct T; simpl; omega.
  destruct (typ_size T). omega.
  simpl in *.
  rewrite mult_comm in *.
  simpl.
  rewrite mult_plus_distr_r.
  omega.
Qed.

Lemma typ_subst_decr_all : forall v T S pairs,
  v # S ->
  all_size (compose (v ~ T) S) pairs <= typ_size T * all_size S pairs.
Proof.
  unfold all_size; induction pairs; intros; simpl. omega.
  repeat rewrite mult_plus_distr_l.
  use (IHpairs H); clear IHpairs.
  use (typ_subst_decr T S (fst a) H).
  use (typ_subst_decr T S (snd a) H).
  omega.
Qed.

Lemma size_pairs_decr : forall v T S pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  size_pairs (compose (v ~ T) S) pairs < size_pairs S ((typ_fvar v,T)::pairs).
Proof.
  intros.
  unfold size_pairs.
  use (cardinal_decr T S pairs H H0).
  set (S.cardinal (all_fv (compose (v ~ T) S) pairs)) in *.
  set (S.cardinal (all_fv S ((typ_fvar v, T) :: pairs))) in *.
  clearbody n n0.
  destruct n0; try omega.
  simpl.
  apply pow2exp_lt_le; try omega.
  use (typ_subst_decr_all T S pairs H).
  assert (typ_size T < all_size S ((typ_fvar v, T) :: pairs)).
    unfold all_size; simpl.
    rewrite* get_notin_dom.
    rewrite (typ_subst_fresh S T); try disjoint_solve.
    simpl; omega.
  assert (all_size S pairs < all_size S ((typ_fvar v, T) :: pairs)).
    unfold all_size; simpl.
    rewrite* get_notin_dom.
    simpl; omega.
  eapply le_lt_trans. apply H2.
  rewrite mult_comm.
  eapply le_lt_trans; try (eapply mult_lt_compat_r; try apply H4).
    apply mult_le_compat_l. omega.
  destruct T; simpl; omega.
Qed.

Lemma size_pairs_comm : forall S T1 T2 pairs,
  size_pairs S ((T1,T2)::pairs) = size_pairs S ((T2,T1)::pairs).
Proof.
  intros; unfold size_pairs, all_size, all_fv; simpl.
  repeat rewrite union_assoc.
  rewrite (@union_comm (typ_fv (typ_subst S T2))).
  repeat rewrite plus_assoc.
  rewrite* (@plus_comm (typ_size (typ_subst S T2))).
Qed.

Lemma size_pairs_decr' : forall S0 t t0 pairs h v,
  is_subst S0 ->
  S.mem v (typ_fv (typ_subst S0 t0)) = false ->
  size_pairs S0 ((t, t0) :: pairs) < S h ->
  typ_subst S0 t = typ_fvar v ->
  size_pairs (add_binding v (typ_subst S0 t0) S0) pairs < h.
Proof.
  intros.
  use (typ_subst_res_fresh _ H H2).
  use (typ_subst_disjoint t0 H).
  eapply lt_le_trans.
    apply* size_pairs_decr.
    assert (disjoint {{v}} (typ_fv (typ_subst S0 t0))).
      intro v0. destruct* (v0 == v).
      subst.
      right; intro.
      rewrite (S.mem_1 H5) in H0. discriminate.
    disjoint_solve.
  replace (size_pairs S0 ((typ_fvar v, typ_subst S0 t0) :: pairs))
    with (size_pairs S0 ((t, t0) :: pairs)).
    omega.
  unfold size_pairs, all_size, all_fv; simpl.
  rewrite* get_notin_dom.
  rewrite H2.
  rewrite* typ_subst_idem.
Qed.

Lemma typ_subst_eq_add : forall S S0 v T T1 T2 pairs,
  (forall T1 T2 : typ,
    In (T1, T2) pairs ->
    typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
  v # S0 ->
  typ_subst S (typ_fvar v) = typ_subst S T ->
  In (T1, T2) pairs -> 
  typ_subst S (typ_subst (compose (v ~ T) S0) T1) =
  typ_subst S (typ_subst (compose (v ~ T) S0) T2).
Proof.
  intros.
  repeat rewrite* typ_subst_add_binding.
  assert (forall T',
            typ_subst S (typ_subst (v ~ T) T') = typ_subst S T').
    clear -H1; induction T'; simpl; try congruence.
    destruct* (v0 == v).
    subst. apply (sym_eq H1).
  repeat rewrite* H3.
Qed.

Lemma typ_subst_no_cycle : forall v S T,
  v \in typ_fv T ->
  1 < typ_size T ->
  typ_size (typ_subst S (typ_fvar v)) < typ_size (typ_subst S T).
Proof.
  induction T; intros. elim (in_empty H).
    simpl in H0. omega.
  simpl in H.
  clear H0.
  assert (forall T, v \in typ_fv T -> T = T1 \/ T = T2 ->
             typ_size (typ_subst S (typ_fvar v)) <
             typ_size (typ_subst S (typ_arrow  T1 T2))).
    intros.
    case_eq (typ_size T); intros. destruct T; discriminate.
    destruct n. destruct T. elim (in_empty H0).
        rewrite (S.singleton_1 H0) in H1.
        destruct H1; subst; simpl; omega.
      destruct T3; simpl in H2; omega.
    assert (typ_size (typ_subst S (typ_fvar v)) < typ_size (typ_subst S T)).
      assert (1 < typ_size T) by omega.
      destruct H1; subst*.
    destruct H1; subst; simpl in *; omega.
  destruct (S.union_1 H); apply* (H0 _ H1).
Qed.

Lemma unify_complete_step : forall pairs S0 S v T h t t0,
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  size_pairs S0 ((t,t0)::pairs) < Datatypes.S h ->
  is_subst S0 ->
  (forall S0, is_subst S0 ->
    size_pairs S0 pairs < h ->
    (forall T1 T2 : typ,
      In (T1, T2) pairs ->
      typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
    exists S' : Env.env typ, unify pairs S0 h = Some S') ->
  (forall T1 T2 : typ,
    In (T1, T2) ((t, t0) :: pairs) ->
    typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
  T <> typ_fvar v ->
  S.mem v (typ_fv T) = false /\
  exists S', unify pairs (compose (v ~ T) S0) h = Some S'.
Proof.
  intros until t0; intros R1 R2 Hsz HS0 IHh Heq HT.
  case_eq (S.mem v (typ_fv T)); intros.
    elimtype False.
    use (S.mem_2 H).
    assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
    use (Heq _ _ H1); clear H1.
    rewrite R1 in H2; rewrite R2 in H2.
    clear -H0 H2 HT.
    destruct T. elim (in_empty H0).
      elim HT; rewrite* (S.singleton_1 H0).
    assert (1 < typ_size (typ_arrow T1 T2)).
      destruct T1; simpl; omega.
    use (typ_subst_no_cycle S _ H0 H).
    rewrite H2 in H1; omega.
  split*.
  rewrite <- R2 in H.
  use (size_pairs_decr' _ _ _ HS0 H Hsz R1).
  rewrite R2 in H0; simpl in H0.
  use (typ_subst_res_fresh _ HS0 R1).
  destruct* (IHh (compose (v ~ T) S0)); clear IHh.
    apply* add_binding_is_subst.
    use (typ_subst_disjoint t0 HS0).
    rewrite R2 in *; simpl in *.
    assert (disjoint {{v}} (typ_fv T)).
      intro x; destruct (x == v); subst; auto.
    disjoint_solve.
  clear HT H H0.
  intros.
  apply* typ_subst_eq_add.
  rewrite <- R1. rewrite <- R2.
  apply* Heq.
Qed.

Lemma unify_complete0 : forall h pairs S0 S,
  is_subst S0 ->
  (forall T1 T2, In (T1, T2) pairs ->
    typ_subst S (typ_subst S0 T1) = typ_subst S (typ_subst S0 T2)) ->
  size_pairs S0 pairs < h ->
  exists S', unify pairs S0 h = Some S'.
Proof.
  induction h.
    intros; elimtype False; omega.
  destruct pairs; introv HS0 Heq Hsz.
    exists S0; intuition.
  destruct p.
  simpl unify.
  case_eq (typ_subst S0 t); introv R1; case_eq (typ_subst S0 t0); introv R2.
          destruct (n === n0).
           subst.
           destruct* (IHh pairs _ S HS0).
           use (size_pairs_grows S0 (t,t0) pairs). omega.
          assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
          use (Heq _ _ H).
          rewrite R1 in H0; rewrite R2 in H0.
          simpl in H0. inversions* H0.
         rewrite size_pairs_comm in Hsz.
         destruct* (unify_complete_step S R2 R1 Hsz).
           simpl; intros. destruct H; subst.
             inversions H; symmetry; apply* Heq.
           apply* Heq.
          intro; discriminate. 
         rewrite* H.
        assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
        use (Heq _ _ H).
        rewrite R1 in H0; rewrite R2 in H0. discriminate.
       destruct* (unify_complete_step S R1 R2 Hsz).
        intro; discriminate.
       rewrite* H.
      destruct (v == v0).
       subst.
       destruct* (IHh pairs _ S HS0).
       use (size_pairs_grows S0 (t,t0) pairs). omega.
      destruct* (unify_complete_step S R1 R2 Hsz).
      intro; elim n. inversions* H.
     destruct* (unify_complete_step S R1 R2 Hsz).
      intro; discriminate.
     rewrite* H.
    assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
    use (Heq _ _ H); clear H.
    rewrite R1 in H0; rewrite R2 in H0.
    discriminate.
   rewrite size_pairs_comm in Hsz.
   destruct* (unify_complete_step S R2 R1 Hsz).
     simpl; intros. destruct H; subst.
       inversions H; symmetry; apply* Heq.
     apply* Heq.
    intro; discriminate.
   rewrite* H.
  destruct* (IHh ((t1,t3)::(t2,t4)::pairs) S0 S); clear IHh.
    clear Hsz; intros.
    assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
    use (Heq _ _ H0).
    rewrite <- (typ_subst_idem t HS0) in H1.
    rewrite <- (typ_subst_idem t0 HS0) in H1.
    rewrite R1 in H1; rewrite R2 in H1.
    simpl in H1; inversions H1; clear H1.
    simpl in H; destruct H.
      inversions* H.
    simpl in H; destruct H.
      inversions* H.
    apply* Heq.
  assert (size_pairs S0 ((t1, t3) :: (t2, t4) :: pairs) <
          size_pairs S0 ((t, t0) :: pairs)).
    unfold size_pairs, all_size, all_fv.
    simpl.
    rewrite <- (typ_subst_idem t HS0).
    rewrite <- (typ_subst_idem t0 HS0).
    rewrite R1; rewrite R2; simpl.
    apply pow2exp_lt_le.
      omega.
    rewrite (union_assoc (typ_fv (typ_subst S0 t3))).
    rewrite (union_comm (typ_fv (typ_subst S0 t3))).
    repeat rewrite union_assoc.
    omega.
  omega.
Qed.

Theorem unify_complete : forall T1 T2 S,
  typ_subst S T1 = typ_subst S T2 ->
  exists S',
    unify ((T1,T2)::nil) id (1 + size_pairs id ((T1,T2)::nil)) = Some S'.
Proof.
  intros.
  apply* unify_complete0.
    apply is_subst_id.
  intros. rewrite (typ_subst_id T0). rewrite (typ_subst_id T3).
  simpl in H0; destruct* H0.
  inversions* H0.
Qed.

End MkInfer.