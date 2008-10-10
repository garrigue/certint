(***************************************************************************
* Principality of unification for mini-ML with structural polymorphism     *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure Cardinal.
Require Import ML_SP_Soundness.

Set Implicit Arguments.

Hint Resolve in_or_app.

Lemma mem_3 : forall v L, S.mem v L = false -> v \notin L.
Proof.
  intros. intro.
  rewrite (S.mem_1 H0) in H.
  discriminate.
Qed.

Hint Resolve mem_3.

Lemma remove_4 : forall y x L, y \in S.remove x L -> ~ E.eq x y.
Proof.
  intros; intro.
  elim (S.remove_1 H0 H).
Qed.

Ltac sets_simpl_hyps x :=
  match goal with
  | H: _ \in {} |- _ => elim (in_empty H)
  | H: _ \in {{?y}} |- _ =>
    puts (proj1 (in_singleton _ _) H); clear H; subst y; try sets_simpl_hyps
  | H: x \in S.diff _ _ |- _ =>
    let H1 := fresh "Hin" in let H2 := fresh "Hn" in
    poses H1 (S.diff_1 H); poses H2 (S.diff_2 H); clear H; try sets_simpl_hyps
  | H: x \in S.inter _ _ |- _ =>
    let H1 := fresh "Hin" in let H2 := fresh "Hin" in
    poses H1 (S.inter_1 H); poses H2 (S.inter_2 H); clear H; try sets_simpl_hyps
  | H: S.mem x _ = false |- _ =>
    let H1 := fresh "Hn" in
    poses H1 (mem_3 H); clear H; try sets_simpl_hyps
  | H: x \in S.remove _ _ |- _ =>
    let H1 := fresh "Hin" in let H2 := fresh "Hn" in
    poses H1 (S.remove_3 H); poses H2 (remove_4 H); clear H; try sets_simpl_hyps
  end.

Ltac sets_simpl :=
  match goal with |- ?x \in _ => try sets_simpl_hyps x end.

Ltac union_solve' x :=
  try sets_simpl_hyps x;
  try match goal with
  | H: x \in _ \u _ |- _ =>
    destruct (S.union_1 H); clear H; union_solve' x
  | H: ?L1 << ?L2 |- _ =>
    match goal with
    | H': x \in ?L1 |- _ =>
      let H1 := fresh "Hin" in poses H1 (H _ H'); clear H; union_solve' x
    end
  end.

Ltac find_in_goal L :=
  match goal with |- ?x \in ?E =>
    match E with context[L] =>
      match goal with
      | |- x \in L => assumption
      | |- _ \in ?L1 \u ?L2 =>
        try (apply S.union_2; find_in_goal L);
          apply S.union_3; find_in_goal L
      | |- _ \in S.diff ?L1 ?L2 =>
        apply S.diff_3; [find_in_goal L | notin_solve]
      | |- _ \in S.remove ?y ?L1 =>
        let H1 := fresh "HE" in
        apply S.remove_2;
        [try assumption; intro HE; rewrite HE in *; solve [auto]
        | find_in_goal L]
      end
    end
  end.


Ltac find_in_solve x :=
  match goal with
  | |- ?y \in _ => puts (S.singleton_2 (refl_equal y)); find_in_goal {{y}}
  | H: x \in ?L |- _ => find_in_goal L
  end.

Ltac sets_solve :=
  match goal with
  | |- ?x \in _ => try union_solve' x; try find_in_solve x
  | |- _ << _ =>
    let y := fresh "y" in let Hy := fresh "Hy" in
    intros y Hy; sets_solve
  end.

Lemma test_remove : forall x L1 L2,
  S.remove x (L1 \u L2) << S.remove x (L2 \u L1).
Proof.
  intros; sets_solve.
Qed.

Hint Extern 1 (_ \in _) => solve [sets_solve].
Hint Extern 1 (_ << _) => solve [sets_solve].

Module MkUnify(Cstr:CstrIntf)(Const:CstIntf).

Module Sound := MkSound(Cstr)(Const).
Import Sound.
Import Infra.
Import Defs.

Module Type Cstr2I.
  Parameter unique : Cstr.cstr -> list var.
  Parameter unique_ok : forall c l, In l (unique c) <-> Cstr.unique c l.
  Parameter lub : Cstr.cstr -> Cstr.cstr -> Cstr.cstr.
  Parameter lub_ok : forall c1 c2 c,
    (Cstr.entails c c1 /\ Cstr.entails c c2) <-> Cstr.entails c (lub c1 c2).
  Parameter valid : forall c, sumbool (Cstr.valid c) (~Cstr.valid c).
  Parameter entails_unique : forall c1 c2 v,
    Cstr.entails c1 c2 -> Cstr.unique c2 v -> Cstr.unique c1 v.
  Parameter entails_valid : forall c1 c2,
    Cstr.entails c1 c2 -> Cstr.valid c1 -> Cstr.valid c2.
End Cstr2I.

Module Mk2(Cstr2:Cstr2I).

Definition compose S1 S2 : subs := S1 & map (typ_subst S1) S2.

Definition extends S S0 :=
  forall T, typ_subst S (typ_subst S0 T) = typ_subst S T.

Definition unifies S pairs :=
  forall T1 T2, In (T1, T2) pairs -> typ_subst S T1 = typ_subst S T2.

Definition is_subst S := env_prop (fun T => disjoint (dom S) (typ_fv T)) S.

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

Ltac case_rewrite t H :=
  case_eq t; introv H; rewrite H in *; try discriminate.

Lemma get_none_notin_list : forall (A:Set) x (a:A) E,
  get x E = None -> ~In (x,a) E.
Proof.
  induction E; simpl; intros. auto.
  destruct a0. destruct (x == v). discriminate.
  intro. destruct H0. inversions H0. elim n; auto.
  intuition.
Qed.

Lemma unify_coherent : forall kc kr,
  coherent kc (fst (unify_kind_rel kr nil (Cstr2.unique kc) nil)).
Proof.
  intros until kr.
  set (kr' := @nil (var*typ)).
  set (pairs' := @nil (typ*typ)).
  assert (coherent kc kr'). intro; intros. elim H0.
  gen kr' pairs'.
  induction kr; simpl; intros. auto.
  destruct a.
  destruct (In_dec eq_var_dec v (Cstr2.unique kc)).
    case_eq (get v kr'); intros. apply* IHkr.
    apply IHkr.
    rename H0 into R1.
    intro; intros.
    simpl in *; destruct H1; [inversions H1|]; destruct H2. inversions* H2.
        elim (get_none_notin_list _ _ _ R1 H2).
      inversions* H2; elim (get_none_notin_list _ _ _ R1 H1).
    apply* (H x).
  apply IHkr.
  intro; intros.
  destruct (x == v).
    subst. elim (n (proj2 (Cstr2.unique_ok _ _) H0)).
  apply* (H x). destruct* H1. inversions* H1.
  destruct* H2. inversions* H2.
Qed.

Definition unify_kinds (k1 k2:kind) : option (kind * list (typ*typ)).
  intros.
  refine (
  match k1, k2 with
  | None, _ => Some (k2, nil)
  | Some _, None => Some (k1, nil)
  | Some (Kind kc1 kv1 kr1 kh1), Some (Kind kc2 kv2 kr2 kh2) =>
    let kc := Cstr2.lub kc1 kc2 in
    if Cstr2.valid kc then
      let krp := unify_kind_rel (kr1 ++ kr2) nil (Cstr2.unique kc) nil in
      Some (Some (@Kind kc _ (fst krp) _), snd krp)
    else None
  end).
    auto.
  unfold krp; apply unify_coherent.
Defined.

Definition get_kind x E : kind :=
  match get x E with
  | Some k  => k
  | None => None
  end.

Lemma binds_get_kind : forall x k K,
  binds x k K -> get_kind x K = k.
Proof.
  intros.
  unfold get_kind. rewrite* H.
Qed.

Lemma get_kind_binds : forall x k K,
  get_kind x K = Some k -> binds x (Some k) K.
Proof.
  unfold get_kind; intros.
  case_rewrite (get x K) R.
  subst*.
Qed.

Definition unify_vars (K:kenv) (x y:var) :=
  match unify_kinds (get_kind x K) (get_kind y K) with
  | Some (k, pairs) => Some (remove_env (remove_env K x) y & y ~ k, pairs)
  | None => None
  end.

Definition unify_nv (unify : kenv -> subs -> option (kenv * subs)) K S x T :=
  if S.mem x (typ_fv T) then None else
    match get_kind x K with
    | Some _ => None
    | None => unify (remove_env K x) (compose (x ~ T) S)
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
        match unify_vars K x y with
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

Lemma notin_disjoint : forall x L, x \notin L -> disjoint {{x}} L.
Proof.
  intros; intro v. destruct (x == v); try subst; auto.
Qed.

Hint Resolve notin_disjoint.

Lemma notin_disjoint_r : forall x L, x \notin L -> disjoint L {{x}}.
Proof.
  intros; apply* disjoint_comm.
Qed.

Hint Resolve notin_disjoint_r.

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
  typ_subst (compose S1 S2) T = typ_subst S1 (typ_subst S2 T).
Proof.
  induction T; simpl; intros; auto.
    unfold compose.
    simpl; case_eq (get v S2); intros.
      rewrite* (binds_prepend S1 (binds_map (typ_subst S1) H)).
    simpl.
    case_eq (get v S1); intros.
      rewrite* (binds_concat_fresh (map (typ_subst S1) S2) H0).
      rewrite dom_map. apply* get_none_notin.
    case_eq (get v (S1 & map (typ_subst S1) S2)); intros; auto.
    destruct (binds_concat_inv H1).
      destruct H2. rewrite H3 in H0. discriminate.
    destruct (binds_map_inv _ _ H2).
    rewrite (proj2 H3) in H; discriminate.
  rewrite* IHT1.
  rewrite* IHT2.
Qed.

Lemma binds_typ_subst : forall x T S,
  binds x T S -> typ_subst S (typ_fvar x) = T.
Proof.
  intros. simpl. rewrite* H.
Qed.

Lemma disjoint_subst : forall x T L T',
  disjoint ({{x}} \u L) (typ_fv T) ->
  disjoint L (typ_fv T') ->
  disjoint ({{x}} \u L) (typ_fv (typ_subst (x ~ T) T')).
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
  disjoint (dom S) (typ_fv T) ->
  x \notin (typ_fv T) ->
  is_subst (compose (x ~ T) S).
Proof.
  intros.
  unfold compose.
  intro; intros.
  binds_cases H2.
    destruct (binds_single_inv B); subst.
    disjoint_solve.
    destruct* (v == x0).
  destruct (binds_map_inv _ _ B0) as [b [F B']].
  subst.
  use (H _ _ B').
  simpl in *.
  apply* disjoint_subst.
  intro y; destruct* (H0 y). destruct* (y == x).
Qed.

Hint Resolve add_binding_is_subst.

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

Lemma typ_subst_res_fresh : forall S T T',
  is_subst S -> typ_subst S T = T' -> disjoint (dom S) (typ_fv T').
Proof.
  intros.
  use (typ_subst_disjoint T H).
  rewrite* <- H0.
Qed.

Lemma typ_subst_res_fresh' : forall S T v,
  is_subst S -> typ_subst S T = typ_fvar v -> v # S.
Proof.
  intros.
  use (typ_subst_res_fresh _ H H0).
Qed.

Hint Resolve typ_subst_disjoint typ_subst_res_fresh typ_subst_res_fresh'.

Lemma binds_add_binding : forall S T0 T1 v x T,
  typ_subst S T0 = typ_fvar v ->
  binds x (typ_subst S T) S ->
  binds x (typ_subst (compose (v ~ T1) S) T) (compose (v ~ T1) S).
Proof.
  intros.
  rewrite typ_subst_compose.
  unfold compose.
  apply binds_prepend.
  apply* binds_map.
Qed.

Hint Resolve binds_add_binding.

Lemma neq_notin_fv : forall v v0,
  v <> v0 -> v \notin (typ_fv (typ_fvar v0)).
Proof. simpl*. Qed.

Hint Resolve neq_notin_fv.

Lemma ok_map0 : forall (A:Set) (f:A->A) E,
  ok E -> ok (map f E).
Proof.
  intros.
  rewrite (app_nil_end (map f E)).
  fold (nil & map f E).
  apply ok_map.
  unfold concat; rewrite* <- (app_nil_end E).
Qed.

Hint Resolve ok_map0.

Hint Unfold extends.

Lemma notin_remove_self : forall v L, v \notin S.remove v L.
Proof.
  intros. apply S.remove_1. reflexivity.
Qed.

Lemma notin_remove : forall x v L,
  v \notin L -> v \notin S.remove x L.
Proof.
  intros; intro.
  elim H; apply* S.remove_3.
Qed.

Hint Resolve notin_remove_self notin_remove.

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
  ok K -> dom (remove_env K v) = S.remove v (dom K).
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

Lemma disjoint_add_binding : forall v T S (K:kenv),
  is_subst S -> ok K ->
  disjoint (dom S) (dom K) ->
  disjoint (dom (compose (v ~ T) S)) (dom (remove_env K v)).
Proof.
  intros.
  rewrite* dom_remove_env.
  unfold compose.
  rewrite dom_concat.
  simpl; rewrite dom_map.
  intro x; destruct (v == x). subst*.
  destruct* (H1 x).
Qed.

Hint Resolve disjoint_add_binding.

Definition kind_entails k k' :=
  match k' with
  | None => True
  | Some c' => match k with
               | Some c => entails c c'
               | None => False
               end
  end.

Lemma kind_entails_well_kinded : forall k k' K T,
  kind_entails k k' ->
  well_kinded K k T ->
  well_kinded K k' T.
Proof.
  unfold kind_entails; intros.
  inversions H0; clear H0; destruct* k'; try apply wk_any.
  apply* wk_kind. apply* entails_trans.
Qed.

Hint Resolve kind_entails_well_kinded.

Section Soundness.

Variables (K':kenv) (S':subs).

Lemma unify_ind : forall (P : kenv -> subs -> list (typ * typ) -> Prop),
  (is_subst S' -> P K' S' nil) ->
  (forall h pairs K T S v t t0,
    let S1 := compose (v ~ T) S in
    let K1 := remove_env K v in
    unify h pairs K1 S1 = Some (K', S') ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = T ->
    is_subst S -> is_subst S1 ->
    v \notin typ_fv T -> get_kind v K = None ->
    P K1 S1 pairs -> P K S ((t,t0)::pairs)) ->
  (forall h pairs K S v v0 k l t t0,
    let S1 := compose (v ~ typ_fvar v0) S in
    let K1 := remove_env (remove_env K v) v0 & v0 ~ k in
    unify_kinds (get_kind v K) (get_kind v0 K) = Some (k, l) ->
    unify h (l ++ pairs) K1 S1 = Some (K', S') ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = typ_fvar v0 ->
    is_subst S -> is_subst S1 ->
    v <> v0 ->
    P K1 S1 (l ++ pairs) -> P K S ((t,t0)::pairs)) ->
  (forall h K S t t0 pairs n,
    unify h pairs K S = Some (K', S') -> is_subst S ->
    typ_subst S t = typ_bvar n ->
    typ_subst S t0 = typ_bvar n ->
    P K S pairs -> P K S ((t,t0)::pairs)) ->
  (forall h K S t t0 pairs v,
    unify h pairs K S = Some (K', S') -> is_subst S ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = typ_fvar v ->
    P K S pairs -> P K S ((t,t0)::pairs)) ->
  (forall h K S t t0 pairs t1 t2 t3 t4,
    unify h ((t1,t3)::(t2,t4)::pairs) K S = Some (K',S') -> is_subst S ->
    typ_subst S t = typ_arrow t1 t2 ->
    typ_subst S t0 = typ_arrow t3 t4 ->
    P K S ((t1,t3)::(t2,t4)::pairs) -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs,
    P K S ((t,t0)::pairs) -> P K S ((t0,t)::pairs)) ->
  forall h pairs K S,
    unify h pairs K S = Some (K', S') ->
    is_subst S ->
    P K S pairs.
Proof.
  introv Hnil Hnv Hvars Hbv Hfv. intros Harr Hsw.
  induction h; simpl; intros pairs K S HU HS.
    discriminate.
  destruct pairs.
    inversions HU.
    auto.
  destruct p.
  assert (Hnv1: forall v T t t0,
    typ_subst S t = typ_fvar v -> typ_subst S t0 = T ->
    unify_nv (unify h pairs) K S v T = Some (K',S') -> P K S ((t,t0)::pairs)).
    unfold unify_nv; simpl. introv R1 R2 H'.
    case_rewrite (S.mem v (typ_fv T)) R3.
    fold kind in *.
    case_rewrite (get_kind v K) R4.
    apply* Hnv.
  case_rewrite (typ_subst S t) R1; case_rewrite (typ_subst S t0) R2.
        destruct (n === n0).
          subst n0.
          auto*.
        discriminate.
       rewrite <- R1 in HU.
       apply Hsw.
       apply* Hnv1.
      rewrite <- R2 in HU.
      apply* Hnv1.
     destruct (v == v0).
       subst v0. auto*.
     unfold unify_vars in HU.
     case_rewrite (unify_kinds (get_kind v K) (get_kind v0 K)) R3.
     destruct p.
     apply* Hvars.
    rewrite <- R2 in HU.
    apply* Hnv1.
   rewrite <- R1 in HU.
   apply Hsw.
   apply* Hnv1.
  apply* Harr.
Qed.

Lemma unify_keep : forall h pairs K S,
  unify h pairs K S = Some (K', S') ->
  is_subst S ->
  is_subst S' /\
  forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'.
Proof.
  intros.
  apply* (unify_ind
    (fun K S _ => is_subst S' /\
      forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'));
    clear H H0 h pairs K S; intros.
    destruct H6; split*.
    intros. apply H7.
    unfold S1. apply* binds_add_binding.
  intros.
  intuition.
  apply H8; unfold S1. apply* binds_add_binding.
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

Lemma typ_subst_extend : forall h pairs K S,
  is_subst S ->
  unify h pairs K S = Some (K', S') ->
  extends S' S.
Proof.
  intros.
  destruct* (unify_keep _ _ _ H0).
  clear H0.
  intro.
  induction T. simpl*.
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

Hint Resolve typ_subst_extend.

Theorem unify_types : forall h pairs K S,
  unify h pairs K S = Some (K',S') ->
  is_subst S ->
  unifies S' pairs.
Proof.
  intros.
  apply* (unify_ind (fun _ _ => unifies S')); clear H H0 h K S pairs; intros;
    intro; simpl; intros; intuition;
    try (unfold S1 in *; inversions H8; clear H8);
    try (inversions H5; clear H5; rewrite <- (typ_subst_extend _ _ _ H0 H);
         rewrite <- (typ_subst_extend _ _ _ H0 H T2); congruence).
        rewrite <- (typ_subst_extend _ _ _ H3 H).
        rewrite <- (typ_subst_extend _ _ _ H3 H T2).
        rewrite typ_subst_compose. rewrite H0.
        simpl. destruct* (v == v).
        rewrite typ_subst_compose.
        rewrite* (typ_subst_fresh (v ~ typ_subst S T2)).
        simpl. intro x; destruct* (x == v).
      rewrite <- (typ_subst_extend _ _ _ H4 H0).
      rewrite <- (typ_subst_extend _ _ _ H4 H0 T2).
      do 2 rewrite typ_subst_compose. rewrite H1; rewrite H2.
      simpl. destruct* (v == v). destruct* (v0 == v).
    inversions H5; clear H5.
    rewrite <- (typ_subst_extend _ _ _ H0 H).
    rewrite <- (typ_subst_extend _ _ _ H0 H T2).
    rewrite H2; rewrite H1.
    simpl.
    rewrite* (H3 t1 t3).
    rewrite* (H3 t2 t4).
  inversions H1.
  symmetry.
  apply* H.
Qed.

Lemma kind_subst_idem : forall S k,
  is_subst S -> kind_subst S (kind_subst S k) = kind_subst S k.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|].
    simpl.
    apply* kind_pi; simpl.
    clear kh; induction kr; simpl. auto.
    rewrite IHkr.
    rewrite* typ_subst_idem.
  auto.
Qed.

Lemma kind_subst_combine : forall S S1 S2 k,
  (forall T, typ_subst S1 (typ_subst S2 T) = typ_subst S T) ->
  kind_subst S1 (kind_subst S2 k) = kind_subst S k.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|].
    simpl; apply* kind_pi; simpl.
    clear kv kh.
    induction kr. auto.
    simpl. rewrite IHkr. rewrite* H.
  auto.
Qed.

Lemma binds_orig_remove_env : forall (A:Set) v x (k:A) E,
  ok E -> binds x k (remove_env E v) -> binds x k E.
Proof.
  unfold binds.
  induction E; simpl; intros. auto.
  destruct a.
  inversions H.
  destruct (v == v0); simpl in H0.
    subst.
    destruct* (x == v0).
    subst. elim (binds_fresh H0 H5).
  destruct* (x == v0).
Qed.

Lemma get_kind_subst : forall S x K,
  get_kind x (map (kind_subst S) K) = kind_subst S (get_kind x K).
Proof.
  unfold get_kind; intros.
  case_eq (get x K); introv R1.
    rewrite* (binds_map (kind_subst S) R1).
  rewrite* (map_get_none (kind_subst S) _ _ R1).
Qed.

Lemma binds_in : forall (A:Set) x (a:A) E,
  binds x a E -> In (x, a) E.
Proof.
  unfold binds; induction E; intros. elim (binds_empty H).
  destruct a0; simpl in *.
  destruct* (x == v). inversions* H.
Qed.

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

Lemma unify_kind_rel_incl : forall kr pairs un S kr0 kr' pairs',
  unify_kind_rel kr0 kr' un pairs' = (kr, pairs) ->
  unifies S pairs ->
  incl (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT))) kr0)
    (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT))) kr).
Proof.
  induction kr0; intros; intros T HT. elim HT.
  destruct T.
  destruct a.
  simpl in *.
  destruct (In_dec eq_var_dec v0 un);
    try case_rewrite (get v0 kr') R1; simpl in HT; destruct HT;
      try solve [apply* (IHkr0 _ _ H)]; inversions H1; clear H1;
        destruct (unify_kind_rel_keep _ _ _ _ H).
      use (H1 _ (binds_in R1)); clear H1.
      assert (In (t0,t1) pairs) by auto.
      use (H0 _ _ H1).
      rewrite H4.
      refine (in_map _ _ _ H3).
    assert (In (v,t0) kr) by auto.
    refine (in_map _ _ _ H3).
  assert (In (v,t0) kr) by auto.
  refine (in_map _ _ _ H3).
Qed.

Lemma unify_kinds_sound : forall k k0 k1 l S,
  unify_kinds k k0 = Some (k1, l) ->
  unifies S l ->
  kind_entails (kind_subst S k1) (kind_subst S k) /\
  kind_entails (kind_subst S k1) (kind_subst S k0).
Proof.
  unfold unify_kinds, kind_entails.
  intros.
  destruct k as [[kc kv kr kh]|]; destruct k0 as [[kc0 kv0 kr0 kh0]|]; simpl.
     destruct (Cstr2.valid (Cstr2.lub kc kc0)); try discriminate.
     case_eq (unify_kind_rel (kr ++ kr0) nil (Cstr2.unique (Cstr2.lub kc kc0))
       nil); intros l0 l1 R1.
     inversions H; clear H.
     rewrite R1 in *.
     use (unify_kind_rel_incl _ _ _ _ R1 H0).
     destruct (proj2 (Cstr2.lub_ok kc kc0 _) (Cstr.entails_refl _)).
     split; split*; simpl; intros;
       rewrite R1; apply H; rewrite* map_app.
    split*.
    inversions H; clear H.
    simpl. apply entails_refl.
   split*.
   inversions H; clear H.
   simpl. apply entails_refl.
  auto.
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
  destruct* (x == v); simpl; intros y Hy; auto.
Qed.

Lemma map_snd_env_map : forall (A:Set) (f:A->A) l,
  List.map (fun X:var*A => (fst X, f (snd X))) l = Env.map f l.
Proof.
  induction l; simpl*.
  destruct a. rewrite* IHl.
Qed.

Lemma unify_kinds_subst : forall k1 k2 k3 l S,
  unify_kinds k1 k2 = Some (k3, l) ->
  unify_kinds (kind_subst S k1) (kind_subst S k2) =
  Some (kind_subst S k3,
        List.map (fun T => (typ_subst S (fst T), typ_subst S (snd T))) l).
Proof.
  intros.
  destruct k1 as [[kc1 kv1 kr1 kh1]|]; destruct k2 as [[kc2 kv2 kr2 kh2]|];
    simpl in *; try solve [inversions* H].
  case_rewrite (Cstr2.valid (Cstr2.lub kc1 kc2)) R1.
  inversions H; clear H.
  rewrite <- map_app.
  simpl.
  refine (f_equal (@Some _) _).
  set (kr:=@nil(var*typ)).
  set (pairs:=@nil(typ*typ)).
  assert (kr = List.map (fun T:var*typ => (fst T, typ_subst S (snd T))) kr)
    by reflexivity.
  assert (pairs =
    List.map (fun T => (typ_subst S (fst T), typ_subst S (snd T))) pairs)
    by reflexivity.
  clear kh1 kh2 R1.
  apply injective_projections; simpl; try apply kind_pi; simpl*;
    pattern kr at 1; rewrite H;
    pattern pairs at 1; rewrite H0; clear H H0;
    gen kr pairs; induction (kr1++kr2); intros; simpl*; destruct a;
    simpl; destruct (In_dec eq_var_dec v0 (Cstr2.unique (Cstr2.lub kc1 kc2)));
    try rewrite* <- IHl;
    case_eq (get v0 kr); intros; rewrite <- IHl;
    repeat rewrite map_snd_env_map;
    try rewrite* (binds_map (typ_subst S) H);
    rewrite* (map_get_none (typ_subst S) _ _ H).
Qed.

Lemma well_subst_unify : forall k1 l v v0 S K h pairs,
  unify h (l ++ pairs) (remove_env (remove_env K v) v0 & v0 ~ k1)
    (compose (v ~ typ_fvar v0) S) = Some (K', S') ->
  unify_kinds (get_kind v K) (get_kind v0 K) = Some (k1, l) ->
  is_subst (compose (v ~ typ_fvar v0) S) ->
  v # S ->
  well_subst (remove_env (remove_env K v) v0 & v0 ~ k1)
     (map (kind_subst S') K') S' ->
  well_subst K (map (kind_subst S') K') S'.
Proof.
  intros until 1; intros HU HS1 Hv WS x; intros.
  unfold well_subst in WS.
  poses Hext (typ_subst_extend _ _ _ HS1 H).
  poses Hunif (unify_types _ _ _ H HS1). 
  assert (Hunif': unifies S' l) by (intro; intros; auto).
  clear HS1 H.
  destruct (x == v0); subst.
    destruct* (unify_kinds_sound _ _ HU Hunif') as [_ Wk].
    rewrite* <- (binds_get_kind H0).
  destruct (x == v); subst.
    assert (well_kinded (map (kind_subst S') K') (kind_subst S' k1)
               (typ_subst S' (typ_fvar v))).
      rewrite <- Hext.
      rewrite* typ_subst_compose.
      rewrite (typ_subst_fresh S); simpl*.
      destruct* (v == v).
    destruct* (unify_kinds_sound _ _ HU Hunif') as [Wk _].
    rewrite* <- (binds_get_kind H0).
  assert (x # v0 ~ k1) by simpl*.
  use (binds_concat_fresh _ (binds_remove_env (binds_remove_env H0 n0) n) H).
Qed.

Lemma unify_kinds_ok : forall h pairs K S,
  unify h pairs K S = Some (K',S') -> is_subst S ->
  ok K -> disjoint (dom S) (dom K) ->
  ok K' /\ disjoint (dom S') (dom K') /\
  well_subst K (map (kind_subst S') K') S'.
Proof.
  introv H H0.
  apply* (unify_ind (fun K S pairs =>
    ok K -> disjoint (dom S) (dom K) ->
    ok K' /\ disjoint (dom S') (dom K') /\
    well_subst K (map (kind_subst S') K') S'));
    clear H H0 h pairs K S.
      intuition.
      intro; intros.
      rewrite* typ_subst_fresh.
        destruct* k.
        use (binds_map (kind_subst S') H2).
        simpl in *; apply* wk_kind. apply entails_refl.
      simpl; intro. destruct* (x == Z). subst.
      destruct* (H1 Z).
      elim (binds_fresh H2 H3).
    intros until 1.
    intros R1 R2 Hs HS1 n R3 IHh HK Dis.
    unfold S1, K1 in *; clear S1 K1.
    destruct* IHh.
    intuition.
    clear -R3 H3.
    intro; intros.
    destruct (Z == v).
      subst.
      rewrite (binds_get_kind H) in R3. subst*.
    use (H3 _ _ (binds_remove_env H n)).
  intros until K1.
  intros R3 H R1 R2 HS HS1 n IHh HK Dis.
  unfold S1, K1 in *; clear S1 K1.
  destruct* IHh.
      constructor. repeat apply ok_remove_env. auto.
      rewrite* dom_remove_env.
    simpl.
    repeat rewrite* dom_remove_env.
    unfold compose.
    rewrite dom_concat. rewrite dom_map. simpl.
    intro x; destruct* (x == v).
      subst; right.
      apply* notin_union_l.
    destruct* (x == v0).
      subst; left.
      use (typ_subst_res_fresh' _ HS R2).
    destruct* (Dis x).
    right; apply* notin_union_l.
  intuition.
  subst; apply* well_subst_unify.
  apply* typ_subst_res_fresh'.
Qed.

End Soundness.

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
      simpl*.
    simpl in *; destruct H0.
      subst. sets_solve. apply* H.
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

Section Mgu.

Variables (K':kenv) (S':subs) (HS' : is_subst S').

Definition mgu_spec K S K0 S0 pairs :=
  ok K0 ->
  extends S' S0 ->
  unifies S' pairs ->
  well_subst K0 K' S' ->
  extends S' S /\ well_subst K K' S'.

Lemma get_remove_env : forall (A:Set) v (E:Env.env A),
  ok E -> get v (remove_env E v) = None.
Proof.
  induction E; simpl; intros. auto.
  destruct a. destruct* (v == v0).
    subst v0; inversions H.
    case_eq (get v E); intros. elim (binds_fresh H0 H4). auto.
  simpl. destruct* (v == v0). inversions* H.
Qed.

Lemma kind_map2_eq : forall f1 f2 f3 f4 k,
  (forall T, f1 (f2 T) = f3 (f4 T)) ->
  kind_map f1 (kind_map f2 k) = kind_map f3 (kind_map f4 k).
Proof.
  intros.
  destruct k as [[kc kv kr kh]|]; simpl*.
  apply* kind_pi. simpl.
  clear kh; induction kr; simpl*.
  rewrite H; rewrite* IHkr.
Qed.

Lemma kind_subst_compose : forall S1 S2 k,
  kind_subst (compose S1 S2) k = kind_subst S1 (kind_subst S2 k).
Proof.
  intros; symmetry; apply kind_subst_combine.
  intro; symmetry; apply* typ_subst_compose.
Qed.

Lemma unify_mgu_nv : forall K0 S0 pairs K S h t t0 v T,
  let S1 := compose (v ~ T) S0 in
  let K1 := remove_env K0 v in
  unify h pairs K1 S1 = Some (K, S) ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  is_subst S0 ->
  get_kind v K0 = None ->
  mgu_spec K S K1 S1 pairs ->
  mgu_spec K S K0 S0 ((t, t0) :: pairs).
Proof.
  intros until K1; unfold K1, S1; clear K1 S1.
  intros HU R1 R2 HS0 R4 IHh HK0 Hext Heq WS.
  assert (BS': typ_subst S' T = typ_subst S' (typ_fvar v)).
    rewrite <- R2. rewrite Hext. rewrite* <- (Heq t t0).
    rewrite <- R1. rewrite* Hext.
  assert (Hv: v # S0) by apply* typ_subst_res_fresh'.
  assert (Dis: disjoint (dom (v ~ T)) (dom S0)).
    simpl. intro x; destruct* (x == v).
  assert (Sv: extends S' (v ~ T)).
    intro.
    induction T0; simpl. auto.
      destruct (v0 == v). subst. rewrite BS'. reflexivity.
      reflexivity.
    congruence.
  destruct* IHh.
      intro. rewrite* typ_subst_compose.
      rewrite Sv. apply Hext.
    intro; intros. apply* Heq.
  intro; intros.
  destruct (Z == v).
    subst.
    elim (binds_fresh H).
    fold S.elt in v.
    rewrite* dom_remove_env.
  apply WS.
  apply* binds_orig_remove_env.
Qed.

Lemma entails_unique' : forall c1 c2,
  Cstr.entails c1 c2 -> incl (Cstr2.unique c2) (Cstr2.unique c1).
Proof.
  intros. intros x Hx. refine (proj2 (Cstr2.unique_ok _ _) _).
  refine (Cstr2.entails_unique H _).
  apply (proj1 (Cstr2.unique_ok _ _) Hx).
Qed.

Lemma in_app_mid : forall (A:Set) (x a:A) l1 l2,
  In x (l1 ++ a :: l2) -> a = x \/ In x (l1 ++ l2).
Proof.
  intros.
  destruct* (in_app_or _ _ _ H).
  simpl in H0; destruct* H0.
Qed.

Lemma unify_kinds_complete : forall k k0 k' S,
  kind_entails k' (kind_subst S k) ->
  kind_entails k' (kind_subst S k0) ->
  exists k1, exists l,
    unify_kinds k k0 = Some (k1, l) /\
    unifies S l /\ kind_entails k' (kind_subst S k1).
Proof.
  unfold unify_kinds, unifies.
  intros.
  destruct k as [[kc kv kr kh]|]; destruct k0 as [[kc0 kv0 kr0 kh0]|];
    simpl in *;
    try solve [esplit; esplit; intuition; elim H1].
  destruct k' as [[kc' kv' kr' kh']|]; try contradiction.
  destruct H. destruct H0.
  simpl in H, H0.
  destruct (Cstr2.lub_ok kc kc0 kc').
  use (H3 (conj H H0)).
  use (Cstr2.entails_valid H5 kv').
  destruct* (Cstr2.valid (Cstr2.lub kc kc0)).
  esplit. esplit. split. reflexivity.
  poses Huniq (entails_unique' H5).
  clear H H0 H3 H4 H6.
  simpl in H1, H2. clear kv kv0 kh kh0.
  set (pairs := nil(A:=typ*typ)).
  set (krs := nil(A:=var*typ)).
  assert (forall T,
    In T (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT)))
      ((kr ++ kr0) ++ krs)) ->
    In T kr').
    intros.
    repeat rewrite map_app in H.
    destruct (in_app_or _ _ _ H).
      destruct* (in_app_or _ _ _ H0).
    elim H0.
  clear H1 H2.
  assert (Hunif: unifies S pairs) by (intros T1 T2 HE; elim HE).
  unfold kind_entails, entails; simpl.
  intros; gen pairs krs; induction (kr++kr0); simpl; intros. auto.
  destruct a.
  destruct (In_dec eq_var_dec v0 (Cstr2.unique (Cstr2.lub kc kc0))).
    use (Huniq _ i).
    case_eq (get v0 krs); [intros t0 R1|intros R1].
      assert (unifies S ((t,t0)::pairs)).
        intro; simpl; intros.
        destruct* H1.
        inversions H1; clear H1.
        apply* (kh' v0). apply* (proj1 (Cstr2.unique_ok _ _) H0).
        apply H.
        right.
        rewrite map_app.
        use (in_map (fun XT => (fst XT, typ_subst S (snd XT)))
                    _ _ (binds_in R1)).
      intuition.
        refine (proj1 (IHl _ _ _ _) _ _ H2); auto.
      refine (proj2 (proj2 (IHl _ _ _ _)) _ H2); auto.
    intuition;
      [ refine (proj1 (IHl _ _ _ _) _ _ H1)
      | refine (proj2 (proj2 (IHl _ _ _ _)) _ H1)];
      auto; simpl; intros;
      repeat rewrite map_app in *; apply H; apply* in_app_mid.
  intuition;
  [ refine (proj1 (IHl _ _ _ _) _ _ H0)
  | refine (proj2 (proj2 (IHl _ _ _ _)) _ H0)];
  auto; simpl; intros;
  repeat rewrite map_app in *; apply H; apply* in_app_mid.
Qed.

Lemma well_kinded_get_kind : forall K x,
  well_kinded K (get_kind x K) (typ_fvar x).
Proof.
  intros.
  case_eq (get_kind x K); intros.
    apply* wk_kind. apply* get_kind_binds.
    apply entails_refl.
  apply wk_any.
Qed.

Lemma well_subst_get_kind : forall K K' S x,
  well_subst K K' S ->
  well_kinded K' (kind_subst S (get_kind x K)) (typ_subst S (typ_fvar x)).
Proof.
  intros.
  case_eq (get_kind x K); intros.
    apply H. apply* get_kind_binds.
  apply wk_any.
Qed.

Lemma unify_mgu_vars : forall K0 S0 pairs K S h t t0 v v0 k l,
  let S1 := compose (v ~ typ_fvar v0) S0 in
  let K1 := remove_env (remove_env K0 v) v0 & v0 ~ k in
  unify_kinds (get_kind v K0) (get_kind v0 K0) = Some (k, l) ->
  unify h (l ++ pairs) K1 S1 = Some (K, S) ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = typ_fvar v0 ->
  is_subst S0 -> is_subst S1 -> v <> v0 ->
  mgu_spec K S K1 S1 (l ++ pairs) -> mgu_spec K S K0 S0 ((t, t0) :: pairs).
Proof.
  intros until K1; unfold S1; clear S1.
  intros R4 HU R1 R2 HS0 HS1 n IHh HK0 Hext Heq WS.
  assert (BS': typ_subst S' (typ_fvar v0) = typ_subst S' (typ_fvar v)).
    rewrite <- R1; rewrite <- R2.
    repeat rewrite Hext.
    symmetry; apply* Heq.
  assert (Hv: v # S0) by apply* typ_subst_res_fresh'.
  assert (Hv0: v0 # S0) by apply* typ_subst_res_fresh'.
  assert (Dis: disjoint (dom (v ~ typ_fvar v0)) (dom S0)).
    simpl. intro x; destruct* (x == v).
  assert (Sv: extends S' (v ~ typ_fvar v0)).
    intro. induction T; simpl. auto.
      destruct (v1 == v). subst. rewrite BS'. reflexivity.
      reflexivity.
    congruence.
  assert (HK1: ok K1).
    unfold K1.
    assert (ok (remove_env K0 v)) by auto.
    apply (@ok_push _ _ v0 k (ok_remove_env v0 H)).
    rewrite* dom_remove_env.
  poses Wk (well_subst_get_kind v WS).
  rewrite <- Sv in Wk.
  simpl typ_subst in Wk. destruct* (v == v). clear e.
  poses Wk0 (well_subst_get_kind v0 WS).
  assert (Hke: forall v1, typ_subst S' (typ_fvar v0) = typ_fvar v1 ->
               let k' := get_kind v1 K' in
               let gk x := kind_subst S' (get_kind x K0) in
               kind_entails k' (gk v) /\ kind_entails k' (gk v0)).
    intros.
    split; [inversions Wk | inversions Wk0]; simpl*; unfold k', gk;
      try (rewrite <- H2; simpl* );
      rewrite <- H0; simpl in H; rewrite H in H1; inversions H1;
      rewrite* (binds_get_kind H3).
  assert (Hk: k = None /\ l = nil \/
              exists v1, typ_subst S' (typ_fvar v0) = typ_fvar v1).
    case_rewrite (typ_subst S' (typ_fvar v0)) R5;
    case_rewrite (get_kind v0 K0) R6;
    simpl in Wk0 ; inversion_clear Wk0;
    case_rewrite (get_kind v K0) R7;
    simpl in Wk; inversion_clear Wk;
    simpl in R4; inversion* R4.
  destruct* IHh.
      intro.
      rewrite* typ_subst_compose.
      rewrite Sv. rewrite* Hext.
    intro; intros.
    destruct (in_app_or _ _ _ H); clear H; try solve [apply* Heq].
    destruct Hk as [[_ Hl]|[v1 R5]]. subst; elim H0.
    destruct* (Hke v1); clear Hke.
    destruct (unify_kinds_complete _ _ _ _ H H1) as [k3 [l3 [HU1 [HU2 HU3]]]].
    rewrite R4 in HU1.
    clearbody K1.
    inversions HU1; clear HU1.
    apply* HU2.
  intro; intros.
  destruct (Z == v0).
    subst.
    unfold binds in H; simpl in H; destruct* (v0 == v0).
    clearbody K1.
    inversions H; clear e H.
    destruct Hk as [[Hk _]|[v1 R5]]. subst*.
    rewrite R5.
    destruct* (Hke v1); clear Hke.
    destruct (unify_kinds_complete _ _ _ _ H H0) as [k3 [l3 [HU1 [HU2 HU3]]]].
    rewrite R4 in HU1.
    inversions HU1; clear HU1.
    apply* kind_entails_well_kinded.
    apply* well_kinded_get_kind.
  destruct* k0.
  unfold K1 in H.
  unfold binds in H; simpl in H. destruct* (Z == v0). clear n1.
  use (binds_orig_remove_env _ (ok_remove_env v HK0) H).
  use (binds_orig_remove_env _ HK0 H0).
Qed.

Lemma unifies_tl : forall S p pairs,
  unifies S (p::pairs) -> unifies S pairs.
Proof.
  intros; intro; intros; apply* H.
Qed.

Hint Resolve unifies_tl.

Lemma unify_mgu0 : forall h pairs K0 S0 K S,
  unify h pairs K0 S0 = Some (K,S) -> is_subst S0 ->
  mgu_spec K S K0 S0 pairs.
Proof.
  intros.
  apply* (unify_ind (K':=K) (S':=S) (mgu_spec K S));
    clear H H0 K0 S0 pairs h.
        unfold mgu_spec; auto*.
       intros; unfold K1, S1 in *; apply* unify_mgu_nv.
      intros; unfold K1, S1 in *; apply* unify_mgu_vars.
     unfold mgu_spec; intros; apply* H3.
    unfold mgu_spec; intros; apply* H3.
   unfold mgu_spec; intros. apply* H3.
   assert (Heq: typ_subst S' t = typ_subst S' t0).
     apply* H6.
   rewrite <- (H5 t) in Heq.
   rewrite <- (H5 t0) in Heq.
   rewrite H1 in Heq; rewrite H2 in Heq; simpl in Heq.
   inversions Heq.
   intro; intros.
   destruct H8. inversions* H8.
   destruct* H8. inversions* H8.
  unfold mgu_spec; intros.
  apply* H.
  intro; intros.
  destruct* H4.
  inversions H4. symmetry; apply* H2.
Qed.

Theorem unify_mgu : forall h T1 T2 K0 K S,
  unify h ((T1,T2)::nil) K0 id = Some (K, S) ->
  ok K0 ->
  typ_subst S' T1 = typ_subst S' T2 ->
  well_subst K0 K' S' ->
  (forall T3 T4,
    typ_subst S T3 = typ_subst S T4 -> typ_subst S' T3 = typ_subst S' T4) /\
  well_subst K K' S'.
Proof.
  intros.
  destruct* (unify_mgu0 _ H is_subst_id).
      intro. rewrite* typ_subst_id.
    intro; simpl; intros.
    destruct* H3.
    inversions* H3.
  split*.
  intros.
  rewrite <- (H3 T3).
  rewrite <- (H3 T4).
  rewrite* H5.
Qed.

End Mgu.

Section Accum.
  Variables A B : Set.
  Variables (f : A -> B) (op : B->B->B) (unit : B).

  Fixpoint accum (l:list A) {struct l} : B :=
    match l with
    | nil => unit
    | a::rem => op (f a) (accum rem)
    end.

  Variable op_assoc : forall a b c, op a (op b c) = op (op a b) c.
  Variable op_unit : forall a, op unit a = a.

  Lemma accum_app : forall l2 l1,
    accum (l1 ++ l2) = op (accum l1) (accum l2).
  Proof.
    induction l1; simpl. rewrite* op_unit.
    rewrite <- op_assoc.
    rewrite* IHl1.
  Qed.

End Accum.

Fixpoint all_types S (pairs:list(typ*typ)) {struct pairs} : list typ :=
  match pairs with
  | nil => nil
  | p::rem =>
      typ_subst S (fst p) :: typ_subst S (snd p) :: all_types S rem
  end.

Definition all_fv S pairs :=
  accum typ_fv S.union {} (all_types S pairs).

Fixpoint typ_size (T : typ) : nat :=
  match T with
  | typ_arrow T1 T2 => S (typ_size T1 + typ_size T2)
  | _ => 1
  end.

Definition typ_size' S := fun T => typ_size (typ_subst S T).

Definition kenv_types :=
  accum (fun (X:var*kind) => kind_types (snd X)) (@app typ) nil.

Definition kinds_size S kl :=
  length kl * accum (typ_size' S) plus 0 kl.

Definition all_size S K pairs :=
  accum typ_size plus 0 (all_types S pairs) + kinds_size S (kenv_types K).

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

Definition really_all_fv S K pairs :=
  fv_in kind_fv (map (kind_subst S) K) \u all_fv S pairs.

Definition size_pairs S K pairs :=
  pow2exp (all_size S K pairs) (S.cardinal (really_all_fv S K pairs)).

Lemma size_pairs_grows : forall S K p pairs,
  size_pairs S K pairs < size_pairs S K (p :: pairs).
Proof.
  intros.
  unfold size_pairs.
  apply pow2exp_lt_le.
    unfold all_size; simpl.
    destruct (typ_subst S (fst p)); simpl; omega.
  unfold really_all_fv, all_fv; simpl.
  apply cardinal_subset.
  sets_solve.
Qed.

Lemma typ_fv_decr : forall v T S T1,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  typ_fv (typ_subst (compose (v ~ T) S) T1) <<
  S.remove v (typ_fv T \u typ_fv (typ_subst S T1)).
Proof.
  intros.
  rewrite* typ_subst_compose.
  induction (typ_subst S T1); simpl in *; sets_solve.
  destruct (v0 == v).
    subst.
    destruct* (H0 y).
  simpl in Hy. auto.
Qed.

Lemma kind_fv_decr : forall v T S k,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  kind_fv (kind_subst (compose (v ~ T) S) k) <<
  S.remove v (typ_fv T \u kind_fv (kind_subst S k)).
Proof.
  intros.
  unfold kind_fv.
  destruct k as [[kc kv kr kh]|]; simpl*.
  clear kc kv kh.
  induction kr; simpl*.
  sets_solve.
  use (typ_fv_decr _ _ _ H H0 H1).
Qed.

Lemma fv_in_decr : forall (A:Set) v T S (E:Env.env A) fv (sub:subs -> A -> A),
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  (forall a,
    fv (sub (compose (v ~ T) S) a) << S.remove v (typ_fv T \u fv (sub S a))) ->
  fv_in fv (map (sub (compose (v ~ T) S)) E) <<
  S.remove v (typ_fv T \u fv_in fv (map (sub S) E)).
Proof.
  intros.
  induction E; simpl*.
  destruct a.
  simpl.
  sets_solve.
  use (H1 a).
Qed.

Lemma all_fv_decr : forall v T S pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  all_fv (compose (v ~ T) S) pairs <<
  S.remove v (all_fv S ((typ_fvar v, T) :: pairs)).
Proof.
  unfold all_fv.
  induction pairs; intros; simpl*.
  rewrite* get_notin_dom.
  sets_solve.
    use (typ_fv_decr _ _ _ H H0 H1).
    apply* remove_subset.
    sets_solve.
    rewrite <- (@typ_subst_fresh S T) in H3; auto.
    disjoint_solve.
   use (typ_fv_decr _ _ _ H H0 H2).
   apply* remove_subset.
   sets_solve.
   rewrite <- (@typ_subst_fresh S T) in H3; auto.
   disjoint_solve.
  use (IHpairs H H0 _ H2).
  apply* remove_subset.
  simpl.
  rewrite* get_notin_dom.
  simpl*.
Qed.

Lemma really_all_fv_decr : forall S K pairs v T,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) -> ok K ->
  really_all_fv (compose (v ~ T) S) K pairs <<
  S.remove v (really_all_fv S K ((typ_fvar v, T) :: pairs)).
Proof.
  intros until T. intros Hv Dis HK.
  unfold really_all_fv.
  sets_solve.
    unfold all_fv; simpl. rewrite* get_notin_dom.
    repeat rewrite union_assoc.
    rewrite* typ_subst_fresh; try disjoint_solve.
    rewrite remove_union; apply S.union_2.
    rewrite union_comm; rewrite union_assoc.
    rewrite remove_union; apply S.union_2.
    refine (fv_in_decr _ _ _ _ _ _ _ _ _); auto.
    intros; apply* kind_fv_decr.
  use (all_fv_decr _ _ _ Hv Dis H).
Qed.

Lemma cardinal_decr : forall v T S K pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) -> ok K ->
  S.cardinal (really_all_fv (compose (v ~ T) S) (remove_env K v) pairs) <
  S.cardinal (really_all_fv S K ((typ_fvar v, T) :: pairs)).
Proof.
  intros.
  use (really_all_fv_decr (pairs:=pairs) _ _ H H0 H1).
  use (le_lt_n_Sm _ _ (cardinal_subset H2)).
  rewrite cardinal_remove in H3.
    eapply le_lt_trans; try apply H3.
    apply cardinal_subset.
    unfold really_all_fv. rewrite map_remove_env.
    sets_solve.
    apply S.union_2. refine (fv_in_remove_env _ _ _ H4).
  unfold really_all_fv, all_fv; simpl.
  rewrite* get_notin_dom.
  simpl*.
Qed.

Lemma typ_subst_decr : forall v T S T1,
  v # S ->
  typ_size (typ_subst (compose (v ~ T) S) T1) <=
  typ_size T * typ_size (typ_subst S T1).
Proof.
  intros.
  rewrite* typ_subst_compose.
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

Lemma typ_subst_decr_all : forall v T S K pairs,
  v # S ->
  all_size (compose (v ~ T) S) K pairs <= typ_size T * all_size S K pairs.
Proof.
  intros; unfold all_size; induction pairs; simpl.
    unfold kinds_size.
    rewrite (mult_comm (typ_size T)).
    rewrite <- mult_assoc.
    apply mult_le_compat_l.
    rewrite mult_comm.
    induction (kenv_types K); simpl. omega.
    rewrite mult_plus_distr_l.
    use (typ_subst_decr T S a H).
    unfold typ_size' in *; omega.
  repeat rewrite mult_plus_distr_l in *.
  repeat rewrite plus_assoc in *.
  use (typ_subst_decr T S (fst a) H).
  use (typ_subst_decr T S (snd a) H).
  omega.
Qed.

Lemma length_kenv_types_remove : forall v K,
  length (kenv_types (remove_env K v)) <= length (kenv_types K).
Proof.
  induction K; simpl. omega.
  destruct a. destruct (v == v0).
    rewrite app_length. omega.
  simpl. repeat rewrite app_length. omega.
Qed.

Lemma all_size_remove : forall S K pairs v,
  all_size S (remove_env K v) pairs <= all_size S K pairs.
Proof.
  intros.
  unfold all_size.
  repeat rewrite* accum_app; try (intros; omega).
  apply plus_le_compat_l.
  unfold kinds_size.
  eapply le_trans.
    apply mult_le_compat_r. apply length_kenv_types_remove.
  apply mult_le_compat_l.
  induction K; simpl. omega.
  destruct a.
  destruct (v == v0); simpl; repeat rewrite accum_app; intros; omega.
Qed.

Lemma size_pairs_decr : forall v T K S pairs,
  v # S -> ok K ->
  disjoint (typ_fv T) ({{v}} \u dom S) ->
  size_pairs (compose (v ~ T) S) (remove_env K v) pairs <
  size_pairs S K ((typ_fvar v,T)::pairs).
Proof.
  intros.
  unfold size_pairs.
  use (cardinal_decr _ _ pairs H H1 H0).
  case_rewrite (S.cardinal (really_all_fv S K ((typ_fvar v, T) :: pairs))) R1.
    omega.
  simpl.
  apply* pow2exp_lt_le; try omega.
  use (typ_subst_decr_all T S K pairs H).
  assert (typ_size T < all_size S K ((typ_fvar v, T) :: pairs)).
    unfold all_size; simpl.
    rewrite* get_notin_dom.
    rewrite (typ_subst_fresh S T); try disjoint_solve.
    rewrite plus_assoc. rewrite <- plus_assoc.
    simpl typ_size.
    fold (all_size S K pairs). omega.
  assert (all_size S K pairs < all_size S K ((typ_fvar v, T) :: pairs)).
    unfold all_size; simpl.
    rewrite* get_notin_dom.
    simpl; omega.
  eapply le_lt_trans. apply all_size_remove.
  eapply le_lt_trans. apply H3.
  clear -H4 H5.
  eapply le_lt_trans; try eapply mult_lt_compat_r; try apply H4.
    apply mult_le_compat_l. omega.
  omega.
Qed.

Lemma size_pairs_comm : forall S K T1 T2 pairs,
  size_pairs S K ((T1,T2)::pairs) = size_pairs S K ((T2,T1)::pairs).
Proof.
  intros; unfold size_pairs, all_size, really_all_fv, all_fv; simpl.
  repeat rewrite plus_assoc.
  rewrite* (@plus_comm (typ_size (typ_subst S T2))).
  rewrite (union_assoc (typ_fv (typ_subst S T1))).
  rewrite (union_comm (typ_fv (typ_subst S T1))).
  repeat rewrite union_assoc. auto.
Qed.

Lemma size_pairs_decr' : forall S0 K0 t t0 pairs h v,
  is_subst S0 -> ok K0 ->
  S.mem v (typ_fv (typ_subst S0 t0)) = false ->
  size_pairs S0 K0 ((t, t0) :: pairs) < S h ->
  typ_subst S0 t = typ_fvar v ->
  size_pairs (compose (v ~ typ_subst S0 t0) S0) (remove_env K0 v) pairs < h.
Proof.
  intros.
  use (typ_subst_res_fresh _ H H3).
  use (typ_subst_disjoint t0 H).
  eapply lt_le_trans.
    apply* size_pairs_decr.
    assert (disjoint {{v}} (typ_fv (typ_subst S0 t0))).
      intro v0. destruct* (v0 == v).
      subst.
      right; intro.
      rewrite (S.mem_1 H6) in H1. discriminate.
    disjoint_solve.
  replace (size_pairs S0 K0 ((typ_fvar v, typ_subst S0 t0) :: pairs))
    with (size_pairs S0 K0 ((t, t0) :: pairs)).
    omega.
  unfold size_pairs, all_size, really_all_fv, all_fv; simpl.
  rewrite* get_notin_dom.
  rewrite H3.
  rewrite* typ_subst_idem.
Qed.

Lemma accum_le : forall (A:Set) f (a:A) l,
  In a l -> f a <= accum f plus 0 l.
Proof.
  induction l; simpl; intros. elim H.
  destruct H. subst; omega.
  use (IHl H). omega.
Qed.

Lemma length_accum : forall (A:Set) l,
  length l = accum (fun x:A => 1) plus 0 l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma unify_kinds_size : forall k k0 k1 l S,
  unify_kinds k k0 = Some (k1, l) ->
  (forall f, accum f plus 0 (kind_types k1)
    <= accum f plus 0 (kind_types k ++ kind_types k0)) /\
  accum typ_size plus 0 (all_types S l) + kinds_size S (kind_types k1) <=
  kinds_size S (kind_types k ++ kind_types k0).
Proof.
  unfold unify_kinds; intros.
  destruct k as [[kc kv kr kh]|]; destruct k0 as [[kc0 kv0 kr0 kh0]|].
     destruct (Cstr2.valid (Cstr2.lub kc kc0)); try discriminate.
     simpl.
     inversions H; clear H. simpl.
     set (un := Cstr2.unique (Cstr2.lub kc kc0)); clearbody un.
     clear v kv kh kv0 kh0 kc kc0.
     set (pairs := @nil (typ*typ)).
     set (kr' := @nil (var*typ)).
     rewrite <- map_app.
     pattern (kr++kr0) at 2.
     replace (kr++kr0) with ((kr++kr0)++kr')
       by (unfold kr'; rewrite* <- app_nil_end).
     replace (kinds_size S (List.map (fun x : var * typ => snd x) (kr ++ kr0)))
       with (accum typ_size plus 0 (all_types S pairs) +
             kinds_size S (List.map (fun x : var * typ => snd x)
               ((kr ++ kr0) ++ kr')))
       by (unfold pairs, kr'; simpl; rewrite* <- app_nil_end).
     gen pairs kr'; induction (kr ++ kr0); simpl; intros. auto.
     clear kr kr0.
     destruct a.
     assert (In v un /\ get v kr' <> None \/ (~In v un \/ get v kr' = None)).
       destruct (In_dec eq_var_dec v un); case_eq (get v kr'); intros; auto.
       left; split*. intro; discriminate.
     destruct H.
       destruct H.
       destruct* (In_dec eq_var_dec v un).
       case_rewrite (get v kr') R1; simpl*.
       destruct (IHl ((t,t0)::pairs) kr'); clear IHl.
       split. intros; use (H1 f); omega.
       eapply le_trans; try apply H2. clear H2.
       unfold kinds_size; simpl.
       fold (typ_size' S t). fold (typ_size' S t0).
       rewrite (plus_comm (typ_size' S t0)).
       repeat rewrite plus_assoc.
       rewrite (plus_comm (typ_size' S t)).
       repeat rewrite <- plus_assoc.
       do 2 apply plus_le_compat_l.
       rewrite mult_plus_distr_l.
       repeat rewrite plus_assoc.
       apply plus_le_compat_r.
       rewrite map_app. rewrite accum_app; try (intros; omega).
       use (in_map (fun x : var * typ => snd x) _ _ (binds_in R1)).
       simpl in H2.
       eapply le_trans. apply (accum_le (typ_size' S) _ _ H2).
       rewrite <- plus_assoc.
       refine (le_trans _ _ _ _ (le_plus_r _ _)).
       apply le_plus_l.
     assert (forall a (b:list(var*typ)*list(typ*typ)),
       (if In_dec eq_var_dec v un
        then match get v kr' with Some T' => a T' | None => b end
        else b) = b).
       intros.
       destruct* (In_dec eq_var_dec v un).
       destruct* H. rewrite* H.
     rewrite H0; clear H H0.
     destruct (IHl pairs ((v,t)::kr')); clear IHl.
     assert
       (length (List.map (fun x : var * typ => snd x) (l ++ (v, t) :: kr')) <=
         (length (t :: List.map (fun x : var * typ => snd x) (l ++ kr')))).
       simpl.
       repeat rewrite map_length.
       repeat rewrite app_length.
       simpl. omega.
     split.
       intros; eapply le_trans. apply (H f).
       repeat rewrite map_app; simpl.
       repeat rewrite accum_app; simpl; intros; omega.
     eapply le_trans. apply H0.
     apply plus_le_compat_l.
     clear -H1.
     unfold kinds_size.
     eapply le_trans.
       apply mult_le_compat_r. apply H1.
     apply mult_le_compat_l.
     clear; repeat rewrite map_app.
     simpl; repeat rewrite accum_app; simpl; intros; omega.
    inversions H; simpl. rewrite* <- app_nil_end.
   inversions H; simpl*.
  inversions H; simpl*.
Qed.

Lemma accum_remove_env : forall f v K,
  accum f plus 0 (kind_types (get_kind v K) ++ kenv_types (remove_env K v)) =
  accum f plus 0 (kenv_types K).
Proof.
  induction K; simpl. auto.
  destruct a; simpl.
  unfold get_kind in *. simpl.
  destruct (v == v0). auto.
  simpl.
  repeat (rewrite accum_app in *; try (intros; omega)).
Qed.

Lemma length_remove_env : forall v K,
  length (kind_types (get_kind v K) ++ kenv_types (remove_env K v)) =
  length (kenv_types K).
Proof.
  intros; repeat rewrite length_accum.
  apply accum_remove_env.
Qed.

Lemma all_types_app : forall S l1 l2,
  all_types S (l1 ++ l2) = all_types S l1 ++ all_types S l2.
Proof.
  intros; induction l1; simpl. auto.
  rewrite* <- IHl1.
Qed.

Lemma typ_size'_var : forall v v0 T,
  typ_size (typ_subst (v ~ typ_fvar v0) T) = typ_size T.
Proof.
  induction T; simpl. auto.
    destruct* (v1 == v).
  congruence.
Qed.

Lemma all_size_var : forall v v0 S K pairs,
  v # S ->
  all_size (compose (v ~ typ_fvar v0) S) K pairs = all_size S K pairs.
Proof.
  unfold all_size; intros.
  assert (disjoint (dom (v ~ typ_fvar v0)) (dom S)).
    simpl. intro x; destruct* (x == v).
  induction pairs; simpl.
    unfold kinds_size.
    refine (f_equal (mult _) _).
    induction (kenv_types K); simpl. auto.
    rewrite IHl.
    unfold typ_size'.
    rewrite* typ_subst_compose.
    rewrite* typ_size'_var.
  rewrite plus_assoc.
  rewrite <- plus_assoc.
  rewrite IHpairs. clear IHpairs.
  repeat rewrite* typ_subst_compose.
  repeat rewrite typ_size'_var.
  repeat rewrite plus_assoc. auto.
Qed.

Lemma get_kind_fv_in : forall S v K,
  kind_fv (kind_subst S (get_kind v K)) << fv_in kind_fv (map (kind_subst S) K).
Proof.
  induction K; simpl. apply subset_refl.
  unfold get_kind; simpl.
  destruct a. destruct (v == v0).
    simpl. intros x Hx; auto with sets.
  fold (get_kind v K).
  intros x Hx.
  simpl. apply S.union_3. apply* IHK.
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
  unify_kinds k k0 = Some (k1, l) ->
  kind_fv (kind_subst S k1) \u all_fv S l <<
  kind_fv (kind_subst S k) \u kind_fv (kind_subst S k0).
Proof.
  unfold unify_kinds; intros.
  destruct k as [[kc kv kr kh]|].
    destruct k0 as [[kc0 kv0 kr0 kh0]|].
      destruct (Cstr2.valid (Cstr2.lub kc kc0)); try discriminate.
      inversions H; clear H.
      simpl.
      unfold kind_fv; simpl.
      repeat rewrite map_map; simpl.
      rewrite <- fv_list_map. rewrite <- map_app.
      set (pairs := nil(A:=typ*typ)).
      set (kr' := nil(A:=var*typ)).
      intros x Hx.
      rewrite <- union_empty_r.
      replace {} with
        (typ_fv_list (List.map (fun x : var * typ => typ_subst S (snd x)) kr'))
        by reflexivity.
      rewrite <- union_empty_r.
      replace {} with (all_fv S pairs) by reflexivity.
      clearbody pairs kr'.
      gen pairs kr'; induction (kr ++ kr0); simpl; intros.
        rewrite <- union_assoc; auto with sets.
      destruct a; simpl in *.
      destruct (In_dec eq_var_dec v0 (Cstr2.unique (Cstr2.lub kc kc0))).
        case_rewrite (get v0 kr') R1;
          poses Hsub (IHl _ _ Hx); clear -Hsub R1.
          unfold all_fv in *; simpl in *.
          sets_solve.
          use (binds_in R1).
          use (in_map (fun x : var * typ => typ_subst S (snd x)) _ _ H0).
          use (in_typ_fv _ _ H1 H).
        simpl in Hsub. auto.
      poses Hsub (IHl _ _ Hx); clear -Hsub.
      simpl in Hsub; auto.
    inversions H.
    unfold kind_fv, all_fv; simpl*.
  inversions H.
  unfold kind_fv, all_fv; simpl*.
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

Lemma size_pairs_decr_vars : forall S0 K0 t t0 pairs h v v0 x0 l,
  is_subst S0 -> ok K0 ->
  size_pairs S0 K0 ((t, t0) :: pairs) < S h ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = typ_fvar v0 ->
  v <> v0 ->
  unify_kinds (get_kind v K0) (get_kind v0 K0) = Some (x0, l) ->
  size_pairs (compose (v ~ typ_fvar v0) S0)
    (remove_env (remove_env K0 v) v0 & v0 ~ x0) (l ++ pairs) < h.
Proof.
  intros.
  use (typ_subst_res_fresh' _ H H3).
  poses Hv (typ_subst_res_fresh' _ H H2).
  use (typ_subst_disjoint t0 H).
  eapply lt_le_trans; try apply (lt_n_Sm_le _ _ H1).
  clear H1.
  unfold size_pairs.
  assert (v \in really_all_fv S0 K0 ((t,t0)::pairs)).
    unfold really_all_fv, all_fv.
    simpl. rewrite H2. simpl*.
  rewrite <- (cardinal_remove H1). clear H1.
  simpl.
  set (S := compose (v ~ typ_fvar v0) S0).
  apply pow2exp_lt_le.
    eapply le_lt_trans.
      instantiate (1 := all_size S K0 pairs).
      destruct (unify_kinds_size _ _ S H5).
      unfold all_size, kinds_size; simpl.
      rewrite <- (length_remove_env v K0).
      repeat rewrite app_length.
      rewrite <- (length_remove_env v0 (remove_env K0 v)).
      assert (get_kind v0 (remove_env K0 v) = get_kind v0 K0).
        unfold get_kind.
        case_eq (get v0 K0); intros.
          rewrite* (binds_remove_env (v:=v) H9).
        case_eq (get v0 (remove_env K0 v)); intros.
          rewrite (binds_orig_remove_env _ H0 H10) in H9. discriminate.
        auto.
      rewrite H9.
      repeat rewrite app_length.
      rewrite plus_assoc.
      rewrite <- (accum_remove_env (typ_size' S) v K0).
      rewrite all_types_app.
      repeat rewrite accum_app; try (intros; omega).
      rewrite <- (accum_remove_env (typ_size' S) v0 (remove_env K0 v)).
      rewrite accum_app; try (intros; omega).
      rewrite H9. clear H9.
      unfold kinds_size in H8.
      set (K := kenv_types (remove_env (remove_env K0 v) v0)) in *.
      set (kv := kind_types (get_kind v K0)) in *.
      set (kv0 := kind_types (get_kind v0 K0)) in *.
      set (kx0 := kind_types x0) in *.
      rewrite plus_assoc.
      replace (accum (typ_size' S) plus 0 kv + accum (typ_size' S) plus 0 kv0)
        with (accum (typ_size' S) plus 0 (kv ++ kv0))
        by (rewrite accum_app; intros; omega).
      replace (length kv + length kv0) with (length (kv ++ kv0))
        by rewrite* app_length.
      rewrite mult_plus_distr_r.
      rewrite mult_plus_distr_r.
      repeat rewrite plus_assoc.
      repeat rewrite mult_plus_distr_l.
      repeat rewrite plus_assoc.
      apply plus_le_compat_r.
      use (mult_le_compat_l _ _ (length K) (H1 (typ_size' S))).
      use (H1 (fun _ => 1)). repeat rewrite <- length_accum in H10.
      use (mult_le_compat_r _ _ (accum (typ_size' S) plus 0 K) H10).
      omega.
    unfold S; clear S.
    rewrite* all_size_var.
    unfold all_size; simpl.
    set (T := typ_subst S0 t).
    assert (typ_size T > 0). destruct T; simpl; omega.
    destruct (typ_size T). omega.
    simpl.
    repeat rewrite <- plus_assoc.
    apply le_lt_n_Sm.
    eapply le_trans; [|apply le_plus_r].
    eapply le_trans; [|apply le_plus_r].
    rewrite plus_assoc. apply le_plus_l.
  poses Hfv (unify_kinds_fv _ _ S H5).
  apply cardinal_subset.
  sets_solve.
  replace (really_all_fv S0 K0 ((t, t0) :: pairs))
    with (really_all_fv S0 K0 ((typ_fvar v, typ_fvar v0) :: pairs)).
    apply* really_all_fv_decr.
      simpl; intro x; destruct* (x == v0). subst*.
    fold S.
    unfold really_all_fv in *.
    simpl in *.
    rewrite all_fv_app in Hy.
    sets_solve.
      use (Hfv y (S.union_2 _ H8)).
      clear -H1.
      apply S.union_2.
      destruct (S.union_1 H1); apply (get_kind_fv_in _ _ _ H).
     rewrite map_remove_env in H8.
     use (fv_in_remove_env _ _ _ H8).
     rewrite map_remove_env in H1.
     use (fv_in_remove_env _ _ _ H1).
    use (Hfv _ (S.union_3 _ H8)).
    apply S.union_2.
    clear -H1.
    destruct (S.union_1 H1); apply (get_kind_fv_in _ _ _ H).
  unfold really_all_fv, all_fv.
  rewrite <- H2; rewrite <- H3.
  simpl.
  repeat rewrite* typ_subst_idem.
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
  assert (disjoint (dom (v ~ T)) (dom S0)).
    simpl. intro x; destruct* (x == v).
  repeat rewrite* typ_subst_compose.
  assert (forall T',
            typ_subst S (typ_subst (v ~ T) T') = typ_subst S T').
    clear -H1; induction T'; simpl; try congruence.
    destruct* (v0 == v).
    subst. apply (sym_eq H1).
  repeat rewrite* H4.
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

Section Completeness.

Variables (K:kenv) (S:subs).

Definition complete_spec S0 K0 pairs h :=
  is_subst S0 -> ok K0 ->
  extends S S0 ->
  unifies S pairs ->
  well_subst K0 K S ->
  size_pairs S0 K0 pairs < h ->
  unify h pairs K0 S0 <> None.

Lemma unify_complete_nv : forall pairs K0 S0 v T h t t0,
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  size_pairs S0 K0 ((t,t0)::pairs) < Datatypes.S h ->
  is_subst S0 -> ok K0 ->
  well_subst K0 K S ->
  (forall K0 S0, complete_spec K0 S0 pairs h) ->
  extends S S0 ->
  unifies S ((t, t0) :: pairs) ->
  (forall x, T <> typ_fvar x) ->
  unify_nv (unify h pairs) K0 S0 v T <> None.
Proof.
  intros until t0; intros R1 R2 Hsz HS0 HK0 WS IHh Hext Heq HT.
  unfold unify_nv.
  assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
  use (Heq _ _ H); clear H.
  rewrite <- Hext in H0; rewrite R1 in H0.
  rewrite <- (Hext t0) in H0; rewrite R2 in H0.
  case_eq (S.mem v (typ_fv T)); intros.
    elimtype False.
    use (S.mem_2 H).
    clear -H0 H1 HT.
    destruct T. elim (in_empty H1).
      elim (HT v); rewrite* (S.singleton_1 H1).
    assert (1 < typ_size (typ_arrow T1 T2)).
      destruct T1; simpl; omega.
    use (typ_subst_no_cycle S _ H1 H).
    rewrite H0 in H2; omega.
  intro.
  case_rewrite (get_kind v K0) R3.
    poses Wk (WS _ _ (get_kind_binds _ _ R3)).
    rewrite H0 in Wk.
    simpl in Wk; inversions Wk.
    clear -H3 HT.
    destruct (typ_subst S0 t0); try discriminate.
    elim (HT v). auto.
  rewrite <- R2 in H.
  use (size_pairs_decr' _ _ _ HS0 HK0 H Hsz R1).
  rewrite R2 in H2.
  use (typ_subst_res_fresh' _ HS0 R1).
  rewrite R2 in H.
  revert H1; apply* IHh; clear IHh.
      intro. rewrite* typ_subst_compose.
      rewrite typ_subst_prebind. apply Hext. congruence.
    intro; auto*.
  clear H0.
  intro; intros.
  destruct k; try (simpl; apply wk_any).
  destruct (v == Z).
    elim (binds_fresh H0).
    rewrite* dom_remove_env. apply* S.remove_1.
  apply WS.
  apply* binds_orig_remove_env.
Qed.

Lemma well_kinded_kind_entails: forall K k x,
  well_kinded K k (typ_fvar x) -> kind_entails (get_kind x K) k.
Proof.
  intros; unfold kind_entails.
  inversions H. auto.
  rewrite* (binds_get_kind H1).
Qed.

Lemma unify_complete_vars : forall h t t0 pairs K0 S0 v v0,
  is_subst S0 -> ok K0 ->
  extends S S0 ->
  unifies S ((t, t0) :: pairs) ->
  well_subst K0 K S ->
  size_pairs S0 K0 ((t, t0) :: pairs) < Datatypes.S h ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = typ_fvar v0 ->
  v <> v0 ->
  (forall pairs K0 S0, complete_spec S0 K0 pairs h) ->
  match unify_vars K0 v v0 with
  | Some (pair K' pairs0) =>
    unify h (pairs0 ++ pairs) K' (compose (v ~ typ_fvar v0) S0)
  | None => None (A:=kenv * subs)
  end <> None.
Proof.
  intros until v0; intros HS0 HK0 Hext Heq WS Hsz R1 R2 n IHh.
  unfold unify_vars.
  poses Hv (typ_subst_res_fresh' _ HS0 R1).
  poses Wk (well_subst_get_kind v WS).
  poses Wk0 (well_subst_get_kind v0 WS).
  set (S0' := compose (v ~ typ_fvar v0) S0) in *.
  assert (HS0': is_subst S0') by (unfold S0'; auto*).
  assert (HK0': forall y, ok (remove_env (remove_env K0 v) v0 & v0 ~ y)).
    use (ok_remove_env v HK0).
    constructor. apply* ok_remove_env.
    rewrite* dom_remove_env.
  assert (Hext': forall T, typ_subst S (typ_subst S0' T) = typ_subst S T).
    intros. unfold S0'. rewrite* typ_subst_compose.
    rewrite typ_subst_prebind. apply Hext.
    rewrite <- R1; rewrite <- R2.
    symmetry; repeat rewrite Hext; apply* Heq.
  assert (Sv_Sv0 : typ_subst S (typ_fvar v) = typ_subst S (typ_fvar v0)).
    rewrite <- R1; rewrite <- R2.
    repeat rewrite Hext. apply* Heq.
  assert (get_kind v K0 = None /\ get_kind v0 K0 = None \/
        exists v1, typ_subst S (typ_fvar v0) = typ_fvar v1
          /\ kind_entails (get_kind v1 K) (kind_subst S (get_kind v K0))
          /\ kind_entails (get_kind v1 K) (kind_subst S (get_kind v0 K0))).
    case_rewrite (get_kind v0 K0) R3.
      inversions Wk0. right; exists x. rewrite H0; split*.
      simpl in Wk0; rewrite <- H0 in Wk0.
      rewrite Sv_Sv0 in Wk; simpl in Wk; rewrite <- H0 in Wk.
      split; apply* well_kinded_kind_entails.
    case_rewrite (get_kind v K0) R4.
      inversions Wk. right; exists x.
      rewrite <- Sv_Sv0; rewrite H0.
      split*.
      split; apply well_kinded_kind_entails.
      rewrite* H0.
      apply wk_any.
    left*.
  destruct H as [[G G0]|[v1 [Hv1 [KEv KEv0]]]].
    rewrite G; rewrite G0.
    simpl unify_kinds. lazy iota beta.
    apply* IHh.
        intro; auto*.
      intro; intros.
      binds_cases H.
        use (binds_orig_remove_env _ (ok_remove_env v HK0) B).
        destruct (Z == v).
          subst. elim (binds_fresh H).
          rewrite dom_remove_env. apply S.remove_1. reflexivity. auto.
        use (binds_orig_remove_env _ HK0 H).
      subst. apply wk_any.
    unfold S0'. apply* size_pairs_decr_vars.
    rewrite G; rewrite G0; reflexivity.
  destruct (unify_kinds_complete _ _ _ _ KEv KEv0)
    as [k1 [l [HU [Heql KEk1]]]].
  rewrite HU.
  apply* IHh.
      intro; intros. destruct* (in_app_or _ _ _ H).
    intro; intros.
    binds_cases H.
      apply WS.
      apply* binds_orig_remove_env.
      apply* binds_orig_remove_env.
    subst.
    rewrite Hv1.
    case_rewrite (get_kind v1 K) R3.
      destruct* k1.
      simpl. use (get_kind_binds _ _ R3).
    destruct* (kind_subst S k1).
  unfold S0'; apply* size_pairs_decr_vars.
Qed.

Lemma unify_complete0 : forall h pairs K0 S0,
  complete_spec S0 K0 pairs h.
Proof.
  induction h.
    intros; intro; intros; elimtype False; omega.
  destruct pairs; intros until S0; intros HS0 HK0 Hext Heq WS Hsz.
    intro; discriminate.
  destruct p.
  simpl unify.
  assert (Heq0: unifies S pairs) by (intro; auto*).
  case_eq (typ_subst S0 t); introv R1; case_eq (typ_subst S0 t0); introv R2.
          destruct (n === n0).
           subst.
           apply* (IHh pairs _ _ HS0 HK0).
           use (size_pairs_grows S0 K0 (t,t0) pairs). omega.
          assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
          poses Ht (Heq _ _ H).
          rewrite <- Hext in Ht; rewrite R1 in Ht.
          rewrite <- (Hext t0) in Ht; rewrite R2 in Ht.
          simpl in Ht. inversions* Ht.
         rewrite size_pairs_comm in Hsz.
         apply* (unify_complete_nv R2 R1 Hsz).
           intro; simpl; intros. destruct H; subst.
             inversions H; symmetry; apply* Heq.
           apply* Heq.
         intros x Hx; discriminate.
        assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
        poses Ht (Heq _ _ H).
        rewrite <- Hext in Ht; rewrite R1 in Ht.
        rewrite <- (Hext t0) in Ht; rewrite R2 in Ht.
        simpl in Ht; inversions Ht.
       apply* (unify_complete_nv R1 R2 Hsz).
       intros x Hx; discriminate.
      destruct (v == v0).
       subst.
       apply* (IHh pairs K0 S0 HS0).
       use (size_pairs_grows S0 K0 (t,t0) pairs). omega.
      apply* unify_complete_vars.
     apply* unify_complete_nv.
     intro; discriminate.
    assert (In (t,t0) ((t,t0)::pairs)) by auto.
    poses E (Heq _ _ H).
    rewrite <- (Hext t) in E. rewrite R1 in E.
    rewrite <- (Hext t0) in E. rewrite R2 in E.
    discriminate.
   rewrite size_pairs_comm in Hsz.
   apply* unify_complete_nv.
     intro; simpl; intros. destruct H; subst.
       inversions H; symmetry; apply* Heq.
     apply* Heq.
   intro; discriminate.
  apply* IHh.
    clear IHh Hsz; intro; intros.
    assert (In (t,t0) ((t,t0)::pairs)) by auto.
    use (Heq _ _ H0).
    rewrite <- (Hext t) in H1.
    rewrite <- (Hext t0) in H1.
    rewrite R1 in H1; rewrite R2 in H1.
    simpl in H1; inversions H1.
    simpl in H; destruct H. inversions* H.
    destruct H. inversions* H.
    apply* Heq.
  assert (size_pairs S0 K0 ((t1, t3) :: (t2, t4) :: pairs) <
          size_pairs S0 K0 ((t, t0) :: pairs)).
    unfold size_pairs, all_size, really_all_fv, all_fv.
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

Theorem unify_complete : forall T1 T2 K0,
  ok K0 -> well_subst K0 K S ->
  typ_subst S T1 = typ_subst S T2 ->
  unify (1 + size_pairs id K0 ((T1,T2)::nil)) ((T1,T2)::nil) K0 id <> None.
Proof.
  intros.
  apply* unify_complete0.
      apply is_subst_id.
    intro; rewrite* typ_subst_id.
  intro; intros; simpl in H2; destruct* H2.
  inversions* H2.
Qed.

End Completeness.

Lemma extends_trans : forall S1 S2 S3,
  extends S1 S2 -> extends S2 S3 -> extends S1 S3.
Proof.
  intros; intro.
  rewrite <- H. rewrite <- (H T).
  rewrite* H0.
Qed.

Theorem unify_monotone : forall h pairs K1 S1 K1' S1' K0 S0,
  unify h pairs K1 S1 = Some (K1', S1') ->
  extends S1 S0 -> well_subst K0 (map (kind_subst S1) K1) S1 ->
  is_subst S1 -> ok K1 -> disjoint (dom S1) (dom K1) ->
  is_subst S0 -> ok K0 ->
  exists h', exists K0', exists S0',
    unify h' pairs K0 S0 = Some (K0', S0') /\
    extends S1' S0' /\ well_subst K0' (map (kind_subst S1') K1') S1'.
Proof.
  intros until S0; intros HU Hext WS HS1 HK1 Dis1 HS0 HK0.
  poses Hext1 (typ_subst_extend _ _ _ HS1 HU).
  assert (Hext': extends S1' S0) by apply* extends_trans.
  destruct* (unify_kinds_ok _ _ HU) as [HK1' [Dis1' WS1']].
  assert (WS': well_subst K0 (map (kind_subst S1') K1') S1').
    intro; intros.
    use (WS _ _ H).
    rewrite <- Hext1.
    rewrite <- (kind_subst_combine _ _ _ k Hext1).
    inversions H0.  auto.
    destruct (binds_map_inv _ _ H4) as [k1 [Hk1 Bk1]].
    use (WS1' _ _ Bk1).
    simpl. rewrite <- H2.
    rewrite <- (kind_subst_combine _ _ _ k1 Hext1) in H3.
    rewrite Hk1 in H3.
    inversions H3.
    simpl; rewrite <- H7. clear H2 H7.
    eapply wk_kind. apply H9.
    apply* entails_trans. apply* kind_subst_entails.
  exists (1 + size_pairs S0 K0 pairs).
  assert (Hunif: unifies S1' pairs) by apply* (unify_types _ _ _ HU).
  assert (unify (1 + size_pairs S0 K0 pairs) pairs K0 S0 <> None).
    apply* (unify_complete0 (K:=map (kind_subst S1') K1') (S:=S1')).
  case_rewrite (unify (1 + size_pairs S0 K0 pairs) pairs K0 S0) R1;
    try (elim H; reflexivity).
  destruct p as [K0' S0']. clear H.
  esplit; esplit; split*.
  destruct* (unify_mgu0 _ R1 (K':=map (kind_subst S1') K1') (S':=S1')).
Qed.

End Mk2.

End MkUnify.