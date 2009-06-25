(***************************************************************************
* Principality of unification for mini-ML with structural polymorphism     *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import Arith List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure Cardinal.
Require Import ML_SP_Soundness ML_SP_Eval.

Set Implicit Arguments.

Module MkUnify(Cstr:CstrIntf)(Const:CstIntf).

Module MyEval := MkEval(Cstr)(Const).
Import MyEval.
Import Sound.
Import Infra.
Import Defs.

(* Composition of substitutions *)
Definition compose S1 S2 : subs := S1 & map (typ_subst S1) S2.

(* Inclusion of substitutions. Very handy to use in proofs *)
Definition extends S S0 :=
  forall T, typ_subst S (typ_subst S0 T) = typ_subst S T.

(* Unifiers *)
Definition unifies S pairs :=
  forall T1 T2, In (T1, T2) pairs -> typ_subst S T1 = typ_subst S T2.

(* Subsititions should be in normal form *)
Definition is_subst (S : subs) :=
  env_prop (fun T => disjoint (dom S) (typ_fv T)) S.

Section Moregen.
  (* Here we relate extends with the more usual notional of generality *)

  Definition moregen S0 S :=
    exists S1, forall T, typ_subst S T = typ_subst S1 (typ_subst S0 T).

  (* Extends implies more general *)
  Lemma extends_moregen : forall S S0,
    extends S S0 -> moregen S0 S.
  Proof.
    intros.
    exists* S.
  Qed.

  Lemma typ_subst_idem : forall S T,
    is_subst S -> typ_subst S (typ_subst S T) = typ_subst S T.
  Proof.
    intros.
    induction T; simpl. auto.
      case_eq (get v S); intros.
        rewrite* typ_subst_fresh.
      simpl.
      rewrite* H0.
    simpl; congruence.
  Qed.

  (* For substitutions in normal form, moregeneral implies extends *)
  Lemma moregen_extends : forall S S0,
    moregen S0 S -> is_subst S0 -> extends S S0.
  Proof.
    intros; intro.
    destruct H as [S1 Heq].
    rewrite Heq.
    rewrite* typ_subst_idem.
  Qed.

End Moregen.

Fixpoint unify_kind_rel (kr kr':list(var*typ)) (uniq:var -> bool)
  (pairs:list(typ*typ)) {struct kr} :=
  match kr with
  | nil => (kr', pairs)
  | (l,T)::krem =>
    if uniq l then
      match get l kr' with
      | None => unify_kind_rel krem ((l,T)::kr') uniq pairs
      | Some T' => unify_kind_rel krem kr' uniq ((T,T')::pairs)
      end
    else unify_kind_rel krem ((l,T)::kr') uniq pairs
  end.

Fixpoint remove_env (A:Set) (E:Env.env A) (x:var) {struct E} : Env.env A :=
  match E with
  | nil => nil
  | (y,a)::E' =>
    if x == y then E' else (y,a) :: remove_env E' x
  end.

Lemma unify_coherent : forall kc kr,
  coherent kc (fst (unify_kind_rel kr nil (Cstr.unique kc) nil)).
Proof.
  intros until kr.
  set (kr' := @nil (var*typ)).
  set (pairs' := @nil (typ*typ)).
  assert (coherent kc kr'). intro; intros. elim H0.
  gen kr' pairs'.
  induction kr; simpl; intros. auto.
  destruct a.
  case_eq (Cstr.unique kc v); introv R.
    case_eq (get v kr'); introv R1. apply* IHkr.
    apply IHkr.
    intro; intros.
    simpl in *; destruct H1; [inversions H1|]; destruct H2. inversions* H2.
        elim (get_none_notin_list _ _ _ R1 H2).
      inversions H2; elim (get_none_notin_list _ _ _ R1 H1).
    apply* (H x).
  apply IHkr.
  intro; intros.
  destruct (x == v).
    subst. rewrite R in H0; discriminate.
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
    let kc := Cstr.lub kc1 kc2 in
    if Cstr.valid_dec kc then
      let krp := unify_kind_rel (kr1 ++ kr2) nil (Cstr.unique kc) nil in
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
  case_rewrite R (get x K).
  subst*.
Qed.

Section Accum.
  Variables A B : Type.
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

Definition pair_subst S T := (typ_subst S (fst T), typ_subst S (snd T)).

Fixpoint all_types S (pairs:list(typ*typ)) {struct pairs} : list typ :=
  match pairs with
  | nil => nil
  | p::rem =>
      typ_subst S (fst p) :: typ_subst S (snd p) :: all_types S rem
  end.

Fixpoint typ_size (T : typ) : nat :=
  match T with
  | typ_arrow T1 T2 => S (typ_size T1 + typ_size T2)
  | _ => 1
  end.

Definition pair_size (p:typ*typ) :=
  1 + typ_size (fst p) + typ_size (snd p).

Definition pairs_size S pairs := 
  accum pair_size plus 0 (List.map (pair_subst S) pairs).

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
  rewrite dom_concat; rewrite dom_map.
  simpl. rewrite union_empty_r.
  destruct (in_app_or _ _ _ H2).
    destruct (in_map_inv _ _ _ _ H3) as [b [F B']].
    subst.
    use (H _ _ B').
    simpl in *.
    apply* disjoint_subst.
    intro y; destruct* (H0 y). destruct* (y == x).
  simpl in H3. destruct* H3.
  inversions H3.
  disjoint_solve.
  destruct* (v == x0).
Qed.
Hint Resolve add_binding_is_subst.

Lemma typ_subst_disjoint : forall S T,
  is_subst S -> disjoint (dom S) (typ_fv (typ_subst S T)).
Proof.
  intros; induction T; simpl in *.
      intro; auto.
    case_eq (get v S); intros.
      use (H _ _ (binds_in H0)).
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

Definition all_fv S pairs :=
  accum (fun p:typ*typ => typ_fv (fst p) \u typ_fv (snd p))
    S.union {} (List.map (pair_subst S) pairs).

Definition really_all_fv S K pairs :=
  fv_in kind_fv (map (kind_subst S) K) \u all_fv S pairs.

Definition size_pairs S K pairs :=
  1+S.cardinal (really_all_fv S K pairs).

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
  induction E; simpl*; intros.
  destruct a.
  simpl.
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
  destruct a; simpl.
  sets_solve;
    try solve [
      use (typ_fv_decr _ _ _ H H0 H2);
      apply* remove_subset;
        sets_solve;
        rewrite <- (@typ_subst_fresh S T) in H3; auto;
        disjoint_solve].
  use (IHpairs H H0 _ H1).
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
  induction E; simpl; intros. auto.
  destruct a. destruct* (x == v); simpl*.
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
    auto.
  unfold really_all_fv, all_fv; simpl.
  rewrite* get_notin_dom.
  simpl*.
Qed.

Lemma size_pairs_decr : forall v T K S pairs,
  v # S -> ok K ->
  disjoint (typ_fv T) ({{v}} \u dom S) ->
  size_pairs (compose (v ~ T) S) (remove_env K v) pairs <
  size_pairs S K ((typ_fvar v,T)::pairs).
Proof.
  intros.
  unfold size_pairs.
  apply lt_n_S.
  apply* cardinal_decr.
Qed.

Lemma size_pairs_comm : forall S K T1 T2 pairs,
  size_pairs S K ((T1,T2)::pairs) = size_pairs S K ((T2,T1)::pairs).
Proof.
  intros; unfold size_pairs, really_all_fv, all_fv; simpl.
  rewrite* (union_comm (typ_fv (typ_subst S T1))).
Qed.

Lemma get_kind_fv_in : forall S v K,
  kind_fv (kind_subst S (get_kind v K)) << fv_in kind_fv (map (kind_subst S) K).
Proof.
  induction K; simpl. apply subset_refl.
  unfold get_kind; simpl.
  destruct a. destruct (v == v0).
    simpl*.
  fold (get_kind v K).
  simpl*.
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
      destruct (Cstr.valid_dec (Cstr.lub kc kc0)); try discriminate.
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
      case_rewrite R (Cstr.unique (Cstr.lub kc kc0) v0).
        case_rewrite R1 (get v0 kr');
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

Lemma size_pairs_decr_vars : forall S0 K0 pairs v v0 x0 l,
  is_subst S0 -> ok K0 ->
  v # S0 ->
  v0 # S0 ->
  v <> v0 ->
  unify_kinds (get_kind v K0) (get_kind v0 K0) = Some (x0, l) ->
  size_pairs (compose (v ~ typ_fvar v0) S0)
    (remove_env (remove_env K0 v) v0 & v0 ~ x0) (l ++ pairs)
    < size_pairs S0 K0 ((typ_fvar v, typ_fvar v0) :: pairs).
Proof.
  intros.
  unfold size_pairs.
  assert (v \in really_all_fv S0 K0 ((typ_fvar v,typ_fvar v0)::pairs)).
    unfold really_all_fv, all_fv.
    simpl. rewrite* get_notin_dom. simpl*.
  rewrite <- (cardinal_remove H5). clear H5.
  simpl.
  set (S := compose (v ~ typ_fvar v0) S0).
  poses Hfv (unify_kinds_fv _ _ S H4).
  apply le_lt_n_Sm. apply le_n_S.
  apply cardinal_subset.
  sets_solve.
  apply* really_all_fv_decr.
    simpl; intro x; destruct* (x == v0). subst*.
  fold S.
  unfold really_all_fv in *.
  simpl in *.
  rewrite all_fv_app in Hy.
  do 2 rewrite map_remove_env in Hy.
  sets_solve; try use (get_kind_fv_in _ _ _ H5).
  apply S.union_2.
  refine (fv_in_remove_env _ v _ _); auto.
  refine (fv_in_remove_env _ v0 _ _); auto.
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

Definition unify_vars (K:kenv) (x y:var) :=
  match unify_kinds (get_kind x K) (get_kind y K) with
  | Some (k, pairs) => Some (remove_env (remove_env K x) y & y ~ k, pairs)
  | None => None
  end.

Definition decidable (A : Type) (P : A -> Prop) :=
  forall x, sumbool (P x) (~P x).

Definition in_dec L : decidable (fun x => x \in L).
  intros L x.
  case_eq (S.mem x L); intros. left. exact (S.mem_2 H).
  right. exact (mem_3 H).
Qed.

Section Wf2.
  Variables A B:Set.
  Variable ltA : A -> A -> Prop.
  Variable ltB : B -> B -> Prop.

  Definition ltAB (p1 p2:A*B) :=
    ltA (fst p1) (fst p2) \/ fst p1 = fst p2 /\ ltB (snd p1) (snd p2).

  Hypothesis ltA_wf : well_founded ltA.
  Hypothesis ltB_wf : well_founded ltB.

  Theorem ltAB_wf : well_founded ltAB.
  Proof.
    intros [a b].
    puts (ltA_wf a).
    gen b; induction H; intros.
    puts (ltB_wf b).
    induction H1.
    apply Acc_intro; intros.
    destruct y; destruct H3; simpl in H3.
      apply* H0.
    destruct H3.
    subst.
    apply* H2.
  Defined.
End Wf2.

Definition lt2 := ltAB lt lt.

Lemma lt_wf : forall n, Acc lt n.
Proof.
  induction n; apply Acc_intro; intros.
    elim (le_Sn_O _ H).
  unfold lt in H.
  destruct (Lt.le_lt_or_eq _ _ (Le.le_S_n _ _ H)).
    apply (Acc_inv IHn _ H0).
  subst*.
Defined.

Definition lt2_wf := ltAB_wf lt_wf lt_wf.

Definition Acc_lt2_lt : forall a b c d,
  c < a -> Acc lt2 (a,b) -> Acc lt2 (c,d).
  intros.
  apply (Acc_inv H0).
  left; simpl*.
Defined.

Definition Acc_lt2_le : forall a b c d,
  c <= a -> d < b -> Acc lt2 (a,b) -> Acc lt2 (c,d).
  intros.
  apply (Acc_inv H1).
  destruct H; [right|left]; simpl*.
  auto with arith.
Defined.

Definition size_pairs2 S K pairs :=
  (size_pairs S K pairs, pairs_size S pairs).

Definition Accu S K pairs :=
  Acc lt2 (size_pairs2 S K pairs).

Definition typ_subst_res : forall S (HS:is_subst S) T0,
  sig (fun T => disjoint (dom S) (typ_fv T) /\ typ_subst S T0 = T).
  intros S HS T0.
  exists* (typ_subst S T0).
Qed.

Definition pairs_inv_spec S K pairs pairs0 T1 T1' T2 T2' pairs' :=
   Accu S K pairs0 ->
   List.map (pair_subst S) pairs0 = (T1,T2)::List.map (pair_subst S) pairs ->
   T1 = T1' -> T2 = T2' ->
   Accu S K pairs'.

Lemma pairs_inv_tl : forall S K pairs pairs0 T1 T1' T2 T2',
  pairs_inv_spec S K pairs pairs0 T1' T1 T2' T2 pairs.
Proof.
  introv P eq eq1 eq2.
  unfold Accu, size_pairs2, pairs_size, size_pairs, really_all_fv, all_fv in *.
  rewrite eq in P; simpl in P.
  rewrite eq1 in P; rewrite eq2 in P; simpl in P.
  refine (Acc_lt2_le _ _ P).
    apply le_n_S.
    apply* cardinal_subset.
  auto with arith.
Defined.

Lemma pairs_eq : forall pairs T1 T1' T2 T2' pairs0 S,
  T1 = T1' -> T2 = T2' ->
  List.map (pair_subst S) pairs0 = (T1,T2)::List.map (pair_subst S) pairs ->
  List.map (pair_subst S) pairs0 = (T1',T2')::List.map (pair_subst S) pairs.
Proof.
  intros.
  rewrite <- H. rewrite* <- H0.
Qed.

Lemma typ_fv_arrow : forall T11 T12 T21 T22 L,
  (typ_fv T11 \u typ_fv T21 \u (typ_fv T12 \u typ_fv T22 \u L)) =
  (typ_fv (typ_arrow T11 T12) \u typ_fv (typ_arrow T21 T22) \u L).
Proof.
  intros; simpl. repeat rewrite union_assoc.
  rewrite <- (union_assoc (typ_fv T11)).
  rewrite (union_comm (typ_fv T21)).
  repeat rewrite union_assoc. auto.
Qed.

Lemma pairs_inv_arrow : forall S K pairs pairs0 T11 T12 T1' T21 T22 T2',
  is_subst S ->
  disjoint (dom S) (typ_fv T1') ->
  disjoint (dom S) (typ_fv T2') ->
  pairs_inv_spec S K pairs pairs0 T1' (typ_arrow T11 T12) T2'
    (typ_arrow T21 T22) ((T11,T21)::(T12,T22)::pairs).
Proof.
  introv HS D1 D2. intros P eq eq1 eq2.
  unfold Accu, size_pairs2, pairs_size, size_pairs, really_all_fv, all_fv in *.
  rewrite eq in P; simpl in *. 
  rewrite typ_fv_arrow.
  puts (f_equal (typ_subst S) eq1). simpl in H. rewrite <- H. clear H.
  puts (f_equal (typ_subst S) eq2). simpl in H. rewrite <- H. clear H.
  do 2 rewrite* (typ_subst_fresh S).
  refine (Acc_lt2_le _ _ P). left*.
  rewrite* <- (typ_subst_fresh S T1').
  rewrite* <- (typ_subst_fresh S T2').
  rewrite eq1; rewrite eq2. simpl.
  omega.
Defined.

Lemma Accu_pairs_nv : forall S K pairs x T,
  ok K ->
  Accu S K ((typ_fvar x,T)::pairs) ->
  disjoint (dom S) (typ_fv T) ->
  disjoint (dom S) {{x}} ->
  x \notin (typ_fv T) ->
  Accu (compose (x ~ T) S) (remove_env K x) pairs.
Proof.
  introv HK h D Dx n.
  refine (Acc_lt2_lt _ _ h).
  apply* size_pairs_decr. apply disjoint_comm; apply* disjoint_union.
Defined.

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

Lemma dom_remove_env : forall (A:Set) v (K:Env.env A),
  ok K -> dom (remove_env K v) = S.remove v (dom K).
Proof.
  induction K; simpl; intros.
    apply eq_ext; intros; split; intro. elim (in_empty H0).
    use (S.remove_3 H0).
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

Lemma neq_notin_fv : forall v v0,
  v <> v0 -> v \notin (typ_fv (typ_fvar v0)).
Proof. simpl*. Qed.
Hint Resolve neq_notin_fv.

Lemma is_subst_compose_var : forall S x y,
  is_subst S -> x <> y -> disjoint (dom S) {{y}} ->
  is_subst (compose (x ~ typ_fvar y) S).
Proof.
  intros.
  apply* add_binding_is_subst.
Qed.

Lemma disjoint_eq : forall L T1 T2,
  T1 = T2 -> disjoint L (typ_fv T1) -> disjoint L (typ_fv T2).
Proof. intros; rewrite* <- H. Qed.

Definition proj1a (A B:Prop) (P : A /\ B) :=
  let (PA,_) := P in PA.
Definition proj2a (A B:Prop) (P : A /\ B) :=
  let (_,PB) := P in PB.

Lemma Accu_pairs_eq : forall S T1 T1' T2 T2' K pairs pairs',
  is_subst S ->
  List.map (pair_subst S) pairs = (T1,T2)::List.map (pair_subst S) pairs' ->
  disjoint (dom S) (typ_fv T1) -> disjoint (dom S) (typ_fv T2) ->
  T1 = T1' -> T2 = T2' ->
  Accu S K pairs ->
  Accu S K ((T1',T2')::pairs').
Proof.
  unfold Accu, size_pairs2, pairs_size, size_pairs, really_all_fv, all_fv.
  introv HS; intros eq D1 D2 eq1 eq2 h.
  rewrite eq in h.
  rewrite <- eq1; rewrite <- eq2.
  simpl.
  rewrite (typ_subst_fresh _ T1 D1).
  rewrite (typ_subst_fresh _ T2 D2).
  assumption.
Defined.

Lemma Accu_pairs_comm : forall S T1 T2 K pairs,
  Accu S K ((T1,T2)::pairs) ->
  Accu S K ((T2,T1)::pairs).
Proof.
  intros.
  unfold Accu, size_pairs2.
  rewrite size_pairs_comm.
  unfold pairs_size. simpl.
  rewrite (plus_comm (typ_size _)).
  assumption.
Defined.

Lemma unify_vars_kok : forall K x y pairs K',
  unify_vars K x y = Some (K', pairs) -> ok K -> ok K'.
Proof.
  intros until K'.
  unfold unify_vars.
  destruct (unify_kinds (get_kind x K) (get_kind y K));
    intros; try discriminate.
  destruct p. inversions H.
  apply* ok_cons.
  rewrite* dom_remove_env.
Qed.

Definition unify_vars_res K x y S pairs:
  is_subst S -> ok K ->
  disjoint (dom S) {{x}} ->
  disjoint (dom S) {{y}} ->
  x <> y ->
  sumor (sig (fun Kp:kenv*list(typ*typ) =>
    unify_vars K x y = Some Kp /\
    let (K',l) := Kp in let S' := compose (x ~ typ_fvar y) S in
    is_subst S' /\ ok K' /\ size_pairs S' K' (l ++ pairs) <
      size_pairs S K ((typ_fvar x,typ_fvar y)::pairs)))
    (unify_vars K x y = None).
Proof.
  introv HS HK Dx Dy dxy.
  case_eq (unify_vars K x y); intros.
    left. exists p. split*.
    destruct p as [K' pairs'].
    split. apply* is_subst_compose_var.
    split. apply* unify_vars_kok.
    unfold unify_vars in H.
    case_rewrite R (unify_kinds (get_kind x K) (get_kind y K)).
    destruct p.
    inversions H.
    env_fix.
    apply* size_pairs_decr_vars.
  right*.
Qed.

Definition unify_nv K x T (f : x \notin typ_fv T -> option (kenv * subs)) :=
  match in_dec (typ_fv T) x with
  | left _  => None
  | right n =>
    match get_kind x K with
    | Some _ => None
    | None => f n
    end
  end.

Fixpoint unify (pairs:list(typ*typ)) (K:kenv) (S:subs)
  (HS:is_subst S) (HK:ok K) (h:Accu S K pairs)
  {struct h} : option (kenv * subs) :=
  match pairs as pairs0 return
    List.map (pair_subst S) pairs = List.map (pair_subst S) pairs0 ->
    option (kenv * subs)
  with
  | nil => fun _ => Some (K,S)
  | (T1,T2) :: pairs' => fun eq =>
    let DT1 := typ_subst_res HS T1 in
    let DT2 := typ_subst_res HS T2 in
    let D1 := proj2_sig DT1 in let D2 := proj2_sig DT2 in
    let eq := pairs_eq _ _ _ (proj2 D1) (proj2 D2) eq in
    let ST1 := proj1_sig DT1 in let ST2 := proj1_sig DT2 in
    match  ST1 as T1', ST2 as T2'
    return ST1 = T1' -> ST2 = T2' -> option (kenv*subs) with
    | typ_bvar n, typ_bvar m => fun eq1 eq2 =>
      if n === m then
        unify HS HK (pairs_inv_tl _ h eq eq1 eq2)
      else None
    | typ_fvar x, typ_fvar y => fun eq1 eq2 =>
      match x == y with
      | left _ =>
        unify HS HK (pairs_inv_tl _ h eq eq1 eq2)
      | right dxy =>
        match @unify_vars_res K x y S pairs' HS HK
          (disjoint_eq eq1 (proj1 D1)) (disjoint_eq eq2 (proj1 D2)) dxy with
        | inleft (exist (K',l) (conj _ (conj HS' (conj HK' Hlt)))) =>
          unify HS' HK'
            (Acc_lt2_lt _ Hlt
              (Accu_pairs_eq _ HS eq (proj1 D1) (proj1 D2) eq1 eq2 h))
        | inright _ => None
        end
      end
    | typ_fvar x, T => fun eq1 eq2 =>
      let D1 := proj1 D1 in let D2 := proj1 D2 in
      unify_nv K T (fun n =>
        @unify pairs' (remove_env K x) _
        (add_binding_is_subst _ HS (disjoint_eq eq2 D2) n)
        (ok_remove_env _ HK)
        (Accu_pairs_nv HK (Accu_pairs_eq _ HS eq D1 D2 eq1 eq2 h)
          (disjoint_eq eq2 D2) (disjoint_eq eq1 D1) n))
    | T, typ_fvar x => fun eq1 eq2 =>
      let D1 := proj1 D1 in let D2 := proj1 D2 in
      unify_nv K T (fun n =>
        @unify pairs' (remove_env K x) _
        (add_binding_is_subst _ HS (disjoint_eq eq1 D1) n)
        (ok_remove_env _ HK)
        (Accu_pairs_nv HK
          (Accu_pairs_comm (Accu_pairs_eq _ HS eq D1 D2 eq1 eq2 h))
          (disjoint_eq eq1 D1) (disjoint_eq eq2 D2) n))
    | typ_arrow T11 T12, typ_arrow T21 T22 => fun eq1 eq2 =>
      let D1 := disjoint_eq eq1 (proj1 D1) in
      let D2 := disjoint_eq eq2 (proj1 D2) in
      let eq := pairs_eq _ _ _ eq1 eq2 eq in
      unify HS HK
        (pairs_inv_arrow _ HS D1 D2 h eq (refl_equal _) (refl_equal _))
    | _, _ => fun _ _ =>
      None
    end (refl_equal ST1) (refl_equal ST2)
  end (refl_equal (List.map (pair_subst S) pairs)).

Lemma normalize_unify : forall pairs K S HS HK h,
  @unify pairs K S HS HK h = @unify pairs K S HS HK (lt2_wf _).
Proof.
  intros.
  apply f_equal.
  apply ProofIrrelevance.proof_irrelevance.
Qed.

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

Definition id := Env.empty (A:=typ).

Lemma typ_subst_id : forall T, typ_subst id T = T.
Proof.
  intro.
  apply typ_subst_fresh.
  simpl. intro; auto.
Qed.

Lemma is_subst_id : is_subst id.
Proof.
  unfold id, is_subst. intro; intros. elim H.
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

Lemma normalize_Acc_intro : forall (a b:nat) h,
  Acc_intro (a,b) h = Acc_intro (a,b) (Acc_inv (lt2_wf (a,b))).
Proof.
  intros; apply f_equal. apply ProofIrrelevance.proof_irrelevance.
Qed.

Lemma lt2_le : forall a b c d,
  a <= c -> b < d -> lt2 (a,b) (c,d).
Proof.
  intros; destruct H. right; simpl*. left; simpl; omega.
Qed.

Lemma size_pairs2_tl : forall S K pairs p,
  lt2 (size_pairs2 S K pairs) (size_pairs2 S K (p :: pairs)).
Proof.
  intros.
  apply lt2_le.
    unfold size_pairs2, size_pairs, really_all_fv, all_fv; simpl.
    apply le_n_S. apply cardinal_subset. auto.
  unfold pairs_size; simpl. omega.
Qed.

Lemma size_pairs2_comm : forall S K T1 T2 pairs,
  size_pairs2 S K ((T1,T2)::pairs) = size_pairs2 S K ((T2,T1)::pairs).
Proof.
  intros. unfold size_pairs2. rewrite size_pairs_comm.
  unfold pairs_size; simpl. rewrite* (plus_comm (typ_size (typ_subst S T1))).
Qed.

Lemma size_pairs2_nv : forall S K T1 T2 v T pairs,
  is_subst S -> ok K ->
  typ_subst S T1 = typ_fvar v ->
  typ_subst S T2 = T ->
  v \notin typ_fv T ->
  lt2 (size_pairs2 (compose (v ~ T) S) (remove_env K v) pairs)
    (size_pairs2 S K ((T1, T2) :: pairs)).
Proof.
  left. simpl.
  unfold size_pairs at 2, size_pairs, really_all_fv, all_fv; simpl.
  rewrite* <- (typ_subst_idem T1 H).
  rewrite* <- (typ_subst_idem T2 H).
  rewrite H1; rewrite H2.
  puts size_pairs_decr.
  apply* (@size_pairs_decr v T K S pairs).
    apply* typ_subst_res_fresh'.
  apply disjoint_comm; apply* disjoint_union.
Qed.

Lemma size_pairs2_arrow : forall S K T1 T2 t t0 t1 t2 pairs,
  is_subst S ->
  typ_subst S T1 = typ_arrow t1 t2 ->
  typ_subst S T2 = typ_arrow t t0 ->
  lt2 (size_pairs2 S K ((t1, t) :: (t2, t0) :: pairs))
     (size_pairs2 S K ((T1, T2) :: pairs)).
Proof.
  intros.
  unfold size_pairs2, size_pairs, really_all_fv, all_fv, pairs_size; simpl.
  rewrite <- (typ_subst_idem T1 H).
  rewrite <- (typ_subst_idem T2 H).
  rewrite H0; rewrite H1.
  right; simpl; split.
    repeat rewrite union_assoc.
    rewrite <- (union_assoc _ (typ_fv (typ_subst S t))).
    rewrite <- (union_comm _ (typ_fv (typ_subst S t))).
    rewrite* union_assoc.
  omega.
Qed.

Hint Resolve size_pairs2_tl size_pairs2_nv size_pairs2_arrow.

Section Soundness.

Variables (K':kenv) (S':subs).

Lemma unify_ind : forall (P : kenv -> subs -> list (typ * typ) -> Prop),
  (is_subst S' -> P K' S' nil) ->
  (forall pairs K T S v t t0 (HS:is_subst S) (HK:ok K),
    let S1 := compose (v ~ T) S in
    let K1 := remove_env K v in
    forall HS1 HK1 h,
    @unify pairs K1 S1 HS1 HK1 h = Some (K', S') ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = T ->
    v \notin typ_fv T -> get_kind v K = None ->
    P K1 S1 pairs -> P K S ((t,t0)::pairs)) ->
  (forall pairs K S v v0 k l t t0 (HS:is_subst S) (HK:ok K),
    let S1 := compose (v ~ typ_fvar v0) S in
    let K1 := remove_env (remove_env K v) v0 & v0 ~ k in
    forall HS1 HK1 h,
    unify_kinds (get_kind v K) (get_kind v0 K) = Some (k, l) ->
    @unify (l ++ pairs) K1 S1 HS1 HK1 h = Some (K', S') ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = typ_fvar v0 ->
    v <> v0 ->
    P K1 S1 (l ++ pairs) -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs n HS HK h,
    @unify pairs K S HS HK h  = Some (K', S') ->
    typ_subst S t = typ_bvar n ->
    typ_subst S t0 = typ_bvar n ->
    P K S pairs -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs v HS HK h,
    @unify pairs K S HS HK h = Some (K', S') ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = typ_fvar v ->
    P K S pairs -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs t1 t2 t3 t4 (HS:is_subst S) (HK:ok K) h,
    @unify ((t1,t3)::(t2,t4)::pairs) K S HS HK h = Some (K',S') ->
    typ_subst S t = typ_arrow t1 t2 ->
    typ_subst S t0 = typ_arrow t3 t4 ->
    P K S ((t1,t3)::(t2,t4)::pairs) -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs,
    P K S ((t,t0)::pairs) -> P K S ((t0,t)::pairs)) ->
  forall pairs K S HS HK h,
    @unify pairs K S HS HK h = Some (K', S') ->
    P K S pairs.
Proof.
  introv Hnil Hnv Hvars Hbv Hfv. intros Harr Hsw. intros until S.
  pose (h1 := (size_pairs S K pairs + 1, pairs_size S pairs)).
  assert (lt2 (size_pairs2 S K pairs) h1)
    by (unfold h1, size_pairs2, size_pairs; left; simpl; omega).
  clearbody h1; gen pairs K S.
  induction h1 using (well_founded_ind lt2_wf); simpl; intros until h.
  rewrite normalize_unify.
  destruct pairs as [|[T1 T2]]; intro HU.
    simpl in HU.
    inversions HU.
    auto.
  revert HU.
  simpl lt2_wf.
  rewrite normalize_Acc_intro.
  lazy [unify]; fold unify.
  destruct (typ_subst_res HS T1) as [ST1 [D1 eq1]].
  destruct (typ_subst_res HS T2) as [ST2 [D2 eq2]].
  simpl proj1_sig; simpl proj2_sig.
  simpl pairs_eq.
  revert D1 eq1 D2 eq2.
  case ST1; case ST2; intros; try discriminate.
        destruct (n0===n); try discriminate.
        subst. apply* Hbv.
       unfold unify_nv in HU.
       destruct (in_dec (typ_fv (typ_bvar n)) v). discriminate.
       case_rewrite R1 (get_kind v K).
       rewrite normalize_unify in HU.
       apply Hsw.
       apply* Hnv.
       apply* H. rewrite* size_pairs2_comm.
      unfold unify_nv in HU.
      destruct (in_dec (typ_fv (typ_bvar n)) v). discriminate.
      case_rewrite R1 (get_kind v K).
      rewrite normalize_unify in HU.
      apply* Hnv.
     destruct (v0 == v).
       subst v0. rewrite normalize_unify in HU.
       apply* Hfv.
     destruct (unify_vars_res pairs HS HK
           (disjoint_eq (refl_equal (typ_fvar v0)) (proj41 conj D1 eq1))
           (disjoint_eq (refl_equal (typ_fvar v)) (proj41 conj D2 eq2)) n);
       try discriminate.
     destruct s as [[K1 l] [eq [HS1 [HK1 Hlt]]]].
     rewrite normalize_unify in HU.
     unfold unify_vars in eq.
     case_rewrite R1 (unify_kinds (get_kind v0 K) (get_kind v K)).
     destruct p.
     inversions eq.
     apply* Hvars.
     apply* H. left; simpl.
     unfold size_pairs at 2, really_all_fv, all_fv. simpl accum.
     rewrite eq1; rewrite eq2.
     rewrite <- (typ_subst_fresh _ (typ_fvar v0) D1).
     rewrite <- (typ_subst_fresh _ (typ_fvar v) D2) at 2.
     auto.
    unfold unify_nv in HU.
    destruct (in_dec (typ_fv (typ_arrow t t0)) v). discriminate.
    case_rewrite R1 (get_kind v K).
    rewrite normalize_unify in HU.
    apply* Hnv.
   unfold unify_nv in HU.
   destruct (in_dec (typ_fv (typ_arrow t t0)) v). discriminate.
   case_rewrite R1 (get_kind v K).
   rewrite normalize_unify in HU.
   apply Hsw.
   apply* Hnv.
   apply* H.
   rewrite* size_pairs2_comm.
  rewrite normalize_unify in HU.
  apply* Harr.
Qed.

Lemma unify_keep : forall pairs K S HS HK h,
  @unify pairs K S HS HK h = Some (K', S') ->
  is_subst S' /\
  forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'.
Proof.
  intros.
  apply* (unify_ind
    (fun K S _ => is_subst S' /\
      forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'));
    clear; intros.
    destruct H4; split*.
    intros. apply H5.
    unfold S1. apply* binds_add_binding.
  intros.
  intuition.
  apply H6; unfold S1. apply* binds_add_binding.
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

Lemma typ_subst_extend : forall pairs K S HS HK h,
  @unify pairs K S HS HK h = Some (K', S') ->
  extends S' S.
Proof.
  intros.
  destruct* (unify_keep _ _ _ H).
  clear H.
  intro.
  induction T. simpl*.
    remember (typ_subst S (typ_fvar v)) as T'.
    use (f_equal (typ_subst S) HeqT').
    rewrite typ_subst_idem in H; auto.
    simpl in H.
    case_rewrite R (get v S).
      subst.
      use (H1 _ _ R).
      rewrite* (binds_typ_subst H).
    simpl in HeqT'. rewrite R in HeqT'. subst*.
  simpl. congruence.
Qed.

Hint Resolve typ_subst_extend.

Theorem unify_types : forall pairs K S HS HK h,
  @unify pairs K S HS HK h = Some (K',S') ->
  unifies S' pairs.
Proof.
  intros.
  apply* (unify_ind (fun _ _ => unifies S')); intros;
    intro; simpl; intros; intuition;
    try (unfold S1 in *; inversions H7; clear H7);
    try (inversions H5; clear H5;
      rewrite <- (typ_subst_extend _ _ _ H0);
      rewrite <- (typ_subst_extend _ _ _ H0 T2);
      rewrite H1; rewrite* H2).
        rewrite <- (typ_subst_extend _ _ _ H0).
        rewrite <- (typ_subst_extend _ _ _ H0 T2).
        rewrite typ_subst_compose. rewrite H1.
        simpl. destruct* (v == v).
        rewrite typ_subst_compose.
        rewrite* (typ_subst_fresh (v ~ typ_subst S0 T2)).
        simpl. intro x; destruct* (x == v).
      rewrite <- (typ_subst_extend _ _ _ H1).
      rewrite <- (typ_subst_extend _ _ _ H1 T2).
      unfold S1; do 2 rewrite typ_subst_compose.
      rewrite H2; rewrite H3.
      simpl. destruct* (v == v). destruct* (v0 == v).
    simpl.
    rewrite* (H3 t1 t3).
    rewrite* (H3 t2 t4).
  inversions H2.
  symmetry.
  apply* H0.
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

Lemma unify_kind_rel_keep : forall kr kr' uniq pairs k' l,
  unify_kind_rel kr kr' uniq pairs = (k', l) ->
  incl kr' k' /\ incl pairs l.
Proof.
  induction kr; simpl; intros. inversions H. split*.
  destruct a.
  case_rewrite R (uniq v).
    case_rewrite R1 (get v kr'); destruct* (IHkr _ _ _ _ _ H).
  destruct* (IHkr _ _ _ _ _ H).
Qed.

Lemma unify_kind_rel_incl : forall kr pairs uniq S kr0 kr' pairs',
  unify_kind_rel kr0 kr' uniq pairs' = (kr, pairs) ->
  unifies S pairs ->
  incl (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT))) kr0)
    (List.map (fun XT : var * typ => (fst XT, typ_subst S (snd XT))) kr).
Proof.
  induction kr0; intros; intros T HT. elim HT.
  destruct T.
  destruct a.
  simpl in *.
  case_rewrite R (uniq v0);
    try case_rewrite R1 (get v0 kr'); simpl in HT; destruct HT;
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
     destruct (Cstr.valid_dec (Cstr.lub kc kc0)); try discriminate.
     case_eq (unify_kind_rel (kr ++ kr0) nil (Cstr.unique (Cstr.lub kc kc0))
       nil); intros l0 l1 R1.
     inversions H; clear H.
     rewrite R1 in *.
     use (unify_kind_rel_incl _ _ _ _ R1 H0).
     destruct (proj2 (Cstr.entails_lub kc kc0 _) (Cstr.entails_refl _)).
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

Lemma unify_kinds_subst : forall k1 k2 k3 l S,
  unify_kinds k1 k2 = Some (k3, l) ->
  unify_kinds (kind_subst S k1) (kind_subst S k2) =
  Some (kind_subst S k3,
        List.map (fun T => (typ_subst S (fst T), typ_subst S (snd T))) l).
Proof.
  intros.
  destruct k1 as [[kc1 kv1 kr1 kh1]|]; destruct k2 as [[kc2 kv2 kr2 kh2]|];
    simpl in *; try solve [inversions* H].
  destruct (Cstr.valid_dec (Cstr.lub kc1 kc2)); try discriminate.
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
  clear kh1 kh2.
  apply injective_projections; simpl; try apply kind_pi; simpl*;
    pattern kr at 1; rewrite H;
    pattern pairs at 1; rewrite H0; clear H H0;
    gen kr pairs; induction (kr1++kr2); intros; simpl*; destruct a;
    simpl; destruct (Cstr.unique (Cstr.lub kc1 kc2) v0);
    try rewrite* <- IHl;
    case_eq (get v0 kr); intros; rewrite <- IHl;
    repeat rewrite map_snd_env_map;
    try rewrite* (binds_map (typ_subst S) H);
    rewrite* (map_get_none (typ_subst S) _ _ H).
Qed.

Lemma well_subst_unify : forall k1 l v v0 S K pairs HS1 HK1 h,
  @unify (l ++ pairs) (remove_env (remove_env K v) v0 & v0 ~ k1)
    (compose (v ~ typ_fvar v0) S) HS1 HK1 h = Some (K', S') ->
  unify_kinds (get_kind v K) (get_kind v0 K) = Some (k1, l) ->
  v # S ->
  well_subst (remove_env (remove_env K v) v0 & v0 ~ k1)
     (map (kind_subst S') K') S' ->
  well_subst K (map (kind_subst S') K') S'.
Proof.
  intros until h; intros H HU Hv WS x; intros.
  unfold well_subst in WS.
  poses Hext (typ_subst_extend _ _ _ H).
  poses Hunif (unify_types _ _ _ H).
  assert (Hunif': unifies S' l) by (intro; intros; auto).
  clear HS1 HK1 H h.
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

Lemma unify_kinds_ok : forall pairs K S HS HK h,
  @unify pairs K S HS HK h = Some (K',S') ->
  disjoint (dom S) (dom K) ->
  ok K' /\ disjoint (dom S') (dom K') /\
  well_subst K (map (kind_subst S') K') S'.
Proof.
  intros until h; intro H.
  apply* (unify_ind (fun K S pairs =>
    ok K -> disjoint (dom S) (dom K) ->
    ok K' /\ disjoint (dom S') (dom K') /\
    well_subst K (map (kind_subst S') K') S'));
    clear H HS h pairs K S HK.
      intuition.
      intro; intros.
      rewrite* typ_subst_fresh.
        destruct* k.
        use (binds_map (kind_subst S') H2).
        simpl in *; apply* wk_kind. apply entails_refl.
      simpl; intro. destruct* (x == Z). subst.
      destruct* (H1 Z).
      elim (binds_fresh H2 H3).
    intros until h.
    intros H R1 R2 n R3 IHh _ Dis.
    unfold S1, K1 in *; clear S1 K1.
    destruct* IHh.
    intuition.
    clear -R3 H3.
    intro; intros.
    destruct (Z == v).
      subst.
      rewrite (binds_get_kind H) in R3. subst*.
    use (H3 _ _ (binds_remove_env H n)).
  intros until h.
  intros R3 H R1 R2 n IHh _ Dis.
  unfold S1, K1 in *; clear S1 K1.
  destruct* IHh.
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
    rewrite <- (binds_typ_subst (in_ok_binds _ _ H1 H0)).
    apply* typ_subst_idem.
  clear HeqS0 H.
  induction S0. auto.
  inversions H0.
  simpl. rewrite (H1 x a0).
    rewrite* IHS0.
    intro; intros.
    apply (H1 x0 a).
    simpl.
    destruct* (x0 == x).
  simpl*.
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

Lemma unify_mgu_nv : forall K0 S0 pairs K S t t0 v T,
  let S1 := compose (v ~ T) S0 in
  let K1 := remove_env K0 v in
  forall HK1 HS1 h,
  @unify pairs K1 S1 HS1 HK1 h = Some (K, S) ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  is_subst S0 ->
  ok K0 ->
  get_kind v K0 = None ->
  mgu_spec K S K1 S1 pairs ->
  mgu_spec K S K0 S0 ((t, t0) :: pairs).
Proof.
  intros until h; unfold K1, S1 in *; clear K1 S1.
  intros HU R1 R2 HS0 HK0 R4 IHh Hext Heq WS.
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
  destruct (Cstr.entails_lub kc kc0 kc').
  use (H3 (conj H H0)).
  use (Cstr.entails_valid H5 kv').
  destruct* (Cstr.valid_dec (Cstr.lub kc kc0)).
  esplit. esplit. split. reflexivity.
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
  case_eq (Cstr.unique (Cstr.lub kc kc0) v0); introv R.
    puts (Cstr.entails_unique H5 R).
    case_eq (get v0 krs); [intros t0 R1|intros R1].
      assert (unifies S ((t,t0)::pairs)).
        intro; simpl; intros.
        destruct H1; [|auto*].
        inversions H1; clear H1.
        apply* (kh' v0).
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

Definition typ_kind K T :=
  match T with
  | typ_fvar x => get_kind x K
  | _  => None
  end.

Lemma well_kinded_kind_entails: forall K k T,
  well_kinded K k T -> kind_entails (typ_kind K T) k.
Proof.
  intros; unfold kind_entails.
  inversions H. auto.
  simpl.
  rewrite* (binds_get_kind H0).
Qed.

Lemma well_kinded_typ_kind : forall K T,
  well_kinded K (typ_kind K T) T.
Proof.
  destruct T; auto.
  simpl.
  apply well_kinded_get_kind.
Qed.

Lemma unify_vars_complete : forall v0 v K0,
  ok K0 ->
  typ_subst S' (typ_fvar v0) = typ_subst S' (typ_fvar v) ->
  well_subst K0 K' S' ->
  exists K, exists l,
    unify_vars K0 v0 v = Some (K, l) /\ unifies S' l /\
    well_subst K K' S'.
Proof.
  introv HK0 Heq WS.
  unfold unify_vars.
  puts (well_kinded_kind_entails (well_subst_get_kind v0 WS)).
  puts (well_kinded_kind_entails (well_subst_get_kind v WS)).
  rewrite Heq in H.
  destruct* (unify_kinds_complete _ _ _ _ H H0) as [k [l [HU [Heq' Hke]]]].
  rewrite HU; clear HU.
  esplit; esplit; split*.
  split*.
  intro; intros.
  unfold binds in H1; simpl in H1. destruct (Z == v). inversions H1.
    apply* kind_entails_well_kinded.
    apply well_kinded_typ_kind.
  apply WS.
  puts (binds_orig_remove_env _ (ok_remove_env v0 HK0) H1).
  apply* binds_orig_remove_env.
Qed.

Lemma unify_mgu_vars : forall K0 S0 pairs K S t t0 v v0 k l,
  let S1 := compose (v ~ typ_fvar v0) S0 in
  let K1 := remove_env (remove_env K0 v) v0 & v0 ~ k in
  forall HS1 HK1 h,
  unify_kinds (get_kind v K0) (get_kind v0 K0) = Some (k, l) ->
  @unify (l ++ pairs) K1 S1 HS1 HK1 h = Some (K, S) ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = typ_fvar v0 ->
  is_subst S0 -> ok K0 -> v <> v0 ->
  mgu_spec K S K1 S1 (l ++ pairs) -> mgu_spec K S K0 S0 ((t, t0) :: pairs).
Proof.
  intros until h; unfold S1 in *; clear S1.
  intros R4 HU R1 R2 HS0 HK0 n IHh Hext Heq WS.
  assert (Heq0: typ_subst S' (typ_fvar v) = typ_subst S' (typ_fvar v0)).
    rewrite <- R1; rewrite <- R2. do 2 rewrite Hext. auto.
  destruct* (unify_vars_complete v v0 HK0) as [K2 [l' [HU' [Heq' Hke]]]].
  unfold unify_vars in HU'.
  rewrite R4 in HU'.
  inversions HU'; clear HU'.
  simpl in K1. fold K1 in Hke.
  apply* IHh.
    intro. rewrite* typ_subst_compose.
    rewrite* typ_subst_prebind.
  intro; intros.
  destruct* (in_app_or _ _ _ H).
Qed.


Lemma unifies_tl : forall S p pairs,
  unifies S (p::pairs) -> unifies S pairs.
Proof.
  intros; intro; intros; apply* H.
Qed.
Hint Resolve unifies_tl.

Lemma unify_mgu0 : forall pairs K0 S0 HS0 HK0 h K S,
  @unify pairs K0 S0 HS0 HK0 h = Some (K,S) ->
  mgu_spec K S K0 S0 pairs.
Proof.
  intros.
  apply* (unify_ind (K':=K) (S':=S) (mgu_spec K S));
    clear H K0 S0 HS0 HK0 pairs h.
        unfold mgu_spec; auto*.
       intros; unfold K1, S1 in *; apply* unify_mgu_nv.
      intros; unfold K1, S1 in *; apply* unify_mgu_vars.
     unfold mgu_spec; intros; apply* H2.
    unfold mgu_spec; intros; apply* H2.
   unfold mgu_spec; intros. apply* H2.
   assert (Heq: typ_subst S' t = typ_subst S' t0).
     apply* H4.
   rewrite <- (H3 t) in Heq.
   rewrite <- (H3 t0) in Heq.
   rewrite H0 in Heq; rewrite H1 in Heq; simpl in Heq.
   inversions Heq.
   intro; intros.
   destruct H6. inversions* H6.
   destruct* H6. inversions* H6.
  unfold mgu_spec; intros.
  apply* H.
  intro; intros.
  destruct* H3.
  inversions H3. symmetry; apply* H1.
Qed.

Theorem unify_mgu : forall T1 T2 K0 HK0 h K S,
  @unify ((T1,T2)::nil) K0 id is_subst_id HK0 h = Some (K, S) ->
  typ_subst S' T1 = typ_subst S' T2 ->
  well_subst K0 K' S' ->
  (forall T3 T4,
    typ_subst S T3 = typ_subst S T4 -> typ_subst S' T3 = typ_subst S' T4) /\
  well_subst K K' S'.
Proof.
  intros.
  destruct* (unify_mgu0 is_subst_id HK0 h H).
      intro. rewrite* typ_subst_id.
    intro; simpl; intros.
    destruct* H2.
    inversions* H2.
  split*.
  intros.
  rewrite <- (H2 T3).
  rewrite <- (H2 T4).
  rewrite* H4.
Qed.

End Mgu.

Section Completeness.

Variables (K:kenv) (S:subs).

Definition complete_spec K0 S0 pairs :=
  forall HS0 HK0 h,
  extends S S0 ->
  unifies S pairs ->
  well_subst K0 K S ->
  @unify pairs K0 S0 HS0 HK0 h <> None.

Lemma unify_complete_nv : forall pairs K0 S0 v T DT h t t0
  (HS0:is_subst S0) (HK0:ok K0),
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  well_subst K0 K S ->
  (forall K S,
    lt2 (size_pairs2 S K pairs) (size_pairs2 S0 K0 ((t, t0) :: pairs)) ->
    complete_spec K S pairs) ->
  extends S S0 ->
  unifies S ((t, t0) :: pairs) ->
  (forall x, T <> typ_fvar x) ->
  unify_nv K0 T (fun n0 : v \notin typ_fv T =>
    unify (pairs:=pairs) (add_binding_is_subst T HS0 (DT n0) n0)
    (ok_remove_env v HK0) (h n0))
  <> None.
Proof.
  intros until HK0; intros R1 R2 WS IHh Hext Heq HT.
  unfold unify_nv.
  assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
  puts (Heq _ _ H); clear H.
  rewrite <- Hext in H0; rewrite R1 in H0.
  rewrite <- (Hext t0) in H0; rewrite R2 in H0.
  destruct (in_dec (typ_fv T) v).
    elimtype False.
    clear -H0 HT i.
    destruct T. elim (in_empty i).
      elim (HT v); rewrite* (S.singleton_1 i).
    assert (1 < typ_size (typ_arrow T1 T2)).
      destruct T1; simpl; omega.
    use (typ_subst_no_cycle S _ i H).
    rewrite H0 in H1; omega.
  intro.
  case_rewrite R3 (get_kind v K0).
    poses Wk (WS _ _ (get_kind_binds _ _ R3)).
    rewrite H0 in Wk.
    simpl in Wk; inversions Wk.
    clear -H2 HT.
    destruct (typ_subst S0 t0); try discriminate.
    elim (HT v). auto.
  refine (IHh _ _ _ _ _ _ _ _ _ H); auto*.
      intro. rewrite* typ_subst_compose.
      rewrite typ_subst_prebind. apply Hext. congruence.
    intro; auto*.
  intro; intros.
  destruct k; try (simpl; apply wk_any).
  destruct (v == Z).
    elim (binds_fresh H1).
    rewrite* dom_remove_env. apply* S.remove_1.
  apply WS.
  apply* binds_orig_remove_env.
Qed.

Lemma unify_complete0 : forall pairs K0 S0,
  complete_spec K0 S0 pairs.
Proof.
  intros.
  pose (h1 := (1+size_pairs S0 K0 pairs, pairs_size S0 pairs)).
  assert (Hsz: lt2 (size_pairs2 S0 K0 pairs) h1)
    by (unfold h1, size_pairs2, size_pairs; left; simpl; omega).
  clearbody h1; gen pairs K0 S0.
  induction h1 using (well_founded_ind lt2_wf); simpl; intros.
  intros HS0 HK0 h Hext Heq WS.
  rewrite normalize_unify.
  destruct pairs as [|[T1 T2] pairs]; simpl lt2_wf; rewrite normalize_Acc_intro.
    intro; discriminate.
  assert (Heq0: unifies S pairs) by (intro; auto*).
  lazy [unify]; fold unify.
  destruct (typ_subst_res HS0 T1) as [ST1 [D1 eq1]].
  destruct (typ_subst_res HS0 T2) as [ST2 [D2 eq2]].
  simpl proj1_sig; simpl proj2_sig.
  simpl pairs_eq.
  assert (E: typ_subst S ST1 = typ_subst S ST2).
    rewrite <- eq1; rewrite <- eq2; do 2 rewrite Hext. auto.
  revert D1 eq1 D2 eq2 E.
  case ST1; case ST2; intros; intro HU.
          destruct (n0 === n).
           subst.
           apply* H.
          inversions* E.
         rewrite size_pairs2_comm in Hsz.
         refine (unify_complete_nv _ _ HS0 HK0 eq2 eq1 WS _ _ _ _ HU); auto*.
           intro; simpl; intros. destruct H0; subst.
             inversions* H0; symmetry; apply* Heq.
           apply* Heq.
         intros x Hx; discriminate.
        discriminate.
       refine (unify_complete_nv _ _ HS0 HK0 eq1 eq2 _ _ _ _ _ HU); auto*.
       intros x Hx; discriminate.
      destruct (v0 == v).
       subst.
       apply* H.
      destruct* (unify_vars_complete (K':=K) (S':=S) v0 v HK0)
        as [K' [l' [HU' [Heq' Hke]]]].
      destruct (unify_vars_res pairs HS0 HK0
           (disjoint_eq (refl_equal (typ_fvar v0)) (proj41 conj D1 eq1))
           (disjoint_eq (refl_equal (typ_fvar v)) (proj41 conj D2 eq2)) n).
        destruct s. destruct x.
        gen a.
        intros [e [HS' [Hk Hsz']]].
        rewrite e in HU'. inversions HU'; clear e HU'.
        apply* H.
            left. simpl.
            unfold size_pairs at 2, really_all_fv, all_fv; simpl.
            rewrite <- (typ_subst_idem T1 HS0).
            rewrite <- (typ_subst_idem T2 HS0).
            rewrite eq1; rewrite* eq2.
          intro. rewrite* typ_subst_compose.
          rewrite typ_subst_prebind. apply Hext. symmetry; auto.
        intro; intros. destruct* (in_app_or _ _ _ H0).
      rewrite e in HU'; discriminate.
     refine (unify_complete_nv _ _ HS0 HK0 eq1 eq2 _ _ _ _ _ HU); auto*.
     intro; discriminate.
    discriminate.
   rewrite size_pairs2_comm in Hsz.
   refine (unify_complete_nv _ _ HS0 HK0 eq2 eq1 WS _ _ _ _ HU); auto*.
     intro; simpl; intros. destruct H0; subst.
       inversions H0; symmetry; apply* Heq.
     apply* Heq.
   intros; discriminate.
  refine (H _ _ _ _ _ _ _ _ _ _ _ _ HU); auto*.
  clear HU H; intro; intros.
  inversions E.
  simpl in H; destruct H. inversions* H.
  destruct H. inversions* H.
  apply* Heq.
Qed.

Theorem unify_complete : forall T1 T2 K0 HK0,
  well_subst K0 K S ->
  typ_subst S T1 = typ_subst S T2 ->
  @unify ((T1,T2)::nil) K0 id is_subst_id HK0 (lt2_wf _) <> None.
Proof.
  intros.
  apply* unify_complete0.
    intro; rewrite* typ_subst_id.
  intro; intros; simpl in H1; destruct* H1.
  inversions* H1.
Qed.

End Completeness.

Lemma extends_trans : forall S1 S2 S3,
  extends S1 S2 -> extends S2 S3 -> extends S1 S3.
Proof.
  intros; intro.
  rewrite <- H. rewrite <- (H T).
  rewrite* H0.
Qed.

End MkUnify.