(***************************************************************************
* Principality of unification for mini-ML with structural polymorphism     *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import Arith List Metatheory Cardinal.
Require Import ML_SP_Definitions ML_SP_Eval.

Set Implicit Arguments.

Module MkUnify(Cstr:CstrIntf)(Const:CstIntf).

Module MyEval := MkEval(Cstr)(Const).
Import MyEval.
Import Rename.
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


(** Various properties of substitutions *)

Lemma extends_trans : forall S1 S2 S3,
  extends S1 S2 -> extends S2 S3 -> extends S1 S3.
Proof.
  intros; intro T.
  rewrite <- H. rewrite <- (H T).
  rewrite* H0.
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
  induction T'; simpl; intros; auto.
    destruct* (v == x).
    simpl*.
  forward~ IHT'1 as HT1.
  forward~ IHT'2 as HT2.
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
  simpl in H3. destruct* H3.
  inversions* H3.
Qed.

Hint Resolve add_binding_is_subst.

Lemma typ_subst_disjoint : forall S T,
  is_subst S -> disjoint (dom S) (typ_fv (typ_subst S T)).
Proof.
  intros; induction T; simpl in *; auto.
  case_eq (get v S); intros.
    use (H _ _ (binds_in H0)).
  simpl*.
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

Lemma neq_notin_fv : forall v v0,
  v <> v0 -> v \notin (typ_fv (typ_fvar v0)).
Proof. simpl*. Qed.
Hint Resolve neq_notin_fv.

Lemma is_subst_compose_var : forall S x y,
  is_subst S -> x <> y -> disjoint (dom S) {{y}} ->
  is_subst (compose (x ~ typ_fvar y) S).
Proof.
  intros. auto*.
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
  apply* typ_subst_fresh.
Qed.

Lemma is_subst_id : is_subst id.
Proof.
  unfold id, is_subst. intro; intros. simpl*.
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

(* get a kind safely from a kenv *)

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
Hint Resolve get_kind_binds.

Lemma get_kind_subst : forall S x K,
  get_kind x (map (kind_subst S) K) = kind_subst S (get_kind x K).
Proof.
  unfold get_kind; intros.
  case_eq (get x K); introv R1.
    rewrite* (binds_map (kind_subst S) R1).
  rewrite* (map_get_none (kind_subst S) _ _ R1).
Qed.

(* Decidability of membership *)

Definition decidable (A : Type) (P : A -> Prop) :=
  forall x, {P x}+{~P x}.

Definition in_dec L : decidable (fun x => x \in L).
  intros L x.
  case_eq (S.mem x L); intros. left. exact (S.mem_2 H).
  right. exact (mem_3 H).
Qed.

Section RemoveEnv.
  (* Removing an element from an env *)
  Variable A : Set.

  Fixpoint remove_env (E:Env.env A) (x:var) {struct E} : Env.env A :=
    match E with
    | nil => nil
    | (y,a)::E' =>
      if x == y then E' else (y,a) :: remove_env E' x
    end.

  Lemma map_remove_env : forall x f (E:Env.env A),
    map f (remove_env E x) = remove_env (map f E) x.
  Proof.
    induction E; simpl in *. auto.
    destruct a; simpl.
    destruct (x == v); simpl*.
    rewrite* IHE.
  Qed.

  Lemma fv_in_remove_env : forall (fv:A->vars) x E,
    fv_in fv (remove_env E x) << fv_in fv E.
  Proof.
    induction E; simpl; intros. auto.
    destruct a. destruct* (x == v); simpl*.
  Qed.

  Lemma notin_remove_env : forall x v (E:Env.env A),
    x # E -> x # remove_env E v.
  Proof.
    induction E; simpl; intros. auto.
    destruct a. destruct* (v == v0).
    simpl. apply* notin_union.
  Qed.

  Lemma ok_remove_env : forall v (E:Env.env A),
    ok E -> ok (remove_env E v).
  Proof.
    induction 1; simpl. apply ok_empty.
    destruct* (v == x). 
    apply* ok_cons.
    apply* notin_remove_env.
  Qed.

  Lemma dom_remove_env : forall v (K:Env.env A),
    ok K -> dom (remove_env K v) = S.remove v (dom K).
  Proof.
    induction 1; simpl; intros.
      apply eq_ext; intros; split; intro. elim (in_empty H).
      use (S.remove_3 H).
    destruct (v == x).
      subst.
      rewrite remove_union.
      rewrite remove_single. rewrite* remove_notin. rewrite* union_empty_l.
    simpl.
    rewrite remove_union.
    rewrite IHok.
    rewrite* (@remove_notin v {{x}}).
  Qed.

  Lemma binds_remove_env : forall v K x (a:A),
    binds x a K -> x <> v -> binds x a (remove_env K v).
  Proof.
    unfold binds; induction K; simpl; intros. auto.
    destruct a; simpl in *.
    destruct (x == v0); destruct (v == v0); simpl; subst. elim H0; auto.
        destruct* (v0 == v0).
      auto.
    destruct* (x == v0).
  Qed.

  Lemma binds_orig_remove_env : forall v x (k:A) E,
    ok E -> binds x k (remove_env E v) -> binds x k E.
  Proof.
    unfold binds; induction E; simpl; intros. auto.
    destruct a.
    inversions H.
    destruct (v == v0); simpl in H0.
      subst.
      destruct* (x == v0).
      subst. elim (binds_fresh H0 H5).
    destruct* (x == v0).
  Qed.

  Lemma get_remove_env : forall v (E:Env.env A),
    ok E -> get v (remove_env E v) = None.
  Proof.
    induction 1; simpl; intros. auto.
    destruct (v == x).
      subst. apply* get_notin_dom.
    simpl. destruct* (v == x).
  Qed.

End RemoveEnv.

Hint Resolve ok_remove_env notin_remove_env.

Lemma disjoint_add_binding : forall v T S (K:kenv),
  is_subst S -> ok K ->
  disjoint (dom S) (dom K) ->
  disjoint (dom (compose (v ~ T) S)) (dom (remove_env K v)).
Proof.
  intros.
  rewrite* dom_remove_env.
  unfold compose.
  rewrite dom_concat.
  simpl; rewrite* dom_map.
Qed.

Hint Resolve disjoint_add_binding.

(* ====================================================================== *)
(** Start of the algorithm *)

(* Unification of kinds *)

Fixpoint unify_kind_rel (kr kr':list(Cstr.attr*typ)) (uniq:Cstr.attr -> bool)
  (pairs:list(typ*typ)) {struct kr} :=
  match kr with
  | nil => (kr', pairs)
  | (l,T)::krem =>
    if uniq l then
      match assoc Cstr.eq_dec l kr' with
      | None => unify_kind_rel krem ((l,T)::kr') uniq pairs
      | Some T' => unify_kind_rel krem kr' uniq ((T,T')::pairs)
      end
    else unify_kind_rel krem ((l,T)::kr') uniq pairs
  end.

Lemma unify_coherent : forall kc kr,
  coherent kc (fst (unify_kind_rel kr nil (Cstr.unique kc) nil)).
Proof.
  intros until kr.
  set (kr' := @nil (Cstr.attr*typ)).
  set (pairs' := @nil (typ*typ)).
  assert (coherent kc kr'). intro; intros. elim H0.
  gen kr' pairs'.
  induction kr; simpl; intros. auto.
  destruct a.
  case_eq (Cstr.unique kc a); introv R.
    case_eq (assoc Cstr.eq_dec a kr'); introv R1. apply* IHkr.
    apply IHkr.
    intro; intros.
    simpl in *; destruct H1; [inversions H1|]; destruct H2. inversions* H2.
        elim (assoc_complete _ _ _ _ R1 H2).
      inversions H2; elim (assoc_complete _ _ _ _ R1 H1).
    apply* (H x).
  apply IHkr.
  intro; intros.
  simpl in *.
  destruct (Cstr.eq_dec x a).
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

Inductive unify_kinds_spec
  : kind -> kind -> option (kind*list(typ*typ)) -> Prop :=
  | UKnone1 : forall k, unify_kinds_spec None k (Some (k,nil))
  | UKnone2 : forall k, unify_kinds_spec k None (Some (k,nil))
  | UKok : forall k1 k2 k pairs,
      kind_cstr k = Cstr.lub (kind_cstr k1) (kind_cstr k2) ->
      Cstr.valid (kind_cstr k) ->
      unify_kind_rel (kind_rel k1 ++ kind_rel k2) nil
                     (Cstr.unique (kind_cstr k)) nil = (kind_rel k, pairs) ->
      unify_kinds_spec (Some k1) (Some k2) (Some (Some k, pairs))
  | UKfail : forall k1 k2,
      ~Cstr.valid (Cstr.lub (kind_cstr k1) (kind_cstr k2)) ->
      unify_kinds_spec (Some k1) (Some k2) None.

Lemma unify_kinds_spec_ok : forall k1 k2,
  unify_kinds_spec k1 k2 (unify_kinds k1 k2).
Proof.
  intros [[kc1 kv1 kr1 kh1]|] k2.
    destruct k2 as [[kc2 kv2 kr2 kh2]|].
      simpl.
      destruct (Cstr.valid_dec (Cstr.lub kc1 kc2)).
        apply* UKok.
        apply surjective_pairing.
      apply* UKfail.
    apply UKnone2.
  apply UKnone1.
Qed.

Inductive unif_res : Set :=
  | Uok   : list (typ*typ) -> kenv -> subs -> unif_res
  | Ufail : unif_res.

Definition unify_vars K S x y :=
  match unify_kinds (get_kind x K) (get_kind y K) with
  | Some (k, pairs) => Uok pairs (remove_env (remove_env K x) y & y ~ k)
                                 (compose (x ~ typ_fvar y) S)
  | None            => Ufail
  end.

Inductive unify_vars_spec K S x y : unif_res -> Prop :=
  | UVok : forall k pairs,
      unify_kinds_spec (get_kind x K) (get_kind y K) (Some (k, pairs)) ->
      unify_vars_spec K S x y
        (Uok pairs (remove_env (remove_env K x) y & y ~ k)
                   (compose (x ~ typ_fvar y) S))
  | UVfail :
      unify_kinds_spec (get_kind x K) (get_kind y K) None ->
      unify_vars_spec K S x y Ufail.

Definition unify_nv K S x T :=
  if S.mem x (typ_fv T) then Ufail else
    match get_kind x K with
    | Some _ => Ufail
    | None => Uok nil (remove_env K x) (compose (x ~ T) S)
    end.

Definition unify1 (T1 T2:typ) (K:kenv) (S:subs) : unif_res :=
  match typ_subst S T1, typ_subst S T2 with
  | typ_bvar n, typ_bvar m =>
    if n === m then Uok nil K S else Ufail
  | typ_fvar x, typ_fvar y =>
    if x == y then Uok nil K S else unify_vars K S x y
  | typ_fvar x, T =>
    unify_nv K S x T 
  | T, typ_fvar x =>
    unify_nv K S x T 
  | typ_arrow T11 T12, typ_arrow T21 T22 =>
    Uok ((T11,T21)::(T12,T22)::nil) K S
  | _, _ =>
    Ufail
  end.

Inductive unify_spec : list (typ*typ) -> kenv -> subs ->
                       option (kenv*subs) -> Prop :=
  | USnil  : forall K S (HS:is_subst S) (HK:ok K),
    unify_spec nil K S (Some (K,S))
  | USok   : forall T1 T2 pairs K S pairs' K' S' r (HS:is_subst S) (HK:ok K),
    unify1 T1 T2 K S = Uok pairs' K' S' ->
    unify_spec (pairs' ++ pairs) K' S' r ->
    unify_spec ((T1,T2)::pairs) K S r
  | USfail : forall T1 T2 pairs K S (HS:is_subst S) (HK:ok K),
    unify1 T1 T2 K S = Ufail ->
    unify_spec ((T1,T2)::pairs) K S None.

(* Termination measure *)

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

(* pairs_size : total size of types (after substitution) *)

Fixpoint typ_size (T : typ) : nat :=
  match T with
  | typ_arrow T1 T2 => S (typ_size T1 + typ_size T2)
  | _ => 1
  end.

Definition pair_size (p:typ*typ) :=
  1 + typ_size (fst p) + typ_size (snd p).

Definition pairs_size S pairs := 
  accum pair_size plus 0 (List.map (pair_subst S) pairs).

(* size_pairs : total numbers of variables (after substitution) *)

Definition all_fv S pairs :=
  accum (fun p:typ*typ => typ_fv (fst p) \u typ_fv (snd p))
    S.union {} (List.map (pair_subst S) pairs).

Definition really_all_fv S K pairs :=
  fv_in kind_fv (map (kind_subst S) K) \u all_fv S pairs.

Definition size_pairs S K pairs :=
  1+S.cardinal (really_all_fv S K pairs).

(* Lemmas for termination *)

Lemma typ_fv_decr : forall v T S T1,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  typ_fv (typ_subst (compose (v ~ T) S) T1) <<
  S.remove v (typ_fv T \u typ_fv (typ_subst S T1)).
Proof.
  intros.
  rewrite* typ_subst_compose.
  induction (typ_subst S T1); simpl in *; disjoint_solve.
  destruct* (v0 == v).
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
  sets_solve.
    puts (typ_fv_decr _ _ _ H H0 H2).
    rewrite* (@typ_subst_fresh S T).
   puts (typ_fv_decr _ _ _ H H0 H2).
   rewrite* (@typ_subst_fresh S T).
  use (IHpairs H H0 _ H1).
  simpl in H2.
  rewrite get_notin_dom in H2; auto.
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
    rewrite* typ_subst_fresh.
    forward~ (fv_in_decr _ _ K kind_fv kind_subst Hv Dis); intros.
        apply* kind_fv_decr.
      apply H.
    auto*.
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
    auto.
  unfold really_all_fv, all_fv; simpl.
  rewrite* get_notin_dom.
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
  destruct* H.
  subst; simpl*.
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
      repeat rewrite list_snd_map_snd.
      rewrite <- fv_list_map.
      unfold list_snd; rewrite <- map_app.
      set (pairs := nil(A:=typ*typ)).
      set (kr' := nil(A:=Cstr.attr*typ)).
      intros x Hx.
      rewrite <- union_empty_r.
      replace {} with (typ_fv_list (List.map (typ_subst S) (list_snd kr')))
        by reflexivity.
      rewrite <- union_empty_r.
      replace {} with (all_fv S pairs) by reflexivity.
      clearbody pairs kr'.
      rewrite <- map_app.
      gen pairs kr'; induction (kr ++ kr0); simpl; intros.
        rewrite <- union_assoc; auto with sets.
      destruct a; simpl in *.
      case_rewrite R (Cstr.unique (Cstr.lub kc kc0) a).
        case_rewrite R1 (assoc Cstr.eq_dec a kr');
          poses Hsub (IHl _ _ Hx); clear -Hsub R1.
          unfold all_fv in *; simpl in *.
          sets_solve.
          puts (assoc_sound _ _ _ R1).
          puts (in_map_snd (typ_subst S) _ _ _ H0).
          rewrite <- combine_fst_snd in H1.
          puts (in_combine_r _ _ _ _ H1).
          rewrite list_snd_map_snd in H2.
          use (in_typ_fv _ _ H2 H).
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
    clearbody S; simpl*.
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

(* Well-foundedness of pair ordering *)

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

Lemma normalize_Acc_intro : forall (a b:nat) h,
  Acc_intro (a,b) h = Acc_intro (a,b) (Acc_inv (lt2_wf (a,b))).
Proof.
  intros; apply f_equal. apply ProofIrrelevance.proof_irrelevance.
Qed.

(* The real termination measure *)

Definition size_pairs2 S K pairs :=
  (size_pairs S K pairs, pairs_size S pairs).

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
Hint Resolve size_pairs2_tl.

Lemma size_pairs2_comm : forall S K T1 T2 pairs,
  size_pairs2 S K ((T1,T2)::pairs) = size_pairs2 S K ((T2,T1)::pairs).
Proof.
  intros. unfold size_pairs2. rewrite size_pairs_comm.
  unfold pairs_size; simpl. rewrite* (plus_comm (typ_size (typ_subst S T1))).
Qed.

Section Unify1.
Variables (pairs pairs':list (typ*typ)) (K K':kenv) (S S':subs).
Hypothesis HK : ok K.
Hypothesis HS : is_subst S.
Let size T1 T2 := size_pairs2 S K ((T1,T2)::pairs).
Let size' := size_pairs2 S' K' (pairs' ++ pairs).

Lemma size_pairs2_nv : forall v T T1 T2,
  typ_subst S T1 = typ_fvar v ->
  typ_subst S T2 = T ->
  v \notin typ_fv T ->
  lt2 (size_pairs2 (compose (v ~ T) S) (remove_env K v) pairs) (size T1 T2).
Proof.
  introv R1 R2 R3.
  left. simpl.
  unfold size_pairs at 2, size_pairs, really_all_fv, all_fv; simpl.
  rewrite* <- (typ_subst_idem T1 HS).
  rewrite* <- (typ_subst_idem T2 HS).
  rewrite R1; rewrite R2.
  apply* (@size_pairs_decr v T K S pairs).
    apply* typ_subst_res_fresh'.
  use (typ_subst_res_fresh _ HS R2).
Qed.

Lemma size_pairs2_arrow : forall t t0 t1 t2 T1 T2,
  typ_subst S T1 = typ_arrow t1 t2 ->
  typ_subst S T2 = typ_arrow t t0 ->
  lt2 (size_pairs2 S K ((t1, t) :: (t2, t0) :: pairs)) (size T1 T2).
Proof.
  introv R1 R2.
  unfold size, size_pairs2, size_pairs, really_all_fv, all_fv, pairs_size;
    simpl.
  rewrite <- (typ_subst_idem T1 HS).
  rewrite <- (typ_subst_idem T2 HS).
  rewrite R1; rewrite R2.
  right; simpl; split.
    repeat rewrite union_assoc.
    rewrite <- (union_assoc _ (typ_fv (typ_subst S t))).
    rewrite <- (union_comm _ (typ_fv (typ_subst S t))).
    rewrite* union_assoc.
  omega.
Qed.

Hint Resolve size_pairs2_tl size_pairs2_nv size_pairs2_arrow.

Lemma unify1_decr_nv : forall v T T1 T2,
  unify_nv K S v T = Uok pairs' K' S' ->
  typ_subst S T1 = typ_fvar v ->
  typ_subst S T2 = T ->
  lt2 size' (size T1 T2).
Proof.
  unfold unify_nv, size', size.
  introv HU R1 R2.
  case_rewrite R3 (S.mem v (typ_fv T)).
  use (mem_3 R3).
  case_rewrite R4 (get_kind v K).
  inversions HU.
  apply* size_pairs2_nv.
Qed.

Lemma unify1_decr : forall T1 T2,
  unify1 T1 T2 K S = Uok pairs' K' S' -> lt2 size' (size T1 T2).
Proof.
  unfold unify1, size', size.
  introv HU.
  case_rewrite R1 (typ_subst S T1);
    case_rewrite R2 (typ_subst S T2);
      try discriminate.
        destruct (n === n0); try discriminate.
        inversions* HU.
       rewrite size_pairs2_comm.
       apply* unify1_decr_nv.
      apply* unify1_decr_nv.
     destruct (v == v0).
       inversions* HU.
     unfold unify_vars in HU.
     case_rewrite R3 (unify_kinds (get_kind v K) (get_kind v0 K)).
     destruct p. inversions HU; clear HU.
     left. simpl.
     unfold size_pairs at 2, really_all_fv, all_fv. simpl.
     rewrite <- (typ_subst_idem T1 HS).
     rewrite <- (typ_subst_idem T2 HS).
     rewrite R1; rewrite R2.
     refine (size_pairs_decr_vars _ _ _ _ _ _ _); auto.
       apply* typ_subst_res_fresh'.
     apply* typ_subst_res_fresh'.
    apply* unify1_decr_nv.
   rewrite size_pairs2_comm.
   apply* unify1_decr_nv.
  inversion HU. subst S' K' pairs'.
  simpl.
  apply* size_pairs2_arrow.
Qed.
      
Lemma unify_vars_kok : forall x y,
  unify_vars K S x y = Uok pairs' K' S' -> ok K'.
Proof.
  unfold unify_vars.
  introv HU.
  destruct (unify_kinds (get_kind x K) (get_kind y K)); try discriminate.
  destruct p. inversions HU.
  apply* ok_cons.
  rewrite* dom_remove_env.
Qed.

Lemma unify_nv_kok : forall x T,
  unify_nv K S x T = Uok pairs' K' S' -> ok K'.
Proof.
  unfold unify_nv.
  intros.
  case_rewrite R1 (S.mem x (typ_fv T)).
  case_rewrite R2 (get_kind x K).
  inversions* H.
Qed.

Lemma unify1_kok : forall T1 T2,
  unify1 T1 T2 K S = Uok pairs' K' S' -> ok K'.
Proof.
  unfold unify1.
  introv HU.
  case_rewrite R1 (typ_subst S T1);
    case_rewrite R2 (typ_subst S T2);
      try discriminate; try solve [apply* unify_nv_kok].
    destruct (n === n0); try discriminate.
    inversions* HU.
   destruct (v == v0). inversions* HU.
   apply* unify_vars_kok.
  inversions* HU.
Qed.

Lemma unify1_subst_nv : forall v T T1 T2,
  unify_nv K S v T = Uok pairs' K' S' ->
  typ_subst S T1 = typ_fvar v ->
  typ_subst S T2 = T ->
  is_subst S'.
Proof.
  unfold unify_nv.
  introv HU R1 R2.
  case_rewrite R3 (S.mem v (typ_fv T)).
  use (mem_3 R3).
  case_rewrite R4 (get_kind v K).
  inversions* HU.
Qed.

Lemma unify1_subst : forall T1 T2,
  unify1 T1 T2 K S = Uok pairs' K' S' -> is_subst S'.
Proof.
  clear HK.
  unfold unify1.
  introv HU.
  case_rewrite R1 (typ_subst S T1);
    case_rewrite R2 (typ_subst S T2);
      try discriminate; try solve [apply* unify1_subst_nv].
    destruct (n === n0); try discriminate.
    inversions* HU.
   destruct (v == v0). inversions* HU.
   unfold unify_vars in HU.
   puts (unify_kinds_spec_ok (get_kind v K) (get_kind v0 K)).
   set (u := unify_kinds (get_kind v K) (get_kind v0 K)) in *.
   clearbody u.
   inversions H; try discriminate; inversions* HU.
  inversions* HU.
Qed.

End Unify1.

Hint Resolve unify1_kok unify1_subst unify1_decr.

(* Termination lemmas used directly inside the algorithm *)

Definition Accu S K pairs :=
  Acc lt2 (size_pairs2 S K pairs).

(*
Program Fixpoint unify pairs K S (HS:is_subst S) (HK:ok K) (h:Accu S K pairs)
  {struct h} : option (kenv * subs) :=
  match pairs with
  | nil => Some (K, S)
  | (T1, T2) :: pairs =>
    match unify1 T1 T2 K S with
    | Ufail => None
    | Uok pairs' K' S' =>
      @unify (pairs' ++ pairs) K' S' _ _ _
    end
  end.
Next Obligation.
  apply (unify1_subst _ HS _ _ (sym_eq Heq_anonymous)).
Defined.
Next Obligation.
  apply (unify1_kok HK HS _ _ (sym_eq Heq_anonymous)).
Defined.
Next Obligation.
  apply (Acc_inv h).
  apply* unify1_decr.
Qed.
*)

Lemma Accu_pairs_eq : forall pairs T1 T2 pairs0 K S,
  pairs = (T1,T2) :: pairs0 ->
  Accu S K pairs ->
  Accu S K ((T1,T2) :: pairs0).
Proof.
  intros.
  rewrite* <- H.
Qed.

Definition unify1_dep : forall T1 T2 K S,
  is_subst S -> ok K ->
  {PKS:list(typ*typ)*kenv*subs |
   let (PK,S') := PKS in let (pairs',K') := PK in
   unify1 T1 T2 K S = Uok pairs' K' S' /\
   ok K' /\ is_subst S' /\
   forall pairs pairs0, pairs = (T1,T2)::pairs0 ->
     lt2 (size_pairs2 S' K' (pairs' ++ pairs0)) (size_pairs2 S K pairs)}+
  {unify1 T1 T2 K S = Ufail}.
introv HS HK.
case_eq (unify1 T1 T2 K S); introv R1.
  left; exists (l,k,s); intuition eauto.
  rewrite H; apply* unify1_decr.
right*.
Qed.

Fixpoint unify pairs K S (HS:is_subst S) (HK:ok K) (h:Accu S K pairs) {struct h}
  : option (kenv * subs) :=
  match pairs as pairs0 return pairs = pairs0 -> option (kenv * subs) with
  | nil => fun _ => Some (K, S)
  | (T1, T2) :: pairs => fun eq =>
    match @unify1_dep T1 T2 K S HS HK with
    | inright _ => None
    | inleft (exist (pairs', K', S') (conj _ (conj HK' (conj HS' lt')))) =>
      @unify (pairs' ++ pairs) K' S' HS' HK'
       (Acc_inv h _ (lt' _ _ eq))
    end
  end (refl_equal pairs).

Lemma normalize_unify : forall pairs K S HS HK h,
  @unify pairs K S HS HK h = @unify pairs K S HS HK (lt2_wf _).
Proof.
  intros.
  apply f_equal.
  apply ProofIrrelevance.proof_irrelevance.
Qed.

Lemma unify_spec_sound : forall pairs K S HS HK h,
  unify_spec pairs K S (@unify pairs K S HS HK h).
Proof.
  intros.
  rewrite normalize_unify.
  pose (h1 := (size_pairs S K pairs + 1, pairs_size S pairs)).
  assert (lt2 (size_pairs2 S K pairs) h1)
    by (unfold h1, size_pairs2, size_pairs; left; simpl; omega).
  clearbody h1; gen pairs K S.
  induction h1 using (well_founded_ind lt2_wf); intros.
  destruct pairs as [|[T1 T2]].
    simpl. apply* USnil.
  simpl lt2_wf.
  rewrite normalize_Acc_intro.
  lazy [unify]; fold unify.
  destruct (unify1_dep T1 T2 HS HK).
    destruct s as [[[pairs' K'] S'] [HU [HK' [HS' lt']]]].
    rewrite normalize_unify.
    apply* USok.
    apply* (H _ H0 (pairs'++pairs) K' HK' S' HS').
    apply (Acc_inv h). apply* lt'.
  apply* USfail.
Qed.

Lemma unify_spec_kok : forall pairs K S r,
  unify_spec pairs K S r -> ok K.
Proof.
  induction 1; auto.
Qed.

Lemma unify_spec_subst : forall pairs K S r,
  unify_spec pairs K S r -> is_subst S.
Proof.
  induction 1; auto.
Qed.

Hint Resolve unify_spec_subst unify_spec_kok.

Definition kind_entails k k' :=
  match k', k with
  | Some c', Some c => entails c c'
  | None, _ => True
  | _, _ => False
  end.

Lemma kind_entails_well_kinded : forall k k' K T,
  kind_entails k k' ->
  well_kinded K k T ->
  well_kinded K k' T.
Proof.
  unfold kind_entails; intros.
  inversions H0; clear H0; destruct* k'; try apply wk_any.
  apply* (@wk_kind k'0). apply* (@entails_trans k'0 k0).
Qed.

Hint Resolve kind_entails_well_kinded.

Lemma unifies_nil : forall S, unifies S nil.
Proof.
  intros; intro; intros; contradiction.
Qed.
Hint Resolve unifies_nil.

Section Soundness.

Variables (K':kenv) (S':subs).

Lemma unify_ind : forall (P : kenv -> subs -> list (typ * typ) -> Prop),
  (is_subst S' -> ok K' -> P K' S' nil) ->
  (forall pairs K T S v t t0 (HS:is_subst S) (HK:ok K),
    let S1 := compose (v ~ T) S in
    let K1 := remove_env K v in
    unify_spec pairs K1 S1 (Some (K', S')) ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = T ->
    v \notin typ_fv T -> get_kind v K = None ->
    P K1 S1 pairs -> P K S ((t,t0)::pairs)) ->
  (forall pairs K S v v0 k l t t0 (HS:is_subst S) (HK:ok K),
    let S1 := compose (v ~ typ_fvar v0) S in
    let K1 := remove_env (remove_env K v) v0 & v0 ~ k in
    unify_kinds (get_kind v K) (get_kind v0 K) = Some (k, l) ->
    unify_spec (l ++ pairs) K1 S1 (Some (K', S')) ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = typ_fvar v0 ->
    v <> v0 ->
    P K1 S1 (l ++ pairs) -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs n,
    unify_spec pairs K S  (Some (K', S')) ->
    typ_subst S t = typ_bvar n ->
    typ_subst S t0 = typ_bvar n ->
    P K S pairs -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs v,
    unify_spec pairs K S (Some (K', S')) ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = typ_fvar v ->
    P K S pairs -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs t1 t2 t3 t4,
    unify_spec ((t1,t3)::(t2,t4)::pairs) K S (Some (K',S')) ->
    typ_subst S t = typ_arrow t1 t2 ->
    typ_subst S t0 = typ_arrow t3 t4 ->
    P K S ((t1,t3)::(t2,t4)::pairs) -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs,
    P K S ((t,t0)::pairs) -> P K S ((t0,t)::pairs)) ->
  forall pairs K S,
    unify_spec pairs K S (Some (K', S')) ->
    P K S pairs.
Proof.
  introv Hnil Hnv Hvars Hbv Hfv. intros Harr Hsw. intros.
  remember (Some (K',S')) as KS'.
  rewrite HeqKS' in *. rewrite <- HeqKS' in H.
  induction H; intros; try discriminate. inversions* HeqKS'.
  subst r.
  poses HU H.
  poses HK'0 (unify1_kok pairs HK HS _ _ H).
  poses HS'0 (unify1_subst pairs K HS _ _ H).
  unfold unify1 in H.
  case_rewrite R1 (typ_subst S T1); case_rewrite R2 (typ_subst S T2);
    try discriminate;
      try (unfold unify_nv in H;
        (case_rewrite R3 (S.mem v (typ_fv (typ_bvar n))) ||
         case_rewrite R3 (S.mem v (typ_fv (typ_arrow t t0))));
        case_rewrite R4 (get_kind v K);
        inversions H;
        solve [apply* Hnv | apply Hsw; apply* Hnv]).
      destruct (n === n0); try discriminate.
      inversions* H.
    destruct (v == v0). inversions* H.
    unfold unify_vars in H.
    case_rewrite R3 (unify_kinds (get_kind v K) (get_kind v0 K)).
    destruct p.
    inversions H. apply (Hvars _ _ _ _ _ _ _ _ _ HS HK R3); auto.
  inversions H.
  simpl in *.
  apply* Harr.
Qed.

Lemma unify_keep : forall pairs K S,
  unify_spec pairs K S (Some (K', S')) ->
  is_subst S' /\
  forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'.
Proof.
  intros until S.
  apply* (unify_ind
    (fun K S _ => is_subst S' /\
      forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'));
    intros.
    destruct H4; split*.
    intros. apply H5.
    unfold S1. apply* binds_add_binding.
  intuition.
  apply H6; unfold S1. apply* binds_add_binding.
Qed.

Lemma typ_subst_extend : forall pairs K S,
  unify_spec pairs K S (Some (K', S')) ->
  extends S' S.
Proof.
  intros.
  destruct* (unify_keep H).
  poses HS (unify_spec_subst H).
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

Theorem unify_types : forall pairs K S,
  unify_spec pairs K S (Some (K',S')) ->
  unifies S' pairs.
Proof.
  intros until S.
  apply (unify_ind (fun _ _ => unifies S')); intros;
    try (intro; simpl; intros); intuition;
    try fold (v \notin typ_fv T) in H2;
    try (match goal with H: _ = _ |- _ => inversion H; clear H; subst t t0 end);
    try (match goal with H: unify_spec _ _ _ _ |- _ =>
           rewrite <- (typ_subst_extend H);
           rewrite <- (typ_subst_extend H T2) end);
    try (subst S1 K1; do 2 rewrite typ_subst_compose);
    try (rewrite H0; rewrite H1; simpl*);
    try (rewrite H1; rewrite H2; simpl; destruct* (v == v);
         destruct* (v0 == v)).
      destruct* (v == v). rewrite* (typ_subst_fresh (v ~ T)). simpl*.
    simpl.
    rewrite* (H2 t1 t3).
    rewrite* (H2 t2 t4).
  symmetry.
  apply* H.
Qed.

Lemma unify_kind_rel_keep : forall kr kr' uniq pairs k' l,
  unify_kind_rel kr kr' uniq pairs = (k', l) ->
  incl kr' k' /\ incl pairs l.
Proof.
  induction kr; simpl; intros. inversions H. split*.
  destruct a.
  case_rewrite R (uniq a).
    case_rewrite R1 (assoc Cstr.eq_dec a kr'); destruct* (IHkr _ _ _ _ _ H).
  destruct* (IHkr _ _ _ _ _ H).
Qed.

Lemma unify_kind_rel_incl : forall kr pairs uniq S kr0 kr' pairs',
  unify_kind_rel kr0 kr' uniq pairs' = (kr, pairs) ->
  unifies S pairs ->
  incl (map_snd (typ_subst S) kr0) (map_snd (typ_subst S) kr).
Proof.
  induction kr0; intros; intros T HT. elim HT.
  destruct T.
  destruct a.
  simpl in *.
  case_rewrite R (uniq a);
    try case_rewrite R1 (assoc Cstr.eq_dec a kr'); simpl in HT; destruct HT;
      try solve [apply* (IHkr0 _ _ H)]; inversions H1; clear H1;
        destruct (unify_kind_rel_keep _ _ _ _ H).
      puts (H1 _ (assoc_sound _ _ _ R1)); clear H1.
      assert (In (t0,t1) pairs) by auto.
      use (H0 _ _ H1).
      rewrite* H4.
    apply* in_map_snd.
  apply* in_map_snd.
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
       rewrite R1; apply H; unfold map_snd; rewrite* map_app.
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
  unfold map_snd; rewrite <- map_app.
  fold (map_snd (typ_subst S) (kr1++kr2)).
  simpl.
  refine (f_equal (@Some _) _).
  set (kr:=@nil(Cstr.attr*typ)).
  set (pairs:=@nil(typ*typ)).
  assert (kr = map_snd (typ_subst S) kr) by reflexivity.
  assert (pairs =
    List.map (fun T => (typ_subst S (fst T), typ_subst S (snd T))) pairs)
    by reflexivity.
  clear kh1 kh2.
  apply injective_projections; simpl; try apply kind_pi; simpl*;
    pattern kr at 1; rewrite H;
    pattern pairs at 1; rewrite H0; clear H H0;
    gen kr pairs; induction (kr1++kr2); intros; simpl*; destruct a;
    simpl; destruct (Cstr.unique (Cstr.lub kc1 kc2) a);
    try rewrite* <- IHl;
    case_eq (assoc Cstr.eq_dec a kr); intros; rewrite <- IHl;
    try rewrite* (assoc_map _ (typ_subst S) _ _ H).
Qed.

Lemma well_subst_unify : forall k1 l v v0 S K pairs,
  unify_spec (l ++ pairs) (remove_env (remove_env K v) v0 & v0 ~ k1)
    (compose (v ~ typ_fvar v0) S) (Some (K', S')) ->
  unify_kinds (get_kind v K) (get_kind v0 K) = Some (k1, l) ->
  v # S ->
  well_subst (remove_env (remove_env K v) v0 & v0 ~ k1)
     (map (kind_subst S') K') S' ->
  well_subst K (map (kind_subst S') K') S'.
Proof.
  introv H HU Hv WS x; intros.
  unfold well_subst in WS.
  poses Hext (typ_subst_extend H).
  poses Hunif (unify_types H).
  assert (Hunif': unifies S' l) by (intro; intros; auto).
  clear H.
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

Lemma unify_kinds_ok : forall pairs K S,
  unify_spec pairs K S (Some (K',S')) ->
  disjoint (dom S) (dom K) ->
  ok K' /\ disjoint (dom S') (dom K') /\
  well_subst K (map (kind_subst S') K') S'.
Proof.
  refine (unify_ind _ _ _ _ _ _ _ _); auto.
      intuition.
      intro; intros.
      rewrite* typ_subst_fresh.
      destruct* k.
      use (binds_map (kind_subst S') H2).
      simpl in *; apply* wk_kind.
    intros until K1.
    intros H R1 R2 n R3 IH Dis.
    subst S1 K1.
    destruct* IH.
    intuition.
    clear -R3 H3.
    intro; intros.
    destruct (Z == v).
      subst.
      rewrite (binds_get_kind H) in R3. subst*.
    use (H3 _ _ (binds_remove_env H n)).
  intros until K1.
  intros R3 H R1 R2 n IH Dis.
  subst S1 K1.
  destruct* IH.
    simpl.
    repeat rewrite* dom_remove_env.
    unfold compose.
    use (typ_subst_res_fresh' _ HS R2).
  intuition.
  subst; apply* well_subst_unify.
  apply* typ_subst_res_fresh'.
Qed.

End Soundness.

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
  (* poses Huniq (Cstr.entails_unique H5). *)
  clear H H0 H3 H4 H6.
  simpl in H1, H2. clear kv kv0 kh kh0.
  set (pairs := nil(A:=typ*typ)).
  set (krs := nil(A:=Cstr.attr*typ)).
  assert (forall T,
          In T (map_snd (typ_subst S) ((kr ++ kr0) ++ krs)) -> In T kr').
    intros.
    unfold map_snd in H; repeat rewrite map_app in H.
    destruct (in_app_or _ _ _ H).
      destruct* (in_app_or _ _ _ H0).
    elim H0.
  clear H1 H2.
  assert (Hunif: unifies S pairs) by (intros T1 T2 HE; elim HE).
  unfold kind_entails, entails; simpl.
  intros; gen pairs krs; induction (kr++kr0); simpl; intros. auto.
  destruct a.
  case_eq (Cstr.unique (Cstr.lub kc kc0) a); introv R.
    puts (Cstr.entails_unique H5 R).
    case_eq (assoc Cstr.eq_dec a krs); [intros t0 R1|intros R1].
      assert (unifies S ((t,t0)::pairs)).
        intro; simpl; intros.
        destruct H1; [|auto*].
        inversions H1; clear H1.
        apply* (kh' a).
        apply H.
        right.
        unfold map_snd; rewrite map_app.
        use (in_map_snd (typ_subst S) _ _ _ (assoc_sound _ _ _ R1)).
      intuition.
        refine (proj1 (IHl _ _ _ _) _ _ H2); auto.
      refine (proj2 (proj2 (IHl _ _ _ _)) _ H2); auto.
    intuition;
      [ refine (proj1 (IHl _ _ _ _) _ _ H1)
      | refine (proj2 (proj2 (IHl _ _ _ _)) _ H1)];
      auto; simpl; intros;
      unfold map_snd in *;
      repeat rewrite map_app in *; apply H; apply* in_app_mid.
  unfold map_snd in *.
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
  case_eq (get_kind x K); intros; auto*.
Qed.

Lemma well_subst_get_kind : forall K K' S x,
  well_subst K K' S ->
  well_kinded K' (kind_subst S (get_kind x K)) (typ_subst S (typ_fvar x)).
Proof.
  intros.
  case_eq (get_kind x K); intros; auto*.
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

Section Completeness.

Variables (K:kenv) (S:subs).

Section Unify1_Complete.

Variables (S0:subs) (K0:kenv).
Hypothesis (HS0:is_subst S0) (HK0:ok K0).
Hypothesis WS : well_subst K0 K S.
Hypothesis Hext : extends S S0.

Lemma unify_nv_complete : forall v T t t0,
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  typ_subst S (typ_fvar v) = typ_subst S T ->
  (forall x, T <> typ_fvar x) ->
  exists K', exists S', exists pairs',
    unify_nv K0 S0 v T = Uok pairs' K' S' /\
    unifies S pairs' /\ extends S S' /\ well_subst K' K S.
Proof.
  introv R1 R2 Heq HT.
  unfold unify_nv.
  case_eq (S.mem v (typ_fv T)); introv R3.
    elimtype False.
    clear -Heq HT R3.
    poses i (S.mem_2 R3).
    destruct T. elim (in_empty i).
      elim (HT v); rewrite* (S.singleton_1 i).
    assert (1 < typ_size (typ_arrow T1 T2)).
      destruct T1; simpl; omega.
    use (typ_subst_no_cycle S _ i H).
    rewrite Heq in H0; omega.
  clear R3.
  case_eq (get_kind v K0); introv R3.
    poses Wk (WS (get_kind_binds _ _ R3)).
    rewrite Heq in Wk.
    simpl in Wk; inversions Wk.
    clear -H0 HT.
    destruct (typ_subst S0 t0); try discriminate.
    elim (HT v). auto.
  esplit; esplit; esplit; split*. intuition.
    intro. rewrite* typ_subst_compose.
    rewrite typ_subst_prebind. apply Hext. congruence.
  intro; intros.
  destruct k; try (simpl; apply wk_any).
  destruct (v == Z).
    elim (binds_fresh H).
    rewrite* dom_remove_env. apply* S.remove_1.
  apply WS.
  apply* binds_orig_remove_env.
Qed.

Lemma unify_vars_complete : forall v0 v,
  typ_subst S (typ_fvar v0) = typ_subst S (typ_fvar v) ->
  exists K', exists S', exists pairs',
    unify_vars K0 S0 v0 v = Uok pairs' K' S' /\ unifies S pairs' /\
    extends S S' /\ well_subst K' K S.
Proof.
  introv Heq.
  unfold unify_vars.
  puts (well_kinded_kind_entails (well_subst_get_kind v0 WS)).
  puts (well_kinded_kind_entails (well_subst_get_kind v WS)).
  rewrite Heq in H.
  destruct* (unify_kinds_complete _ _ _ _ H H0) as [k [l [HU [Heq' Hke]]]].
  rewrite HU; clear HU.
  esplit; esplit; esplit; split*. intuition.
    intro. rewrite* typ_subst_compose.
    rewrite typ_subst_prebind. apply Hext. congruence.
  intro; intros.
  unfold binds in H1; simpl in H1. destruct (Z == v). inversions H1.
    apply* kind_entails_well_kinded.
    apply well_kinded_typ_kind.
  apply WS.
  puts (binds_orig_remove_env _ (ok_remove_env v0 HK0) H1).
  apply* binds_orig_remove_env.
Qed.

Lemma unify1_complete : forall T1 T2,
  typ_subst S T1 = typ_subst S T2 ->
  exists K', exists S', exists pairs',
    unify1 T1 T2 K0 S0 = Uok pairs' K' S' /\
    unifies S pairs' /\ extends S S' /\ well_subst K' K S.
Proof.
  introv E.
  unfold unify1.
  rewrite <- Hext in E. rewrite <- (Hext T2) in E.
  case_rewrite R1 (typ_subst S0 T1); case_rewrite R2 (typ_subst S0 T2); simpl;
    try solve [apply* unify_nv_complete; intros x Hx; discriminate].
      inversions E.
      destruct* (n0 === n0).
      esplit; esplit; esplit; split*.
    destruct (v == v0).
      esplit; esplit; esplit; split*.
    apply* unify_vars_complete.
  simpl in E; inversions E.
  esplit; esplit; esplit; split*. intuition.
  intro; intros.
  simpl in H; destruct H. inversions* H.
  destruct* H. inversions* H.
Qed.

End Unify1_Complete.

Lemma unify_complete0 : forall pairs K0 S0 r,
  unify_spec pairs K0 S0 r ->
  extends S S0 ->
  unifies S pairs ->
  well_subst K0 K S ->
  exists K', exists S', r = Some (K', S') /\ extends S S' /\ well_subst K' K S.
Proof.
  introv H Hext Heq WS.
  induction H.
      esplit; esplit; split*.
    assert (E: typ_subst S T1 = typ_subst S T2) by auto.
    destruct (unify1_complete HK WS Hext T1 T2 E)
      as [K'0 [S'0 [pairs0 [HU1 H']]]].
    rewrite HU1 in H. inversions H.
    apply* IHunify_spec.
    intro; intros. destruct* (in_app_or _ _ _ H1).
  assert (E: typ_subst S T1 = typ_subst S T2) by auto.
  destruct (unify1_complete HK WS Hext T1 T2 E)
    as [K'0 [S'0 [pairs0 [HU1 H']]]].
  rewrite HU1 in H. inversion H.
Qed.

Theorem unify_complete : forall T1 T2 K0,
  ok K0 ->
  well_subst K0 K S ->
  typ_subst S T1 = typ_subst S T2 ->
  exists K', exists S',
    unify_spec ((T1,T2)::nil) K0 id (Some (K',S')) /\
    extends S S' /\ well_subst K' K S.
Proof.
  introv HK0 WS E.
  puts (@unify_spec_sound ((T1,T2)::nil) K0 id is_subst_id HK0 (lt2_wf _)).
  destruct* (unify_complete0 H) as [K' [S' [HU H']]].
      intro; rewrite* typ_subst_id.
    intro; intros; simpl in H0; destruct* H0.
    inversions* H0.
  rewrite HU in H.
  esplit; esplit; split*.
Qed.

End Completeness.

End MkUnify.
