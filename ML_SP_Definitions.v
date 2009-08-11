(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Definitions                *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - May 2008                                *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory List Arith.

(* Constraint domain specification *)

Module Type CstrIntf.
  Parameter cstr attr : Set.
  Parameter valid : cstr -> Prop.
  Parameter valid_dec : forall c, sumbool (valid c) (~valid c).
  Parameter eq_dec : forall x y:attr, {x=y}+{x<>y}.
  Parameter unique : cstr -> attr -> bool.
  Parameter lub : cstr -> cstr -> cstr.
  Parameter entails : cstr -> cstr -> Prop.
  Parameter entails_refl : forall c, entails c c.
  Hint Resolve entails_refl.
  Parameter entails_trans : forall c1 c2 c3,
    entails c1 c2 -> entails c2 c3 -> entails c1 c3.
  Parameter entails_lub : forall c1 c2 c,
    (entails c c1 /\ entails c c2) <-> entails c (lub c1 c2).
  Parameter entails_unique : forall c1 c2 v,
    entails c1 c2 -> unique c2 v = true -> unique c1 v = true.
  Parameter entails_valid : forall c1 c2,
    entails c1 c2 -> valid c1 -> valid c2.
End CstrIntf.

Module Type CstIntf.
  Parameter const : Set.
  Parameter arity : const -> nat.
End CstIntf.

(* Parameterized definitions *)

Module MkDefs(Cstr:CstrIntf)(Const:CstIntf).

(* ********************************************************************** *)
(** ** Description of types *)

(** Grammar of types. *)

Inductive typ : Set :=
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ
  | typ_arrow : typ -> typ -> typ.

(** Types are inhabited, giving us a default value. *)

Definition typ_def := typ_bvar 0.

(** Constraint domain *)

Definition coherent kc (kr:list(Cstr.attr*typ)) := forall x T U,
  Cstr.unique kc x = true -> In (x,T) kr -> In (x,U) kr -> T = U.

Record ckind : Set := Kind {
  kind_cstr : Cstr.cstr;
  kind_valid : Cstr.valid kind_cstr;
  kind_rel  : list (Cstr.attr*typ);
  kind_coherent : coherent kind_cstr kind_rel }.

Definition kind := option ckind.

Definition entails K K' :=
  Cstr.entails (kind_cstr K) (kind_cstr K') /\
  forall T:Cstr.attr*typ, In T (kind_rel K') -> In T (kind_rel K).

(** Type schemes. *)

Record sch : Set := Sch { 
  sch_type  : typ ;
  sch_kinds : list kind }.

Notation "'sch_arity' M" :=
  (length (sch_kinds M)) (at level 20, no associativity).

(** Opening body of type schemes. *)

Fixpoint typ_open (T : typ) (Vs : list typ) {struct T} : typ :=
  match T with
  | typ_bvar i      => nth i Vs typ_def
  | typ_fvar x      => typ_fvar x 
  | typ_arrow T1 T2 => typ_arrow (typ_open T1 Vs) (typ_open T2 Vs)
  end.

(** Opening body of type schemes with variables *)

Definition typ_fvars := 
  List.map typ_fvar.

Definition typ_open_vars T Xs := 
  typ_open T (typ_fvars Xs).

(** Instanciation of a type scheme *)

Definition sch_open M := 
  typ_open (sch_type M).

Definition sch_open_vars M := 
  typ_open_vars (sch_type M).
  
Notation "M ^^ Vs" := (sch_open M Vs) 
  (at level 67, only parsing) : typ_scope.
Notation "M ^ Xs" := 
  (sch_open_vars M Xs) (only parsing) : typ_scope.

Bind Scope typ_scope with typ.
Open Scope typ_scope.

(** Locally closed types *)

Inductive type : typ -> Prop :=
  | type_fvar : forall X, 
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2).

(** List of n locally closed types *)

Definition types := list_for_n type.

(** Iterating and opening kinds *)

Definition kind_types (K:kind) :=
  match K with
  | None => nil
  | Some k => list_snd (kind_rel k)
  end.

Definition All_kind_types (P:typ->Prop) K :=
  list_forall P (kind_types K).

Lemma map_coherent : forall f kc kr,
  coherent kc kr ->
  coherent kc (map_snd f kr).
Proof.
  intros. intro; intros.
  puts (H x).
  destruct (map_snd_inv _ _ _ _ H1) as [T' [Heq Hin]].
  destruct (map_snd_inv _ _ _ _ H2) as [U' [Heq' Hin']].
  subst.
  rewrite* (H3 T' U').
Qed.

Definition ckind_map_spec (f:typ->typ) (k:ckind):
  {k' |  kind_cstr k = kind_cstr k' /\ 
  kind_rel k' = map_snd f (kind_rel k)}.
Proof.
  intros.
  destruct k as [kc kv kr kh].
  exists (Kind kv (map_coherent f kh)).
  simpl. auto.
Defined.

Definition ckind_map f k := proj1_sig (ckind_map_spec f k).

Definition kind_map f (K:kind) : kind :=
  match K with
  | None => None
  | Some k => Some (ckind_map f k)
  end.

Definition kind_open K Vs := kind_map (fun T => typ_open T Vs) K.

(** Body of a scheme *)

Definition typ_body T Ks :=
  forall Xs, length Ks = length Xs ->
    type (typ_open_vars T Xs) /\
    list_forall (All_kind_types (fun T' => type (typ_open_vars T' Xs))) Ks.

(** Definition of a well-formed scheme *)

Definition scheme M :=
   typ_body (sch_type M) (sch_kinds M).

(* ********************************************************************** *)
(** ** Description of terms *)

(** Grammar of terms. *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_let  : trm -> trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_cst  : Const.const -> trm.

(** Opening term binders. *)

Fixpoint trm_open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => if k === i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x 
  | trm_abs t1    => trm_abs (trm_open_rec (S k) u t1) 
  | trm_let t1 t2 => trm_let (trm_open_rec k u t1) (trm_open_rec (S k) u t2) 
  | trm_app t1 t2 => trm_app (trm_open_rec k u t1) (trm_open_rec k u t2)
  | trm_cst c     => trm_cst c
  end.

Definition trm_open t u := trm_open_rec 0 u t.

(* Notation "{ k ~> u } t" := (trm_open_rec k u t) (at level 67). *)
Notation "t ^^ u" := (trm_open t u) (at level 67).
Notation "t ^ x" := (trm_open t (trm_fvar x)).

(** Locally closed termessions *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1)
  | term_let : forall L t1 t2,
      term t1 -> 
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_let t1 t2)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2)
  | term_cst : forall c,
      term (trm_cst c).

(** Definition of the body of an abstraction *)

Definition term_body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

(** Term instanciation *)

Definition trm_def := trm_bvar 0.

Fixpoint trm_inst_rec (k : nat) (tl : list trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => if le_lt_dec k i then nth (i-k) tl t else trm_bvar i
  | trm_fvar x    => trm_fvar x 
  | trm_abs t1    => trm_abs (trm_inst_rec (S k) tl t1) 
  | trm_let t1 t2 => trm_let (trm_inst_rec k tl t1) (trm_inst_rec (S k) tl t2) 
  | trm_app t1 t2 => trm_app (trm_inst_rec k tl t1) (trm_inst_rec k tl t2)
  | trm_cst c     => trm_cst c
  end.

Definition trm_inst t tl := trm_inst_rec 0 tl t.

(** Applying a constant *)

Definition const_app c vl := fold_left trm_app vl (trm_cst c).

(* ********************************************************************** *)
(** ** Description of typing *)

(** Definition of kinding environments *)

Definition kenv := env kind.

Definition kenv_ok K :=
  ok K /\ env_prop (All_kind_types type) K.

(** Proper instanciation *)

Inductive well_kinded : kenv -> kind -> typ -> Prop :=
  | wk_any : forall K T,
      well_kinded K None T
  | wk_kind : forall k' K k x,
      binds x (Some k') K ->
      entails k' k ->
      well_kinded K (Some k) (typ_fvar x).

Hint Constructors well_kinded.

Definition kinds_open Ks Us :=
  List.map (fun k:kind => kind_open k Us) Ks.

Definition proper_instance K Ks Us :=
  types (length Ks) Us /\
  list_forall2 (well_kinded K) (kinds_open Ks Us) Us.

Definition kinds_open_vars Ks Xs :=
  List.combine Xs (kinds_open Ks (typ_fvars Xs)).

(** Definition of typing environments *)

Definition env := env sch.

Definition env_ok (E:env) := ok E /\ env_prop scheme E.

(** Computing free variables of a type. *)

Fixpoint typ_fv (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar i      => {}
  | typ_fvar x      => {{x}}
  | typ_arrow T1 T2 => (typ_fv T1) \u (typ_fv T2)
  end.

(** Computing free variables of a list of terms. *)

Definition typ_fv_list :=
  List.fold_right (fun t acc => typ_fv t \u acc) {}.

(** Computing free variables of a kind. *)

Definition kind_fv k :=
  typ_fv_list (kind_types k).

Definition kind_fv_list :=
  List.fold_right (fun t acc => kind_fv t \u acc) {}.

(** Computing free variables of a type scheme. *)

Definition sch_fv M := 
  typ_fv (sch_type M) \u kind_fv_list (sch_kinds M).

(** Computing free type variables of the values of an environment. *)

Definition env_fv := 
  fv_in sch_fv.

(** Grammar of values *)

Inductive valu : nat -> trm -> Prop :=
  | value_abs : forall t1, term (trm_abs t1) -> valu 0 (trm_abs t1)
  | value_cst : forall c, valu (Const.arity c) (trm_cst c)
  | value_app : forall n t1 n2 t2,
      valu (S n) t1 ->
      valu n2 t2 ->
      valu n (trm_app t1 t2).

Definition value t := exists n, valu n t.

(** Another functor for delta-rules *)

Module Type DeltaIntf.
  Parameter type : Const.const -> sch.
  Parameter closed : forall c, sch_fv (type c) = {}.
  Parameter scheme : forall c, scheme (type c).
  Parameter reduce : forall c tl,
    list_for_n value (S(Const.arity c)) tl -> trm.
  Parameter term : forall c tl vl,
    term (@reduce c tl vl).
End DeltaIntf.

Module MkJudge(Delta:DeltaIntf).

(** The typing judgment *)

Reserved Notation "K ; E | gc |= t ~: T" (at level 69).

Inductive gc_kind : Set := GcAny | GcLet.
Definition gc_info : Set := (bool * gc_kind)%type.
Fixpoint gc_ok (gc:gc_info) := fst gc = true. 
Fixpoint gc_raise (gc:gc_info) : gc_info :=
  match snd gc with
  | GcLet => (true, GcLet)
  | _ => gc
  end.
Fixpoint gc_lower (gc:gc_info) : gc_info :=
  match snd gc with
  | GcLet => (false, GcLet)
  | _ => gc
  end.

Inductive typing(gc:gc_info) : kenv -> env -> trm -> typ -> Prop :=
  | typing_var : forall K E x M Us,
      kenv_ok K ->
      env_ok E -> 
      binds x M E -> 
      proper_instance K (sch_kinds M) Us ->
      K ; E | gc |= (trm_fvar x) ~: (M ^^ Us)
  | typing_abs : forall L K E U T t1, 
      type U ->
      (forall x, x \notin L -> 
        K ; (E & x ~ Sch U nil) | gc_raise gc |= (t1 ^ x) ~: T) -> 
      K ; E | gc |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_let : forall M L1 L2 K E T2 t1 t2,
      (forall Xs, fresh L1 (sch_arity M) Xs ->
         (K & kinds_open_vars (sch_kinds M) Xs); E | gc_raise gc |=
           t1 ~: (M ^ Xs)) ->
      (forall x, x \notin L2 ->
         K ; (E & x ~ M) | gc_raise gc |= (t2 ^ x) ~: T2) -> 
      K ; E | gc |= (trm_let t1 t2) ~: T2
  | typing_app : forall K E S T t1 t2, 
      K ; E | gc_lower gc |= t1 ~: (typ_arrow S T) ->
      K ; E | gc_lower gc |= t2 ~: S ->   
      K ; E | gc |= (trm_app t1 t2) ~: T
  | typing_cst : forall K E Us c,
      kenv_ok K ->
      env_ok E ->
      proper_instance K (sch_kinds (Delta.type c)) Us ->
      K ; E | gc |= (trm_cst c) ~: (Delta.type c ^^ Us)
  | typing_gc : forall Ks L K E t T,
      gc_ok gc ->
      (forall Xs, fresh L (length Ks) Xs ->
        K & kinds_open_vars Ks Xs; E | gc |= t ~: T) ->
      K ; E | gc |= t ~: T

where "K ; E | gc |= t ~: T" := (typing gc K E t T).


(* ********************************************************************** *)
(** ** Description of the semantics *)

(** Reduction rules *)

Inductive red : trm -> trm -> Prop :=
  | red_abs : forall t1 t2, 
      term (trm_abs t1) -> 
      value t2 ->  
      red (trm_app (trm_abs t1) t2) (t1 ^^ t2)
  | red_let : forall t1 t2, 
      term (trm_let t1 t2) ->
      value t1 -> 
      red (trm_let t1 t2) (t2 ^^ t1)
  | red_delta : forall c tl vl,
      red (const_app c tl) (@Delta.reduce c tl vl)
  | red_let_1 : forall t1 t1' t2, 
      term_body t2 ->
      red t1 t1' -> 
      red (trm_let t1 t2) (trm_let t1' t2)
  | red_app_1 : forall t1 t1' t2,
      value t2 ->
      red t1 t1' -> 
      red (trm_app t1 t2) (trm_app t1' t2)
  | red_app_2 : forall t1 t2 t2', 
      term t1 ->
      red t2 t2' ->
      red (trm_app t1 t2) (trm_app t1 t2').
                  
Notation "t --> t'" := (red t t') (at level 68).


(* ********************************************************************** *)
(** ** Description of the results *)

(** Goal is to prove preservation and progress *)

Definition preservation := forall K E t t' T,
  K ; E | (true,GcAny) |= t ~: T ->
  t --> t' ->
  K ; E | (true,GcAny) |= t' ~: T.

Definition progress := forall K t T, 
  K ; empty | (true,GcAny) |= t ~: T ->
     value t
  \/ exists t', t --> t'.

End MkJudge.

End MkDefs.