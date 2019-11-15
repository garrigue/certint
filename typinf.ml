
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S m0 -> eq_dec n0 m0)
 end

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | Nil -> default
          | Cons (x, _) -> x)
  | S m -> (match l with
            | Nil -> default
            | Cons (_, t0) -> nth m t0 default)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t0) -> fold_left f t0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

(** val split : ('a1, 'a2) prod list -> ('a1 list, 'a2 list) prod **)

let rec split = function
| Nil -> Pair (Nil, Nil)
| Cons (p, tl) ->
  let Pair (x, y) = p in
  let Pair (left, right) = split tl in
  Pair ((Cons (x, left)), (Cons (y, right)))

(** val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec combine l l' =
  match l with
  | Nil -> Nil
  | Cons (x, tl) ->
    (match l' with
     | Nil -> Nil
     | Cons (y, tl') -> Cons ((Pair (x, y)), (combine tl tl')))

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> Nil
| S len0 -> Cons (start, (seq (S start) len0))

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
  | O -> Left
  | S n0 -> (match m with
             | O -> Right
             | S m0 -> le_lt_dec n0 m0)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos x0 -> (match y with
                  | Zpos p0 -> Pos.eq_dec x0 p0
                  | _ -> Right)
    | Zneg x0 -> (match y with
                  | Zneg p0 -> Pos.eq_dec x0 p0
                  | _ -> Right)
 end

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> Left
    | _ -> Right

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Left -> True
    | Right -> False
 end

module type UsualOrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module Z_as_OT =
 struct
  type t = z

  (** val compare : z -> z -> z compare0 **)

  let compare x y =
    match Z.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec =
    Z.eq_dec
 end

module type S =
 sig
  module E :
   OrderedType

  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val compare : t -> t -> t compare0

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> (t, t) prod

  val cardinal : t -> nat

  val elements : t -> elt list

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val choose : t -> elt option
 end

module type FinSet =
 sig
  module E :
   UsualOrderedType

  module S :
   S with module E = E

  type fset = S.t

  type elt = S.elt
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    Nil

  (** val is_empty : t -> bool **)

  let is_empty = function
  | Nil -> True
  | Cons (_, _) -> False

  (** val mem : elt -> t -> bool **)

  let rec mem x = function
  | Nil -> False
  | Cons (y, l) ->
    (match X.compare x y with
     | LT -> False
     | EQ -> True
     | GT -> mem x l)

  (** val add : elt -> t -> t **)

  let rec add x s = match s with
  | Nil -> Cons (x, Nil)
  | Cons (y, l) ->
    (match X.compare x y with
     | LT -> Cons (x, s)
     | EQ -> s
     | GT -> Cons (y, (add x l)))

  (** val singleton : elt -> t **)

  let singleton x =
    Cons (x, Nil)

  (** val remove : elt -> t -> t **)

  let rec remove x s = match s with
  | Nil -> Nil
  | Cons (y, l) ->
    (match X.compare x y with
     | LT -> s
     | EQ -> l
     | GT -> Cons (y, (remove x l)))

  (** val union : t -> t -> t **)

  let rec union s = match s with
  | Nil -> (fun s' -> s')
  | Cons (x, l) ->
    let rec union_aux s' = match s' with
    | Nil -> s
    | Cons (x', l') ->
      (match X.compare x x' with
       | LT -> Cons (x, (union l s'))
       | EQ -> Cons (x, (union l l'))
       | GT -> Cons (x', (union_aux l')))
    in union_aux

  (** val inter : t -> t -> t **)

  let rec inter = function
  | Nil -> (fun _ -> Nil)
  | Cons (x, l) ->
    let rec inter_aux s' = match s' with
    | Nil -> Nil
    | Cons (x', l') ->
      (match X.compare x x' with
       | LT -> inter l s'
       | EQ -> Cons (x, (inter l l'))
       | GT -> inter_aux l')
    in inter_aux

  (** val diff : t -> t -> t **)

  let rec diff s = match s with
  | Nil -> (fun _ -> Nil)
  | Cons (x, l) ->
    let rec diff_aux s' = match s' with
    | Nil -> s
    | Cons (x', l') ->
      (match X.compare x x' with
       | LT -> Cons (x, (diff l s'))
       | EQ -> diff l l'
       | GT -> diff_aux l')
    in diff_aux

  (** val equal : t -> t -> bool **)

  let rec equal s s' =
    match s with
    | Nil -> (match s' with
              | Nil -> True
              | Cons (_, _) -> False)
    | Cons (x, l) ->
      (match s' with
       | Nil -> False
       | Cons (x', l') ->
         (match X.compare x x' with
          | EQ -> equal l l'
          | _ -> False))

  (** val subset : t -> t -> bool **)

  let rec subset s s' =
    match s with
    | Nil -> True
    | Cons (x, l) ->
      (match s' with
       | Nil -> False
       | Cons (x', l') ->
         (match X.compare x x' with
          | LT -> False
          | EQ -> subset l l'
          | GT -> subset s l'))

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let rec fold f s i =
    match s with
    | Nil -> i
    | Cons (x, l) -> fold f l (f x i)

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | Nil -> Nil
  | Cons (x, l) ->
    (match f x with
     | True -> Cons (x, (filter f l))
     | False -> filter f l)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | Nil -> True
  | Cons (x, l) -> (match f x with
                    | True -> for_all f l
                    | False -> False)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | Nil -> False
  | Cons (x, l) -> (match f x with
                    | True -> True
                    | False -> exists_ f l)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let rec partition f = function
  | Nil -> Pair (Nil, Nil)
  | Cons (x, l) ->
    let Pair (s1, s2) = partition f l in
    (match f x with
     | True -> Pair ((Cons (x, s1)), s2)
     | False -> Pair (s1, (Cons (x, s2))))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements x =
    x

  (** val min_elt : t -> elt option **)

  let min_elt = function
  | Nil -> None
  | Cons (x, _) -> Some x

  (** val max_elt : t -> elt option **)

  let rec max_elt = function
  | Nil -> None
  | Cons (x, l) -> (match l with
                    | Nil -> Some x
                    | Cons (_, _) -> max_elt l)

  (** val choose : t -> elt option **)

  let choose =
    min_elt

  (** val compare : t -> t -> t compare0 **)

  let rec compare l s' =
    match l with
    | Nil -> (match s' with
              | Nil -> EQ
              | Cons (_, _) -> LT)
    | Cons (y, l0) ->
      (match s' with
       | Nil -> GT
       | Cons (a', l') ->
         (match X.compare y a' with
          | LT -> LT
          | EQ -> (match compare l0 l' with
                   | LT -> LT
                   | EQ -> EQ
                   | GT -> GT)
          | GT -> GT))
 end

module MakeRaw =
 functor (X:UsualOrderedType) ->
 struct
  module Raw = Raw(X)

  module E = X

  module OTFacts = OrderedTypeFacts(E)

  type slist =
    Raw.t
    (* singleton inductive, whose constructor was Build_slist *)

  (** val this : slist -> Raw.t **)

  let this s =
    s

  (** val coq_Build_slist' : Raw.t -> slist **)

  let coq_Build_slist' xs =
    xs

  type t = slist

  type elt = E.t

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    coq_Build_slist' (Raw.add x (this s))

  (** val remove : elt -> t -> t **)

  let remove x s =
    coq_Build_slist' (Raw.remove x (this s))

  (** val singleton : elt -> t **)

  let singleton x =
    coq_Build_slist' (Raw.singleton x)

  (** val union : t -> t -> t **)

  let union s s' =
    coq_Build_slist' (Raw.union (this s) (this s'))

  (** val inter : t -> t -> t **)

  let inter s s' =
    coq_Build_slist' (Raw.inter (this s) (this s'))

  (** val diff : t -> t -> t **)

  let diff s s' =
    coq_Build_slist' (Raw.diff (this s) (this s'))

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    coq_Build_slist' Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    coq_Build_slist' (Raw.filter f (this s))

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition f s =
    let p = Raw.partition f (this s) in
    Pair ((coq_Build_slist' (fst p)), (coq_Build_slist' (snd p)))

  (** val compare : t -> t -> t compare0 **)

  let compare s s' =
    match Raw.compare (this s) (this s') with
    | LT -> LT
    | EQ -> EQ
    | GT -> GT

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec s s' =
    match equal s s' with
    | True -> Left
    | False -> Right
 end

module Make =
 functor (X:UsualOrderedType) ->
 struct
  module E = X

  module S = MakeRaw(X)

  type fset = S.t

  type elt = S.elt
 end

module type VARIABLES =
 sig
  type var

  val var_default : var

  module Var_as_OT :
   UsualOrderedType with type t = var

  module VarSet :
   FinSet with module E = Var_as_OT

  type vars = VarSet.S.t

  val var_generate : vars -> var

  val var_fresh : vars -> var

  val var_of_Z : z -> var

  val coq_Z_of_var : var -> z
 end

module Variables =
 struct
  type var = z

  (** val var_default : var **)

  let var_default =
    Z0

  (** val var_of_Z : var -> var **)

  let var_of_Z x =
    x

  (** val coq_Z_of_var : z -> z **)

  let coq_Z_of_var x =
    x

  module Var_as_OT = Z_as_OT

  module VarSet = Make(Var_as_OT)

  type vars = VarSet.S.t

  (** val finite_nat_list_max : z list -> z **)

  let rec finite_nat_list_max = function
  | Nil -> Z0
  | Cons (y, l0) -> Z.max (finite_nat_list_max l0) y

  (** val finite_nat_list_max' : z list -> z **)

  let finite_nat_list_max' l =
    Z.add (finite_nat_list_max l) (Zpos XH)

  (** val var_generate : vars -> var **)

  let var_generate l =
    finite_nat_list_max' (VarSet.S.elements l)

  (** val var_generate_spec : __ **)

  let var_generate_spec =
    __

  (** val var_fresh : vars -> var **)

  let var_fresh =
    var_generate
 end

module Var_as_OT_Facts = OrderedTypeFacts(Variables.Var_as_OT)

(** val eq_var_dec : Variables.var -> Variables.var -> sumbool **)

let eq_var_dec =
  Var_as_OT_Facts.eq_dec

(** val var_freshes : Variables.vars -> nat -> Variables.var list **)

let rec var_freshes l = function
| O -> Nil
| S n0 ->
  let s = Variables.var_fresh l in
  let s0 =
    var_freshes (Variables.VarSet.S.union l (Variables.VarSet.S.singleton s))
      n0
  in
  Cons (s, s0)

module Env =
 struct
  type 'a env = (Variables.var, 'a) prod list

  (** val empty : 'a1 env **)

  let empty =
    Nil

  (** val single : Variables.var -> 'a1 -> (Variables.var, 'a1) prod list **)

  let single x a =
    Cons ((Pair (x, a)), Nil)

  (** val concat : 'a1 env -> 'a1 env -> (Variables.var, 'a1) prod list **)

  let concat e f =
    app f e

  (** val dom : 'a1 env -> Variables.vars **)

  let rec dom = function
  | Nil -> Variables.VarSet.S.empty
  | Cons (p, e') ->
    let Pair (x, _) = p in
    Variables.VarSet.S.union (Variables.VarSet.S.singleton x) (dom e')

  (** val map : ('a1 -> 'a1) -> 'a1 env -> 'a1 env **)

  let rec map f = function
  | Nil -> Nil
  | Cons (p, e') ->
    let Pair (x, v) = p in Cons ((Pair (x, (f v))), (map f e'))

  (** val get : Variables.var -> 'a1 env -> 'a1 option **)

  let rec get x = function
  | Nil -> None
  | Cons (p, e') ->
    let Pair (y, a) = p in
    (match eq_var_dec x y with
     | Left -> Some a
     | Right -> get x e')

  (** val fv_in : ('a1 -> Variables.vars) -> 'a1 env -> Variables.vars **)

  let rec fv_in fv = function
  | Nil -> Variables.VarSet.S.empty
  | Cons (p, e') ->
    let Pair (_, a) = p in Variables.VarSet.S.union (fv a) (fv_in fv e')
 end

(** val index :
    ('a1 -> 'a1 -> sumbool) -> nat -> 'a1 -> 'a1 list -> nat option **)

let rec index eq_dec0 i x = function
| Nil -> None
| Cons (y, l') ->
  (match eq_dec0 x y with
   | Left -> Some i
   | Right -> index eq_dec0 (S i) x l')

(** val list_snd : ('a1, 'a2) prod list -> 'a2 list **)

let list_snd l =
  map snd l

(** val map_snd :
    ('a2 -> 'a2) -> ('a1, 'a2) prod list -> ('a1, 'a2) prod list **)

let map_snd f =
  map (fun p -> Pair ((fst p), (f (snd p))))

(** val assoc :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> ('a1, 'a2) prod list -> 'a2 option **)

let rec assoc eq_dec0 x = function
| Nil -> None
| Cons (p, r) ->
  let Pair (y, z0) = p in
  (match eq_dec0 x y with
   | Left -> Some z0
   | Right -> assoc eq_dec0 x r)

(** val cut : nat -> 'a1 list -> ('a1 list, 'a1 list) prod **)

let rec cut n l =
  match n with
  | O -> Pair (Nil, l)
  | S n0 ->
    (match l with
     | Nil -> Pair (Nil, Nil)
     | Cons (a, l0) ->
       let Pair (l1, l2) = cut n0 l0 in Pair ((Cons (a, l1)), l2))

(** val mkset : Variables.var list -> Variables.vars **)

let rec mkset = function
| Nil -> Variables.VarSet.S.empty
| Cons (h, t0) ->
  Variables.VarSet.S.union (Variables.VarSet.S.singleton h) (mkset t0)

type 'a set = 'a list

(** val set_add : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| Nil -> Cons (a, Nil)
| Cons (a1, x1) ->
  (match aeq_dec a a1 with
   | Left -> Cons (a1, x1)
   | Right -> Cons (a1, (set_add aeq_dec a x1)))

(** val set_mem : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
| Nil -> False
| Cons (a1, x1) ->
  (match aeq_dec a a1 with
   | Left -> True
   | Right -> set_mem aeq_dec a x1)

(** val set_inter :
    ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_inter aeq_dec x y =
  match x with
  | Nil -> Nil
  | Cons (a1, x1) ->
    (match set_mem aeq_dec a1 y with
     | True -> Cons (a1, (set_inter aeq_dec x1 y))
     | False -> set_inter aeq_dec x1 y)

(** val set_union :
    ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
| Nil -> x
| Cons (a1, y1) -> set_add aeq_dec a1 (set_union aeq_dec x y1)

module type CstrIntf =
 sig
  type cstr

  type attr

  val valid_dec : cstr -> sumbool

  val eq_dec : attr -> attr -> sumbool

  val unique : cstr -> attr -> bool

  val lub : cstr -> cstr -> cstr
 end

module type CstIntf =
 sig
  type const

  val arity : const -> nat
 end

module MkDefs =
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct
  type typ =
  | Coq_typ_bvar of nat
  | Coq_typ_fvar of Variables.var
  | Coq_typ_arrow of typ * typ

  (** val typ_rect :
      (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1 ->
      'a1) -> typ -> 'a1 **)

  let rec typ_rect f f0 f1 = function
  | Coq_typ_bvar n -> f n
  | Coq_typ_fvar v -> f0 v
  | Coq_typ_arrow (t1, t2) ->
    f1 t1 (typ_rect f f0 f1 t1) t2 (typ_rect f f0 f1 t2)

  (** val typ_rec :
      (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1 ->
      'a1) -> typ -> 'a1 **)

  let rec typ_rec f f0 f1 = function
  | Coq_typ_bvar n -> f n
  | Coq_typ_fvar v -> f0 v
  | Coq_typ_arrow (t1, t2) ->
    f1 t1 (typ_rec f f0 f1 t1) t2 (typ_rec f f0 f1 t2)

  (** val typ_def : typ **)

  let typ_def =
    Coq_typ_bvar O

  type ckind = { kind_cstr : Cstr.cstr; kind_rel : (Cstr.attr, typ) prod list }

  (** val kind_cstr : ckind -> Cstr.cstr **)

  let kind_cstr c =
    c.kind_cstr

  (** val kind_rel : ckind -> (Cstr.attr, typ) prod list **)

  let kind_rel c =
    c.kind_rel

  type kind = ckind option

  type sch = { sch_type : typ; sch_kinds : kind list }

  (** val sch_type : sch -> typ **)

  let sch_type s =
    s.sch_type

  (** val sch_kinds : sch -> kind list **)

  let sch_kinds s =
    s.sch_kinds

  (** val typ_open : typ -> typ list -> typ **)

  let rec typ_open t0 vs =
    match t0 with
    | Coq_typ_bvar i -> nth i vs typ_def
    | Coq_typ_fvar x -> Coq_typ_fvar x
    | Coq_typ_arrow (t1, t2) ->
      Coq_typ_arrow ((typ_open t1 vs), (typ_open t2 vs))

  (** val typ_fvars : Variables.var list -> typ list **)

  let typ_fvars =
    map (fun x -> Coq_typ_fvar x)

  (** val typ_open_vars : typ -> Variables.var list -> typ **)

  let typ_open_vars t0 xs =
    typ_open t0 (typ_fvars xs)

  (** val sch_open : sch -> typ list -> typ **)

  let sch_open m =
    typ_open (sch_type m)

  (** val sch_open_vars : sch -> Variables.var list -> typ **)

  let sch_open_vars m =
    typ_open_vars (sch_type m)

  (** val kind_types : kind -> typ list **)

  let kind_types = function
  | Some k0 -> list_snd (kind_rel k0)
  | None -> Nil

  (** val ckind_map_spec : (typ -> typ) -> ckind -> ckind **)

  let ckind_map_spec f k =
    let { kind_cstr = kc; kind_rel = kr } = k in
    { kind_cstr = kc; kind_rel = (map_snd f kr) }

  (** val ckind_map : (typ -> typ) -> ckind -> ckind **)

  let ckind_map =
    ckind_map_spec

  (** val kind_map : (typ -> typ) -> kind -> kind **)

  let kind_map f = function
  | Some k0 -> Some (ckind_map f k0)
  | None -> None

  (** val kind_open : kind -> typ list -> kind **)

  let kind_open k vs =
    kind_map (fun t0 -> typ_open t0 vs) k

  type trm =
  | Coq_trm_bvar of nat
  | Coq_trm_fvar of Variables.var
  | Coq_trm_abs of trm
  | Coq_trm_let of trm * trm
  | Coq_trm_app of trm * trm
  | Coq_trm_cst of Const.const

  (** val trm_rect :
      (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) -> (trm
      -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) ->
      (Const.const -> 'a1) -> trm -> 'a1 **)

  let rec trm_rect f f0 f1 f2 f3 f4 = function
  | Coq_trm_bvar n -> f n
  | Coq_trm_fvar v -> f0 v
  | Coq_trm_abs t1 -> f1 t1 (trm_rect f f0 f1 f2 f3 f4 t1)
  | Coq_trm_let (t1, t2) ->
    f2 t1 (trm_rect f f0 f1 f2 f3 f4 t1) t2 (trm_rect f f0 f1 f2 f3 f4 t2)
  | Coq_trm_app (t1, t2) ->
    f3 t1 (trm_rect f f0 f1 f2 f3 f4 t1) t2 (trm_rect f f0 f1 f2 f3 f4 t2)
  | Coq_trm_cst c -> f4 c

  (** val trm_rec :
      (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) -> (trm
      -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) ->
      (Const.const -> 'a1) -> trm -> 'a1 **)

  let rec trm_rec f f0 f1 f2 f3 f4 = function
  | Coq_trm_bvar n -> f n
  | Coq_trm_fvar v -> f0 v
  | Coq_trm_abs t1 -> f1 t1 (trm_rec f f0 f1 f2 f3 f4 t1)
  | Coq_trm_let (t1, t2) ->
    f2 t1 (trm_rec f f0 f1 f2 f3 f4 t1) t2 (trm_rec f f0 f1 f2 f3 f4 t2)
  | Coq_trm_app (t1, t2) ->
    f3 t1 (trm_rec f f0 f1 f2 f3 f4 t1) t2 (trm_rec f f0 f1 f2 f3 f4 t2)
  | Coq_trm_cst c -> f4 c

  (** val trm_open_rec : nat -> trm -> trm -> trm **)

  let rec trm_open_rec k u = function
  | Coq_trm_bvar i ->
    (match Nat.eq_dec k i with
     | Left -> u
     | Right -> Coq_trm_bvar i)
  | Coq_trm_abs t1 -> Coq_trm_abs (trm_open_rec (S k) u t1)
  | Coq_trm_let (t1, t2) ->
    Coq_trm_let ((trm_open_rec k u t1), (trm_open_rec (S k) u t2))
  | Coq_trm_app (t1, t2) ->
    Coq_trm_app ((trm_open_rec k u t1), (trm_open_rec k u t2))
  | x -> x

  (** val trm_open : trm -> trm -> trm **)

  let trm_open t0 u =
    trm_open_rec O u t0

  (** val trm_def : trm **)

  let trm_def =
    Coq_trm_bvar O

  (** val trm_inst_rec : nat -> trm list -> trm -> trm **)

  let rec trm_inst_rec k tl t0 = match t0 with
  | Coq_trm_bvar i ->
    (match le_lt_dec k i with
     | Left -> nth (sub i k) tl t0
     | Right -> Coq_trm_bvar i)
  | Coq_trm_abs t1 -> Coq_trm_abs (trm_inst_rec (S k) tl t1)
  | Coq_trm_let (t1, t2) ->
    Coq_trm_let ((trm_inst_rec k tl t1), (trm_inst_rec (S k) tl t2))
  | Coq_trm_app (t1, t2) ->
    Coq_trm_app ((trm_inst_rec k tl t1), (trm_inst_rec k tl t2))
  | x -> x

  (** val trm_inst : trm -> trm list -> trm **)

  let trm_inst t0 tl =
    trm_inst_rec O tl t0

  (** val const_app : Const.const -> trm list -> trm **)

  let const_app c vl =
    fold_left (fun x x0 -> Coq_trm_app (x, x0)) vl (Coq_trm_cst c)

  type kenv = kind Env.env

  (** val kinds_open : kind list -> typ list -> kind list **)

  let kinds_open ks us =
    map (fun k -> kind_open k us) ks

  (** val kinds_open_vars :
      kind list -> Variables.var list -> (Variables.var, kind) prod list **)

  let kinds_open_vars ks xs =
    combine xs (kinds_open ks (typ_fvars xs))

  type env = sch Env.env

  (** val typ_fv : typ -> Variables.vars **)

  let rec typ_fv = function
  | Coq_typ_bvar _ -> Variables.VarSet.S.empty
  | Coq_typ_fvar x -> Variables.VarSet.S.singleton x
  | Coq_typ_arrow (t1, t2) -> Variables.VarSet.S.union (typ_fv t1) (typ_fv t2)

  (** val typ_fv_list : typ list -> Variables.VarSet.S.t **)

  let typ_fv_list =
    fold_right (fun t0 acc -> Variables.VarSet.S.union (typ_fv t0) acc)
      Variables.VarSet.S.empty

  (** val kind_fv : kind -> Variables.VarSet.S.t **)

  let kind_fv k =
    typ_fv_list (kind_types k)

  (** val kind_fv_list : kind list -> Variables.VarSet.S.t **)

  let kind_fv_list =
    fold_right (fun t0 acc -> Variables.VarSet.S.union (kind_fv t0) acc)
      Variables.VarSet.S.empty

  (** val sch_fv : sch -> Variables.VarSet.S.t **)

  let sch_fv m =
    Variables.VarSet.S.union (typ_fv (sch_type m))
      (kind_fv_list (sch_kinds m))

  (** val env_fv : sch Env.env -> Variables.vars **)

  let env_fv =
    Env.fv_in sch_fv

  module type DeltaIntf =
   sig
    val coq_type : Const.const -> sch

    val reduce : Const.const -> trm list -> trm
   end

  module MkJudge =
   functor (Delta:DeltaIntf) ->
   struct
    type gc_kind =
    | GcAny
    | GcLet

    (** val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1 **)

    let gc_kind_rect f f0 = function
    | GcAny -> f
    | GcLet -> f0

    (** val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1 **)

    let gc_kind_rec f f0 = function
    | GcAny -> f
    | GcLet -> f0

    type gc_info = (bool, gc_kind) prod

    (** val gc_raise : gc_info -> gc_info **)

    let rec gc_raise gc =
      match snd gc with
      | GcAny -> gc
      | GcLet -> Pair (True, GcLet)

    (** val gc_lower : gc_info -> gc_info **)

    let rec gc_lower gc =
      match snd gc with
      | GcAny -> gc
      | GcLet -> Pair (False, GcLet)
   end
 end

module MkInfra =
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct
  module Defs = MkDefs(Cstr)(Const)

  (** val trm_fv : Defs.trm -> Variables.vars **)

  let rec trm_fv = function
  | Defs.Coq_trm_fvar x -> Variables.VarSet.S.singleton x
  | Defs.Coq_trm_abs t1 -> trm_fv t1
  | Defs.Coq_trm_let (t1, t2) ->
    Variables.VarSet.S.union (trm_fv t1) (trm_fv t2)
  | Defs.Coq_trm_app (t1, t2) ->
    Variables.VarSet.S.union (trm_fv t1) (trm_fv t2)
  | _ -> Variables.VarSet.S.empty

  type subs = Defs.typ Env.env

  (** val typ_subst : subs -> Defs.typ -> Defs.typ **)

  let rec typ_subst s t0 = match t0 with
  | Defs.Coq_typ_bvar i -> Defs.Coq_typ_bvar i
  | Defs.Coq_typ_fvar x -> (match Env.get x s with
                            | Some t' -> t'
                            | None -> t0)
  | Defs.Coq_typ_arrow (t1, t2) ->
    Defs.Coq_typ_arrow ((typ_subst s t1), (typ_subst s t2))

  (** val kind_subst : subs -> Defs.kind -> Defs.kind **)

  let kind_subst s =
    Defs.kind_map (typ_subst s)

  (** val sch_subst : subs -> Defs.sch -> Defs.sch **)

  let sch_subst s m =
    { Defs.sch_type = (typ_subst s (Defs.sch_type m)); Defs.sch_kinds =
      (map (kind_subst s) (Defs.sch_kinds m)) }

  (** val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm **)

  let rec trm_subst z0 u = function
  | Defs.Coq_trm_fvar x ->
    (match eq_var_dec x z0 with
     | Left -> u
     | Right -> Defs.Coq_trm_fvar x)
  | Defs.Coq_trm_abs t1 -> Defs.Coq_trm_abs (trm_subst z0 u t1)
  | Defs.Coq_trm_let (t1, t2) ->
    Defs.Coq_trm_let ((trm_subst z0 u t1), (trm_subst z0 u t2))
  | Defs.Coq_trm_app (t1, t2) ->
    Defs.Coq_trm_app ((trm_subst z0 u t1), (trm_subst z0 u t2))
  | x -> x

  module MkJudgInfra =
   functor (Delta:Defs.DeltaIntf) ->
   struct
    module Judge = Defs.MkJudge(Delta)
   end
 end

module MkSound =
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct
  module Infra = MkInfra(Cstr)(Const)

  module Mk2 =
   functor (Delta:Infra.Defs.DeltaIntf) ->
   struct
    module JudgInfra = Infra.MkJudgInfra(Delta)

    module type SndHypIntf =
     sig
     end

    module Mk3 =
     functor (SH:SndHypIntf) ->
     struct
     end
   end
 end

module MkRename =
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct
  module Sound = MkSound(Cstr)(Const)

  module Mk2 =
   functor (Delta:Sound.Infra.Defs.DeltaIntf) ->
   struct
    module Sound2 = Sound.Mk2(Delta)

    (** val typ_generalize :
        Variables.var list -> Sound.Infra.Defs.typ -> Sound.Infra.Defs.typ **)

    let rec typ_generalize bs t0 = match t0 with
    | Sound.Infra.Defs.Coq_typ_bvar n ->
      Sound.Infra.Defs.Coq_typ_bvar (add (length bs) n)
    | Sound.Infra.Defs.Coq_typ_fvar x ->
      (match index eq_var_dec O x bs with
       | Some n -> Sound.Infra.Defs.Coq_typ_bvar n
       | None -> t0)
    | Sound.Infra.Defs.Coq_typ_arrow (t1, t2) ->
      Sound.Infra.Defs.Coq_typ_arrow ((typ_generalize bs t1),
        (typ_generalize bs t2))

    (** val sch_generalize :
        Variables.var list -> Sound.Infra.Defs.typ -> Sound.Infra.Defs.kind
        list -> Sound.Infra.Defs.sch **)

    let sch_generalize bs t0 ks =
      { Sound.Infra.Defs.sch_type = (typ_generalize bs t0);
        Sound.Infra.Defs.sch_kinds =
        (map (Sound.Infra.Defs.kind_map (typ_generalize bs)) ks) }
   end
 end

module MkEval =
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct
  module Rename = MkRename(Cstr)(Const)

  type clos =
  | Coq_clos_abs of Rename.Sound.Infra.Defs.trm * clos list
  | Coq_clos_const of Const.const * clos list

  (** val clos_rect :
      (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
      clos list -> 'a1) -> clos -> 'a1 **)

  let clos_rect f f0 = function
  | Coq_clos_abs (x, x0) -> f x x0
  | Coq_clos_const (x, x0) -> f0 x x0

  (** val clos_rec :
      (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
      clos list -> 'a1) -> clos -> 'a1 **)

  let clos_rec f f0 = function
  | Coq_clos_abs (x, x0) -> f x x0
  | Coq_clos_const (x, x0) -> f0 x x0

  (** val clos2trm : clos -> Rename.Sound.Infra.Defs.trm **)

  let rec clos2trm = function
  | Coq_clos_abs (t0, l) ->
    Rename.Sound.Infra.Defs.trm_inst (Rename.Sound.Infra.Defs.Coq_trm_abs t0)
      (map clos2trm l)
  | Coq_clos_const (cst, l) ->
    Rename.Sound.Infra.Defs.const_app cst (map clos2trm l)

  type frame = { frm_benv : clos list; frm_app : clos list;
                 frm_trm : Rename.Sound.Infra.Defs.trm }

  (** val frm_benv : frame -> clos list **)

  let frm_benv f =
    f.frm_benv

  (** val frm_app : frame -> clos list **)

  let frm_app f =
    f.frm_app

  (** val frm_trm : frame -> Rename.Sound.Infra.Defs.trm **)

  let frm_trm f =
    f.frm_trm

  (** val is_bvar : Rename.Sound.Infra.Defs.trm -> bool **)

  let is_bvar = function
  | Rename.Sound.Infra.Defs.Coq_trm_bvar _ -> True
  | _ -> False

  (** val app_trm :
      Rename.Sound.Infra.Defs.trm -> Rename.Sound.Infra.Defs.trm ->
      Rename.Sound.Infra.Defs.trm **)

  let app_trm t1 t2 =
    match t1 with
    | Rename.Sound.Infra.Defs.Coq_trm_abs t0 ->
      Rename.Sound.Infra.Defs.Coq_trm_let (t2, t0)
    | _ -> Rename.Sound.Infra.Defs.Coq_trm_app (t1, t2)

  (** val app2trm :
      Rename.Sound.Infra.Defs.trm -> clos list -> Rename.Sound.Infra.Defs.trm **)

  let app2trm t0 args =
    fold_left app_trm (map clos2trm args) t0

  (** val inst :
      Rename.Sound.Infra.Defs.trm -> clos list -> Rename.Sound.Infra.Defs.trm **)

  let inst t0 benv =
    Rename.Sound.Infra.Defs.trm_inst t0 (map clos2trm benv)

  (** val stack2trm :
      Rename.Sound.Infra.Defs.trm -> frame list -> Rename.Sound.Infra.Defs.trm **)

  let rec stack2trm t0 = function
  | Nil -> t0
  | Cons (f, rem) ->
    let { frm_benv = benv; frm_app = args; frm_trm = t1 } = f in
    let t2 = inst t1 benv in
    let t3 = match is_bvar t0 with
             | True -> t2
             | False -> app_trm t2 t0 in
    stack2trm (app2trm t3 args) rem

  type eval_res =
  | Result of nat * clos
  | Inter of frame list

  (** val eval_res_rect :
      (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1 **)

  let eval_res_rect f f0 = function
  | Result (x, x0) -> f x x0
  | Inter x -> f0 x

  (** val eval_res_rec :
      (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1 **)

  let eval_res_rec f f0 = function
  | Result (x, x0) -> f x x0
  | Inter x -> f0 x

  (** val res2trm : eval_res -> Rename.Sound.Infra.Defs.trm **)

  let res2trm = function
  | Result (_, cl) -> clos2trm cl
  | Inter l -> stack2trm Rename.Sound.Infra.Defs.trm_def l

  (** val clos_def : clos **)

  let clos_def =
    Coq_clos_abs (Rename.Sound.Infra.Defs.trm_def, Nil)

  (** val trm2clos :
      clos list -> clos Env.env -> Rename.Sound.Infra.Defs.trm -> clos **)

  let trm2clos benv fenv = function
  | Rename.Sound.Infra.Defs.Coq_trm_bvar n -> nth n benv clos_def
  | Rename.Sound.Infra.Defs.Coq_trm_fvar v ->
    (match Env.get v fenv with
     | Some c -> c
     | None -> clos_def)
  | Rename.Sound.Infra.Defs.Coq_trm_abs t1 -> Coq_clos_abs (t1, benv)
  | Rename.Sound.Infra.Defs.Coq_trm_cst c -> Coq_clos_const (c, Nil)
  | _ -> clos_def

  (** val trm2app :
      Rename.Sound.Infra.Defs.trm -> (Rename.Sound.Infra.Defs.trm,
      Rename.Sound.Infra.Defs.trm) prod option **)

  let trm2app = function
  | Rename.Sound.Infra.Defs.Coq_trm_let (t2, t1) ->
    Some (Pair ((Rename.Sound.Infra.Defs.Coq_trm_abs t1), t2))
  | Rename.Sound.Infra.Defs.Coq_trm_app (t1, t2) -> Some (Pair (t1, t2))
  | _ -> None

  module Mk2 =
   functor (Delta:Rename.Sound.Infra.Defs.DeltaIntf) ->
   struct
    module Rename2 = Rename.Mk2(Delta)

    (** val coq_Gc : (bool, Rename2.Sound2.JudgInfra.Judge.gc_kind) prod **)

    let coq_Gc =
      Pair (False, Rename2.Sound2.JudgInfra.Judge.GcAny)

    module type SndHypIntf2 =
     sig
      val reduce_clos : Const.const -> clos list -> (clos, clos list) prod
     end

    module Mk3 =
     functor (SH:SndHypIntf2) ->
     struct
      module Sound3 = Rename2.Sound2.Mk3(SH)

      (** val result :
          (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> frame
          list -> eval_res) -> nat -> clos -> frame list -> eval_res **)

      let result eval0 h c = function
      | Nil -> Result (h, c)
      | Cons (y, rem) ->
        let { frm_benv = benv'; frm_app = app'; frm_trm = t0 } = y in
        eval0 benv' (Cons (c, app')) t0 rem

      (** val eval :
          clos Env.env -> nat -> clos list -> clos list ->
          Rename.Sound.Infra.Defs.trm -> frame list -> eval_res **)

      let rec eval fenv h benv app0 t0 stack =
        match h with
        | O ->
          Inter (Cons ({ frm_benv = benv; frm_app = app0; frm_trm = t0 },
            stack))
        | S h0 ->
          (match trm2app t0 with
           | Some p ->
             let Pair (t1, t2) = p in
             eval fenv h0 benv Nil t2 (Cons ({ frm_benv = benv; frm_app =
               app0; frm_trm = t1 }, stack))
           | None ->
             let c = trm2clos benv fenv t0 in
             (match app0 with
              | Nil -> result (eval fenv h0) h0 c stack
              | Cons (c1, rem) ->
                (match c with
                 | Coq_clos_abs (t1, benv0) ->
                   eval fenv h0 (Cons (c1, benv0)) rem t1 stack
                 | Coq_clos_const (cst, l) ->
                   let nargs = add (length l) (length app0) in
                   let nred = S (Const.arity cst) in
                   (match le_lt_dec nred nargs with
                    | Left ->
                      let Pair (args, app') = cut nred (app l app0) in
                      let Pair (c0, app3) = SH.reduce_clos cst args in
                      (match c0 with
                       | Coq_clos_abs (t1, benv0) ->
                         eval fenv h0 benv0 (app app3 app')
                           (Rename.Sound.Infra.Defs.Coq_trm_abs t1) stack
                       | Coq_clos_const (cst', app'') ->
                         eval fenv h0 Nil (app app'' (app app3 app'))
                           (Rename.Sound.Infra.Defs.Coq_trm_cst cst') stack)
                    | Right ->
                      result (eval fenv h0) h0 (Coq_clos_const (cst,
                        (app l app0))) stack))))

      (** val is_abs : Rename.Sound.Infra.Defs.trm -> bool **)

      let is_abs = function
      | Rename.Sound.Infra.Defs.Coq_trm_abs _ -> True
      | _ -> False

      (** val eval_restart :
          clos Env.env -> nat -> frame list -> eval_res -> eval_res **)

      let eval_restart fenv h fl = function
      | Result (h', c) ->
        (match fl with
         | Nil -> Result ((add h' h), c)
         | Cons (y, rem) ->
           let { frm_benv = benv'; frm_app = app'; frm_trm = t0 } = y in
           eval fenv (add h' h) benv' (Cons (c, app')) t0 rem)
      | Inter l ->
        (match l with
         | Nil -> Inter fl
         | Cons (f, fl') ->
           let { frm_benv = benv; frm_app = args; frm_trm = t0 } = f in
           eval fenv h benv args t0 (app fl' fl))

      (** val reduce_clos : Const.const -> clos list -> clos list -> frame **)

      let reduce_clos c args args' =
        let Pair (c0, args3) = SH.reduce_clos c args in
        (match c0 with
         | Coq_clos_abs (t1, benv) ->
           { frm_benv = benv; frm_app = (app args3 args'); frm_trm =
             (Rename.Sound.Infra.Defs.Coq_trm_abs t1) }
         | Coq_clos_const (c', args'') ->
           { frm_benv = Nil; frm_app = (app args'' (app args3 args'));
             frm_trm = (Rename.Sound.Infra.Defs.Coq_trm_cst c') })

      (** val is_app : Rename.Sound.Infra.Defs.trm -> bool **)

      let is_app = function
      | Rename.Sound.Infra.Defs.Coq_trm_app (_, _) -> True
      | _ -> False

      (** val check_const_app : Rename.Sound.Infra.Defs.trm -> bool **)

      let check_const_app = function
      | Rename.Sound.Infra.Defs.Coq_trm_app (_, _) -> True
      | Rename.Sound.Infra.Defs.Coq_trm_cst _ -> True
      | _ -> False

      (** val eval_res_cont : eval_res -> bool **)

      let eval_res_cont = function
      | Result (n, _) -> (match n with
                          | O -> False
                          | S _ -> True)
      | Inter _ -> False
     end
   end
 end

module MkUnify =
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct
  module MyEval = MkEval(Cstr)(Const)

  (** val compose :
      MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
      MyEval.Rename.Sound.Infra.subs **)

  let compose s1 s2 =
    Env.concat s1 (Env.map (MyEval.Rename.Sound.Infra.typ_subst s1) s2)

  (** val id : MyEval.Rename.Sound.Infra.Defs.typ Env.env **)

  let id =
    Env.empty

  (** val get_kind :
      Variables.var -> MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.kind **)

  let get_kind x e =
    match Env.get x e with
    | Some k -> k
    | None -> None

  type 'a decidable = 'a -> sumbool

  (** val in_dec :
      Variables.VarSet.S.t -> Variables.VarSet.S.elt decidable **)

  let in_dec l x =
    match Variables.VarSet.S.mem x l with
    | True -> Left
    | False -> Right

  (** val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env **)

  let rec remove_env e x =
    match e with
    | Nil -> Nil
    | Cons (p, e') ->
      let Pair (y, a) = p in
      (match eq_var_dec x y with
       | Left -> e'
       | Right -> Cons ((Pair (y, a)), (remove_env e' x)))

  (** val unify_kind_rel :
      (Cstr.attr, MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      (Cstr.attr, MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (Cstr.attr
      -> bool) -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> ((Cstr.attr,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list,
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list) prod **)

  let rec unify_kind_rel kr kr' uniq pairs =
    match kr with
    | Nil -> Pair (kr', pairs)
    | Cons (p, krem) ->
      let Pair (l, t0) = p in
      (match uniq l with
       | True ->
         (match assoc Cstr.eq_dec l kr' with
          | Some t' ->
            unify_kind_rel krem kr' uniq (Cons ((Pair (t0, t')), pairs))
          | None ->
            unify_kind_rel krem (Cons ((Pair (l, t0)), kr')) uniq pairs)
       | False -> unify_kind_rel krem (Cons ((Pair (l, t0)), kr')) uniq pairs)

  (** val unify_kinds :
      MyEval.Rename.Sound.Infra.Defs.kind ->
      MyEval.Rename.Sound.Infra.Defs.kind ->
      (MyEval.Rename.Sound.Infra.Defs.kind,
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list) prod option **)

  let unify_kinds k1 k2 =
    match k1 with
    | Some c ->
      let { MyEval.Rename.Sound.Infra.Defs.kind_cstr = kc1;
        MyEval.Rename.Sound.Infra.Defs.kind_rel = kr1 } = c
      in
      (match k2 with
       | Some c0 ->
         let { MyEval.Rename.Sound.Infra.Defs.kind_cstr = kc2;
           MyEval.Rename.Sound.Infra.Defs.kind_rel = kr2 } = c0
         in
         let kc = Cstr.lub kc1 kc2 in
         (match Cstr.valid_dec kc with
          | Left ->
            let krp = unify_kind_rel (app kr1 kr2) Nil (Cstr.unique kc) Nil in
            Some (Pair ((Some { MyEval.Rename.Sound.Infra.Defs.kind_cstr =
            kc; MyEval.Rename.Sound.Infra.Defs.kind_rel = (fst krp) }),
            (snd krp)))
          | Right -> None)
       | None -> Some (Pair (k1, Nil)))
    | None -> Some (Pair (k2, Nil))

  type unif_res =
  | Uok of (MyEval.Rename.Sound.Infra.Defs.typ,
           MyEval.Rename.Sound.Infra.Defs.typ) prod list
     * MyEval.Rename.Sound.Infra.Defs.kenv * MyEval.Rename.Sound.Infra.subs
  | Ufail

  (** val unif_res_rect :
      ((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> 'a1) -> 'a1 -> unif_res -> 'a1 **)

  let unif_res_rect f f0 = function
  | Uok (x, x0, x1) -> f x x0 x1
  | Ufail -> f0

  (** val unif_res_rec :
      ((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> 'a1) -> 'a1 -> unif_res -> 'a1 **)

  let unif_res_rec f f0 = function
  | Uok (x, x0, x1) -> f x x0 x1
  | Ufail -> f0

  (** val unify_vars :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env -> Variables.var ->
      Variables.var -> unif_res **)

  let unify_vars k s x y =
    match unify_kinds (get_kind x k) (get_kind y k) with
    | Some p ->
      let Pair (k0, pairs) = p in
      Uok (pairs,
      (Env.concat (remove_env (remove_env k x) y) (Env.single y k0)),
      (compose (Env.single x (MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar y))
        s))
    | None -> Ufail

  (** val unify_nv :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env -> Variables.VarSet.S.elt ->
      MyEval.Rename.Sound.Infra.Defs.typ -> unif_res **)

  let unify_nv k s x t0 =
    match Variables.VarSet.S.mem x (MyEval.Rename.Sound.Infra.Defs.typ_fv t0) with
    | True -> Ufail
    | False ->
      (match get_kind x k with
       | Some _ -> Ufail
       | None -> Uok (Nil, (remove_env k x), (compose (Env.single x t0) s)))

  (** val unify1 :
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> unif_res **)

  let unify1 t1 t2 k s =
    match MyEval.Rename.Sound.Infra.typ_subst s t1 with
    | MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar n ->
      (match MyEval.Rename.Sound.Infra.typ_subst s t2 with
       | MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar m ->
         (match Nat.eq_dec n m with
          | Left -> Uok (Nil, k, s)
          | Right -> Ufail)
       | MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar x ->
         unify_nv k s x (MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar n)
       | MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow (_, _) -> Ufail)
    | MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar x ->
      (match MyEval.Rename.Sound.Infra.typ_subst s t2 with
       | MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar x0 ->
         (match eq_var_dec x x0 with
          | Left -> Uok (Nil, k, s)
          | Right -> unify_vars k s x x0)
       | x0 -> unify_nv k s x x0)
    | MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow (t11, t12) ->
      (match MyEval.Rename.Sound.Infra.typ_subst s t2 with
       | MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar _ -> Ufail
       | MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar x ->
         unify_nv k s x (MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow (t11,
           t12))
       | MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow (t21, t22) ->
         Uok ((Cons ((Pair (t11, t21)), (Cons ((Pair (t12, t22)), Nil)))), k,
           s))

  (** val accum :
      ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

  let rec accum f op unit0 = function
  | Nil -> unit0
  | Cons (a, rem) -> op (f a) (accum f op unit0 rem)

  (** val pair_subst :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod ->
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod **)

  let pair_subst s t0 =
    Pair ((MyEval.Rename.Sound.Infra.typ_subst s (fst t0)),
      (MyEval.Rename.Sound.Infra.typ_subst s (snd t0)))

  (** val typ_size : MyEval.Rename.Sound.Infra.Defs.typ -> nat **)

  let rec typ_size = function
  | MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow (t1, t2) ->
    S (add (typ_size t1) (typ_size t2))
  | _ -> S O

  (** val pair_size :
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod -> nat **)

  let pair_size p =
    add (add (S O) (typ_size (fst p))) (typ_size (snd p))

  (** val pairs_size :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> nat **)

  let pairs_size s pairs =
    accum pair_size add O (map (pair_subst s) pairs)

  (** val all_fv :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> Variables.VarSet.S.t **)

  let all_fv s pairs =
    accum (fun p ->
      Variables.VarSet.S.union
        (MyEval.Rename.Sound.Infra.Defs.typ_fv (fst p))
        (MyEval.Rename.Sound.Infra.Defs.typ_fv (snd p)))
      Variables.VarSet.S.union Variables.VarSet.S.empty
      (map (pair_subst s) pairs)

  (** val really_all_fv :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> Variables.VarSet.S.t **)

  let really_all_fv s k pairs =
    Variables.VarSet.S.union
      (Env.fv_in MyEval.Rename.Sound.Infra.Defs.kind_fv
        (Env.map (MyEval.Rename.Sound.Infra.kind_subst s) k)) (all_fv s pairs)

  (** val size_pairs :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> nat **)

  let size_pairs s k pairs =
    add (S O) (Variables.VarSet.S.cardinal (really_all_fv s k pairs))

  (** val size_pairs2 :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (nat, nat) prod **)

  let size_pairs2 s k pairs =
    Pair ((size_pairs s k pairs), (pairs_size s pairs))

  (** val unify1_dep :
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.subs ->
      (((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list,
      MyEval.Rename.Sound.Infra.Defs.kenv) prod,
      MyEval.Rename.Sound.Infra.subs) prod sumor **)

  let unify1_dep t1 t2 k s =
    match unify1 t1 t2 k s with
    | Uok (l, k0, s0) -> Inleft (Pair ((Pair (l, k0)), s0))
    | Ufail -> Inright

  (** val unify :
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.kenv,
      MyEval.Rename.Sound.Infra.subs) prod option **)

  let rec unify pairs k s =
    match pairs with
    | Nil -> Some (Pair (k, s))
    | Cons (p, pairs0) ->
      let Pair (t1, t2) = p in
      (match unify1_dep t1 t2 k s with
       | Inleft s0 ->
         let Pair (p0, s') = s0 in
         let Pair (pairs', k') = p0 in unify (app pairs' pairs0) k' s'
       | Inright -> None)

  (** val typ_kind :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.ckind option **)

  let typ_kind k = function
  | MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar x -> get_kind x k
  | _ -> None
 end

module MkInfer =
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct
  module Unify = MkUnify(Cstr)(Const)

  module Mk2 =
   functor (Delta:Unify.MyEval.Rename.Sound.Infra.Defs.DeltaIntf) ->
   struct
    module MyEval2 = Unify.MyEval.Mk2(Delta)

    (** val fvs :
        Unify.MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
        Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
        Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
        Variables.VarSet.S.t **)

    let fvs s k e =
      Variables.VarSet.S.union
        (Variables.VarSet.S.union
          (Variables.VarSet.S.union
            (Variables.VarSet.S.union (Env.dom s)
              (Env.fv_in Unify.MyEval.Rename.Sound.Infra.Defs.typ_fv s))
            (Env.dom k))
          (Env.fv_in Unify.MyEval.Rename.Sound.Infra.Defs.kind_fv k))
        (Unify.MyEval.Rename.Sound.Infra.Defs.env_fv e)

    (** val unify_dep :
        Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
        Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
        Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
        Unify.MyEval.Rename.Sound.Infra.subs ->
        (Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
        Unify.MyEval.Rename.Sound.Infra.subs) prod sumor **)

    let unify_dep t1 t2 k s =
      let o = Unify.unify (Cons ((Pair (t1, t2)), Nil)) k s in
      (match o with
       | Some p -> Inleft p
       | None -> Inright)

    (** val close_fvars :
        nat -> Unify.MyEval.Rename.Sound.Infra.Defs.kenv -> Variables.vars ->
        Variables.vars -> Variables.vars **)

    let rec close_fvars n k vK vs =
      match n with
      | O -> vs
      | S n' ->
        (match Variables.VarSet.S.choose (Variables.VarSet.S.inter vK vs) with
         | Some x ->
           let vK' = Variables.VarSet.S.remove x vK in
           let vs' =
             match Env.get x k with
             | Some k0 ->
               Variables.VarSet.S.union vs
                 (Unify.MyEval.Rename.Sound.Infra.Defs.kind_fv k0)
             | None -> vs
           in
           close_fvars n' k vK' vs'
         | None -> vs)

    (** val close_fvk :
        (Variables.var, Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list
        -> Variables.vars -> Variables.vars **)

    let close_fvk k =
      close_fvars (length k) k (Env.dom k)

    (** val split_env :
        Variables.vars -> 'a1 Env.env -> ('a1 Env.env, 'a1 Env.env) prod **)

    let rec split_env b = function
    | Nil -> Pair (Nil, Nil)
    | Cons (xk, e') ->
      let Pair (eb, eB) = split_env b e' in
      (match Variables.VarSet.S.mem (fst xk) b with
       | True -> Pair (eb, (Cons (xk, eB)))
       | False -> Pair ((Cons (xk, eb)), eB))

    (** val vars_subst :
        Unify.MyEval.Rename.Sound.Infra.subs -> Variables.VarSet.S.t ->
        Variables.VarSet.S.t **)

    let vars_subst s l =
      Unify.MyEval.Rename.Sound.Infra.Defs.typ_fv_list
        (map (fun x ->
          Unify.MyEval.Rename.Sound.Infra.typ_subst s
            (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar x))
          (Variables.VarSet.S.elements l))

    (** val typinf_generalize :
        (Variables.var, Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list
        -> Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env -> Variables.vars
        -> Unify.MyEval.Rename.Sound.Infra.Defs.typ -> ((Variables.var,
        Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list,
        Unify.MyEval.Rename.Sound.Infra.Defs.sch) prod **)

    let typinf_generalize k' e' l t1 =
      let ftve = close_fvk k' (Unify.MyEval.Rename.Sound.Infra.Defs.env_fv e')
      in
      let Pair (k'', kA) = split_env ftve k' in
      let b = close_fvk k' (Unify.MyEval.Rename.Sound.Infra.Defs.typ_fv t1) in
      let Pair (_, kB) = split_env b k'' in
      let Pair (bs, ks) = split kB in
      let bs' =
        Variables.VarSet.S.elements
          (Variables.VarSet.S.diff b
            (Variables.VarSet.S.union ftve (Env.dom kB)))
      in
      let ks' = map (fun _ -> None) bs' in
      let Pair (_, kC) = split_env l k'' in
      Pair ((Env.concat kA kC),
      (MyEval2.Rename2.sch_generalize (app bs bs') t1 (app ks ks')))

    (** val kdom :
        Unify.MyEval.Rename.Sound.Infra.Defs.kenv -> Variables.vars **)

    let rec kdom = function
    | Nil -> Variables.VarSet.S.empty
    | Cons (p, e') ->
      let Pair (x, k) = p in
      (match k with
       | Some _ ->
         Variables.VarSet.S.union (Variables.VarSet.S.singleton x) (kdom e')
       | None -> kdom e')

    (** val trm_depth : Unify.MyEval.Rename.Sound.Infra.Defs.trm -> nat **)

    let rec trm_depth = function
    | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_abs t1 -> S (trm_depth t1)
    | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_let (t1, t2) ->
      S (Nat.max (trm_depth t1) (trm_depth t2))
    | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_app (t1, t2) ->
      S (Nat.max (trm_depth t1) (trm_depth t2))
    | _ -> O

    (** val get_dep : Variables.var -> 'a1 Env.env -> 'a1 sumor **)

    let get_dep x e =
      match Env.get x e with
      | Some a -> Inleft a
      | None -> Inright

    (** val typinf :
        Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
        Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
        Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
        Unify.MyEval.Rename.Sound.Infra.Defs.typ -> Variables.VarSet.S.t ->
        Unify.MyEval.Rename.Sound.Infra.subs ->
        ((Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
        Unify.MyEval.Rename.Sound.Infra.subs) prod, Variables.vars) prod
        option **)

    let rec typinf k e t0 t1 l s =
      match t0 with
      | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_bvar _ -> None
      | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_fvar x ->
        (match get_dep x e with
         | Inleft s0 ->
           let vs =
             var_freshes l
               (length (Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds s0))
           in
           (match unify_dep
                    (Unify.MyEval.Rename.Sound.Infra.Defs.sch_open_vars s0 vs)
                    t1
                    (Env.concat k
                      (Unify.MyEval.Rename.Sound.Infra.Defs.kinds_open_vars
                        (Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds s0)
                        vs)) s with
            | Inleft s1 ->
              Some (Pair (s1, (Variables.VarSet.S.union l (mkset vs))))
            | Inright -> None)
         | Inright -> None)
      | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_abs t2 ->
        let x =
          Variables.var_fresh
            (Variables.VarSet.S.union (Env.dom e)
              (Unify.MyEval.Rename.Sound.Infra.trm_fv t2))
        in
        let v1 = Variables.var_fresh l in
        let v2 =
          Variables.var_fresh
            (Variables.VarSet.S.union l (Variables.VarSet.S.singleton v1))
        in
        (match unify_dep (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow
                 ((Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar v1),
                 (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar v2))) t1
                 k s with
         | Inleft s0 ->
           let Pair (k', s') = s0 in
           typinf k'
             (Env.concat e
               (Env.single x
                 { Unify.MyEval.Rename.Sound.Infra.Defs.sch_type =
                 (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar v1);
                 Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds = Nil }))
             (Unify.MyEval.Rename.Sound.Infra.Defs.trm_open t2
               (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_fvar x))
             (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar v2)
             (Variables.VarSet.S.union
               (Variables.VarSet.S.union l (Variables.VarSet.S.singleton v1))
               (Variables.VarSet.S.singleton v2)) s'
         | Inright -> None)
      | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_let (t2, t3) ->
        let v = Variables.var_fresh l in
        (match typinf k e t2
                 (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar v)
                 (Variables.VarSet.S.union l (Variables.VarSet.S.singleton v))
                 s with
         | Some s0 ->
           let Pair (p, l') = s0 in
           let Pair (k0, s') = p in
           let k' = Env.map (Unify.MyEval.Rename.Sound.Infra.kind_subst s') k0
           in
           let e' = Env.map (Unify.MyEval.Rename.Sound.Infra.sch_subst s') e
           in
           let t4 =
             Unify.MyEval.Rename.Sound.Infra.typ_subst s'
               (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar v)
           in
           let kAM = typinf_generalize k' e' (vars_subst s' (kdom k)) t4 in
           let x =
             Variables.var_fresh
               (Variables.VarSet.S.union
                 (Variables.VarSet.S.union (Env.dom e)
                   (Unify.MyEval.Rename.Sound.Infra.trm_fv t2))
                 (Unify.MyEval.Rename.Sound.Infra.trm_fv t3))
           in
           typinf (fst kAM) (Env.concat e (Env.single x (snd kAM)))
             (Unify.MyEval.Rename.Sound.Infra.Defs.trm_open t3
               (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_fvar x)) t1 l' s'
         | None -> None)
      | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_app (t2, t3) ->
        let v = Variables.var_fresh l in
        (match typinf k e t2
                 (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow
                 ((Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar v), t1))
                 (Variables.VarSet.S.union l (Variables.VarSet.S.singleton v))
                 s with
         | Some s0 ->
           let Pair (p, l') = s0 in
           let Pair (k', s') = p in
           typinf k' e t3 (Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar
             v) l' s'
         | None -> None)
      | Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_cst c ->
        let m = Delta.coq_type c in
        let vs =
          var_freshes l
            (length (Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds m))
        in
        (match unify_dep
                 (Unify.MyEval.Rename.Sound.Infra.Defs.sch_open_vars m vs) t1
                 (Env.concat k
                   (Unify.MyEval.Rename.Sound.Infra.Defs.kinds_open_vars
                     (Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds m) vs)) s with
         | Inleft s0 ->
           Some (Pair (s0, (Variables.VarSet.S.union l (mkset vs))))
         | Inright -> None)

    (** val typinf0 :
        Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
        Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
        Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
        Unify.MyEval.Rename.Sound.Infra.Defs.typ -> Variables.VarSet.S.t ->
        Unify.MyEval.Rename.Sound.Infra.subs ->
        ((Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
        Unify.MyEval.Rename.Sound.Infra.subs) prod, Variables.vars) prod
        option **)

    let typinf0 =
      typinf

    (** val typinf' :
        Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
        Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
        (Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env,
        Unify.MyEval.Rename.Sound.Infra.Defs.typ) prod option **)

    let typinf' e t0 =
      let min_vars =
        Variables.VarSet.S.union
          (Unify.MyEval.Rename.Sound.Infra.Defs.env_fv e)
          (Variables.VarSet.S.singleton Variables.var_default)
      in
      let v = Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_fvar
        Variables.var_default
      in
      (match typinf Env.empty e t0 v min_vars Unify.id with
       | Some s0 ->
         let Pair (p, _) = s0 in
         let Pair (k, s) = p in
         Some (Pair
         ((Env.map (Unify.MyEval.Rename.Sound.Infra.kind_subst s) k),
         (Unify.MyEval.Rename.Sound.Infra.typ_subst s v)))
       | None -> None)

    (** val coq_Gc :
        (bool, MyEval2.Rename2.Sound2.JudgInfra.Judge.gc_kind) prod **)

    let coq_Gc =
      Pair (False, MyEval2.Rename2.Sound2.JudgInfra.Judge.GcLet)
   end
 end

(** val set_incl :
    ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1 list -> sumbool **)

let rec set_incl eq_dec0 s1 s2 =
  match s1 with
  | Nil -> Left
  | Cons (y, l) ->
    (match set_mem eq_dec0 y s2 with
     | True -> set_incl eq_dec0 l s2
     | False -> Right)

module Cstr =
 struct
  type attr = nat

  (** val eq_dec : nat -> nat -> sumbool **)

  let eq_dec =
    Nat.eq_dec

  type ksort =
  | Ksum
  | Kprod
  | Kbot

  (** val ksort_rect : 'a1 -> 'a1 -> 'a1 -> ksort -> 'a1 **)

  let ksort_rect f f0 f1 = function
  | Ksum -> f
  | Kprod -> f0
  | Kbot -> f1

  (** val ksort_rec : 'a1 -> 'a1 -> 'a1 -> ksort -> 'a1 **)

  let ksort_rec f f0 f1 = function
  | Ksum -> f
  | Kprod -> f0
  | Kbot -> f1

  type cstr_impl = { cstr_sort : ksort; cstr_low : nat list;
                     cstr_high : nat list option }

  (** val cstr_sort : cstr_impl -> ksort **)

  let cstr_sort c =
    c.cstr_sort

  (** val cstr_low : cstr_impl -> nat list **)

  let cstr_low c =
    c.cstr_low

  (** val cstr_high : cstr_impl -> nat list option **)

  let cstr_high c =
    c.cstr_high

  type cstr = cstr_impl

  (** val unique : cstr_impl -> nat -> bool **)

  let unique c v =
    set_mem Nat.eq_dec v c.cstr_low

  (** val sort_lub : ksort -> ksort -> ksort **)

  let sort_lub s1 s2 =
    match s1 with
    | Ksum -> (match s2 with
               | Ksum -> Ksum
               | _ -> Kbot)
    | Kprod -> (match s2 with
                | Ksum -> Kbot
                | x -> x)
    | Kbot -> Kbot

  (** val lub : cstr_impl -> cstr_impl -> cstr_impl **)

  let lub c1 c2 =
    { cstr_sort = (sort_lub c1.cstr_sort c2.cstr_sort); cstr_low =
      (set_union Nat.eq_dec c1.cstr_low c2.cstr_low); cstr_high =
      (match c1.cstr_high with
       | Some s1 ->
         (match c2.cstr_high with
          | Some s2 -> Some (set_inter Nat.eq_dec s1 s2)
          | None -> Some s1)
       | None -> c2.cstr_high) }

  (** val ksort_dec : ksort -> sumbool **)

  let ksort_dec = function
  | Kbot -> Left
  | _ -> Right

  (** val valid_dec : cstr_impl -> sumbool **)

  let valid_dec c =
    let s = ksort_dec c.cstr_sort in
    (match s with
     | Left -> Right
     | Right ->
       (match c.cstr_high with
        | Some l -> set_incl Nat.eq_dec c.cstr_low l
        | None -> Left))
 end

module Const =
 struct
  type ops =
  | Coq_tag of Cstr.attr
  | Coq_matches of Cstr.attr list
  | Coq_record of Cstr.attr list
  | Coq_sub of Cstr.attr
  | Coq_recf

  (** val ops_rect :
      (Cstr.attr -> 'a1) -> (Cstr.attr list -> __ -> 'a1) -> (Cstr.attr list
      -> __ -> 'a1) -> (Cstr.attr -> 'a1) -> 'a1 -> ops -> 'a1 **)

  let ops_rect f f0 f1 f2 f3 = function
  | Coq_tag x -> f x
  | Coq_matches x -> f0 x __
  | Coq_record x -> f1 x __
  | Coq_sub x -> f2 x
  | Coq_recf -> f3

  (** val ops_rec :
      (Cstr.attr -> 'a1) -> (Cstr.attr list -> __ -> 'a1) -> (Cstr.attr list
      -> __ -> 'a1) -> (Cstr.attr -> 'a1) -> 'a1 -> ops -> 'a1 **)

  let ops_rec f f0 f1 f2 f3 = function
  | Coq_tag x -> f x
  | Coq_matches x -> f0 x __
  | Coq_record x -> f1 x __
  | Coq_sub x -> f2 x
  | Coq_recf -> f3

  type const = ops

  (** val arity : ops -> nat **)

  let arity = function
  | Coq_matches l -> length l
  | Coq_record l -> length l
  | Coq_sub _ -> O
  | _ -> S O
 end

module Infer = MkInfer(Cstr)(Const)

module Delta =
 struct
  (** val matches_arg :
      nat -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ **)

  let matches_arg n =
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow
      ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar n),
      (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar (S O)))

  (** val coq_type :
      Const.const -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch **)

  let coq_type = function
  | Const.Coq_tag t0 ->
    { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_type =
      (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow
      ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar O),
      (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar (S O))));
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds = (Cons (None,
      (Cons ((Some { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_cstr =
      { Cstr.cstr_sort = Cstr.Ksum; Cstr.cstr_low = (Cons (t0, Nil));
      Cstr.cstr_high = None };
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_rel = (Cons ((Pair (t0,
      (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar O))),
      Nil)) }), Nil)))) }
  | Const.Coq_matches l ->
    { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_type =
      (fold_right (fun x x0 ->
        Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow (x, x0))
        (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow
        ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar O),
        (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar (S O))))
        (map matches_arg (seq (S (S O)) (length l))));
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds = (Cons ((Some
      { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_cstr =
      { Cstr.cstr_sort = Cstr.Ksum; Cstr.cstr_low = Nil; Cstr.cstr_high =
      (Some l) }; Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_rel =
      (combine l
        (map (fun x ->
          Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar x)
          (seq (S (S O)) (length l)))) }),
      (map (fun _ -> None) (seq O (S (length l)))))) }
  | Const.Coq_record l ->
    { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_type =
      (fold_right (fun x x0 ->
        Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow (x, x0))
        (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar O)
        (map (fun x ->
          Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar x)
          (seq (S O) (length l))));
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds = (Cons ((Some
      { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_cstr =
      { Cstr.cstr_sort = Cstr.Kprod; Cstr.cstr_low = Nil; Cstr.cstr_high =
      (Some l) }; Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_rel =
      (combine l
        (map (fun x ->
          Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar x)
          (seq (S O) (length l)))) }),
      (map (fun _ -> None) (seq O (length l))))) }
  | Const.Coq_sub f ->
    { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_type =
      (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow
      ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar (S O)),
      (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar O)));
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds = (Cons (None,
      (Cons ((Some { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_cstr =
      { Cstr.cstr_sort = Cstr.Kprod; Cstr.cstr_low = (Cons (f, Nil));
      Cstr.cstr_high = None };
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_rel = (Cons ((Pair (f,
      (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar O))),
      Nil)) }), Nil)))) }
  | Const.Coq_recf ->
    let t0 = Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow
      ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar O),
      (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_bvar (S O)))
    in
    { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_type =
    (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow
    ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_typ_arrow (t0, t0)),
    t0)); Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds = (Cons (None,
    (Cons (None, Nil)))) }

  (** val trm_default : Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm **)

  let trm_default =
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_abs
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm_def

  (** val record_args :
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm list -> (nat list,
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm list) prod **)

  let rec record_args t0 tl =
    match t0 with
    | Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_app (t1, t2) ->
      record_args t1 (Cons (t2, tl))
    | Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_cst c ->
      (match c with
       | Const.Coq_record l -> Pair (l, tl)
       | _ -> Pair (Nil, Nil))
    | _ -> Pair (Nil, Nil)

  (** val is_record : Const.ops -> bool **)

  let is_record = function
  | Const.Coq_record _ -> True
  | _ -> False

  (** val reduce :
      Const.ops -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm list ->
      Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm **)

  let reduce c tl =
    match c with
    | Const.Coq_matches l ->
      (match nth (length l) tl
               Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm_def with
       | Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_app (t0, t1) ->
         (match t0 with
          | Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_cst c0 ->
            (match c0 with
             | Const.Coq_tag t2 ->
               (match index Nat.eq_dec O t2 l with
                | Some i ->
                  Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_app
                    ((nth i tl
                       Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm_def),
                    t1)
                | None -> trm_default)
             | _ -> trm_default)
          | _ -> trm_default)
       | _ -> trm_default)
    | Const.Coq_sub f ->
      (match tl with
       | Nil -> trm_default
       | Cons (t0, _) ->
         let Pair (l, fl) = record_args t0 Nil in
         (match index Nat.eq_dec O f l with
          | Some i -> nth i fl trm_default
          | None -> trm_default))
    | Const.Coq_recf ->
      (match tl with
       | Nil -> trm_default
       | Cons (f, l) ->
         (match l with
          | Nil -> trm_default
          | Cons (a, _) ->
            Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_app
              ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_app (f,
              (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_app
              ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.Coq_trm_cst
              Const.Coq_recf), f)))), a)))
    | _ -> trm_default
 end

module Infer2 = Infer.Mk2(Delta)

module SndHyp =
 struct
  (** val reduce_clos :
      Const.ops -> Infer.Unify.MyEval.clos list -> (Infer.Unify.MyEval.clos,
      Infer.Unify.MyEval.clos list) prod **)

  let reduce_clos c cl =
    match c with
    | Const.Coq_matches l ->
      (match nth (length l) cl Infer.Unify.MyEval.clos_def with
       | Infer.Unify.MyEval.Coq_clos_abs (_, _) ->
         Pair (Infer.Unify.MyEval.clos_def, Nil)
       | Infer.Unify.MyEval.Coq_clos_const (c0, l0) ->
         (match c0 with
          | Const.Coq_tag t0 ->
            (match l0 with
             | Nil -> Pair (Infer.Unify.MyEval.clos_def, Nil)
             | Cons (cl1, l1) ->
               (match l1 with
                | Nil ->
                  (match index Nat.eq_dec O t0 l with
                   | Some i ->
                     Pair ((nth i cl Infer.Unify.MyEval.clos_def), (Cons
                       (cl1, Nil)))
                   | None -> Pair (Infer.Unify.MyEval.clos_def, Nil))
                | Cons (_, _) -> Pair (Infer.Unify.MyEval.clos_def, Nil)))
          | _ -> Pair (Infer.Unify.MyEval.clos_def, Nil)))
    | Const.Coq_sub f ->
      (match cl with
       | Nil -> Pair (Infer.Unify.MyEval.clos_def, Nil)
       | Cons (c0, _) ->
         (match c0 with
          | Infer.Unify.MyEval.Coq_clos_abs (_, _) ->
            Pair (Infer.Unify.MyEval.clos_def, Nil)
          | Infer.Unify.MyEval.Coq_clos_const (c1, cls) ->
            (match c1 with
             | Const.Coq_record l ->
               (match index Nat.eq_dec O f l with
                | Some i ->
                  Pair ((nth i cls Infer.Unify.MyEval.clos_def), Nil)
                | None -> Pair (Infer.Unify.MyEval.clos_def, Nil))
             | _ -> Pair (Infer.Unify.MyEval.clos_def, Nil))))
    | Const.Coq_recf ->
      (match cl with
       | Nil -> Pair (Infer.Unify.MyEval.clos_def, Nil)
       | Cons (cl1, rem) ->
         Pair (cl1, (Cons ((Infer.Unify.MyEval.Coq_clos_const
           (Const.Coq_recf, (Cons (cl1, Nil)))), rem))))
    | _ -> Pair (Infer.Unify.MyEval.clos_def, Nil)
 end

module Sound3 = Infer2.MyEval2.Mk3(SndHyp)

type 'a decidable0 = 'a -> sumbool

(** val ok_dec :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env decidable0 **)

let rec ok_dec = function
| Nil -> Left
| Cons (y, l0) ->
  let Pair (v, _) = y in
  (match ok_dec l0 with
   | Left -> (match Env.get v l0 with
              | Some _ -> Right
              | None -> Left)
   | Right -> Right)

(** val type_n_dec :
    nat -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ decidable0 **)

let type_n_dec n t0 =
  Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ_rec (fun n0 ->
    let s = le_lt_dec n n0 in (match s with
                               | Left -> Right
                               | Right -> Left)) (fun _ -> Left)
    (fun _ iHT1 _ iHT2 -> match iHT1 with
                          | Left -> iHT2
                          | Right -> Right) t0

(** val list_forall_dec : 'a1 decidable0 -> 'a1 list decidable0 **)

let rec list_forall_dec hP = function
| Nil -> Left
| Cons (y, l0) ->
  let s = hP y in
  (match s with
   | Left -> list_forall_dec hP l0
   | Right -> Right)

(** val scheme_dec :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch decidable0 **)

let scheme_dec x =
  let { Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_type = t0;
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch_kinds = ks } = x
  in
  let n = length ks in
  let s = type_n_dec n t0 in
  (match s with
   | Left ->
     let h = list_forall_dec (type_n_dec n) in
     list_forall_dec (fun k ->
       h (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind_types k)) ks
   | Right -> Right)

(** val env_prop_dec : 'a1 decidable0 -> 'a1 Env.env decidable0 **)

let rec env_prop_dec hP = function
| Nil -> Left
| Cons (y, l) ->
  let Pair (_, a) = y in
  let s = hP a in (match s with
                   | Left -> env_prop_dec hP l
                   | Right -> Right)

(** val typinf1 :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
    ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ) prod, sumbool) sum **)

let typinf1 e t0 =
  match Variables.VarSet.S.is_empty
          (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.env_fv e) with
  | True ->
    let s = ok_dec e in
    (match s with
     | Left ->
       let s0 = env_prop_dec scheme_dec e in
       (match s0 with
        | Left ->
          (match Infer2.typinf' e t0 with
           | Some p -> Inl p
           | None -> Inr Right)
        | Right -> Inr Right)
     | Right -> Inr Right)
  | False -> Inr Left

(** val eval1 :
    Infer.Unify.MyEval.clos Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> nat ->
    Infer.Unify.MyEval.eval_res **)

let eval1 fenv t0 h =
  Sound3.eval fenv h Nil Nil t0 Nil
