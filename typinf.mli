type __ = Obj.t

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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
  | Eq
  | Lt
  | Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val proj1_sig : 'a1 -> 'a1

type sumbool =
  | Left
  | Right

type 'a sumor =
  | Inleft of 'a
  | Inright

val plus : nat -> nat -> nat

val minus : nat -> nat -> nat

type 'a list =
  | Nil
  | Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val split : ('a1, 'a2) prod list -> ('a1 list, 'a2 list) prod

val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list

val seq : nat -> nat -> nat list

val eq_nat_dec : nat -> nat -> sumbool

val le_lt_dec : nat -> nat -> sumbool

type positive =
  | XI of positive
  | XO of positive
  | XH

val psucc : positive -> positive

val pplus : positive -> positive -> positive

val pplus_carry : positive -> positive -> positive

val pdouble_minus_one : positive -> positive

type positive_mask =
  | IsNul
  | IsPos of positive
  | IsNeg

val pdouble_plus_one_mask : positive_mask -> positive_mask

val pdouble_mask : positive_mask -> positive_mask

val pdouble_minus_two : positive -> positive_mask

val pminus_mask : positive -> positive -> positive_mask

val pminus_mask_carry : positive -> positive -> positive_mask

val pminus : positive -> positive -> positive

val pcompare : positive -> positive -> comparison -> comparison

val max : nat -> nat -> nat

type z =
  | Z0
  | Zpos of positive
  | Zneg of positive

val zplus : z -> z -> z

val zcompare : z -> z -> comparison

val zmax : z -> z -> z

val dcompare_inf : comparison -> sumbool sumor

val zcompare_rec : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

val z_eq_dec : z -> z -> sumbool

type 'x compare =
  | LT
  | EQ
  | GT

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare
  
  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts : 
 functor (O:OrderedType) ->
 sig 
  val eq_dec : O.t -> O.t -> sumbool
  
  val lt_dec : O.t -> O.t -> sumbool
  
  val eqb : O.t -> O.t -> bool
 end

module type UsualOrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare
  
  val eq_dec : t -> t -> sumbool
 end

module Z_as_OT : 
 sig 
  type t = z
  
  val compare : z -> z -> z compare
  
  val eq_dec : z -> z -> sumbool
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
  
  val compare : t -> t -> t compare
  
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

module Raw : 
 functor (X:OrderedType) ->
 sig 
  module MX : 
   sig 
    val eq_dec : X.t -> X.t -> sumbool
    
    val lt_dec : X.t -> X.t -> sumbool
    
    val eqb : X.t -> X.t -> bool
   end
  
  type elt = X.t
  
  type t = elt list
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val choose : t -> elt option
  
  val compare : t -> t -> t compare
 end

module MakeRaw : 
 functor (X:UsualOrderedType) ->
 sig 
  module Raw : 
   sig 
    module MX : 
     sig 
      val eq_dec : X.t -> X.t -> sumbool
      
      val lt_dec : X.t -> X.t -> sumbool
      
      val eqb : X.t -> X.t -> bool
     end
    
    type elt = X.t
    
    type t = elt list
    
    val empty : t
    
    val is_empty : t -> bool
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val singleton : elt -> t
    
    val remove : elt -> t -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val cardinal : t -> nat
    
    val elements : t -> elt list
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
    
    val choose : t -> elt option
    
    val compare : t -> t -> t compare
   end
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t compare
    
    val eq_dec : t -> t -> sumbool
   end
  
  module OTFacts : 
   sig 
    val eq_dec : X.t -> X.t -> sumbool
    
    val lt_dec : X.t -> X.t -> sumbool
    
    val eqb : X.t -> X.t -> bool
   end
  
  type slist =
    Raw.t
    (* singleton inductive, whose constructor was Build_slist *)
  
  val slist_rect : (Raw.t -> __ -> 'a1) -> slist -> 'a1
  
  val slist_rec : (Raw.t -> __ -> 'a1) -> slist -> 'a1
  
  val this : slist -> Raw.t
  
  val coq_Build_slist' : Raw.t -> slist
  
  type t = slist
  
  type elt = X.t
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val remove : elt -> t -> t
  
  val singleton : elt -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val empty : t
  
  val is_empty : t -> bool
  
  val elements : t -> elt list
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val choose : t -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val cardinal : t -> nat
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val compare : t -> t -> t compare
  
  val eq_dec : t -> t -> sumbool
 end

module Make : 
 functor (X:UsualOrderedType) ->
 sig 
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t compare
    
    val eq_dec : t -> t -> sumbool
   end
  
  module S : 
   sig 
    module Raw : 
     sig 
      module MX : 
       sig 
        val eq_dec : X.t -> X.t -> sumbool
        
        val lt_dec : X.t -> X.t -> sumbool
        
        val eqb : X.t -> X.t -> bool
       end
      
      type elt = X.t
      
      type t = elt list
      
      val empty : t
      
      val is_empty : t -> bool
      
      val mem : elt -> t -> bool
      
      val add : elt -> t -> t
      
      val singleton : elt -> t
      
      val remove : elt -> t -> t
      
      val union : t -> t -> t
      
      val inter : t -> t -> t
      
      val diff : t -> t -> t
      
      val equal : t -> t -> bool
      
      val subset : t -> t -> bool
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val filter : (elt -> bool) -> t -> t
      
      val for_all : (elt -> bool) -> t -> bool
      
      val exists_ : (elt -> bool) -> t -> bool
      
      val partition : (elt -> bool) -> t -> (t, t) prod
      
      val cardinal : t -> nat
      
      val elements : t -> elt list
      
      val min_elt : t -> elt option
      
      val max_elt : t -> elt option
      
      val choose : t -> elt option
      
      val compare : t -> t -> t compare
     end
    
    module E : 
     sig 
      type t = X.t
      
      val compare : t -> t -> t compare
      
      val eq_dec : t -> t -> sumbool
     end
    
    module OTFacts : 
     sig 
      val eq_dec : X.t -> X.t -> sumbool
      
      val lt_dec : X.t -> X.t -> sumbool
      
      val eqb : X.t -> X.t -> bool
     end
    
    type slist =
      Raw.t
      (* singleton inductive, whose constructor was Build_slist *)
    
    val slist_rect : (Raw.t -> __ -> 'a1) -> slist -> 'a1
    
    val slist_rec : (Raw.t -> __ -> 'a1) -> slist -> 'a1
    
    val this : slist -> Raw.t
    
    val coq_Build_slist' : Raw.t -> slist
    
    type t = slist
    
    type elt = X.t
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val remove : elt -> t -> t
    
    val singleton : elt -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val empty : t
    
    val is_empty : t -> bool
    
    val elements : t -> elt list
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
    
    val choose : t -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val cardinal : t -> nat
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val compare : t -> t -> t compare
    
    val eq_dec : t -> t -> sumbool
   end
  
  type fset = S.t
  
  type elt = S.elt
 end

module type VARIABLES = 
 sig 
  type var 
  
  val var_default : var
  
  module Var_as_OT : 
   UsualOrderedType with type t= var
  
  module VarSet : 
   FinSet with module E = Var_as_OT
  
  type vars = VarSet.S.t
  
  val var_generate : vars -> var
  
  val var_fresh : vars -> var
  
  val var_of_Z : z -> var
  
  val coq_Z_of_var : var -> z
 end

module Variables : 
 VARIABLES

module Var_as_OT_Facts : 
 sig 
  val eq_dec : Variables.var -> Variables.var -> sumbool
  
  val lt_dec : Variables.var -> Variables.var -> sumbool
  
  val eqb : Variables.var -> Variables.var -> bool
 end

val eq_var_dec : Variables.var -> Variables.var -> sumbool

val var_freshes : Variables.vars -> nat -> Variables.var list

module Env : 
 sig 
  type 'a env = (Variables.var, 'a) prod list
  
  val empty : 'a1 env
  
  val single : Variables.var -> 'a1 -> (Variables.var, 'a1) prod list
  
  val concat : 'a1 env -> 'a1 env -> (Variables.var, 'a1) prod list
  
  val dom : 'a1 env -> Variables.vars
  
  val map : ('a1 -> 'a1) -> 'a1 env -> 'a1 env
  
  val get : Variables.var -> 'a1 env -> 'a1 option
  
  val iter_push :
    Variables.var list -> 'a1 list -> (Variables.var, 'a1) prod list
  
  val fv_in : ('a1 -> Variables.vars) -> 'a1 env -> Variables.vars
 end

val index : ('a1 -> 'a1 -> sumbool) -> nat -> 'a1 -> 'a1 list -> nat option

val list_snd : ('a1, 'a2) prod list -> 'a2 list

val map_snd : ('a2 -> 'a2) -> ('a1, 'a2) prod list -> ('a1, 'a2) prod list

val assoc :
  ('a1 -> 'a1 -> sumbool) -> 'a1 -> ('a1, 'a2) prod list -> 'a2 option

val cut : nat -> 'a1 list -> ('a1 list, 'a1 list) prod

val mkset : Variables.var list -> Variables.vars

type 'a set = 'a list

val set_add : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> 'a1 set

val set_mem : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> bool

val set_inter : ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set

val set_union : ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set

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

module MkDefs : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  type typ =
    | Coq_typ_bvar of nat
    | Coq_typ_fvar of Variables.var
    | Coq_typ_arrow of typ * typ
  
  val typ_rect :
    (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1 ->
    'a1) -> typ -> 'a1
  
  val typ_rec :
    (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1 ->
    'a1) -> typ -> 'a1
  
  val typ_def : typ
  
  type ckind = { kind_cstr : Cstr.cstr; kind_rel : (Cstr.attr, typ) prod list }
  
  val ckind_rect :
    (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) -> ckind ->
    'a1
  
  val ckind_rec :
    (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) -> ckind ->
    'a1
  
  val kind_cstr : ckind -> Cstr.cstr
  
  val kind_rel : ckind -> (Cstr.attr, typ) prod list
  
  type kind = ckind option
  
  type sch = { sch_type : typ; sch_kinds : kind list }
  
  val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1
  
  val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1
  
  val sch_type : sch -> typ
  
  val sch_kinds : sch -> kind list
  
  val typ_open : typ -> typ list -> typ
  
  val typ_fvars : Variables.var list -> typ list
  
  val typ_open_vars : typ -> Variables.var list -> typ
  
  val sch_open : sch -> typ list -> typ
  
  val sch_open_vars : sch -> Variables.var list -> typ
  
  val kind_types : kind -> typ list
  
  val ckind_map_spec : (typ -> typ) -> ckind -> ckind
  
  val ckind_map : (typ -> typ) -> ckind -> ckind
  
  val kind_map : (typ -> typ) -> kind -> kind
  
  val kind_open : kind -> typ list -> kind
  
  type trm =
    | Coq_trm_bvar of nat
    | Coq_trm_fvar of Variables.var
    | Coq_trm_abs of trm
    | Coq_trm_let of trm * trm
    | Coq_trm_app of trm * trm
    | Coq_trm_cst of Const.const
  
  val trm_rect :
    (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) -> (trm ->
    'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) ->
    (Const.const -> 'a1) -> trm -> 'a1
  
  val trm_rec :
    (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) -> (trm ->
    'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) ->
    (Const.const -> 'a1) -> trm -> 'a1
  
  val trm_open_rec : nat -> trm -> trm -> trm
  
  val trm_open : trm -> trm -> trm
  
  val trm_def : trm
  
  val trm_inst_rec : nat -> trm list -> trm -> trm
  
  val trm_inst : trm -> trm list -> trm
  
  val const_app : Const.const -> trm list -> trm
  
  type kenv = kind Env.env
  
  val kinds_open : kind list -> typ list -> kind list
  
  val kinds_open_vars :
    kind list -> Variables.var list -> (Variables.var, kind) prod list
  
  type env = sch Env.env
  
  val typ_fv : typ -> Variables.vars
  
  val typ_fv_list : typ list -> Variables.VarSet.S.t
  
  val kind_fv : kind -> Variables.VarSet.S.t
  
  val kind_fv_list : kind list -> Variables.VarSet.S.t
  
  val sch_fv : sch -> Variables.VarSet.S.t
  
  val env_fv : sch Env.env -> Variables.vars
  
  module type DeltaIntf = 
   sig 
    val coq_type : Const.const -> sch
    
    val reduce : Const.const -> trm list -> trm
   end
  
  module MkJudge : 
   functor (Delta:DeltaIntf) ->
   sig 
    type gc_kind =
      | GcAny
      | GcLet
    
    val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
    
    val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
    
    type gc_info = (bool, gc_kind) prod
    
    val gc_raise : gc_info -> gc_info
    
    val gc_lower : gc_info -> gc_info
   end
 end

module MkInfra : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module Defs : 
   sig 
    type typ =
      | Coq_typ_bvar of nat
      | Coq_typ_fvar of Variables.var
      | Coq_typ_arrow of typ * typ
    
    val typ_rect :
      (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1 ->
      'a1) -> typ -> 'a1
    
    val typ_rec :
      (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1 ->
      'a1) -> typ -> 'a1
    
    val typ_def : typ
    
    type ckind = { kind_cstr : Cstr.cstr;
                   kind_rel : (Cstr.attr, typ) prod list }
    
    val ckind_rect :
      (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) -> ckind
      -> 'a1
    
    val ckind_rec :
      (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) -> ckind
      -> 'a1
    
    val kind_cstr : ckind -> Cstr.cstr
    
    val kind_rel : ckind -> (Cstr.attr, typ) prod list
    
    type kind = ckind option
    
    type sch = { sch_type : typ; sch_kinds : kind list }
    
    val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1
    
    val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1
    
    val sch_type : sch -> typ
    
    val sch_kinds : sch -> kind list
    
    val typ_open : typ -> typ list -> typ
    
    val typ_fvars : Variables.var list -> typ list
    
    val typ_open_vars : typ -> Variables.var list -> typ
    
    val sch_open : sch -> typ list -> typ
    
    val sch_open_vars : sch -> Variables.var list -> typ
    
    val kind_types : kind -> typ list
    
    val ckind_map_spec : (typ -> typ) -> ckind -> ckind
    
    val ckind_map : (typ -> typ) -> ckind -> ckind
    
    val kind_map : (typ -> typ) -> kind -> kind
    
    val kind_open : kind -> typ list -> kind
    
    type trm =
      | Coq_trm_bvar of nat
      | Coq_trm_fvar of Variables.var
      | Coq_trm_abs of trm
      | Coq_trm_let of trm * trm
      | Coq_trm_app of trm * trm
      | Coq_trm_cst of Const.const
    
    val trm_rect :
      (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) -> (trm
      -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) ->
      (Const.const -> 'a1) -> trm -> 'a1
    
    val trm_rec :
      (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) -> (trm
      -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) ->
      (Const.const -> 'a1) -> trm -> 'a1
    
    val trm_open_rec : nat -> trm -> trm -> trm
    
    val trm_open : trm -> trm -> trm
    
    val trm_def : trm
    
    val trm_inst_rec : nat -> trm list -> trm -> trm
    
    val trm_inst : trm -> trm list -> trm
    
    val const_app : Const.const -> trm list -> trm
    
    type kenv = kind Env.env
    
    val kinds_open : kind list -> typ list -> kind list
    
    val kinds_open_vars :
      kind list -> Variables.var list -> (Variables.var, kind) prod list
    
    type env = sch Env.env
    
    val typ_fv : typ -> Variables.vars
    
    val typ_fv_list : typ list -> Variables.VarSet.S.t
    
    val kind_fv : kind -> Variables.VarSet.S.t
    
    val kind_fv_list : kind list -> Variables.VarSet.S.t
    
    val sch_fv : sch -> Variables.VarSet.S.t
    
    val env_fv : sch Env.env -> Variables.vars
    
    module type DeltaIntf = 
     sig 
      val coq_type : Const.const -> sch
      
      val reduce : Const.const -> trm list -> trm
     end
    
    module MkJudge : 
     functor (Delta:DeltaIntf) ->
     sig 
      type gc_kind =
        | GcAny
        | GcLet
      
      val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
      
      val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
      
      type gc_info = (bool, gc_kind) prod
      
      val gc_raise : gc_info -> gc_info
      
      val gc_lower : gc_info -> gc_info
     end
   end
  
  val trm_fv : Defs.trm -> Variables.vars
  
  type subs = Defs.typ Env.env
  
  val typ_subst : subs -> Defs.typ -> Defs.typ
  
  val kind_subst : subs -> Defs.kind -> Defs.kind
  
  val sch_subst : subs -> Defs.sch -> Defs.sch
  
  val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm
  
  module MkJudgInfra : 
   functor (Delta:Defs.DeltaIntf) ->
   sig 
    module Judge : 
     sig 
      type gc_kind =
        | GcAny
        | GcLet
      
      val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
      
      val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
      
      type gc_info = (bool, gc_kind) prod
      
      val gc_raise : gc_info -> gc_info
      
      val gc_lower : gc_info -> gc_info
     end
   end
 end

module MkSound : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module Infra : 
   sig 
    module Defs : 
     sig 
      type typ =
        | Coq_typ_bvar of nat
        | Coq_typ_fvar of Variables.var
        | Coq_typ_arrow of typ * typ
      
      val typ_rect :
        (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1
        -> 'a1) -> typ -> 'a1
      
      val typ_rec :
        (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1
        -> 'a1) -> typ -> 'a1
      
      val typ_def : typ
      
      type ckind = { kind_cstr : Cstr.cstr;
                     kind_rel : (Cstr.attr, typ) prod list }
      
      val ckind_rect :
        (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) -> ckind
        -> 'a1
      
      val ckind_rec :
        (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) -> ckind
        -> 'a1
      
      val kind_cstr : ckind -> Cstr.cstr
      
      val kind_rel : ckind -> (Cstr.attr, typ) prod list
      
      type kind = ckind option
      
      type sch = { sch_type : typ; sch_kinds : kind list }
      
      val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1
      
      val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1
      
      val sch_type : sch -> typ
      
      val sch_kinds : sch -> kind list
      
      val typ_open : typ -> typ list -> typ
      
      val typ_fvars : Variables.var list -> typ list
      
      val typ_open_vars : typ -> Variables.var list -> typ
      
      val sch_open : sch -> typ list -> typ
      
      val sch_open_vars : sch -> Variables.var list -> typ
      
      val kind_types : kind -> typ list
      
      val ckind_map_spec : (typ -> typ) -> ckind -> ckind
      
      val ckind_map : (typ -> typ) -> ckind -> ckind
      
      val kind_map : (typ -> typ) -> kind -> kind
      
      val kind_open : kind -> typ list -> kind
      
      type trm =
        | Coq_trm_bvar of nat
        | Coq_trm_fvar of Variables.var
        | Coq_trm_abs of trm
        | Coq_trm_let of trm * trm
        | Coq_trm_app of trm * trm
        | Coq_trm_cst of Const.const
      
      val trm_rect :
        (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) -> (trm
        -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) ->
        (Const.const -> 'a1) -> trm -> 'a1
      
      val trm_rec :
        (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) -> (trm
        -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) ->
        (Const.const -> 'a1) -> trm -> 'a1
      
      val trm_open_rec : nat -> trm -> trm -> trm
      
      val trm_open : trm -> trm -> trm
      
      val trm_def : trm
      
      val trm_inst_rec : nat -> trm list -> trm -> trm
      
      val trm_inst : trm -> trm list -> trm
      
      val const_app : Const.const -> trm list -> trm
      
      type kenv = kind Env.env
      
      val kinds_open : kind list -> typ list -> kind list
      
      val kinds_open_vars :
        kind list -> Variables.var list -> (Variables.var, kind) prod list
      
      type env = sch Env.env
      
      val typ_fv : typ -> Variables.vars
      
      val typ_fv_list : typ list -> Variables.VarSet.S.t
      
      val kind_fv : kind -> Variables.VarSet.S.t
      
      val kind_fv_list : kind list -> Variables.VarSet.S.t
      
      val sch_fv : sch -> Variables.VarSet.S.t
      
      val env_fv : sch Env.env -> Variables.vars
      
      module type DeltaIntf = 
       sig 
        val coq_type : Const.const -> sch
        
        val reduce : Const.const -> trm list -> trm
       end
      
      module MkJudge : 
       functor (Delta:DeltaIntf) ->
       sig 
        type gc_kind =
          | GcAny
          | GcLet
        
        val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
        
        val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
        
        type gc_info = (bool, gc_kind) prod
        
        val gc_raise : gc_info -> gc_info
        
        val gc_lower : gc_info -> gc_info
       end
     end
    
    val trm_fv : Defs.trm -> Variables.vars
    
    type subs = Defs.typ Env.env
    
    val typ_subst : subs -> Defs.typ -> Defs.typ
    
    val kind_subst : subs -> Defs.kind -> Defs.kind
    
    val sch_subst : subs -> Defs.sch -> Defs.sch
    
    val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm
    
    module MkJudgInfra : 
     functor (Delta:Defs.DeltaIntf) ->
     sig 
      module Judge : 
       sig 
        type gc_kind =
          | GcAny
          | GcLet
        
        val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
        
        val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
        
        type gc_info = (bool, gc_kind) prod
        
        val gc_raise : gc_info -> gc_info
        
        val gc_lower : gc_info -> gc_info
       end
     end
   end
  
  module Mk2 : 
   functor (Delta:Infra.Defs.DeltaIntf) ->
   sig 
    module JudgInfra : 
     sig 
      module Judge : 
       sig 
        type gc_kind =
          | GcAny
          | GcLet
        
        val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
        
        val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
        
        type gc_info = (bool, gc_kind) prod
        
        val gc_raise : gc_info -> gc_info
        
        val gc_lower : gc_info -> gc_info
       end
     end
    
    module type SndHypIntf = 
     sig 
      
     end
    
    module Mk3 : 
     functor (SH:SndHypIntf) ->
     sig 
      
     end
   end
 end

module MkRename : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module Sound : 
   sig 
    module Infra : 
     sig 
      module Defs : 
       sig 
        type typ =
          | Coq_typ_bvar of nat
          | Coq_typ_fvar of Variables.var
          | Coq_typ_arrow of typ * typ
        
        val typ_rect :
          (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1
          -> 'a1) -> typ -> 'a1
        
        val typ_rec :
          (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ -> 'a1
          -> 'a1) -> typ -> 'a1
        
        val typ_def : typ
        
        type ckind = { kind_cstr : Cstr.cstr;
                       kind_rel : (Cstr.attr, typ) prod list }
        
        val ckind_rect :
          (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) ->
          ckind -> 'a1
        
        val ckind_rec :
          (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) ->
          ckind -> 'a1
        
        val kind_cstr : ckind -> Cstr.cstr
        
        val kind_rel : ckind -> (Cstr.attr, typ) prod list
        
        type kind = ckind option
        
        type sch = { sch_type : typ; sch_kinds : kind list }
        
        val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1
        
        val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1
        
        val sch_type : sch -> typ
        
        val sch_kinds : sch -> kind list
        
        val typ_open : typ -> typ list -> typ
        
        val typ_fvars : Variables.var list -> typ list
        
        val typ_open_vars : typ -> Variables.var list -> typ
        
        val sch_open : sch -> typ list -> typ
        
        val sch_open_vars : sch -> Variables.var list -> typ
        
        val kind_types : kind -> typ list
        
        val ckind_map_spec : (typ -> typ) -> ckind -> ckind
        
        val ckind_map : (typ -> typ) -> ckind -> ckind
        
        val kind_map : (typ -> typ) -> kind -> kind
        
        val kind_open : kind -> typ list -> kind
        
        type trm =
          | Coq_trm_bvar of nat
          | Coq_trm_fvar of Variables.var
          | Coq_trm_abs of trm
          | Coq_trm_let of trm * trm
          | Coq_trm_app of trm * trm
          | Coq_trm_cst of Const.const
        
        val trm_rect :
          (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) ->
          (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 ->
          'a1) -> (Const.const -> 'a1) -> trm -> 'a1
        
        val trm_rec :
          (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) ->
          (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 ->
          'a1) -> (Const.const -> 'a1) -> trm -> 'a1
        
        val trm_open_rec : nat -> trm -> trm -> trm
        
        val trm_open : trm -> trm -> trm
        
        val trm_def : trm
        
        val trm_inst_rec : nat -> trm list -> trm -> trm
        
        val trm_inst : trm -> trm list -> trm
        
        val const_app : Const.const -> trm list -> trm
        
        type kenv = kind Env.env
        
        val kinds_open : kind list -> typ list -> kind list
        
        val kinds_open_vars :
          kind list -> Variables.var list -> (Variables.var, kind) prod list
        
        type env = sch Env.env
        
        val typ_fv : typ -> Variables.vars
        
        val typ_fv_list : typ list -> Variables.VarSet.S.t
        
        val kind_fv : kind -> Variables.VarSet.S.t
        
        val kind_fv_list : kind list -> Variables.VarSet.S.t
        
        val sch_fv : sch -> Variables.VarSet.S.t
        
        val env_fv : sch Env.env -> Variables.vars
        
        module type DeltaIntf = 
         sig 
          val coq_type : Const.const -> sch
          
          val reduce : Const.const -> trm list -> trm
         end
        
        module MkJudge : 
         functor (Delta:DeltaIntf) ->
         sig 
          type gc_kind =
            | GcAny
            | GcLet
          
          val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
          
          val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
          
          type gc_info = (bool, gc_kind) prod
          
          val gc_raise : gc_info -> gc_info
          
          val gc_lower : gc_info -> gc_info
         end
       end
      
      val trm_fv : Defs.trm -> Variables.vars
      
      type subs = Defs.typ Env.env
      
      val typ_subst : subs -> Defs.typ -> Defs.typ
      
      val kind_subst : subs -> Defs.kind -> Defs.kind
      
      val sch_subst : subs -> Defs.sch -> Defs.sch
      
      val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm
      
      module MkJudgInfra : 
       functor (Delta:Defs.DeltaIntf) ->
       sig 
        module Judge : 
         sig 
          type gc_kind =
            | GcAny
            | GcLet
          
          val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
          
          val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
          
          type gc_info = (bool, gc_kind) prod
          
          val gc_raise : gc_info -> gc_info
          
          val gc_lower : gc_info -> gc_info
         end
       end
     end
    
    module Mk2 : 
     functor (Delta:Infra.Defs.DeltaIntf) ->
     sig 
      module JudgInfra : 
       sig 
        module Judge : 
         sig 
          type gc_kind =
            | GcAny
            | GcLet
          
          val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
          
          val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
          
          type gc_info = (bool, gc_kind) prod
          
          val gc_raise : gc_info -> gc_info
          
          val gc_lower : gc_info -> gc_info
         end
       end
      
      module type SndHypIntf = 
       sig 
        
       end
      
      module Mk3 : 
       functor (SH:SndHypIntf) ->
       sig 
        
       end
     end
   end
  
  module Mk2 : 
   functor (Delta:Sound.Infra.Defs.DeltaIntf) ->
   sig 
    module Sound2 : 
     sig 
      module JudgInfra : 
       sig 
        module Judge : 
         sig 
          type gc_kind =
            | GcAny
            | GcLet
          
          val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
          
          val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
          
          type gc_info = (bool, gc_kind) prod
          
          val gc_raise : gc_info -> gc_info
          
          val gc_lower : gc_info -> gc_info
         end
       end
      
      module type SndHypIntf = 
       sig 
        
       end
      
      module Mk3 : 
       functor (SH:SndHypIntf) ->
       sig 
        
       end
     end
    
    val typ_generalize :
      Variables.var list -> Sound.Infra.Defs.typ -> Sound.Infra.Defs.typ
    
    val sch_generalize :
      Variables.var list -> Sound.Infra.Defs.typ -> Sound.Infra.Defs.kind
      list -> Sound.Infra.Defs.sch
   end
 end

module MkEval : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module Rename : 
   sig 
    module Sound : 
     sig 
      module Infra : 
       sig 
        module Defs : 
         sig 
          type typ =
            | Coq_typ_bvar of nat
            | Coq_typ_fvar of Variables.var
            | Coq_typ_arrow of typ * typ
          
          val typ_rect :
            (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ ->
            'a1 -> 'a1) -> typ -> 'a1
          
          val typ_rec :
            (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ ->
            'a1 -> 'a1) -> typ -> 'a1
          
          val typ_def : typ
          
          type ckind = { kind_cstr : Cstr.cstr;
                         kind_rel : (Cstr.attr, typ) prod list }
          
          val ckind_rect :
            (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) ->
            ckind -> 'a1
          
          val ckind_rec :
            (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) ->
            ckind -> 'a1
          
          val kind_cstr : ckind -> Cstr.cstr
          
          val kind_rel : ckind -> (Cstr.attr, typ) prod list
          
          type kind = ckind option
          
          type sch = { sch_type : typ; sch_kinds : kind list }
          
          val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1
          
          val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1
          
          val sch_type : sch -> typ
          
          val sch_kinds : sch -> kind list
          
          val typ_open : typ -> typ list -> typ
          
          val typ_fvars : Variables.var list -> typ list
          
          val typ_open_vars : typ -> Variables.var list -> typ
          
          val sch_open : sch -> typ list -> typ
          
          val sch_open_vars : sch -> Variables.var list -> typ
          
          val kind_types : kind -> typ list
          
          val ckind_map_spec : (typ -> typ) -> ckind -> ckind
          
          val ckind_map : (typ -> typ) -> ckind -> ckind
          
          val kind_map : (typ -> typ) -> kind -> kind
          
          val kind_open : kind -> typ list -> kind
          
          type trm =
            | Coq_trm_bvar of nat
            | Coq_trm_fvar of Variables.var
            | Coq_trm_abs of trm
            | Coq_trm_let of trm * trm
            | Coq_trm_app of trm * trm
            | Coq_trm_cst of Const.const
          
          val trm_rect :
            (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) ->
            (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 ->
            'a1) -> (Const.const -> 'a1) -> trm -> 'a1
          
          val trm_rec :
            (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1) ->
            (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm -> 'a1 ->
            'a1) -> (Const.const -> 'a1) -> trm -> 'a1
          
          val trm_open_rec : nat -> trm -> trm -> trm
          
          val trm_open : trm -> trm -> trm
          
          val trm_def : trm
          
          val trm_inst_rec : nat -> trm list -> trm -> trm
          
          val trm_inst : trm -> trm list -> trm
          
          val const_app : Const.const -> trm list -> trm
          
          type kenv = kind Env.env
          
          val kinds_open : kind list -> typ list -> kind list
          
          val kinds_open_vars :
            kind list -> Variables.var list -> (Variables.var, kind) prod
            list
          
          type env = sch Env.env
          
          val typ_fv : typ -> Variables.vars
          
          val typ_fv_list : typ list -> Variables.VarSet.S.t
          
          val kind_fv : kind -> Variables.VarSet.S.t
          
          val kind_fv_list : kind list -> Variables.VarSet.S.t
          
          val sch_fv : sch -> Variables.VarSet.S.t
          
          val env_fv : sch Env.env -> Variables.vars
          
          module type DeltaIntf = 
           sig 
            val coq_type : Const.const -> sch
            
            val reduce : Const.const -> trm list -> trm
           end
          
          module MkJudge : 
           functor (Delta:DeltaIntf) ->
           sig 
            type gc_kind =
              | GcAny
              | GcLet
            
            val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            type gc_info = (bool, gc_kind) prod
            
            val gc_raise : gc_info -> gc_info
            
            val gc_lower : gc_info -> gc_info
           end
         end
        
        val trm_fv : Defs.trm -> Variables.vars
        
        type subs = Defs.typ Env.env
        
        val typ_subst : subs -> Defs.typ -> Defs.typ
        
        val kind_subst : subs -> Defs.kind -> Defs.kind
        
        val sch_subst : subs -> Defs.sch -> Defs.sch
        
        val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm
        
        module MkJudgInfra : 
         functor (Delta:Defs.DeltaIntf) ->
         sig 
          module Judge : 
           sig 
            type gc_kind =
              | GcAny
              | GcLet
            
            val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            type gc_info = (bool, gc_kind) prod
            
            val gc_raise : gc_info -> gc_info
            
            val gc_lower : gc_info -> gc_info
           end
         end
       end
      
      module Mk2 : 
       functor (Delta:Infra.Defs.DeltaIntf) ->
       sig 
        module JudgInfra : 
         sig 
          module Judge : 
           sig 
            type gc_kind =
              | GcAny
              | GcLet
            
            val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            type gc_info = (bool, gc_kind) prod
            
            val gc_raise : gc_info -> gc_info
            
            val gc_lower : gc_info -> gc_info
           end
         end
        
        module type SndHypIntf = 
         sig 
          
         end
        
        module Mk3 : 
         functor (SH:SndHypIntf) ->
         sig 
          
         end
       end
     end
    
    module Mk2 : 
     functor (Delta:Sound.Infra.Defs.DeltaIntf) ->
     sig 
      module Sound2 : 
       sig 
        module JudgInfra : 
         sig 
          module Judge : 
           sig 
            type gc_kind =
              | GcAny
              | GcLet
            
            val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            type gc_info = (bool, gc_kind) prod
            
            val gc_raise : gc_info -> gc_info
            
            val gc_lower : gc_info -> gc_info
           end
         end
        
        module type SndHypIntf = 
         sig 
          
         end
        
        module Mk3 : 
         functor (SH:SndHypIntf) ->
         sig 
          
         end
       end
      
      val typ_generalize :
        Variables.var list -> Sound.Infra.Defs.typ -> Sound.Infra.Defs.typ
      
      val sch_generalize :
        Variables.var list -> Sound.Infra.Defs.typ -> Sound.Infra.Defs.kind
        list -> Sound.Infra.Defs.sch
     end
   end
  
  type clos =
    | Coq_clos_abs of Rename.Sound.Infra.Defs.trm * clos list
    | Coq_clos_const of Const.const * clos list
  
  val clos_rect :
    (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const -> clos
    list -> 'a1) -> clos -> 'a1
  
  val clos_rec :
    (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const -> clos
    list -> 'a1) -> clos -> 'a1
  
  val clos2trm : clos -> Rename.Sound.Infra.Defs.trm
  
  type frame = { frm_benv : clos list; frm_app : clos list;
                 frm_trm : Rename.Sound.Infra.Defs.trm }
  
  val frame_rect :
    (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> 'a1) -> frame
    -> 'a1
  
  val frame_rec :
    (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> 'a1) -> frame
    -> 'a1
  
  val frm_benv : frame -> clos list
  
  val frm_app : frame -> clos list
  
  val frm_trm : frame -> Rename.Sound.Infra.Defs.trm
  
  val is_bvar : Rename.Sound.Infra.Defs.trm -> bool
  
  val app_trm :
    Rename.Sound.Infra.Defs.trm -> Rename.Sound.Infra.Defs.trm ->
    Rename.Sound.Infra.Defs.trm
  
  val app2trm :
    Rename.Sound.Infra.Defs.trm -> clos list -> Rename.Sound.Infra.Defs.trm
  
  val inst :
    Rename.Sound.Infra.Defs.trm -> clos list -> Rename.Sound.Infra.Defs.trm
  
  val stack2trm :
    Rename.Sound.Infra.Defs.trm -> frame list -> Rename.Sound.Infra.Defs.trm
  
  type eval_res =
    | Result of nat * clos
    | Inter of frame list
  
  val eval_res_rect :
    (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
  
  val eval_res_rec :
    (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
  
  val res2trm : eval_res -> Rename.Sound.Infra.Defs.trm
  
  val clos_def : clos
  
  val trm2clos :
    clos list -> clos Env.env -> Rename.Sound.Infra.Defs.trm -> clos
  
  val trm2app :
    Rename.Sound.Infra.Defs.trm -> (Rename.Sound.Infra.Defs.trm,
    Rename.Sound.Infra.Defs.trm) prod option
  
  module Mk2 : 
   functor (Delta:Rename.Sound.Infra.Defs.DeltaIntf) ->
   sig 
    module Rename2 : 
     sig 
      module Sound2 : 
       sig 
        module JudgInfra : 
         sig 
          module Judge : 
           sig 
            type gc_kind =
              | GcAny
              | GcLet
            
            val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            type gc_info = (bool, gc_kind) prod
            
            val gc_raise : gc_info -> gc_info
            
            val gc_lower : gc_info -> gc_info
           end
         end
        
        module type SndHypIntf = 
         sig 
          
         end
        
        module Mk3 : 
         functor (SH:SndHypIntf) ->
         sig 
          
         end
       end
      
      val typ_generalize :
        Variables.var list -> Rename.Sound.Infra.Defs.typ ->
        Rename.Sound.Infra.Defs.typ
      
      val sch_generalize :
        Variables.var list -> Rename.Sound.Infra.Defs.typ ->
        Rename.Sound.Infra.Defs.kind list -> Rename.Sound.Infra.Defs.sch
     end
    
    val coq_Gc : (bool, Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
    
    module type SndHypIntf2 = 
     sig 
      val reduce_clos : Const.const -> clos list -> (clos, clos list) prod
     end
    
    module Mk3 : 
     functor (SH:SndHypIntf2) ->
     sig 
      module Sound3 : 
       sig 
        
       end
      
      val result :
        (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> frame list
        -> eval_res) -> nat -> clos -> frame list -> eval_res
      
      val eval :
        clos Env.env -> nat -> clos list -> clos list ->
        Rename.Sound.Infra.Defs.trm -> frame list -> eval_res
      
      val is_abs : Rename.Sound.Infra.Defs.trm -> bool
      
      val eval_restart :
        clos Env.env -> nat -> frame list -> eval_res -> eval_res
      
      val reduce_clos : Const.const -> clos list -> clos list -> frame
      
      val is_app : Rename.Sound.Infra.Defs.trm -> bool
      
      val check_const_app : Rename.Sound.Infra.Defs.trm -> bool
      
      val eval_res_cont : eval_res -> bool
     end
   end
 end

module MkUnify : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module MyEval : 
   sig 
    module Rename : 
     sig 
      module Sound : 
       sig 
        module Infra : 
         sig 
          module Defs : 
           sig 
            type typ =
              | Coq_typ_bvar of nat
              | Coq_typ_fvar of Variables.var
              | Coq_typ_arrow of typ * typ
            
            val typ_rect :
              (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ ->
              'a1 -> 'a1) -> typ -> 'a1
            
            val typ_rec :
              (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ ->
              'a1 -> 'a1) -> typ -> 'a1
            
            val typ_def : typ
            
            type ckind = { kind_cstr : Cstr.cstr;
                           kind_rel : (Cstr.attr, typ) prod list }
            
            val ckind_rect :
              (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) ->
              ckind -> 'a1
            
            val ckind_rec :
              (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1) ->
              ckind -> 'a1
            
            val kind_cstr : ckind -> Cstr.cstr
            
            val kind_rel : ckind -> (Cstr.attr, typ) prod list
            
            type kind = ckind option
            
            type sch = { sch_type : typ; sch_kinds : kind list }
            
            val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1
            
            val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1
            
            val sch_type : sch -> typ
            
            val sch_kinds : sch -> kind list
            
            val typ_open : typ -> typ list -> typ
            
            val typ_fvars : Variables.var list -> typ list
            
            val typ_open_vars : typ -> Variables.var list -> typ
            
            val sch_open : sch -> typ list -> typ
            
            val sch_open_vars : sch -> Variables.var list -> typ
            
            val kind_types : kind -> typ list
            
            val ckind_map_spec : (typ -> typ) -> ckind -> ckind
            
            val ckind_map : (typ -> typ) -> ckind -> ckind
            
            val kind_map : (typ -> typ) -> kind -> kind
            
            val kind_open : kind -> typ list -> kind
            
            type trm =
              | Coq_trm_bvar of nat
              | Coq_trm_fvar of Variables.var
              | Coq_trm_abs of trm
              | Coq_trm_let of trm * trm
              | Coq_trm_app of trm * trm
              | Coq_trm_cst of Const.const
            
            val trm_rect :
              (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1)
              -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm ->
              'a1 -> 'a1) -> (Const.const -> 'a1) -> trm -> 'a1
            
            val trm_rec :
              (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1)
              -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm ->
              'a1 -> 'a1) -> (Const.const -> 'a1) -> trm -> 'a1
            
            val trm_open_rec : nat -> trm -> trm -> trm
            
            val trm_open : trm -> trm -> trm
            
            val trm_def : trm
            
            val trm_inst_rec : nat -> trm list -> trm -> trm
            
            val trm_inst : trm -> trm list -> trm
            
            val const_app : Const.const -> trm list -> trm
            
            type kenv = kind Env.env
            
            val kinds_open : kind list -> typ list -> kind list
            
            val kinds_open_vars :
              kind list -> Variables.var list -> (Variables.var, kind) prod
              list
            
            type env = sch Env.env
            
            val typ_fv : typ -> Variables.vars
            
            val typ_fv_list : typ list -> Variables.VarSet.S.t
            
            val kind_fv : kind -> Variables.VarSet.S.t
            
            val kind_fv_list : kind list -> Variables.VarSet.S.t
            
            val sch_fv : sch -> Variables.VarSet.S.t
            
            val env_fv : sch Env.env -> Variables.vars
            
            module type DeltaIntf = 
             sig 
              val coq_type : Const.const -> sch
              
              val reduce : Const.const -> trm list -> trm
             end
            
            module MkJudge : 
             functor (Delta:DeltaIntf) ->
             sig 
              type gc_kind =
                | GcAny
                | GcLet
              
              val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              type gc_info = (bool, gc_kind) prod
              
              val gc_raise : gc_info -> gc_info
              
              val gc_lower : gc_info -> gc_info
             end
           end
          
          val trm_fv : Defs.trm -> Variables.vars
          
          type subs = Defs.typ Env.env
          
          val typ_subst : subs -> Defs.typ -> Defs.typ
          
          val kind_subst : subs -> Defs.kind -> Defs.kind
          
          val sch_subst : subs -> Defs.sch -> Defs.sch
          
          val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm
          
          module MkJudgInfra : 
           functor (Delta:Defs.DeltaIntf) ->
           sig 
            module Judge : 
             sig 
              type gc_kind =
                | GcAny
                | GcLet
              
              val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              type gc_info = (bool, gc_kind) prod
              
              val gc_raise : gc_info -> gc_info
              
              val gc_lower : gc_info -> gc_info
             end
           end
         end
        
        module Mk2 : 
         functor (Delta:Infra.Defs.DeltaIntf) ->
         sig 
          module JudgInfra : 
           sig 
            module Judge : 
             sig 
              type gc_kind =
                | GcAny
                | GcLet
              
              val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              type gc_info = (bool, gc_kind) prod
              
              val gc_raise : gc_info -> gc_info
              
              val gc_lower : gc_info -> gc_info
             end
           end
          
          module type SndHypIntf = 
           sig 
            
           end
          
          module Mk3 : 
           functor (SH:SndHypIntf) ->
           sig 
            
           end
         end
       end
      
      module Mk2 : 
       functor (Delta:Sound.Infra.Defs.DeltaIntf) ->
       sig 
        module Sound2 : 
         sig 
          module JudgInfra : 
           sig 
            module Judge : 
             sig 
              type gc_kind =
                | GcAny
                | GcLet
              
              val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              type gc_info = (bool, gc_kind) prod
              
              val gc_raise : gc_info -> gc_info
              
              val gc_lower : gc_info -> gc_info
             end
           end
          
          module type SndHypIntf = 
           sig 
            
           end
          
          module Mk3 : 
           functor (SH:SndHypIntf) ->
           sig 
            
           end
         end
        
        val typ_generalize :
          Variables.var list -> Sound.Infra.Defs.typ -> Sound.Infra.Defs.typ
        
        val sch_generalize :
          Variables.var list -> Sound.Infra.Defs.typ -> Sound.Infra.Defs.kind
          list -> Sound.Infra.Defs.sch
       end
     end
    
    type clos =
      | Coq_clos_abs of Rename.Sound.Infra.Defs.trm * clos list
      | Coq_clos_const of Const.const * clos list
    
    val clos_rect :
      (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
      clos list -> 'a1) -> clos -> 'a1
    
    val clos_rec :
      (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
      clos list -> 'a1) -> clos -> 'a1
    
    val clos2trm : clos -> Rename.Sound.Infra.Defs.trm
    
    type frame = { frm_benv : clos list; frm_app : 
                   clos list; frm_trm : Rename.Sound.Infra.Defs.trm }
    
    val frame_rect :
      (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> 'a1) -> frame
      -> 'a1
    
    val frame_rec :
      (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> 'a1) -> frame
      -> 'a1
    
    val frm_benv : frame -> clos list
    
    val frm_app : frame -> clos list
    
    val frm_trm : frame -> Rename.Sound.Infra.Defs.trm
    
    val is_bvar : Rename.Sound.Infra.Defs.trm -> bool
    
    val app_trm :
      Rename.Sound.Infra.Defs.trm -> Rename.Sound.Infra.Defs.trm ->
      Rename.Sound.Infra.Defs.trm
    
    val app2trm :
      Rename.Sound.Infra.Defs.trm -> clos list -> Rename.Sound.Infra.Defs.trm
    
    val inst :
      Rename.Sound.Infra.Defs.trm -> clos list -> Rename.Sound.Infra.Defs.trm
    
    val stack2trm :
      Rename.Sound.Infra.Defs.trm -> frame list ->
      Rename.Sound.Infra.Defs.trm
    
    type eval_res =
      | Result of nat * clos
      | Inter of frame list
    
    val eval_res_rect :
      (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
    
    val eval_res_rec :
      (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
    
    val res2trm : eval_res -> Rename.Sound.Infra.Defs.trm
    
    val clos_def : clos
    
    val trm2clos :
      clos list -> clos Env.env -> Rename.Sound.Infra.Defs.trm -> clos
    
    val trm2app :
      Rename.Sound.Infra.Defs.trm -> (Rename.Sound.Infra.Defs.trm,
      Rename.Sound.Infra.Defs.trm) prod option
    
    module Mk2 : 
     functor (Delta:Rename.Sound.Infra.Defs.DeltaIntf) ->
     sig 
      module Rename2 : 
       sig 
        module Sound2 : 
         sig 
          module JudgInfra : 
           sig 
            module Judge : 
             sig 
              type gc_kind =
                | GcAny
                | GcLet
              
              val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              type gc_info = (bool, gc_kind) prod
              
              val gc_raise : gc_info -> gc_info
              
              val gc_lower : gc_info -> gc_info
             end
           end
          
          module type SndHypIntf = 
           sig 
            
           end
          
          module Mk3 : 
           functor (SH:SndHypIntf) ->
           sig 
            
           end
         end
        
        val typ_generalize :
          Variables.var list -> Rename.Sound.Infra.Defs.typ ->
          Rename.Sound.Infra.Defs.typ
        
        val sch_generalize :
          Variables.var list -> Rename.Sound.Infra.Defs.typ ->
          Rename.Sound.Infra.Defs.kind list -> Rename.Sound.Infra.Defs.sch
       end
      
      val coq_Gc : (bool, Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
      
      module type SndHypIntf2 = 
       sig 
        val reduce_clos : Const.const -> clos list -> (clos, clos list) prod
       end
      
      module Mk3 : 
       functor (SH:SndHypIntf2) ->
       sig 
        module Sound3 : 
         sig 
          
         end
        
        val result :
          (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> frame
          list -> eval_res) -> nat -> clos -> frame list -> eval_res
        
        val eval :
          clos Env.env -> nat -> clos list -> clos list ->
          Rename.Sound.Infra.Defs.trm -> frame list -> eval_res
        
        val is_abs : Rename.Sound.Infra.Defs.trm -> bool
        
        val eval_restart :
          clos Env.env -> nat -> frame list -> eval_res -> eval_res
        
        val reduce_clos : Const.const -> clos list -> clos list -> frame
        
        val is_app : Rename.Sound.Infra.Defs.trm -> bool
        
        val check_const_app : Rename.Sound.Infra.Defs.trm -> bool
        
        val eval_res_cont : eval_res -> bool
       end
     end
   end
  
  val compose :
    MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
    MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
    MyEval.Rename.Sound.Infra.subs
  
  val id : MyEval.Rename.Sound.Infra.Defs.typ Env.env
  
  val get_kind :
    Variables.var -> MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    MyEval.Rename.Sound.Infra.Defs.kind
  
  type 'a decidable = 'a -> sumbool
  
  val in_dec : Variables.VarSet.S.t -> Variables.VarSet.S.elt decidable
  
  val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
  
  val unify_kind_rel :
    (Cstr.attr, MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (Cstr.attr,
    MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (Cstr.attr -> bool) ->
    (MyEval.Rename.Sound.Infra.Defs.typ, MyEval.Rename.Sound.Infra.Defs.typ)
    prod list -> ((Cstr.attr, MyEval.Rename.Sound.Infra.Defs.typ) prod list,
    (MyEval.Rename.Sound.Infra.Defs.typ, MyEval.Rename.Sound.Infra.Defs.typ)
    prod list) prod
  
  val unify_kinds :
    MyEval.Rename.Sound.Infra.Defs.kind ->
    MyEval.Rename.Sound.Infra.Defs.kind ->
    (MyEval.Rename.Sound.Infra.Defs.kind,
    (MyEval.Rename.Sound.Infra.Defs.typ, MyEval.Rename.Sound.Infra.Defs.typ)
    prod list) prod option
  
  type unif_res =
    | Uok of (MyEval.Rename.Sound.Infra.Defs.typ,
             MyEval.Rename.Sound.Infra.Defs.typ) prod list
       * MyEval.Rename.Sound.Infra.Defs.kenv * MyEval.Rename.Sound.Infra.subs
    | Ufail
  
  val unif_res_rect :
    ((MyEval.Rename.Sound.Infra.Defs.typ, MyEval.Rename.Sound.Infra.Defs.typ)
    prod list -> MyEval.Rename.Sound.Infra.Defs.kenv ->
    MyEval.Rename.Sound.Infra.subs -> 'a1) -> 'a1 -> unif_res -> 'a1
  
  val unif_res_rec :
    ((MyEval.Rename.Sound.Infra.Defs.typ, MyEval.Rename.Sound.Infra.Defs.typ)
    prod list -> MyEval.Rename.Sound.Infra.Defs.kenv ->
    MyEval.Rename.Sound.Infra.subs -> 'a1) -> 'a1 -> unif_res -> 'a1
  
  val unify_vars :
    MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    MyEval.Rename.Sound.Infra.Defs.typ Env.env -> Variables.var ->
    Variables.var -> unif_res
  
  val unify_nv :
    MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    MyEval.Rename.Sound.Infra.Defs.typ Env.env -> Variables.VarSet.S.elt ->
    MyEval.Rename.Sound.Infra.Defs.typ -> unif_res
  
  val unify1 :
    MyEval.Rename.Sound.Infra.Defs.typ -> MyEval.Rename.Sound.Infra.Defs.typ
    -> MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
    -> unif_res
  
  val accum : ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
  
  val pair_subst :
    MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
    MyEval.Rename.Sound.Infra.Defs.typ) prod ->
    (MyEval.Rename.Sound.Infra.Defs.typ, MyEval.Rename.Sound.Infra.Defs.typ)
    prod
  
  val typ_size : MyEval.Rename.Sound.Infra.Defs.typ -> nat
  
  val pair_size :
    (MyEval.Rename.Sound.Infra.Defs.typ, MyEval.Rename.Sound.Infra.Defs.typ)
    prod -> nat
  
  val pairs_size :
    MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
    MyEval.Rename.Sound.Infra.Defs.typ) prod list -> nat
  
  val all_fv :
    MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
    MyEval.Rename.Sound.Infra.Defs.typ) prod list -> Variables.VarSet.S.t
  
  val really_all_fv :
    MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
    Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
    MyEval.Rename.Sound.Infra.Defs.typ) prod list -> Variables.VarSet.S.t
  
  val size_pairs :
    MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
    Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
    MyEval.Rename.Sound.Infra.Defs.typ) prod list -> nat
  
  val size_pairs2 :
    MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
    Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
    MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (nat, nat) prod
  
  val unify1_dep :
    MyEval.Rename.Sound.Infra.Defs.typ -> MyEval.Rename.Sound.Infra.Defs.typ
    -> MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    MyEval.Rename.Sound.Infra.subs -> (((MyEval.Rename.Sound.Infra.Defs.typ,
    MyEval.Rename.Sound.Infra.Defs.typ) prod list,
    MyEval.Rename.Sound.Infra.Defs.kenv) prod,
    MyEval.Rename.Sound.Infra.subs) prod sumor
  
  val unify :
    (MyEval.Rename.Sound.Infra.Defs.typ, MyEval.Rename.Sound.Infra.Defs.typ)
    prod list -> MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.kenv,
    MyEval.Rename.Sound.Infra.subs) prod option
  
  val typ_kind :
    MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    MyEval.Rename.Sound.Infra.Defs.typ ->
    MyEval.Rename.Sound.Infra.Defs.ckind option
 end

module MkInfer : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module Unify : 
   sig 
    module MyEval : 
     sig 
      module Rename : 
       sig 
        module Sound : 
         sig 
          module Infra : 
           sig 
            module Defs : 
             sig 
              type typ =
                | Coq_typ_bvar of nat
                | Coq_typ_fvar of Variables.var
                | Coq_typ_arrow of typ * typ
              
              val typ_rect :
                (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ
                -> 'a1 -> 'a1) -> typ -> 'a1
              
              val typ_rec :
                (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ
                -> 'a1 -> 'a1) -> typ -> 'a1
              
              val typ_def : typ
              
              type ckind = { kind_cstr : Cstr.cstr;
                             kind_rel : (Cstr.attr, typ) prod list }
              
              val ckind_rect :
                (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1)
                -> ckind -> 'a1
              
              val ckind_rec :
                (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1)
                -> ckind -> 'a1
              
              val kind_cstr : ckind -> Cstr.cstr
              
              val kind_rel : ckind -> (Cstr.attr, typ) prod list
              
              type kind = ckind option
              
              type sch = { sch_type : typ; sch_kinds : kind list }
              
              val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1
              
              val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1
              
              val sch_type : sch -> typ
              
              val sch_kinds : sch -> kind list
              
              val typ_open : typ -> typ list -> typ
              
              val typ_fvars : Variables.var list -> typ list
              
              val typ_open_vars : typ -> Variables.var list -> typ
              
              val sch_open : sch -> typ list -> typ
              
              val sch_open_vars : sch -> Variables.var list -> typ
              
              val kind_types : kind -> typ list
              
              val ckind_map_spec : (typ -> typ) -> ckind -> ckind
              
              val ckind_map : (typ -> typ) -> ckind -> ckind
              
              val kind_map : (typ -> typ) -> kind -> kind
              
              val kind_open : kind -> typ list -> kind
              
              type trm =
                | Coq_trm_bvar of nat
                | Coq_trm_fvar of Variables.var
                | Coq_trm_abs of trm
                | Coq_trm_let of trm * trm
                | Coq_trm_app of trm * trm
                | Coq_trm_cst of Const.const
              
              val trm_rect :
                (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1)
                -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm ->
                'a1 -> 'a1) -> (Const.const -> 'a1) -> trm -> 'a1
              
              val trm_rec :
                (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1)
                -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm ->
                'a1 -> 'a1) -> (Const.const -> 'a1) -> trm -> 'a1
              
              val trm_open_rec : nat -> trm -> trm -> trm
              
              val trm_open : trm -> trm -> trm
              
              val trm_def : trm
              
              val trm_inst_rec : nat -> trm list -> trm -> trm
              
              val trm_inst : trm -> trm list -> trm
              
              val const_app : Const.const -> trm list -> trm
              
              type kenv = kind Env.env
              
              val kinds_open : kind list -> typ list -> kind list
              
              val kinds_open_vars :
                kind list -> Variables.var list -> (Variables.var, kind) prod
                list
              
              type env = sch Env.env
              
              val typ_fv : typ -> Variables.vars
              
              val typ_fv_list : typ list -> Variables.VarSet.S.t
              
              val kind_fv : kind -> Variables.VarSet.S.t
              
              val kind_fv_list : kind list -> Variables.VarSet.S.t
              
              val sch_fv : sch -> Variables.VarSet.S.t
              
              val env_fv : sch Env.env -> Variables.vars
              
              module type DeltaIntf = 
               sig 
                val coq_type : Const.const -> sch
                
                val reduce : Const.const -> trm list -> trm
               end
              
              module MkJudge : 
               functor (Delta:DeltaIntf) ->
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
            
            val trm_fv : Defs.trm -> Variables.vars
            
            type subs = Defs.typ Env.env
            
            val typ_subst : subs -> Defs.typ -> Defs.typ
            
            val kind_subst : subs -> Defs.kind -> Defs.kind
            
            val sch_subst : subs -> Defs.sch -> Defs.sch
            
            val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm
            
            module MkJudgInfra : 
             functor (Delta:Defs.DeltaIntf) ->
             sig 
              module Judge : 
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
           end
          
          module Mk2 : 
           functor (Delta:Infra.Defs.DeltaIntf) ->
           sig 
            module JudgInfra : 
             sig 
              module Judge : 
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
            
            module type SndHypIntf = 
             sig 
              
             end
            
            module Mk3 : 
             functor (SH:SndHypIntf) ->
             sig 
              
             end
           end
         end
        
        module Mk2 : 
         functor (Delta:Sound.Infra.Defs.DeltaIntf) ->
         sig 
          module Sound2 : 
           sig 
            module JudgInfra : 
             sig 
              module Judge : 
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
            
            module type SndHypIntf = 
             sig 
              
             end
            
            module Mk3 : 
             functor (SH:SndHypIntf) ->
             sig 
              
             end
           end
          
          val typ_generalize :
            Variables.var list -> Sound.Infra.Defs.typ ->
            Sound.Infra.Defs.typ
          
          val sch_generalize :
            Variables.var list -> Sound.Infra.Defs.typ ->
            Sound.Infra.Defs.kind list -> Sound.Infra.Defs.sch
         end
       end
      
      type clos =
        | Coq_clos_abs of Rename.Sound.Infra.Defs.trm * clos list
        | Coq_clos_const of Const.const * clos list
      
      val clos_rect :
        (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
        clos list -> 'a1) -> clos -> 'a1
      
      val clos_rec :
        (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
        clos list -> 'a1) -> clos -> 'a1
      
      val clos2trm : clos -> Rename.Sound.Infra.Defs.trm
      
      type frame = { frm_benv : clos list; frm_app : 
                     clos list; frm_trm : Rename.Sound.Infra.Defs.trm }
      
      val frame_rect :
        (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> 'a1) ->
        frame -> 'a1
      
      val frame_rec :
        (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> 'a1) ->
        frame -> 'a1
      
      val frm_benv : frame -> clos list
      
      val frm_app : frame -> clos list
      
      val frm_trm : frame -> Rename.Sound.Infra.Defs.trm
      
      val is_bvar : Rename.Sound.Infra.Defs.trm -> bool
      
      val app_trm :
        Rename.Sound.Infra.Defs.trm -> Rename.Sound.Infra.Defs.trm ->
        Rename.Sound.Infra.Defs.trm
      
      val app2trm :
        Rename.Sound.Infra.Defs.trm -> clos list ->
        Rename.Sound.Infra.Defs.trm
      
      val inst :
        Rename.Sound.Infra.Defs.trm -> clos list ->
        Rename.Sound.Infra.Defs.trm
      
      val stack2trm :
        Rename.Sound.Infra.Defs.trm -> frame list ->
        Rename.Sound.Infra.Defs.trm
      
      type eval_res =
        | Result of nat * clos
        | Inter of frame list
      
      val eval_res_rect :
        (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val eval_res_rec :
        (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val res2trm : eval_res -> Rename.Sound.Infra.Defs.trm
      
      val clos_def : clos
      
      val trm2clos :
        clos list -> clos Env.env -> Rename.Sound.Infra.Defs.trm -> clos
      
      val trm2app :
        Rename.Sound.Infra.Defs.trm -> (Rename.Sound.Infra.Defs.trm,
        Rename.Sound.Infra.Defs.trm) prod option
      
      module Mk2 : 
       functor (Delta:Rename.Sound.Infra.Defs.DeltaIntf) ->
       sig 
        module Rename2 : 
         sig 
          module Sound2 : 
           sig 
            module JudgInfra : 
             sig 
              module Judge : 
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
            
            module type SndHypIntf = 
             sig 
              
             end
            
            module Mk3 : 
             functor (SH:SndHypIntf) ->
             sig 
              
             end
           end
          
          val typ_generalize :
            Variables.var list -> Rename.Sound.Infra.Defs.typ ->
            Rename.Sound.Infra.Defs.typ
          
          val sch_generalize :
            Variables.var list -> Rename.Sound.Infra.Defs.typ ->
            Rename.Sound.Infra.Defs.kind list -> Rename.Sound.Infra.Defs.sch
         end
        
        val coq_Gc : (bool, Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
        
        module type SndHypIntf2 = 
         sig 
          val reduce_clos :
            Const.const -> clos list -> (clos, clos list) prod
         end
        
        module Mk3 : 
         functor (SH:SndHypIntf2) ->
         sig 
          module Sound3 : 
           sig 
            
           end
          
          val result :
            (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> frame
            list -> eval_res) -> nat -> clos -> frame list -> eval_res
          
          val eval :
            clos Env.env -> nat -> clos list -> clos list ->
            Rename.Sound.Infra.Defs.trm -> frame list -> eval_res
          
          val is_abs : Rename.Sound.Infra.Defs.trm -> bool
          
          val eval_restart :
            clos Env.env -> nat -> frame list -> eval_res -> eval_res
          
          val reduce_clos : Const.const -> clos list -> clos list -> frame
          
          val is_app : Rename.Sound.Infra.Defs.trm -> bool
          
          val check_const_app : Rename.Sound.Infra.Defs.trm -> bool
          
          val eval_res_cont : eval_res -> bool
         end
       end
     end
    
    val compose :
      MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
      MyEval.Rename.Sound.Infra.subs
    
    val id : MyEval.Rename.Sound.Infra.Defs.typ Env.env
    
    val get_kind :
      Variables.var -> MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.kind
    
    type 'a decidable = 'a -> sumbool
    
    val in_dec : Variables.VarSet.S.t -> Variables.VarSet.S.elt decidable
    
    val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
    
    val unify_kind_rel :
      (Cstr.attr, MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      (Cstr.attr, MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (Cstr.attr
      -> bool) -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> ((Cstr.attr,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list,
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list) prod
    
    val unify_kinds :
      MyEval.Rename.Sound.Infra.Defs.kind ->
      MyEval.Rename.Sound.Infra.Defs.kind ->
      (MyEval.Rename.Sound.Infra.Defs.kind,
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list) prod option
    
    type unif_res =
      | Uok of (MyEval.Rename.Sound.Infra.Defs.typ,
               MyEval.Rename.Sound.Infra.Defs.typ) prod list
         * MyEval.Rename.Sound.Infra.Defs.kenv
         * MyEval.Rename.Sound.Infra.subs
      | Ufail
    
    val unif_res_rect :
      ((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> 'a1) -> 'a1 -> unif_res -> 'a1
    
    val unif_res_rec :
      ((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> 'a1) -> 'a1 -> unif_res -> 'a1
    
    val unify_vars :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env -> Variables.var ->
      Variables.var -> unif_res
    
    val unify_nv :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env -> Variables.VarSet.S.elt ->
      MyEval.Rename.Sound.Infra.Defs.typ -> unif_res
    
    val unify1 :
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> unif_res
    
    val accum : ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
    
    val pair_subst :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod ->
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod
    
    val typ_size : MyEval.Rename.Sound.Infra.Defs.typ -> nat
    
    val pair_size :
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod -> nat
    
    val pairs_size :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> nat
    
    val all_fv :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> Variables.VarSet.S.t
    
    val really_all_fv :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> Variables.VarSet.S.t
    
    val size_pairs :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> nat
    
    val size_pairs2 :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (nat, nat) prod
    
    val unify1_dep :
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.subs ->
      (((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list,
      MyEval.Rename.Sound.Infra.Defs.kenv) prod,
      MyEval.Rename.Sound.Infra.subs) prod sumor
    
    val unify :
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.kenv,
      MyEval.Rename.Sound.Infra.subs) prod option
    
    val typ_kind :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.ckind option
   end
  
  module Mk2 : 
   functor (Delta:Unify.MyEval.Rename.Sound.Infra.Defs.DeltaIntf) ->
   sig 
    module MyEval2 : 
     sig 
      module Rename2 : 
       sig 
        module Sound2 : 
         sig 
          module JudgInfra : 
           sig 
            module Judge : 
             sig 
              type gc_kind =
                | GcAny
                | GcLet
              
              val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              type gc_info = (bool, gc_kind) prod
              
              val gc_raise : gc_info -> gc_info
              
              val gc_lower : gc_info -> gc_info
             end
           end
          
          module type SndHypIntf = 
           sig 
            
           end
          
          module Mk3 : 
           functor (SH:SndHypIntf) ->
           sig 
            
           end
         end
        
        val typ_generalize :
          Variables.var list -> Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
          Unify.MyEval.Rename.Sound.Infra.Defs.typ
        
        val sch_generalize :
          Variables.var list -> Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
          Unify.MyEval.Rename.Sound.Infra.Defs.kind list ->
          Unify.MyEval.Rename.Sound.Infra.Defs.sch
       end
      
      val coq_Gc : (bool, Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
      
      module type SndHypIntf2 = 
       sig 
        val reduce_clos :
          Const.const -> Unify.MyEval.clos list -> (Unify.MyEval.clos,
          Unify.MyEval.clos list) prod
       end
      
      module Mk3 : 
       functor (SH:SndHypIntf2) ->
       sig 
        module Sound3 : 
         sig 
          
         end
        
        val result :
          (Unify.MyEval.clos list -> Unify.MyEval.clos list ->
          Unify.MyEval.Rename.Sound.Infra.Defs.trm -> Unify.MyEval.frame list
          -> Unify.MyEval.eval_res) -> nat -> Unify.MyEval.clos ->
          Unify.MyEval.frame list -> Unify.MyEval.eval_res
        
        val eval :
          Unify.MyEval.clos Env.env -> nat -> Unify.MyEval.clos list ->
          Unify.MyEval.clos list -> Unify.MyEval.Rename.Sound.Infra.Defs.trm
          -> Unify.MyEval.frame list -> Unify.MyEval.eval_res
        
        val is_abs : Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
        
        val eval_restart :
          Unify.MyEval.clos Env.env -> nat -> Unify.MyEval.frame list ->
          Unify.MyEval.eval_res -> Unify.MyEval.eval_res
        
        val reduce_clos :
          Const.const -> Unify.MyEval.clos list -> Unify.MyEval.clos list ->
          Unify.MyEval.frame
        
        val is_app : Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
        
        val check_const_app :
          Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
        
        val eval_res_cont : Unify.MyEval.eval_res -> bool
       end
     end
    
    val fvs :
      Unify.MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
      Variables.VarSet.S.t
    
    val unify_dep :
      Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
      Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
      Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      Unify.MyEval.Rename.Sound.Infra.subs ->
      (Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
      Unify.MyEval.Rename.Sound.Infra.subs) prod sumor
    
    val close_fvars :
      nat -> Unify.MyEval.Rename.Sound.Infra.Defs.kenv -> Variables.vars ->
      Variables.vars -> Variables.vars
    
    val close_fvk :
      (Variables.var, Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list ->
      Variables.vars -> Variables.vars
    
    val split_env :
      Variables.vars -> 'a1 Env.env -> ('a1 Env.env, 'a1 Env.env) prod
    
    val vars_subst :
      Unify.MyEval.Rename.Sound.Infra.subs -> Variables.VarSet.S.t ->
      Variables.VarSet.S.t
    
    val typinf_generalize :
      (Variables.var, Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list ->
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env -> Variables.vars ->
      Unify.MyEval.Rename.Sound.Infra.Defs.typ -> ((Variables.var,
      Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list,
      Unify.MyEval.Rename.Sound.Infra.Defs.sch) prod
    
    val kdom : Unify.MyEval.Rename.Sound.Infra.Defs.kenv -> Variables.vars
    
    val trm_depth : Unify.MyEval.Rename.Sound.Infra.Defs.trm -> nat
    
    val get_dep : Variables.var -> 'a1 Env.env -> 'a1 sumor
    
    val typinf :
      Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
      Unify.MyEval.Rename.Sound.Infra.Defs.typ -> Variables.VarSet.S.t ->
      Unify.MyEval.Rename.Sound.Infra.subs ->
      ((Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
      Unify.MyEval.Rename.Sound.Infra.subs) prod, Variables.vars) prod option
    
    val typinf0 :
      Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
      Unify.MyEval.Rename.Sound.Infra.Defs.typ -> Variables.VarSet.S.t ->
      Unify.MyEval.Rename.Sound.Infra.subs ->
      ((Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
      Unify.MyEval.Rename.Sound.Infra.subs) prod, Variables.vars) prod option
    
    val typinf' :
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
      (Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env,
      Unify.MyEval.Rename.Sound.Infra.Defs.typ) prod option
    
    val coq_Gc : (bool, MyEval2.Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
   end
 end

module Cstr : 
 sig 
  type attr = nat
  
  val eq_dec : nat -> nat -> sumbool
  
  type ksort =
    | Ksum
    | Kprod
    | Kbot
  
  val ksort_rect : 'a1 -> 'a1 -> 'a1 -> ksort -> 'a1
  
  val ksort_rec : 'a1 -> 'a1 -> 'a1 -> ksort -> 'a1
  
  type cstr_impl = { cstr_sort : ksort; cstr_low : 
                     nat list; cstr_high : nat list option }
  
  val cstr_impl_rect :
    (ksort -> nat list -> nat list option -> 'a1) -> cstr_impl -> 'a1
  
  val cstr_impl_rec :
    (ksort -> nat list -> nat list option -> 'a1) -> cstr_impl -> 'a1
  
  val cstr_sort : cstr_impl -> ksort
  
  val cstr_low : cstr_impl -> nat list
  
  val cstr_high : cstr_impl -> nat list option
  
  type cstr = cstr_impl
  
  val unique : cstr_impl -> nat -> bool
  
  val sort_lub : ksort -> ksort -> ksort
  
  val lub : cstr_impl -> cstr_impl -> cstr_impl
  
  val ksort_dec : ksort -> sumbool
  
  val valid_dec : cstr_impl -> sumbool
 end

module Const : 
 sig 
  type ops =
    | Coq_tag of Cstr.attr
    | Coq_matches of Cstr.attr list
    | Coq_record of Cstr.attr list
    | Coq_sub of Cstr.attr
    | Coq_recf
  
  val ops_rect :
    (Cstr.attr -> 'a1) -> (Cstr.attr list -> __ -> 'a1) -> (Cstr.attr list ->
    __ -> 'a1) -> (Cstr.attr -> 'a1) -> 'a1 -> ops -> 'a1
  
  val ops_rec :
    (Cstr.attr -> 'a1) -> (Cstr.attr list -> __ -> 'a1) -> (Cstr.attr list ->
    __ -> 'a1) -> (Cstr.attr -> 'a1) -> 'a1 -> ops -> 'a1
  
  type const = ops
  
  val arity : ops -> nat
 end

module Infer : 
 sig 
  module Unify : 
   sig 
    module MyEval : 
     sig 
      module Rename : 
       sig 
        module Sound : 
         sig 
          module Infra : 
           sig 
            module Defs : 
             sig 
              type typ =
                | Coq_typ_bvar of nat
                | Coq_typ_fvar of Variables.var
                | Coq_typ_arrow of typ * typ
              
              val typ_rect :
                (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ
                -> 'a1 -> 'a1) -> typ -> 'a1
              
              val typ_rec :
                (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 -> typ
                -> 'a1 -> 'a1) -> typ -> 'a1
              
              val typ_def : typ
              
              type ckind = { kind_cstr : Cstr.cstr;
                             kind_rel : (Cstr.attr, typ) prod list }
              
              val ckind_rect :
                (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1)
                -> ckind -> 'a1
              
              val ckind_rec :
                (Cstr.cstr -> __ -> (Cstr.attr, typ) prod list -> __ -> 'a1)
                -> ckind -> 'a1
              
              val kind_cstr : ckind -> Cstr.cstr
              
              val kind_rel : ckind -> (Cstr.attr, typ) prod list
              
              type kind = ckind option
              
              type sch = { sch_type : typ; sch_kinds : kind list }
              
              val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1
              
              val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1
              
              val sch_type : sch -> typ
              
              val sch_kinds : sch -> kind list
              
              val typ_open : typ -> typ list -> typ
              
              val typ_fvars : Variables.var list -> typ list
              
              val typ_open_vars : typ -> Variables.var list -> typ
              
              val sch_open : sch -> typ list -> typ
              
              val sch_open_vars : sch -> Variables.var list -> typ
              
              val kind_types : kind -> typ list
              
              val ckind_map_spec : (typ -> typ) -> ckind -> ckind
              
              val ckind_map : (typ -> typ) -> ckind -> ckind
              
              val kind_map : (typ -> typ) -> kind -> kind
              
              val kind_open : kind -> typ list -> kind
              
              type trm =
                | Coq_trm_bvar of nat
                | Coq_trm_fvar of Variables.var
                | Coq_trm_abs of trm
                | Coq_trm_let of trm * trm
                | Coq_trm_app of trm * trm
                | Coq_trm_cst of Const.const
              
              val trm_rect :
                (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1)
                -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm ->
                'a1 -> 'a1) -> (Const.const -> 'a1) -> trm -> 'a1
              
              val trm_rec :
                (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 -> 'a1)
                -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1 -> trm ->
                'a1 -> 'a1) -> (Const.const -> 'a1) -> trm -> 'a1
              
              val trm_open_rec : nat -> trm -> trm -> trm
              
              val trm_open : trm -> trm -> trm
              
              val trm_def : trm
              
              val trm_inst_rec : nat -> trm list -> trm -> trm
              
              val trm_inst : trm -> trm list -> trm
              
              val const_app : Const.const -> trm list -> trm
              
              type kenv = kind Env.env
              
              val kinds_open : kind list -> typ list -> kind list
              
              val kinds_open_vars :
                kind list -> Variables.var list -> (Variables.var, kind) prod
                list
              
              type env = sch Env.env
              
              val typ_fv : typ -> Variables.vars
              
              val typ_fv_list : typ list -> Variables.VarSet.S.t
              
              val kind_fv : kind -> Variables.VarSet.S.t
              
              val kind_fv_list : kind list -> Variables.VarSet.S.t
              
              val sch_fv : sch -> Variables.VarSet.S.t
              
              val env_fv : sch Env.env -> Variables.vars
              
              module type DeltaIntf = 
               sig 
                val coq_type : Const.const -> sch
                
                val reduce : Const.const -> trm list -> trm
               end
              
              module MkJudge : 
               functor (Delta:DeltaIntf) ->
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
            
            val trm_fv : Defs.trm -> Variables.vars
            
            type subs = Defs.typ Env.env
            
            val typ_subst : subs -> Defs.typ -> Defs.typ
            
            val kind_subst : subs -> Defs.kind -> Defs.kind
            
            val sch_subst : subs -> Defs.sch -> Defs.sch
            
            val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm
            
            module MkJudgInfra : 
             functor (Delta:Defs.DeltaIntf) ->
             sig 
              module Judge : 
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
           end
          
          module Mk2 : 
           functor (Delta:Infra.Defs.DeltaIntf) ->
           sig 
            module JudgInfra : 
             sig 
              module Judge : 
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
            
            module type SndHypIntf = 
             sig 
              
             end
            
            module Mk3 : 
             functor (SH:SndHypIntf) ->
             sig 
              
             end
           end
         end
        
        module Mk2 : 
         functor (Delta:Sound.Infra.Defs.DeltaIntf) ->
         sig 
          module Sound2 : 
           sig 
            module JudgInfra : 
             sig 
              module Judge : 
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
            
            module type SndHypIntf = 
             sig 
              
             end
            
            module Mk3 : 
             functor (SH:SndHypIntf) ->
             sig 
              
             end
           end
          
          val typ_generalize :
            Variables.var list -> Sound.Infra.Defs.typ ->
            Sound.Infra.Defs.typ
          
          val sch_generalize :
            Variables.var list -> Sound.Infra.Defs.typ ->
            Sound.Infra.Defs.kind list -> Sound.Infra.Defs.sch
         end
       end
      
      type clos =
        | Coq_clos_abs of Rename.Sound.Infra.Defs.trm * clos list
        | Coq_clos_const of Const.const * clos list
      
      val clos_rect :
        (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
        clos list -> 'a1) -> clos -> 'a1
      
      val clos_rec :
        (Rename.Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
        clos list -> 'a1) -> clos -> 'a1
      
      val clos2trm : clos -> Rename.Sound.Infra.Defs.trm
      
      type frame = { frm_benv : clos list; frm_app : 
                     clos list; frm_trm : Rename.Sound.Infra.Defs.trm }
      
      val frame_rect :
        (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> 'a1) ->
        frame -> 'a1
      
      val frame_rec :
        (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> 'a1) ->
        frame -> 'a1
      
      val frm_benv : frame -> clos list
      
      val frm_app : frame -> clos list
      
      val frm_trm : frame -> Rename.Sound.Infra.Defs.trm
      
      val is_bvar : Rename.Sound.Infra.Defs.trm -> bool
      
      val app_trm :
        Rename.Sound.Infra.Defs.trm -> Rename.Sound.Infra.Defs.trm ->
        Rename.Sound.Infra.Defs.trm
      
      val app2trm :
        Rename.Sound.Infra.Defs.trm -> clos list ->
        Rename.Sound.Infra.Defs.trm
      
      val inst :
        Rename.Sound.Infra.Defs.trm -> clos list ->
        Rename.Sound.Infra.Defs.trm
      
      val stack2trm :
        Rename.Sound.Infra.Defs.trm -> frame list ->
        Rename.Sound.Infra.Defs.trm
      
      type eval_res =
        | Result of nat * clos
        | Inter of frame list
      
      val eval_res_rect :
        (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val eval_res_rec :
        (nat -> clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val res2trm : eval_res -> Rename.Sound.Infra.Defs.trm
      
      val clos_def : clos
      
      val trm2clos :
        clos list -> clos Env.env -> Rename.Sound.Infra.Defs.trm -> clos
      
      val trm2app :
        Rename.Sound.Infra.Defs.trm -> (Rename.Sound.Infra.Defs.trm,
        Rename.Sound.Infra.Defs.trm) prod option
      
      module Mk2 : 
       functor (Delta:Rename.Sound.Infra.Defs.DeltaIntf) ->
       sig 
        module Rename2 : 
         sig 
          module Sound2 : 
           sig 
            module JudgInfra : 
             sig 
              module Judge : 
               sig 
                type gc_kind =
                  | GcAny
                  | GcLet
                
                val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
                
                type gc_info = (bool, gc_kind) prod
                
                val gc_raise : gc_info -> gc_info
                
                val gc_lower : gc_info -> gc_info
               end
             end
            
            module type SndHypIntf = 
             sig 
              
             end
            
            module Mk3 : 
             functor (SH:SndHypIntf) ->
             sig 
              
             end
           end
          
          val typ_generalize :
            Variables.var list -> Rename.Sound.Infra.Defs.typ ->
            Rename.Sound.Infra.Defs.typ
          
          val sch_generalize :
            Variables.var list -> Rename.Sound.Infra.Defs.typ ->
            Rename.Sound.Infra.Defs.kind list -> Rename.Sound.Infra.Defs.sch
         end
        
        val coq_Gc : (bool, Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
        
        module type SndHypIntf2 = 
         sig 
          val reduce_clos :
            Const.const -> clos list -> (clos, clos list) prod
         end
        
        module Mk3 : 
         functor (SH:SndHypIntf2) ->
         sig 
          module Sound3 : 
           sig 
            
           end
          
          val result :
            (clos list -> clos list -> Rename.Sound.Infra.Defs.trm -> frame
            list -> eval_res) -> nat -> clos -> frame list -> eval_res
          
          val eval :
            clos Env.env -> nat -> clos list -> clos list ->
            Rename.Sound.Infra.Defs.trm -> frame list -> eval_res
          
          val is_abs : Rename.Sound.Infra.Defs.trm -> bool
          
          val eval_restart :
            clos Env.env -> nat -> frame list -> eval_res -> eval_res
          
          val reduce_clos : Const.const -> clos list -> clos list -> frame
          
          val is_app : Rename.Sound.Infra.Defs.trm -> bool
          
          val check_const_app : Rename.Sound.Infra.Defs.trm -> bool
          
          val eval_res_cont : eval_res -> bool
         end
       end
     end
    
    val compose :
      MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
      MyEval.Rename.Sound.Infra.subs
    
    val id : MyEval.Rename.Sound.Infra.Defs.typ Env.env
    
    val get_kind :
      Variables.var -> MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.kind
    
    type 'a decidable = 'a -> sumbool
    
    val in_dec : Variables.VarSet.S.t -> Variables.VarSet.S.elt decidable
    
    val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
    
    val unify_kind_rel :
      (Cstr.attr, MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      (Cstr.attr, MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (Cstr.attr
      -> bool) -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> ((Cstr.attr,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list,
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list) prod
    
    val unify_kinds :
      MyEval.Rename.Sound.Infra.Defs.kind ->
      MyEval.Rename.Sound.Infra.Defs.kind ->
      (MyEval.Rename.Sound.Infra.Defs.kind,
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list) prod option
    
    type unif_res =
      | Uok of (MyEval.Rename.Sound.Infra.Defs.typ,
               MyEval.Rename.Sound.Infra.Defs.typ) prod list
         * MyEval.Rename.Sound.Infra.Defs.kenv
         * MyEval.Rename.Sound.Infra.subs
      | Ufail
    
    val unif_res_rect :
      ((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> 'a1) -> 'a1 -> unif_res -> 'a1
    
    val unif_res_rec :
      ((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> 'a1) -> 'a1 -> unif_res -> 'a1
    
    val unify_vars :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env -> Variables.var ->
      Variables.var -> unif_res
    
    val unify_nv :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ Env.env -> Variables.VarSet.S.elt ->
      MyEval.Rename.Sound.Infra.Defs.typ -> unif_res
    
    val unify1 :
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.kenv -> MyEval.Rename.Sound.Infra.subs
      -> unif_res
    
    val accum : ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
    
    val pair_subst :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod ->
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod
    
    val typ_size : MyEval.Rename.Sound.Infra.Defs.typ -> nat
    
    val pair_size :
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod -> nat
    
    val pairs_size :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> nat
    
    val all_fv :
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> Variables.VarSet.S.t
    
    val really_all_fv :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> Variables.VarSet.S.t
    
    val size_pairs :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> nat
    
    val size_pairs2 :
      MyEval.Rename.Sound.Infra.subs -> MyEval.Rename.Sound.Infra.Defs.kind
      Env.env -> (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list -> (nat, nat) prod
    
    val unify1_dep :
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.subs ->
      (((MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list,
      MyEval.Rename.Sound.Infra.Defs.kenv) prod,
      MyEval.Rename.Sound.Infra.subs) prod sumor
    
    val unify :
      (MyEval.Rename.Sound.Infra.Defs.typ,
      MyEval.Rename.Sound.Infra.Defs.typ) prod list ->
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.subs -> (MyEval.Rename.Sound.Infra.Defs.kenv,
      MyEval.Rename.Sound.Infra.subs) prod option
    
    val typ_kind :
      MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      MyEval.Rename.Sound.Infra.Defs.typ ->
      MyEval.Rename.Sound.Infra.Defs.ckind option
   end
  
  module Mk2 : 
   functor (Delta:Unify.MyEval.Rename.Sound.Infra.Defs.DeltaIntf) ->
   sig 
    module MyEval2 : 
     sig 
      module Rename2 : 
       sig 
        module Sound2 : 
         sig 
          module JudgInfra : 
           sig 
            module Judge : 
             sig 
              type gc_kind =
                | GcAny
                | GcLet
              
              val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
              
              type gc_info = (bool, gc_kind) prod
              
              val gc_raise : gc_info -> gc_info
              
              val gc_lower : gc_info -> gc_info
             end
           end
          
          module type SndHypIntf = 
           sig 
            
           end
          
          module Mk3 : 
           functor (SH:SndHypIntf) ->
           sig 
            
           end
         end
        
        val typ_generalize :
          Variables.var list -> Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
          Unify.MyEval.Rename.Sound.Infra.Defs.typ
        
        val sch_generalize :
          Variables.var list -> Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
          Unify.MyEval.Rename.Sound.Infra.Defs.kind list ->
          Unify.MyEval.Rename.Sound.Infra.Defs.sch
       end
      
      val coq_Gc : (bool, Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
      
      module type SndHypIntf2 = 
       sig 
        val reduce_clos :
          Const.const -> Unify.MyEval.clos list -> (Unify.MyEval.clos,
          Unify.MyEval.clos list) prod
       end
      
      module Mk3 : 
       functor (SH:SndHypIntf2) ->
       sig 
        module Sound3 : 
         sig 
          
         end
        
        val result :
          (Unify.MyEval.clos list -> Unify.MyEval.clos list ->
          Unify.MyEval.Rename.Sound.Infra.Defs.trm -> Unify.MyEval.frame list
          -> Unify.MyEval.eval_res) -> nat -> Unify.MyEval.clos ->
          Unify.MyEval.frame list -> Unify.MyEval.eval_res
        
        val eval :
          Unify.MyEval.clos Env.env -> nat -> Unify.MyEval.clos list ->
          Unify.MyEval.clos list -> Unify.MyEval.Rename.Sound.Infra.Defs.trm
          -> Unify.MyEval.frame list -> Unify.MyEval.eval_res
        
        val is_abs : Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
        
        val eval_restart :
          Unify.MyEval.clos Env.env -> nat -> Unify.MyEval.frame list ->
          Unify.MyEval.eval_res -> Unify.MyEval.eval_res
        
        val reduce_clos :
          Const.const -> Unify.MyEval.clos list -> Unify.MyEval.clos list ->
          Unify.MyEval.frame
        
        val is_app : Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
        
        val check_const_app :
          Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
        
        val eval_res_cont : Unify.MyEval.eval_res -> bool
       end
     end
    
    val fvs :
      Unify.MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
      Variables.VarSet.S.t
    
    val unify_dep :
      Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
      Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
      Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      Unify.MyEval.Rename.Sound.Infra.subs ->
      (Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
      Unify.MyEval.Rename.Sound.Infra.subs) prod sumor
    
    val close_fvars :
      nat -> Unify.MyEval.Rename.Sound.Infra.Defs.kenv -> Variables.vars ->
      Variables.vars -> Variables.vars
    
    val close_fvk :
      (Variables.var, Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list ->
      Variables.vars -> Variables.vars
    
    val split_env :
      Variables.vars -> 'a1 Env.env -> ('a1 Env.env, 'a1 Env.env) prod
    
    val vars_subst :
      Unify.MyEval.Rename.Sound.Infra.subs -> Variables.VarSet.S.t ->
      Variables.VarSet.S.t
    
    val typinf_generalize :
      (Variables.var, Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list ->
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env -> Variables.vars ->
      Unify.MyEval.Rename.Sound.Infra.Defs.typ -> ((Variables.var,
      Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod list,
      Unify.MyEval.Rename.Sound.Infra.Defs.sch) prod
    
    val kdom : Unify.MyEval.Rename.Sound.Infra.Defs.kenv -> Variables.vars
    
    val trm_depth : Unify.MyEval.Rename.Sound.Infra.Defs.trm -> nat
    
    val get_dep : Variables.var -> 'a1 Env.env -> 'a1 sumor
    
    val typinf :
      Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
      Unify.MyEval.Rename.Sound.Infra.Defs.typ -> Variables.VarSet.S.t ->
      Unify.MyEval.Rename.Sound.Infra.subs ->
      ((Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
      Unify.MyEval.Rename.Sound.Infra.subs) prod, Variables.vars) prod option
    
    val typinf0 :
      Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
      Unify.MyEval.Rename.Sound.Infra.Defs.typ -> Variables.VarSet.S.t ->
      Unify.MyEval.Rename.Sound.Infra.subs ->
      ((Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
      Unify.MyEval.Rename.Sound.Infra.subs) prod, Variables.vars) prod option
    
    val typinf' :
      Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
      Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
      (Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env,
      Unify.MyEval.Rename.Sound.Infra.Defs.typ) prod option
    
    val coq_Gc : (bool, MyEval2.Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
   end
 end

module Delta : 
 sig 
  val matches_arg : nat -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ
  
  val coq_type :
    Const.const -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch
  
  val trm_default : Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm
  
  val record_args :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm list -> (nat list,
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm list) prod
  
  val is_record : Const.ops -> bool
  
  val reduce :
    Const.ops -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm list ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm
 end

module Infer2 : 
 sig 
  module MyEval2 : 
   sig 
    module Rename2 : 
     sig 
      module Sound2 : 
       sig 
        module JudgInfra : 
         sig 
          module Judge : 
           sig 
            type gc_kind =
              | GcAny
              | GcLet
            
            val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1
            
            type gc_info = (bool, gc_kind) prod
            
            val gc_raise : gc_info -> gc_info
            
            val gc_lower : gc_info -> gc_info
           end
         end
        
        module type SndHypIntf = 
         sig 
          
         end
        
        module Mk3 : 
         functor (SH:SndHypIntf) ->
         sig 
          
         end
       end
      
      val typ_generalize :
        Variables.var list -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ
        -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ
      
      val sch_generalize :
        Variables.var list -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ
        -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind list ->
        Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch
     end
    
    val coq_Gc : (bool, Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
    
    module type SndHypIntf2 = 
     sig 
      val reduce_clos :
        Const.const -> Infer.Unify.MyEval.clos list ->
        (Infer.Unify.MyEval.clos, Infer.Unify.MyEval.clos list) prod
     end
    
    module Mk3 : 
     functor (SH:SndHypIntf2) ->
     sig 
      module Sound3 : 
       sig 
        
       end
      
      val result :
        (Infer.Unify.MyEval.clos list -> Infer.Unify.MyEval.clos list ->
        Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
        Infer.Unify.MyEval.frame list -> Infer.Unify.MyEval.eval_res) -> nat
        -> Infer.Unify.MyEval.clos -> Infer.Unify.MyEval.frame list ->
        Infer.Unify.MyEval.eval_res
      
      val eval :
        Infer.Unify.MyEval.clos Env.env -> nat -> Infer.Unify.MyEval.clos
        list -> Infer.Unify.MyEval.clos list ->
        Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
        Infer.Unify.MyEval.frame list -> Infer.Unify.MyEval.eval_res
      
      val is_abs : Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
      
      val eval_restart :
        Infer.Unify.MyEval.clos Env.env -> nat -> Infer.Unify.MyEval.frame
        list -> Infer.Unify.MyEval.eval_res -> Infer.Unify.MyEval.eval_res
      
      val reduce_clos :
        Const.const -> Infer.Unify.MyEval.clos list ->
        Infer.Unify.MyEval.clos list -> Infer.Unify.MyEval.frame
      
      val is_app : Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
      
      val check_const_app :
        Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
      
      val eval_res_cont : Infer.Unify.MyEval.eval_res -> bool
     end
   end
  
  val fvs :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
    Variables.VarSet.S.t
  
  val unify_dep :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.subs ->
    (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
    Infer.Unify.MyEval.Rename.Sound.Infra.subs) prod sumor
  
  val close_fvars :
    nat -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kenv -> Variables.vars
    -> Variables.vars -> Variables.vars
  
  val close_fvk :
    (Variables.var, Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod
    list -> Variables.vars -> Variables.vars
  
  val split_env :
    Variables.vars -> 'a1 Env.env -> ('a1 Env.env, 'a1 Env.env) prod
  
  val vars_subst :
    Infer.Unify.MyEval.Rename.Sound.Infra.subs -> Variables.VarSet.S.t ->
    Variables.VarSet.S.t
  
  val typinf_generalize :
    (Variables.var, Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod
    list -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
    Variables.vars -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ ->
    ((Variables.var, Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind) prod
    list, Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch) prod
  
  val kdom :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kenv -> Variables.vars
  
  val trm_depth : Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> nat
  
  val get_dep : Variables.var -> 'a1 Env.env -> 'a1 sumor
  
  val typinf :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ -> Variables.VarSet.S.t ->
    Infer.Unify.MyEval.Rename.Sound.Infra.subs ->
    ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
    Infer.Unify.MyEval.Rename.Sound.Infra.subs) prod, Variables.vars) prod
    option
  
  val typinf0 :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ -> Variables.VarSet.S.t ->
    Infer.Unify.MyEval.Rename.Sound.Infra.subs ->
    ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
    Infer.Unify.MyEval.Rename.Sound.Infra.subs) prod, Variables.vars) prod
    option
  
  val typinf' :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
    (Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kind Env.env,
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ) prod option
  
  val coq_Gc : (bool, MyEval2.Rename2.Sound2.JudgInfra.Judge.gc_kind) prod
 end

module SndHyp : 
 sig 
  val reduce_clos :
    Const.ops -> Infer.Unify.MyEval.clos list -> (Infer.Unify.MyEval.clos,
    Infer.Unify.MyEval.clos list) prod
 end

module Sound3 : 
 sig 
  module Sound3 : 
   sig 
    
   end
  
  val result :
    (Infer.Unify.MyEval.clos list -> Infer.Unify.MyEval.clos list ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
    Infer.Unify.MyEval.frame list -> Infer.Unify.MyEval.eval_res) -> nat ->
    Infer.Unify.MyEval.clos -> Infer.Unify.MyEval.frame list ->
    Infer.Unify.MyEval.eval_res
  
  val eval :
    Infer.Unify.MyEval.clos Env.env -> nat -> Infer.Unify.MyEval.clos list ->
    Infer.Unify.MyEval.clos list ->
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
    Infer.Unify.MyEval.frame list -> Infer.Unify.MyEval.eval_res
  
  val is_abs : Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
  
  val eval_restart :
    Infer.Unify.MyEval.clos Env.env -> nat -> Infer.Unify.MyEval.frame list
    -> Infer.Unify.MyEval.eval_res -> Infer.Unify.MyEval.eval_res
  
  val reduce_clos :
    Const.const -> Infer.Unify.MyEval.clos list -> Infer.Unify.MyEval.clos
    list -> Infer.Unify.MyEval.frame
  
  val is_app : Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
  
  val check_const_app :
    Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> bool
  
  val eval_res_cont : Infer.Unify.MyEval.eval_res -> bool
 end

type 'a decidable0 = 'a -> sumbool

val ok_dec :
  Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch Env.env decidable0

val type_n_dec :
  nat -> Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ decidable0

val list_forall_dec : 'a1 decidable0 -> 'a1 list decidable0

val scheme_dec : Infer.Unify.MyEval.Rename.Sound.Infra.Defs.sch decidable0

val env_prop_dec : 'a1 decidable0 -> 'a1 Env.env decidable0

val typinf1 :
  Infer.Unify.MyEval.Rename.Sound.Infra.Defs.env ->
  Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm ->
  ((Infer.Unify.MyEval.Rename.Sound.Infra.Defs.kenv,
  Infer.Unify.MyEval.Rename.Sound.Infra.Defs.typ) prod, sumbool) sum

val eval1 :
  Infer.Unify.MyEval.clos Env.env ->
  Infer.Unify.MyEval.Rename.Sound.Infra.Defs.trm -> nat ->
  Infer.Unify.MyEval.eval_res

