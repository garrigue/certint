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

type ('a, 'b) prod =
  | Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

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

val in_dec : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> sumbool

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val split : ('a1, 'a2) prod list -> ('a1 list, 'a2 list) prod

val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list

val seq : nat -> nat -> nat list

val eq_nat_dec : nat -> nat -> sumbool

val lt_eq_lt_dec : nat -> nat -> sumbool sumor

val le_lt_dec : nat -> nat -> sumbool

val max : nat -> nat -> nat

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

module Nat_as_OT : 
 sig 
  type t = nat
  
  val compare : t -> t -> nat compare
  
  val eq_dec : nat -> nat -> sumbool
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
  
  val var_of_nat : nat -> var
  
  val nat_of_var : var -> nat
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

val cut : nat -> 'a1 list -> ('a1 list, 'a1 list) prod

val mkset : Variables.var list -> Variables.vars

module type CstrIntf = 
 sig 
  type cstr 
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
  
  type ckind = { kind_cstr : Cstr.cstr;
                 kind_rel : (Variables.var, typ) prod list }
  
  val ckind_rect :
    (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1) -> ckind
    -> 'a1
  
  val ckind_rec :
    (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1) -> ckind
    -> 'a1
  
  val kind_cstr : ckind -> Cstr.cstr
  
  val kind_rel : ckind -> (Variables.var, typ) prod list
  
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
                   kind_rel : (Variables.var, typ) prod list }
    
    val ckind_rect :
      (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1) ->
      ckind -> 'a1
    
    val ckind_rec :
      (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1) ->
      ckind -> 'a1
    
    val kind_cstr : ckind -> Cstr.cstr
    
    val kind_rel : ckind -> (Variables.var, typ) prod list
    
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
  
  val const_app : Const.const -> Defs.trm list -> Defs.trm
  
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
                     kind_rel : (Variables.var, typ) prod list }
      
      val ckind_rect :
        (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1) ->
        ckind -> 'a1
      
      val ckind_rec :
        (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1) ->
        ckind -> 'a1
      
      val kind_cstr : ckind -> Cstr.cstr
      
      val kind_rel : ckind -> (Variables.var, typ) prod list
      
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
    
    val const_app : Const.const -> Defs.trm list -> Defs.trm
    
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

module MkEval : 
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
                       kind_rel : (Variables.var, typ) prod list }
        
        val ckind_rect :
          (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1) ->
          ckind -> 'a1
        
        val ckind_rec :
          (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1) ->
          ckind -> 'a1
        
        val kind_cstr : ckind -> Cstr.cstr
        
        val kind_rel : ckind -> (Variables.var, typ) prod list
        
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
      
      val const_app : Const.const -> Defs.trm list -> Defs.trm
      
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
    type clos =
      | Coq_clos_abs of Sound.Infra.Defs.trm * clos list
      | Coq_clos_const of Const.const * clos list
    
    val clos_rect :
      (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const -> clos list
      -> 'a1) -> clos -> 'a1
    
    val clos_rec :
      (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const -> clos list
      -> 'a1) -> clos -> 'a1
    
    val clos2trm : clos -> Sound.Infra.Defs.trm
    
    val delta_red : Const.const -> clos list -> clos
    
    type frame = { frm_benv : clos list; frm_app : 
                   clos list; frm_trm : Sound.Infra.Defs.trm }
    
    val frame_rect :
      (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame -> 'a1
    
    val frame_rec :
      (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame -> 'a1
    
    val frm_benv : frame -> clos list
    
    val frm_app : frame -> clos list
    
    val frm_trm : frame -> Sound.Infra.Defs.trm
    
    val is_bvar : Sound.Infra.Defs.trm -> bool
    
    val app_trm :
      Sound.Infra.Defs.trm -> Sound.Infra.Defs.trm -> Sound.Infra.Defs.trm
    
    val app2trm : Sound.Infra.Defs.trm -> clos list -> Sound.Infra.Defs.trm
    
    val stack2trm :
      Sound.Infra.Defs.trm -> frame list -> Sound.Infra.Defs.trm
    
    type eval_res =
      | Result of clos
      | Inter of frame list
    
    val eval_res_rect :
      (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
    
    val eval_res_rec :
      (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
    
    val res2trm : eval_res -> Sound.Infra.Defs.trm
    
    val clos_def : clos
    
    val trm2clos : clos list -> clos Env.env -> Sound.Infra.Defs.trm -> clos
    
    val trm2app :
      Sound.Infra.Defs.trm -> (Sound.Infra.Defs.trm, Sound.Infra.Defs.trm)
      prod option
    
    val eval :
      clos Env.env -> nat -> clos list -> clos list -> Sound.Infra.Defs.trm
      -> frame list -> eval_res
    
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
    
    val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
    
    module Mk3 : 
     functor (SH:Sound2.SndHypIntf) ->
     sig 
      module Sound3 : 
       sig 
        
       end
      
      val is_abs : Sound.Infra.Defs.trm -> bool
     end
   end
 end

module MkUnify : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module MyEval : 
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
                         kind_rel : (Variables.var, typ) prod list }
          
          val ckind_rect :
            (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1)
            -> ckind -> 'a1
          
          val ckind_rec :
            (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ -> 'a1)
            -> ckind -> 'a1
          
          val kind_cstr : ckind -> Cstr.cstr
          
          val kind_rel : ckind -> (Variables.var, typ) prod list
          
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
        
        val const_app : Const.const -> Defs.trm list -> Defs.trm
        
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
      type clos =
        | Coq_clos_abs of Sound.Infra.Defs.trm * clos list
        | Coq_clos_const of Const.const * clos list
      
      val clos_rect :
        (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const -> clos
        list -> 'a1) -> clos -> 'a1
      
      val clos_rec :
        (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const -> clos
        list -> 'a1) -> clos -> 'a1
      
      val clos2trm : clos -> Sound.Infra.Defs.trm
      
      val delta_red : Const.const -> clos list -> clos
      
      type frame = { frm_benv : clos list; frm_app : 
                     clos list; frm_trm : Sound.Infra.Defs.trm }
      
      val frame_rect :
        (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame ->
        'a1
      
      val frame_rec :
        (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame ->
        'a1
      
      val frm_benv : frame -> clos list
      
      val frm_app : frame -> clos list
      
      val frm_trm : frame -> Sound.Infra.Defs.trm
      
      val is_bvar : Sound.Infra.Defs.trm -> bool
      
      val app_trm :
        Sound.Infra.Defs.trm -> Sound.Infra.Defs.trm -> Sound.Infra.Defs.trm
      
      val app2trm : Sound.Infra.Defs.trm -> clos list -> Sound.Infra.Defs.trm
      
      val stack2trm :
        Sound.Infra.Defs.trm -> frame list -> Sound.Infra.Defs.trm
      
      type eval_res =
        | Result of clos
        | Inter of frame list
      
      val eval_res_rect :
        (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val eval_res_rec :
        (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val res2trm : eval_res -> Sound.Infra.Defs.trm
      
      val clos_def : clos
      
      val trm2clos :
        clos list -> clos Env.env -> Sound.Infra.Defs.trm -> clos
      
      val trm2app :
        Sound.Infra.Defs.trm -> (Sound.Infra.Defs.trm, Sound.Infra.Defs.trm)
        prod option
      
      val eval :
        clos Env.env -> nat -> clos list -> clos list -> Sound.Infra.Defs.trm
        -> frame list -> eval_res
      
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
      
      val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
      
      module Mk3 : 
       functor (SH:Sound2.SndHypIntf) ->
       sig 
        module Sound3 : 
         sig 
          
         end
        
        val is_abs : Sound.Infra.Defs.trm -> bool
       end
     end
   end
  
  module type Cstr2I = 
   sig 
    val unique : Cstr.cstr -> Variables.var list
    
    val lub : Cstr.cstr -> Cstr.cstr -> Cstr.cstr
    
    val valid : Cstr.cstr -> sumbool
   end
  
  module Mk2 : 
   functor (Cstr2:Cstr2I) ->
   sig 
    val compose :
      MyEval.Sound.Infra.Defs.typ Env.env -> MyEval.Sound.Infra.Defs.typ
      Env.env -> MyEval.Sound.Infra.subs
    
    val unify_kind_rel :
      (Variables.var, MyEval.Sound.Infra.Defs.typ) prod list ->
      (Variables.var, MyEval.Sound.Infra.Defs.typ) prod list -> Variables.var
      list -> (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
      list -> ((Variables.var, MyEval.Sound.Infra.Defs.typ) prod list,
      (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list)
      prod
    
    val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
    
    val unify_kinds :
      MyEval.Sound.Infra.Defs.kind -> MyEval.Sound.Infra.Defs.kind ->
      (MyEval.Sound.Infra.Defs.kind, (MyEval.Sound.Infra.Defs.typ,
      MyEval.Sound.Infra.Defs.typ) prod list) prod option
    
    val get_kind :
      Variables.var -> MyEval.Sound.Infra.Defs.kind Env.env ->
      MyEval.Sound.Infra.Defs.kind
    
    val unify_vars :
      MyEval.Sound.Infra.Defs.kenv -> Variables.var -> Variables.var ->
      ((Variables.var, MyEval.Sound.Infra.Defs.kind) prod list,
      (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list)
      prod option
    
    val unify_nv :
      (MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
      (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option) ->
      MyEval.Sound.Infra.Defs.kind Env.env -> MyEval.Sound.Infra.Defs.typ
      Env.env -> Variables.VarSet.S.elt -> MyEval.Sound.Infra.Defs.typ ->
      (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option
    
    val unify0 :
      ((MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list
      -> MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
      (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option) ->
      nat -> (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
      list -> MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
      (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option
    
    val accum : ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
    
    val all_types :
      MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
      MyEval.Sound.Infra.Defs.typ) prod list -> MyEval.Sound.Infra.Defs.typ
      list
    
    val typ_size : MyEval.Sound.Infra.Defs.typ -> nat
    
    val pairs_size :
      MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
      MyEval.Sound.Infra.Defs.typ) prod list -> nat
    
    val unify :
      nat -> (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
      list -> MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
      (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option
    
    val id : MyEval.Sound.Infra.Defs.typ Env.env
    
    val all_fv :
      MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
      MyEval.Sound.Infra.Defs.typ) prod list -> Variables.vars
    
    val really_all_fv :
      MyEval.Sound.Infra.subs -> MyEval.Sound.Infra.Defs.kind Env.env ->
      (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list ->
      Variables.VarSet.S.t
    
    val size_pairs :
      MyEval.Sound.Infra.subs -> MyEval.Sound.Infra.Defs.kind Env.env ->
      (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list ->
      nat
   end
 end

val index : ('a1 -> 'a1 -> sumbool) -> nat -> 'a1 -> 'a1 list -> nat option

module MkRename : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module Unify : 
   sig 
    module MyEval : 
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
                           kind_rel : (Variables.var, typ) prod list }
            
            val ckind_rect :
              (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ ->
              'a1) -> ckind -> 'a1
            
            val ckind_rec :
              (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ ->
              'a1) -> ckind -> 'a1
            
            val kind_cstr : ckind -> Cstr.cstr
            
            val kind_rel : ckind -> (Variables.var, typ) prod list
            
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
          
          val const_app : Const.const -> Defs.trm list -> Defs.trm
          
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
        type clos =
          | Coq_clos_abs of Sound.Infra.Defs.trm * clos list
          | Coq_clos_const of Const.const * clos list
        
        val clos_rect :
          (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const -> clos
          list -> 'a1) -> clos -> 'a1
        
        val clos_rec :
          (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const -> clos
          list -> 'a1) -> clos -> 'a1
        
        val clos2trm : clos -> Sound.Infra.Defs.trm
        
        val delta_red : Const.const -> clos list -> clos
        
        type frame = { frm_benv : clos list; frm_app : 
                       clos list; frm_trm : Sound.Infra.Defs.trm }
        
        val frame_rect :
          (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame ->
          'a1
        
        val frame_rec :
          (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame ->
          'a1
        
        val frm_benv : frame -> clos list
        
        val frm_app : frame -> clos list
        
        val frm_trm : frame -> Sound.Infra.Defs.trm
        
        val is_bvar : Sound.Infra.Defs.trm -> bool
        
        val app_trm :
          Sound.Infra.Defs.trm -> Sound.Infra.Defs.trm ->
          Sound.Infra.Defs.trm
        
        val app2trm :
          Sound.Infra.Defs.trm -> clos list -> Sound.Infra.Defs.trm
        
        val stack2trm :
          Sound.Infra.Defs.trm -> frame list -> Sound.Infra.Defs.trm
        
        type eval_res =
          | Result of clos
          | Inter of frame list
        
        val eval_res_rect :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val eval_res_rec :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val res2trm : eval_res -> Sound.Infra.Defs.trm
        
        val clos_def : clos
        
        val trm2clos :
          clos list -> clos Env.env -> Sound.Infra.Defs.trm -> clos
        
        val trm2app :
          Sound.Infra.Defs.trm -> (Sound.Infra.Defs.trm,
          Sound.Infra.Defs.trm) prod option
        
        val eval :
          clos Env.env -> nat -> clos list -> clos list ->
          Sound.Infra.Defs.trm -> frame list -> eval_res
        
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
        
        val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
        
        module Mk3 : 
         functor (SH:Sound2.SndHypIntf) ->
         sig 
          module Sound3 : 
           sig 
            
           end
          
          val is_abs : Sound.Infra.Defs.trm -> bool
         end
       end
     end
    
    module type Cstr2I = 
     sig 
      val unique : Cstr.cstr -> Variables.var list
      
      val lub : Cstr.cstr -> Cstr.cstr -> Cstr.cstr
      
      val valid : Cstr.cstr -> sumbool
     end
    
    module Mk2 : 
     functor (Cstr2:Cstr2I) ->
     sig 
      val compose :
        MyEval.Sound.Infra.Defs.typ Env.env -> MyEval.Sound.Infra.Defs.typ
        Env.env -> MyEval.Sound.Infra.subs
      
      val unify_kind_rel :
        (Variables.var, MyEval.Sound.Infra.Defs.typ) prod list ->
        (Variables.var, MyEval.Sound.Infra.Defs.typ) prod list ->
        Variables.var list -> (MyEval.Sound.Infra.Defs.typ,
        MyEval.Sound.Infra.Defs.typ) prod list -> ((Variables.var,
        MyEval.Sound.Infra.Defs.typ) prod list, (MyEval.Sound.Infra.Defs.typ,
        MyEval.Sound.Infra.Defs.typ) prod list) prod
      
      val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
      
      val unify_kinds :
        MyEval.Sound.Infra.Defs.kind -> MyEval.Sound.Infra.Defs.kind ->
        (MyEval.Sound.Infra.Defs.kind, (MyEval.Sound.Infra.Defs.typ,
        MyEval.Sound.Infra.Defs.typ) prod list) prod option
      
      val get_kind :
        Variables.var -> MyEval.Sound.Infra.Defs.kind Env.env ->
        MyEval.Sound.Infra.Defs.kind
      
      val unify_vars :
        MyEval.Sound.Infra.Defs.kenv -> Variables.var -> Variables.var ->
        ((Variables.var, MyEval.Sound.Infra.Defs.kind) prod list,
        (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list)
        prod option
      
      val unify_nv :
        (MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
        (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option)
        -> MyEval.Sound.Infra.Defs.kind Env.env ->
        MyEval.Sound.Infra.Defs.typ Env.env -> Variables.VarSet.S.elt ->
        MyEval.Sound.Infra.Defs.typ -> (MyEval.Sound.Infra.Defs.kenv,
        MyEval.Sound.Infra.subs) prod option
      
      val unify0 :
        ((MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list
        -> MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
        (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option)
        -> nat -> (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ)
        prod list -> MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs
        -> (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod
        option
      
      val accum :
        ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
      
      val all_types :
        MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
        MyEval.Sound.Infra.Defs.typ) prod list -> MyEval.Sound.Infra.Defs.typ
        list
      
      val typ_size : MyEval.Sound.Infra.Defs.typ -> nat
      
      val pairs_size :
        MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
        MyEval.Sound.Infra.Defs.typ) prod list -> nat
      
      val unify :
        nat -> (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ)
        prod list -> MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs
        -> (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod
        option
      
      val id : MyEval.Sound.Infra.Defs.typ Env.env
      
      val all_fv :
        MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
        MyEval.Sound.Infra.Defs.typ) prod list -> Variables.vars
      
      val really_all_fv :
        MyEval.Sound.Infra.subs -> MyEval.Sound.Infra.Defs.kind Env.env ->
        (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list
        -> Variables.VarSet.S.t
      
      val size_pairs :
        MyEval.Sound.Infra.subs -> MyEval.Sound.Infra.Defs.kind Env.env ->
        (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod list
        -> nat
     end
   end
  
  module Mk2 : 
   functor (Delta:Unify.MyEval.Sound.Infra.Defs.DeltaIntf) ->
   sig 
    module MyEval2 : 
     sig 
      type clos =
        | Coq_clos_abs of Unify.MyEval.Sound.Infra.Defs.trm * clos list
        | Coq_clos_const of Const.const * clos list
      
      val clos_rect :
        (Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
        (Const.const -> clos list -> 'a1) -> clos -> 'a1
      
      val clos_rec :
        (Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
        (Const.const -> clos list -> 'a1) -> clos -> 'a1
      
      val clos2trm : clos -> Unify.MyEval.Sound.Infra.Defs.trm
      
      val delta_red : Const.const -> clos list -> clos
      
      type frame = { frm_benv : clos list; frm_app : 
                     clos list; frm_trm : Unify.MyEval.Sound.Infra.Defs.trm }
      
      val frame_rect :
        (clos list -> clos list -> Unify.MyEval.Sound.Infra.Defs.trm -> 'a1)
        -> frame -> 'a1
      
      val frame_rec :
        (clos list -> clos list -> Unify.MyEval.Sound.Infra.Defs.trm -> 'a1)
        -> frame -> 'a1
      
      val frm_benv : frame -> clos list
      
      val frm_app : frame -> clos list
      
      val frm_trm : frame -> Unify.MyEval.Sound.Infra.Defs.trm
      
      val is_bvar : Unify.MyEval.Sound.Infra.Defs.trm -> bool
      
      val app_trm :
        Unify.MyEval.Sound.Infra.Defs.trm ->
        Unify.MyEval.Sound.Infra.Defs.trm ->
        Unify.MyEval.Sound.Infra.Defs.trm
      
      val app2trm :
        Unify.MyEval.Sound.Infra.Defs.trm -> clos list ->
        Unify.MyEval.Sound.Infra.Defs.trm
      
      val stack2trm :
        Unify.MyEval.Sound.Infra.Defs.trm -> frame list ->
        Unify.MyEval.Sound.Infra.Defs.trm
      
      type eval_res =
        | Result of clos
        | Inter of frame list
      
      val eval_res_rect :
        (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val eval_res_rec :
        (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val res2trm : eval_res -> Unify.MyEval.Sound.Infra.Defs.trm
      
      val clos_def : clos
      
      val trm2clos :
        clos list -> clos Env.env -> Unify.MyEval.Sound.Infra.Defs.trm ->
        clos
      
      val trm2app :
        Unify.MyEval.Sound.Infra.Defs.trm ->
        (Unify.MyEval.Sound.Infra.Defs.trm,
        Unify.MyEval.Sound.Infra.Defs.trm) prod option
      
      val eval :
        clos Env.env -> nat -> clos list -> clos list ->
        Unify.MyEval.Sound.Infra.Defs.trm -> frame list -> eval_res
      
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
      
      val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
      
      module Mk3 : 
       functor (SH:Sound2.SndHypIntf) ->
       sig 
        module Sound3 : 
         sig 
          
         end
        
        val is_abs : Unify.MyEval.Sound.Infra.Defs.trm -> bool
       end
     end
    
    val typ_generalize :
      Variables.var list -> Unify.MyEval.Sound.Infra.Defs.typ ->
      Unify.MyEval.Sound.Infra.Defs.typ
    
    val sch_generalize :
      Variables.var list -> Unify.MyEval.Sound.Infra.Defs.typ ->
      Unify.MyEval.Sound.Infra.Defs.kind list ->
      Unify.MyEval.Sound.Infra.Defs.sch
    
    val list_fst : ('a1, 'a2) prod list -> 'a1 list
   end
 end

module MkInfer : 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 sig 
  module Rename : 
   sig 
    module Unify : 
     sig 
      module MyEval : 
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
                             kind_rel : (Variables.var, typ) prod list }
              
              val ckind_rect :
                (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ ->
                'a1) -> ckind -> 'a1
              
              val ckind_rec :
                (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ ->
                'a1) -> ckind -> 'a1
              
              val kind_cstr : ckind -> Cstr.cstr
              
              val kind_rel : ckind -> (Variables.var, typ) prod list
              
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
            
            val const_app : Const.const -> Defs.trm list -> Defs.trm
            
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
          type clos =
            | Coq_clos_abs of Sound.Infra.Defs.trm * clos list
            | Coq_clos_const of Const.const * clos list
          
          val clos_rect :
            (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
            clos list -> 'a1) -> clos -> 'a1
          
          val clos_rec :
            (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
            clos list -> 'a1) -> clos -> 'a1
          
          val clos2trm : clos -> Sound.Infra.Defs.trm
          
          val delta_red : Const.const -> clos list -> clos
          
          type frame = { frm_benv : clos list; frm_app : 
                         clos list; frm_trm : Sound.Infra.Defs.trm }
          
          val frame_rect :
            (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame
            -> 'a1
          
          val frame_rec :
            (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame
            -> 'a1
          
          val frm_benv : frame -> clos list
          
          val frm_app : frame -> clos list
          
          val frm_trm : frame -> Sound.Infra.Defs.trm
          
          val is_bvar : Sound.Infra.Defs.trm -> bool
          
          val app_trm :
            Sound.Infra.Defs.trm -> Sound.Infra.Defs.trm ->
            Sound.Infra.Defs.trm
          
          val app2trm :
            Sound.Infra.Defs.trm -> clos list -> Sound.Infra.Defs.trm
          
          val stack2trm :
            Sound.Infra.Defs.trm -> frame list -> Sound.Infra.Defs.trm
          
          type eval_res =
            | Result of clos
            | Inter of frame list
          
          val eval_res_rect :
            (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
          
          val eval_res_rec :
            (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
          
          val res2trm : eval_res -> Sound.Infra.Defs.trm
          
          val clos_def : clos
          
          val trm2clos :
            clos list -> clos Env.env -> Sound.Infra.Defs.trm -> clos
          
          val trm2app :
            Sound.Infra.Defs.trm -> (Sound.Infra.Defs.trm,
            Sound.Infra.Defs.trm) prod option
          
          val eval :
            clos Env.env -> nat -> clos list -> clos list ->
            Sound.Infra.Defs.trm -> frame list -> eval_res
          
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
          
          val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
          
          module Mk3 : 
           functor (SH:Sound2.SndHypIntf) ->
           sig 
            module Sound3 : 
             sig 
              
             end
            
            val is_abs : Sound.Infra.Defs.trm -> bool
           end
         end
       end
      
      module type Cstr2I = 
       sig 
        val unique : Cstr.cstr -> Variables.var list
        
        val lub : Cstr.cstr -> Cstr.cstr -> Cstr.cstr
        
        val valid : Cstr.cstr -> sumbool
       end
      
      module Mk2 : 
       functor (Cstr2:Cstr2I) ->
       sig 
        val compose :
          MyEval.Sound.Infra.Defs.typ Env.env -> MyEval.Sound.Infra.Defs.typ
          Env.env -> MyEval.Sound.Infra.subs
        
        val unify_kind_rel :
          (Variables.var, MyEval.Sound.Infra.Defs.typ) prod list ->
          (Variables.var, MyEval.Sound.Infra.Defs.typ) prod list ->
          Variables.var list -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list -> ((Variables.var,
          MyEval.Sound.Infra.Defs.typ) prod list,
          (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list) prod
        
        val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
        
        val unify_kinds :
          MyEval.Sound.Infra.Defs.kind -> MyEval.Sound.Infra.Defs.kind ->
          (MyEval.Sound.Infra.Defs.kind, (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list) prod option
        
        val get_kind :
          Variables.var -> MyEval.Sound.Infra.Defs.kind Env.env ->
          MyEval.Sound.Infra.Defs.kind
        
        val unify_vars :
          MyEval.Sound.Infra.Defs.kenv -> Variables.var -> Variables.var ->
          ((Variables.var, MyEval.Sound.Infra.Defs.kind) prod list,
          (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list) prod option
        
        val unify_nv :
          (MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
          (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod
          option) -> MyEval.Sound.Infra.Defs.kind Env.env ->
          MyEval.Sound.Infra.Defs.typ Env.env -> Variables.VarSet.S.elt ->
          MyEval.Sound.Infra.Defs.typ -> (MyEval.Sound.Infra.Defs.kenv,
          MyEval.Sound.Infra.subs) prod option
        
        val unify0 :
          ((MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list -> MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
          (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod
          option) -> nat -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list ->
          MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
          (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option
        
        val accum :
          ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
        
        val all_types :
          MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list ->
          MyEval.Sound.Infra.Defs.typ list
        
        val typ_size : MyEval.Sound.Infra.Defs.typ -> nat
        
        val pairs_size :
          MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list -> nat
        
        val unify :
          nat -> (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ)
          prod list -> MyEval.Sound.Infra.Defs.kenv ->
          MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.kenv,
          MyEval.Sound.Infra.subs) prod option
        
        val id : MyEval.Sound.Infra.Defs.typ Env.env
        
        val all_fv :
          MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list -> Variables.vars
        
        val really_all_fv :
          MyEval.Sound.Infra.subs -> MyEval.Sound.Infra.Defs.kind Env.env ->
          (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list -> Variables.VarSet.S.t
        
        val size_pairs :
          MyEval.Sound.Infra.subs -> MyEval.Sound.Infra.Defs.kind Env.env ->
          (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list -> nat
       end
     end
    
    module Mk2 : 
     functor (Delta:Unify.MyEval.Sound.Infra.Defs.DeltaIntf) ->
     sig 
      module MyEval2 : 
       sig 
        type clos =
          | Coq_clos_abs of Unify.MyEval.Sound.Infra.Defs.trm * clos list
          | Coq_clos_const of Const.const * clos list
        
        val clos_rect :
          (Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
          (Const.const -> clos list -> 'a1) -> clos -> 'a1
        
        val clos_rec :
          (Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
          (Const.const -> clos list -> 'a1) -> clos -> 'a1
        
        val clos2trm : clos -> Unify.MyEval.Sound.Infra.Defs.trm
        
        val delta_red : Const.const -> clos list -> clos
        
        type frame = { frm_benv : clos list; frm_app : 
                       clos list; frm_trm : Unify.MyEval.Sound.Infra.Defs.trm }
        
        val frame_rect :
          (clos list -> clos list -> Unify.MyEval.Sound.Infra.Defs.trm ->
          'a1) -> frame -> 'a1
        
        val frame_rec :
          (clos list -> clos list -> Unify.MyEval.Sound.Infra.Defs.trm ->
          'a1) -> frame -> 'a1
        
        val frm_benv : frame -> clos list
        
        val frm_app : frame -> clos list
        
        val frm_trm : frame -> Unify.MyEval.Sound.Infra.Defs.trm
        
        val is_bvar : Unify.MyEval.Sound.Infra.Defs.trm -> bool
        
        val app_trm :
          Unify.MyEval.Sound.Infra.Defs.trm ->
          Unify.MyEval.Sound.Infra.Defs.trm ->
          Unify.MyEval.Sound.Infra.Defs.trm
        
        val app2trm :
          Unify.MyEval.Sound.Infra.Defs.trm -> clos list ->
          Unify.MyEval.Sound.Infra.Defs.trm
        
        val stack2trm :
          Unify.MyEval.Sound.Infra.Defs.trm -> frame list ->
          Unify.MyEval.Sound.Infra.Defs.trm
        
        type eval_res =
          | Result of clos
          | Inter of frame list
        
        val eval_res_rect :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val eval_res_rec :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val res2trm : eval_res -> Unify.MyEval.Sound.Infra.Defs.trm
        
        val clos_def : clos
        
        val trm2clos :
          clos list -> clos Env.env -> Unify.MyEval.Sound.Infra.Defs.trm ->
          clos
        
        val trm2app :
          Unify.MyEval.Sound.Infra.Defs.trm ->
          (Unify.MyEval.Sound.Infra.Defs.trm,
          Unify.MyEval.Sound.Infra.Defs.trm) prod option
        
        val eval :
          clos Env.env -> nat -> clos list -> clos list ->
          Unify.MyEval.Sound.Infra.Defs.trm -> frame list -> eval_res
        
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
        
        val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
        
        module Mk3 : 
         functor (SH:Sound2.SndHypIntf) ->
         sig 
          module Sound3 : 
           sig 
            
           end
          
          val is_abs : Unify.MyEval.Sound.Infra.Defs.trm -> bool
         end
       end
      
      val typ_generalize :
        Variables.var list -> Unify.MyEval.Sound.Infra.Defs.typ ->
        Unify.MyEval.Sound.Infra.Defs.typ
      
      val sch_generalize :
        Variables.var list -> Unify.MyEval.Sound.Infra.Defs.typ ->
        Unify.MyEval.Sound.Infra.Defs.kind list ->
        Unify.MyEval.Sound.Infra.Defs.sch
      
      val list_fst : ('a1, 'a2) prod list -> 'a1 list
     end
   end
  
  module Mk2 : 
   functor (Delta:Rename.Unify.MyEval.Sound.Infra.Defs.DeltaIntf) ->
   functor (Cstr2:Rename.Unify.Cstr2I) ->
   sig 
    module Rename2 : 
     sig 
      module MyEval2 : 
       sig 
        type clos =
          | Coq_clos_abs of Rename.Unify.MyEval.Sound.Infra.Defs.trm
             * clos list
          | Coq_clos_const of Const.const * clos list
        
        val clos_rect :
          (Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
          (Const.const -> clos list -> 'a1) -> clos -> 'a1
        
        val clos_rec :
          (Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
          (Const.const -> clos list -> 'a1) -> clos -> 'a1
        
        val clos2trm : clos -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val delta_red : Const.const -> clos list -> clos
        
        type frame = { frm_benv : clos list; frm_app : 
                       clos list;
                       frm_trm : Rename.Unify.MyEval.Sound.Infra.Defs.trm }
        
        val frame_rect :
          (clos list -> clos list -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
          -> 'a1) -> frame -> 'a1
        
        val frame_rec :
          (clos list -> clos list -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
          -> 'a1) -> frame -> 'a1
        
        val frm_benv : frame -> clos list
        
        val frm_app : frame -> clos list
        
        val frm_trm : frame -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val is_bvar : Rename.Unify.MyEval.Sound.Infra.Defs.trm -> bool
        
        val app_trm :
          Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val app2trm :
          Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val stack2trm :
          Rename.Unify.MyEval.Sound.Infra.Defs.trm -> frame list ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        type eval_res =
          | Result of clos
          | Inter of frame list
        
        val eval_res_rect :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val eval_res_rec :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val res2trm : eval_res -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val clos_def : clos
        
        val trm2clos :
          clos list -> clos Env.env ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos
        
        val trm2app :
          Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
          (Rename.Unify.MyEval.Sound.Infra.Defs.trm,
          Rename.Unify.MyEval.Sound.Infra.Defs.trm) prod option
        
        val eval :
          clos Env.env -> nat -> clos list -> clos list ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm -> frame list -> eval_res
        
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
        
        val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
        
        module Mk3 : 
         functor (SH:Sound2.SndHypIntf) ->
         sig 
          module Sound3 : 
           sig 
            
           end
          
          val is_abs : Rename.Unify.MyEval.Sound.Infra.Defs.trm -> bool
         end
       end
      
      val typ_generalize :
        Variables.var list -> Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
        Rename.Unify.MyEval.Sound.Infra.Defs.typ
      
      val sch_generalize :
        Variables.var list -> Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.sch
      
      val list_fst : ('a1, 'a2) prod list -> 'a1 list
     end
    
    module Body : 
     sig 
      val compose :
        Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
        Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
        Rename.Unify.MyEval.Sound.Infra.subs
      
      val unify_kind_rel :
        (Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list
        -> (Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod
        list -> Variables.var list ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        ((Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list,
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod
      
      val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
      
      val unify_kinds :
        Rename.Unify.MyEval.Sound.Infra.Defs.kind ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kind,
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod option
      
      val get_kind :
        Variables.var -> Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind
      
      val unify_vars :
        Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.var ->
        Variables.var -> ((Variables.var,
        Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list,
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod option
      
      val unify_nv :
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option) ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
        Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
        Variables.VarSet.S.elt -> Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option
      
      val unify0 :
        ((Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option) -> nat ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option
      
      val accum :
        ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
      
      val all_types :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.typ list
      
      val typ_size : Rename.Unify.MyEval.Sound.Infra.Defs.typ -> nat
      
      val pairs_size :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list -> nat
      
      val unify :
        nat -> (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option
      
      val id : Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env
      
      val all_fv :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list -> Variables.vars
      
      val really_all_fv :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Variables.VarSet.S.t
      
      val size_pairs :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list -> nat
     end
    
    val unify :
      Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
      Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
      Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
      Rename.Unify.MyEval.Sound.Infra.subs ->
      (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Rename.Unify.MyEval.Sound.Infra.subs) prod option
    
    val fvs :
      Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
      Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
      Rename.Unify.MyEval.Sound.Infra.Defs.sch Env.env ->
      Variables.VarSet.S.t
    
    val close_fvars :
      nat -> Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.vars ->
      Variables.vars -> Variables.vars
    
    val close_fvk :
      (Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list ->
      Variables.vars -> Variables.vars
    
    val split_env :
      Variables.vars -> 'a1 Env.env -> ('a1 Env.env, 'a1 Env.env) prod
    
    val vars_subst :
      Rename.Unify.MyEval.Sound.Infra.subs -> Variables.VarSet.S.t ->
      Variables.VarSet.S.t
    
    val typinf_generalize :
      (Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list ->
      Rename.Unify.MyEval.Sound.Infra.Defs.sch Env.env -> Variables.vars ->
      Rename.Unify.MyEval.Sound.Infra.Defs.typ -> ((Variables.var,
      Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list,
      Rename.Unify.MyEval.Sound.Infra.Defs.sch) prod
    
    val kdom : Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.vars
    
    val typinf :
      Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
      Rename.Unify.MyEval.Sound.Infra.Defs.env ->
      Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
      Rename.Unify.MyEval.Sound.Infra.Defs.typ -> Variables.vars ->
      Rename.Unify.MyEval.Sound.Infra.subs -> nat ->
      ((Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Rename.Unify.MyEval.Sound.Infra.subs) prod option, Variables.vars) prod
    
    val trm_depth : Rename.Unify.MyEval.Sound.Infra.Defs.trm -> nat
    
    val typinf' :
      Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
      (Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env,
      Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod option
    
    val coq_Gc : (bool, Rename2.MyEval2.Sound2.JudgInfra.Judge.gc_kind) prod
   end
 end

type 'a set = 'a list

val set_add : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> 'a1 set

val set_mem : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> bool

val set_inter : ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set

val set_union : ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set

module Cstr : 
 sig 
  type cstr_impl = { cstr_low : Variables.var list;
                     cstr_high : Variables.var list option }
  
  val cstr_impl_rect :
    (Variables.var list -> Variables.var list option -> 'a1) -> cstr_impl ->
    'a1
  
  val cstr_impl_rec :
    (Variables.var list -> Variables.var list option -> 'a1) -> cstr_impl ->
    'a1
  
  val cstr_low : cstr_impl -> Variables.var list
  
  val cstr_high : cstr_impl -> Variables.var list option
  
  type cstr = cstr_impl
 end

module Const : 
 sig 
  type ops =
    | Coq_tag of Variables.var
    | Coq_matches of Variables.var list
  
  val ops_rect :
    (Variables.var -> 'a1) -> (Variables.var list -> __ -> 'a1) -> ops -> 'a1
  
  val ops_rec :
    (Variables.var -> 'a1) -> (Variables.var list -> __ -> 'a1) -> ops -> 'a1
  
  type const = ops
  
  val arity : ops -> nat
 end

module Infer : 
 sig 
  module Rename : 
   sig 
    module Unify : 
     sig 
      module MyEval : 
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
                             kind_rel : (Variables.var, typ) prod list }
              
              val ckind_rect :
                (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ ->
                'a1) -> ckind -> 'a1
              
              val ckind_rec :
                (Cstr.cstr -> __ -> (Variables.var, typ) prod list -> __ ->
                'a1) -> ckind -> 'a1
              
              val kind_cstr : ckind -> Cstr.cstr
              
              val kind_rel : ckind -> (Variables.var, typ) prod list
              
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
            
            val const_app : Const.const -> Defs.trm list -> Defs.trm
            
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
          type clos =
            | Coq_clos_abs of Sound.Infra.Defs.trm * clos list
            | Coq_clos_const of Const.const * clos list
          
          val clos_rect :
            (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
            clos list -> 'a1) -> clos -> 'a1
          
          val clos_rec :
            (Sound.Infra.Defs.trm -> clos list -> 'a1) -> (Const.const ->
            clos list -> 'a1) -> clos -> 'a1
          
          val clos2trm : clos -> Sound.Infra.Defs.trm
          
          val delta_red : Const.const -> clos list -> clos
          
          type frame = { frm_benv : clos list; frm_app : 
                         clos list; frm_trm : Sound.Infra.Defs.trm }
          
          val frame_rect :
            (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame
            -> 'a1
          
          val frame_rec :
            (clos list -> clos list -> Sound.Infra.Defs.trm -> 'a1) -> frame
            -> 'a1
          
          val frm_benv : frame -> clos list
          
          val frm_app : frame -> clos list
          
          val frm_trm : frame -> Sound.Infra.Defs.trm
          
          val is_bvar : Sound.Infra.Defs.trm -> bool
          
          val app_trm :
            Sound.Infra.Defs.trm -> Sound.Infra.Defs.trm ->
            Sound.Infra.Defs.trm
          
          val app2trm :
            Sound.Infra.Defs.trm -> clos list -> Sound.Infra.Defs.trm
          
          val stack2trm :
            Sound.Infra.Defs.trm -> frame list -> Sound.Infra.Defs.trm
          
          type eval_res =
            | Result of clos
            | Inter of frame list
          
          val eval_res_rect :
            (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
          
          val eval_res_rec :
            (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
          
          val res2trm : eval_res -> Sound.Infra.Defs.trm
          
          val clos_def : clos
          
          val trm2clos :
            clos list -> clos Env.env -> Sound.Infra.Defs.trm -> clos
          
          val trm2app :
            Sound.Infra.Defs.trm -> (Sound.Infra.Defs.trm,
            Sound.Infra.Defs.trm) prod option
          
          val eval :
            clos Env.env -> nat -> clos list -> clos list ->
            Sound.Infra.Defs.trm -> frame list -> eval_res
          
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
          
          val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
          
          module Mk3 : 
           functor (SH:Sound2.SndHypIntf) ->
           sig 
            module Sound3 : 
             sig 
              
             end
            
            val is_abs : Sound.Infra.Defs.trm -> bool
           end
         end
       end
      
      module type Cstr2I = 
       sig 
        val unique : Cstr.cstr -> Variables.var list
        
        val lub : Cstr.cstr -> Cstr.cstr -> Cstr.cstr
        
        val valid : Cstr.cstr -> sumbool
       end
      
      module Mk2 : 
       functor (Cstr2:Cstr2I) ->
       sig 
        val compose :
          MyEval.Sound.Infra.Defs.typ Env.env -> MyEval.Sound.Infra.Defs.typ
          Env.env -> MyEval.Sound.Infra.subs
        
        val unify_kind_rel :
          (Variables.var, MyEval.Sound.Infra.Defs.typ) prod list ->
          (Variables.var, MyEval.Sound.Infra.Defs.typ) prod list ->
          Variables.var list -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list -> ((Variables.var,
          MyEval.Sound.Infra.Defs.typ) prod list,
          (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list) prod
        
        val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
        
        val unify_kinds :
          MyEval.Sound.Infra.Defs.kind -> MyEval.Sound.Infra.Defs.kind ->
          (MyEval.Sound.Infra.Defs.kind, (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list) prod option
        
        val get_kind :
          Variables.var -> MyEval.Sound.Infra.Defs.kind Env.env ->
          MyEval.Sound.Infra.Defs.kind
        
        val unify_vars :
          MyEval.Sound.Infra.Defs.kenv -> Variables.var -> Variables.var ->
          ((Variables.var, MyEval.Sound.Infra.Defs.kind) prod list,
          (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list) prod option
        
        val unify_nv :
          (MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
          (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod
          option) -> MyEval.Sound.Infra.Defs.kind Env.env ->
          MyEval.Sound.Infra.Defs.typ Env.env -> Variables.VarSet.S.elt ->
          MyEval.Sound.Infra.Defs.typ -> (MyEval.Sound.Infra.Defs.kenv,
          MyEval.Sound.Infra.subs) prod option
        
        val unify0 :
          ((MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list -> MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
          (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod
          option) -> nat -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list ->
          MyEval.Sound.Infra.Defs.kenv -> MyEval.Sound.Infra.subs ->
          (MyEval.Sound.Infra.Defs.kenv, MyEval.Sound.Infra.subs) prod option
        
        val accum :
          ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
        
        val all_types :
          MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list ->
          MyEval.Sound.Infra.Defs.typ list
        
        val typ_size : MyEval.Sound.Infra.Defs.typ -> nat
        
        val pairs_size :
          MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list -> nat
        
        val unify :
          nat -> (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ)
          prod list -> MyEval.Sound.Infra.Defs.kenv ->
          MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.kenv,
          MyEval.Sound.Infra.subs) prod option
        
        val id : MyEval.Sound.Infra.Defs.typ Env.env
        
        val all_fv :
          MyEval.Sound.Infra.subs -> (MyEval.Sound.Infra.Defs.typ,
          MyEval.Sound.Infra.Defs.typ) prod list -> Variables.vars
        
        val really_all_fv :
          MyEval.Sound.Infra.subs -> MyEval.Sound.Infra.Defs.kind Env.env ->
          (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list -> Variables.VarSet.S.t
        
        val size_pairs :
          MyEval.Sound.Infra.subs -> MyEval.Sound.Infra.Defs.kind Env.env ->
          (MyEval.Sound.Infra.Defs.typ, MyEval.Sound.Infra.Defs.typ) prod
          list -> nat
       end
     end
    
    module Mk2 : 
     functor (Delta:Unify.MyEval.Sound.Infra.Defs.DeltaIntf) ->
     sig 
      module MyEval2 : 
       sig 
        type clos =
          | Coq_clos_abs of Unify.MyEval.Sound.Infra.Defs.trm * clos list
          | Coq_clos_const of Const.const * clos list
        
        val clos_rect :
          (Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
          (Const.const -> clos list -> 'a1) -> clos -> 'a1
        
        val clos_rec :
          (Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
          (Const.const -> clos list -> 'a1) -> clos -> 'a1
        
        val clos2trm : clos -> Unify.MyEval.Sound.Infra.Defs.trm
        
        val delta_red : Const.const -> clos list -> clos
        
        type frame = { frm_benv : clos list; frm_app : 
                       clos list; frm_trm : Unify.MyEval.Sound.Infra.Defs.trm }
        
        val frame_rect :
          (clos list -> clos list -> Unify.MyEval.Sound.Infra.Defs.trm ->
          'a1) -> frame -> 'a1
        
        val frame_rec :
          (clos list -> clos list -> Unify.MyEval.Sound.Infra.Defs.trm ->
          'a1) -> frame -> 'a1
        
        val frm_benv : frame -> clos list
        
        val frm_app : frame -> clos list
        
        val frm_trm : frame -> Unify.MyEval.Sound.Infra.Defs.trm
        
        val is_bvar : Unify.MyEval.Sound.Infra.Defs.trm -> bool
        
        val app_trm :
          Unify.MyEval.Sound.Infra.Defs.trm ->
          Unify.MyEval.Sound.Infra.Defs.trm ->
          Unify.MyEval.Sound.Infra.Defs.trm
        
        val app2trm :
          Unify.MyEval.Sound.Infra.Defs.trm -> clos list ->
          Unify.MyEval.Sound.Infra.Defs.trm
        
        val stack2trm :
          Unify.MyEval.Sound.Infra.Defs.trm -> frame list ->
          Unify.MyEval.Sound.Infra.Defs.trm
        
        type eval_res =
          | Result of clos
          | Inter of frame list
        
        val eval_res_rect :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val eval_res_rec :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val res2trm : eval_res -> Unify.MyEval.Sound.Infra.Defs.trm
        
        val clos_def : clos
        
        val trm2clos :
          clos list -> clos Env.env -> Unify.MyEval.Sound.Infra.Defs.trm ->
          clos
        
        val trm2app :
          Unify.MyEval.Sound.Infra.Defs.trm ->
          (Unify.MyEval.Sound.Infra.Defs.trm,
          Unify.MyEval.Sound.Infra.Defs.trm) prod option
        
        val eval :
          clos Env.env -> nat -> clos list -> clos list ->
          Unify.MyEval.Sound.Infra.Defs.trm -> frame list -> eval_res
        
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
        
        val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
        
        module Mk3 : 
         functor (SH:Sound2.SndHypIntf) ->
         sig 
          module Sound3 : 
           sig 
            
           end
          
          val is_abs : Unify.MyEval.Sound.Infra.Defs.trm -> bool
         end
       end
      
      val typ_generalize :
        Variables.var list -> Unify.MyEval.Sound.Infra.Defs.typ ->
        Unify.MyEval.Sound.Infra.Defs.typ
      
      val sch_generalize :
        Variables.var list -> Unify.MyEval.Sound.Infra.Defs.typ ->
        Unify.MyEval.Sound.Infra.Defs.kind list ->
        Unify.MyEval.Sound.Infra.Defs.sch
      
      val list_fst : ('a1, 'a2) prod list -> 'a1 list
     end
   end
  
  module Mk2 : 
   functor (Delta:Rename.Unify.MyEval.Sound.Infra.Defs.DeltaIntf) ->
   functor (Cstr2:Rename.Unify.Cstr2I) ->
   sig 
    module Rename2 : 
     sig 
      module MyEval2 : 
       sig 
        type clos =
          | Coq_clos_abs of Rename.Unify.MyEval.Sound.Infra.Defs.trm
             * clos list
          | Coq_clos_const of Const.const * clos list
        
        val clos_rect :
          (Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
          (Const.const -> clos list -> 'a1) -> clos -> 'a1
        
        val clos_rec :
          (Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1) ->
          (Const.const -> clos list -> 'a1) -> clos -> 'a1
        
        val clos2trm : clos -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val delta_red : Const.const -> clos list -> clos
        
        type frame = { frm_benv : clos list; frm_app : 
                       clos list;
                       frm_trm : Rename.Unify.MyEval.Sound.Infra.Defs.trm }
        
        val frame_rect :
          (clos list -> clos list -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
          -> 'a1) -> frame -> 'a1
        
        val frame_rec :
          (clos list -> clos list -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
          -> 'a1) -> frame -> 'a1
        
        val frm_benv : frame -> clos list
        
        val frm_app : frame -> clos list
        
        val frm_trm : frame -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val is_bvar : Rename.Unify.MyEval.Sound.Infra.Defs.trm -> bool
        
        val app_trm :
          Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val app2trm :
          Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val stack2trm :
          Rename.Unify.MyEval.Sound.Infra.Defs.trm -> frame list ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        type eval_res =
          | Result of clos
          | Inter of frame list
        
        val eval_res_rect :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val eval_res_rec :
          (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
        
        val res2trm : eval_res -> Rename.Unify.MyEval.Sound.Infra.Defs.trm
        
        val clos_def : clos
        
        val trm2clos :
          clos list -> clos Env.env ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos
        
        val trm2app :
          Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
          (Rename.Unify.MyEval.Sound.Infra.Defs.trm,
          Rename.Unify.MyEval.Sound.Infra.Defs.trm) prod option
        
        val eval :
          clos Env.env -> nat -> clos list -> clos list ->
          Rename.Unify.MyEval.Sound.Infra.Defs.trm -> frame list -> eval_res
        
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
        
        val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
        
        module Mk3 : 
         functor (SH:Sound2.SndHypIntf) ->
         sig 
          module Sound3 : 
           sig 
            
           end
          
          val is_abs : Rename.Unify.MyEval.Sound.Infra.Defs.trm -> bool
         end
       end
      
      val typ_generalize :
        Variables.var list -> Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
        Rename.Unify.MyEval.Sound.Infra.Defs.typ
      
      val sch_generalize :
        Variables.var list -> Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.sch
      
      val list_fst : ('a1, 'a2) prod list -> 'a1 list
     end
    
    module Body : 
     sig 
      val compose :
        Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
        Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
        Rename.Unify.MyEval.Sound.Infra.subs
      
      val unify_kind_rel :
        (Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list
        -> (Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod
        list -> Variables.var list ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        ((Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list,
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod
      
      val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
      
      val unify_kinds :
        Rename.Unify.MyEval.Sound.Infra.Defs.kind ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kind,
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod option
      
      val get_kind :
        Variables.var -> Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind
      
      val unify_vars :
        Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.var ->
        Variables.var -> ((Variables.var,
        Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list,
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod option
      
      val unify_nv :
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option) ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
        Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
        Variables.VarSet.S.elt -> Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option
      
      val unify0 :
        ((Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option) -> nat ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option
      
      val accum :
        ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
      
      val all_types :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.typ list
      
      val typ_size : Rename.Unify.MyEval.Sound.Infra.Defs.typ -> nat
      
      val pairs_size :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list -> nat
      
      val unify :
        nat -> (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
        Rename.Unify.MyEval.Sound.Infra.subs) prod option
      
      val id : Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env
      
      val all_fv :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list -> Variables.vars
      
      val really_all_fv :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
        Variables.VarSet.S.t
      
      val size_pairs :
        Rename.Unify.MyEval.Sound.Infra.subs ->
        Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
        (Rename.Unify.MyEval.Sound.Infra.Defs.typ,
        Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list -> nat
     end
    
    val unify :
      Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
      Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
      Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
      Rename.Unify.MyEval.Sound.Infra.subs ->
      (Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Rename.Unify.MyEval.Sound.Infra.subs) prod option
    
    val fvs :
      Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
      Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
      Rename.Unify.MyEval.Sound.Infra.Defs.sch Env.env ->
      Variables.VarSet.S.t
    
    val close_fvars :
      nat -> Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.vars ->
      Variables.vars -> Variables.vars
    
    val close_fvk :
      (Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list ->
      Variables.vars -> Variables.vars
    
    val split_env :
      Variables.vars -> 'a1 Env.env -> ('a1 Env.env, 'a1 Env.env) prod
    
    val vars_subst :
      Rename.Unify.MyEval.Sound.Infra.subs -> Variables.VarSet.S.t ->
      Variables.VarSet.S.t
    
    val typinf_generalize :
      (Variables.var, Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list ->
      Rename.Unify.MyEval.Sound.Infra.Defs.sch Env.env -> Variables.vars ->
      Rename.Unify.MyEval.Sound.Infra.Defs.typ -> ((Variables.var,
      Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list,
      Rename.Unify.MyEval.Sound.Infra.Defs.sch) prod
    
    val kdom : Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.vars
    
    val typinf :
      Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
      Rename.Unify.MyEval.Sound.Infra.Defs.env ->
      Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
      Rename.Unify.MyEval.Sound.Infra.Defs.typ -> Variables.vars ->
      Rename.Unify.MyEval.Sound.Infra.subs -> nat ->
      ((Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Rename.Unify.MyEval.Sound.Infra.subs) prod option, Variables.vars) prod
    
    val trm_depth : Rename.Unify.MyEval.Sound.Infra.Defs.trm -> nat
    
    val typinf' :
      Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
      (Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env,
      Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod option
    
    val coq_Gc : (bool, Rename2.MyEval2.Sound2.JudgInfra.Judge.gc_kind) prod
   end
 end

module Delta : 
 sig 
  val matches_arg : nat -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ
  
  val coq_type :
    Const.const -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.sch
  
  val matches_lhs :
    Variables.var list -> nat ->
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
  
  val matches_rhs : nat -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
 end

module Cstr2 : 
 sig 
  val unique : Cstr.cstr_impl -> Variables.var list
  
  val lub : Cstr.cstr_impl -> Cstr.cstr_impl -> Cstr.cstr_impl
  
  val valid : Cstr.cstr_impl -> sumbool
 end

module Infer2 : 
 sig 
  module Rename2 : 
   sig 
    module MyEval2 : 
     sig 
      type clos =
        | Coq_clos_abs of Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
           * clos list
        | Coq_clos_const of Const.const * clos list
      
      val clos_rect :
        (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1)
        -> (Const.const -> clos list -> 'a1) -> clos -> 'a1
      
      val clos_rec :
        (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list -> 'a1)
        -> (Const.const -> clos list -> 'a1) -> clos -> 'a1
      
      val clos2trm : clos -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
      
      val delta_red : Const.const -> clos list -> clos
      
      type frame = { frm_benv : clos list; frm_app : 
                     clos list;
                     frm_trm : Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm }
      
      val frame_rect :
        (clos list -> clos list ->
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> 'a1) -> frame ->
        'a1
      
      val frame_rec :
        (clos list -> clos list ->
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> 'a1) -> frame ->
        'a1
      
      val frm_benv : frame -> clos list
      
      val frm_app : frame -> clos list
      
      val frm_trm : frame -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
      
      val is_bvar : Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> bool
      
      val app_trm :
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
      
      val app2trm :
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos list ->
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
      
      val stack2trm :
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> frame list ->
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
      
      type eval_res =
        | Result of clos
        | Inter of frame list
      
      val eval_res_rect :
        (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val eval_res_rec :
        (clos -> 'a1) -> (frame list -> 'a1) -> eval_res -> 'a1
      
      val res2trm :
        eval_res -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm
      
      val clos_def : clos
      
      val trm2clos :
        clos list -> clos Env.env ->
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> clos
      
      val trm2app :
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
        (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm,
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm) prod option
      
      val eval :
        clos Env.env -> nat -> clos list -> clos list ->
        Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> frame list ->
        eval_res
      
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
      
      val gc : (bool, Sound2.JudgInfra.Judge.gc_kind) prod
      
      module Mk3 : 
       functor (SH:Sound2.SndHypIntf) ->
       sig 
        module Sound3 : 
         sig 
          
         end
        
        val is_abs : Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> bool
       end
     end
    
    val typ_generalize :
      Variables.var list -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ
    
    val sch_generalize :
      Variables.var list -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind list ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.sch
    
    val list_fst : ('a1, 'a2) prod list -> 'a1 list
   end
  
  module Body : 
   sig 
    val compose :
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
      Infer.Rename.Unify.MyEval.Sound.Infra.subs
    
    val unify_kind_rel :
      (Variables.var, Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod
      list -> (Variables.var, Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ)
      prod list -> Variables.var list ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
      ((Variables.var, Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod
      list, (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod
    
    val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env
    
    val unify_kinds :
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind,
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod option
    
    val get_kind :
      Variables.var -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind
      Env.env -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind
    
    val unify_vars :
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.var ->
      Variables.var -> ((Variables.var,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod list,
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list) prod option
    
    val unify_nv :
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Infer.Rename.Unify.MyEval.Sound.Infra.subs) prod option) ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
      Variables.VarSet.S.elt ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Infer.Rename.Unify.MyEval.Sound.Infra.subs) prod option
    
    val unify0 :
      ((Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Infer.Rename.Unify.MyEval.Sound.Infra.subs) prod option) -> nat ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Infer.Rename.Unify.MyEval.Sound.Infra.subs) prod option
    
    val accum : ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
    
    val all_types :
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ list
    
    val typ_size : Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ -> nat
    
    val pairs_size :
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list -> nat
    
    val unify :
      nat -> (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
      Infer.Rename.Unify.MyEval.Sound.Infra.subs) prod option
    
    val id : Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env
    
    val all_fv :
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
      Variables.vars
    
    val really_all_fv :
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list ->
      Variables.VarSet.S.t
    
    val size_pairs :
      Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
      (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ,
      Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod list -> nat
   end
  
  val unify :
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
    Infer.Rename.Unify.MyEval.Sound.Infra.subs ->
    (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
    Infer.Rename.Unify.MyEval.Sound.Infra.subs) prod option
  
  val fvs :
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ Env.env ->
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env ->
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.sch Env.env ->
    Variables.VarSet.S.t
  
  val close_fvars :
    nat -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.vars
    -> Variables.vars -> Variables.vars
  
  val close_fvk :
    (Variables.var, Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod
    list -> Variables.vars -> Variables.vars
  
  val split_env :
    Variables.vars -> 'a1 Env.env -> ('a1 Env.env, 'a1 Env.env) prod
  
  val vars_subst :
    Infer.Rename.Unify.MyEval.Sound.Infra.subs -> Variables.VarSet.S.t ->
    Variables.VarSet.S.t
  
  val typinf_generalize :
    (Variables.var, Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod
    list -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.sch Env.env ->
    Variables.vars -> Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ ->
    ((Variables.var, Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind) prod
    list, Infer.Rename.Unify.MyEval.Sound.Infra.Defs.sch) prod
  
  val kdom :
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv -> Variables.vars
  
  val typinf :
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv ->
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.env ->
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ -> Variables.vars ->
    Infer.Rename.Unify.MyEval.Sound.Infra.subs -> nat ->
    ((Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kenv,
    Infer.Rename.Unify.MyEval.Sound.Infra.subs) prod option, Variables.vars)
    prod
  
  val trm_depth : Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm -> nat
  
  val typinf' :
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.trm ->
    (Infer.Rename.Unify.MyEval.Sound.Infra.Defs.kind Env.env,
    Infer.Rename.Unify.MyEval.Sound.Infra.Defs.typ) prod option
  
  val coq_Gc : (bool, Rename2.MyEval2.Sound2.JudgInfra.Judge.gc_kind) prod
 end

