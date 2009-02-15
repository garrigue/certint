#load"typinf.cmo";;
open Typinf;;
open Infer2;;
open Infer.Rename.Unify.Sound.Infra.Defs;;
open Variables.VarSet;;

let rec int_of_nat = function O -> 0 | S x -> succ (int_of_nat x);;

let print_nat ppf n = Format.fprintf ppf "%i" (int_of_nat n);;
let print_var ppf v = print_nat ppf (Variables.nat_of_var v);;
#install_printer print_nat;;
#install_printer print_var;;

let rec print_list pp ppf = function
    Nil -> ()
  | Cons (a, Nil) -> pp ppf a
  | Cons (a, l) -> Format.fprintf ppf "%a;@ %a" pp a (print_list pp) l;;
let print_set ppf s =
  Format.fprintf ppf "{@[%a@]}" (print_list print_var) (S.elements s);;
#install_printer print_set;;

let rec list_of_coqlist = function
    Nil -> []
  | Cons (a, l) -> a::list_of_coqlist l;;

let typinf1 trm =
  match typinf' trm with
    Some (Pair (kenv, typ)) ->
      List.map (fun (Pair(a,b)) -> a,b) (list_of_coqlist kenv), typ
  | _ -> failwith "Type Error";;

open Typinf.Cstr;;

(* First example: (Coq_tag A) is a function constant, which takes any value
   and returns a polymorphic variant A with this value as argument *)
(* This example is equivalent to the ocaml term [fun x -> `A0 x] *)
typinf1 (Coq_trm_cst (Const.Coq_tag (Variables.var_of_nat O)));;

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n-1));;

(* Second example: (Coq_matches [A1; ..; An]) is a n+1-ary function constant
   which takes n functions and a polymorphic variant as argument, and
   (fi v) if the argument was (Ai v). *)
(* This example is equivalent to [function `A20 x -> x | `A21 x -> x] *)
let mtch f1 f2 =
  Coq_trm_app (Coq_trm_app (
    Coq_trm_cst
      (Const.Coq_matches
         (Cons (Variables.var_of_nat (nat_of_int 20),
                Cons (Variables.var_of_nat (nat_of_int 21), Nil)))),
               f1),
               f2);;
let trm = mtch (Coq_trm_abs (Coq_trm_bvar O)) (Coq_trm_abs (Coq_trm_bvar O));;
typinf1 trm;;

(* Another example, producing a recursive type *)
(* OCaml equivalent: [fun x -> match x with `A20 y -> y | `A21 y -> x] *)
let trm2 =
  Coq_trm_abs
    (Coq_trm_app
       (mtch (Coq_trm_abs (Coq_trm_bvar O)) (Coq_trm_abs (Coq_trm_bvar (S O))),
        Coq_trm_bvar O));;
typinf1 trm2;;
