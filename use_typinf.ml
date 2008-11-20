#load"typinf.cmo";;
open Typinf;;
open Infer2;;
open Infer.Unify.Sound.Infra.Defs;;
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
    Some (Pair (kenv, Some typ)) ->
      List.map (fun (Pair(a,b)) -> a,b) (list_of_coqlist kenv), typ
  | _ -> failwith "Type Error";;

open Typinf.Cstr;;

typinf1 (Coq_trm_cst (Const.Coq_tag (Variables.var_of_nat O)));;

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n-1));;

let trm =
  Coq_trm_app (Coq_trm_cst
                 (Const.Coq_matches
                    (Cons (Variables.var_of_nat (nat_of_int 5), Nil))),
               Coq_trm_abs (Coq_trm_bvar O));;
(* You need to remove the call to size_pairs in typinf.ml before
   evaluating this one: pow2exp grows too fast! *)
typinf1 trm;;
