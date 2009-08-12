#load"typinf.cmo";;
open Typinf;;
open Infer2;;
open Infer.Unify.MyEval.Rename.Sound.Infra.Defs;;
open Infer.Unify.MyEval;;
open Const;;
open Variables.VarSet;;

let rec int_of_nat = function O -> 0 | S x -> succ (int_of_nat x);;

let print_nat ppf n =
  match n with
  | S m when m == n -> Format.fprintf ppf "omega"
  | _ -> Format.fprintf ppf "%i" (int_of_nat n);;
let print_var ppf v = print_nat ppf (Variables.nat_of_var v);;
#install_printer print_nat;;
#install_printer print_var;;
let rec omega = S omega;; (* In ocaml we can define infinity! *)

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

let rec coqlist_of_list = function
    [] -> Nil
  | a :: l -> Cons (a, coqlist_of_list l);;

let typinf2 env trm =
  match typinf1 env trm with
  | Inl (Pair (kenv, typ)) ->
      List.map (fun (Pair(a,b)) -> a,b) (list_of_coqlist kenv), typ
  | Inr Left  -> failwith "Environment is not closed"
  | Inr Right -> failwith "Type Error";;

open Typinf.Cstr;;

let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n-1));;

let app a b = Coq_trm_app (a,b)
let apps a l = List.fold_left app a l
let abs a = Coq_trm_abs a
let var n = Variables.var_of_nat (nat_of_int n)
let bvar n = Coq_trm_bvar (nat_of_int n)
let matches l = apps
    (Coq_trm_cst (Const.Coq_matches (coqlist_of_list (List.map nat_of_int l))))
let tag n =
  app (Coq_trm_cst (Const.Coq_tag (nat_of_int n)))
let record l = apps
    (Coq_trm_cst (Const.Coq_record (coqlist_of_list (List.map nat_of_int l))))
let sub n =
  app (Coq_trm_cst (Const.Coq_sub (nat_of_int n)))
let recf = app (Coq_trm_cst Const.Coq_recf);;


(* First example: (Coq_tag A) is a function constant, which takes any value
   and returns a polymorphic variant A with this value as argument *)
(* This example is equivalent to the ocaml term [fun x -> `A0 x] *)
typinf2 Nil (abs (tag 0 (bvar 0)));;

(* Second example: (Coq_matches [A1; ..; An]) is a n+1-ary function constant
   which takes n functions and a polymorphic variant as argument, and
   (fi v) if the argument was (Ai v). *)
(* This example is equivalent to [function `A20 x -> x | `A21 x -> x] *)
let trm = matches [20; 21] [abs (bvar 0); abs (bvar 0)];;
typinf2 Nil trm;;

(* Another example, producing a recursive type *)
(* OCaml equivalent: [fun x -> match x with `A20 y -> y | `A21 y -> y] *)
let trm2 =
  abs (matches [20; 21] [abs (bvar 0); abs (bvar 0); bvar 0]) ;;
typinf2 Nil trm2;;

let trm3 = app trm2 (tag 20 (tag 21 (abs (bvar 0)))) ;;
typinf2 Nil trm3;;

let r1 = eval1 Nil trm3 (nat_of_int 10);;
let r2 = eval1 Nil trm3 (nat_of_int 20);;
let r3 = eval1 Nil trm3 omega;;

(* More advanced example: the reverse function *)
(* First define cons and nil. Since there is no unit we use a record *)
let cons x y = tag 1 (record [0;1] [x;y])
let nil = tag 0 (record [] []);;
typinf2 Nil nil;;
typinf2 Nil (cons nil nil);;

(* The rev_append function. DeBruijn indices can be tricky... *)
let rev_append = recf
    (abs
       (abs
	  (abs
	     (matches [0;1]
		[abs (bvar 1);
		 abs (apps (bvar 3)
			[sub 1 (bvar 0); cons (sub 0 (bvar 0)) (bvar 1)]);
		 bvar 1])))) ;;
typinf2 Nil rev_append;;

(* A list of tagged units *)
let mylist =
  app (abs (cons (tag 3 (bvar 0))
	      (cons (tag 4 (bvar 0)) (cons (tag 5 (bvar 0)) nil))))
    (record [] []);;
typinf2 Nil mylist;;

(* Infer types and run! *)
let rlist = apps rev_append [mylist; nil];;
let t = typinf2 Nil rlist;;
let r = eval1 Nil rlist (nat_of_int 134);;
