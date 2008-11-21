Require Import List Metatheory ML_SP_Domain.
Import Infer2.
Import Infer.Unify.Sound.Infra.
Import Defs.

Definition t :=
  trm_app
    (trm_cst (Const.matches (NoDup_nodup (Variables.var_of_nat 5 :: nil))))
    (trm_abs (trm_bvar O)).

(* This doesn't seem to work inside Coq (some things don't get evaluated) *)
(* Eval compute in typinf' t. *)

(* Export and try to do this in ocaml *)
Extraction "typinf" typinf'.