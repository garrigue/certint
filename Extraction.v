Require Import List Metatheory ML_SP_Domain.
Import Infer2.
Import Sound3.
Import Infer.Rename.Unify.MyEval.Sound.Infra.
Import Defs.

Definition t :=
  trm_app
    (trm_cst (Const.matches (NoDup_nodup (Variables.var_of_nat 5 :: nil))))
    (trm_abs (trm_bvar O)).

(* This doesn't seem to work inside Coq (some things don't get evaluated) *)
(* Eval compute in typinf' t. *)

Definition eval' fenv t h := eval fenv h nil nil t nil.

(* Export and try to do this in ocaml *)
Extraction "typinf" typinf' eval'.
