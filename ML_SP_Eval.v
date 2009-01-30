(***************************************************************************
* Principality of type inference for mini-ML with structural polymorphism  *
* Jacques Garrigue, January 2009                                           *
***************************************************************************)

Set Implicit Arguments.

Require Import List Metatheory.
Require Import ML_SP_Definitions ML_SP_Infrastructure.
Require Import ML_SP_Soundness.

Module MkEval(Cstr:CstrIntf)(Const:CstIntf).

Module Sound := MkSound(Cstr)(Const).
Import Sound.
Import Infra.
Import Defs.
Import Metatheory_Env.Env.

Module Mk2(Delta:DeltaIntf).

Inductive clos : Set :=
  | clos_nil : trm -> clos
  | clos_list : trm -> list clos -> clos.

Fixpoint close2trm (c:clos) : trm :=
  match c with
  | clos_nil t => t
  | clos_list t l =>
    fold_left (fun t' c' => trm_let (close2trm c') t')
  

Fixpoint eval (h:nat) (benv:list clos) (fenv:env clos) (app:list clos) (t:trm)
  {struct h} : clos :=
  match h with
  | 0 => (fold_left trm_app app trm,
  | S h =>
    match t with
    | trm_bvar n => eval bennth n benv trm_def
    | trm_fvar v =>
    match get v 
    

Module Sound2 := Sound.Mk2(Delta).
Import Sound2.
Import JudgInfra.
Import Judge.

Module Mk3(SH:SndHypIntf).

Module Sound3 := Sound2.Mk3(SH).
Import Sound3.

End Mk3.
End Mk2.
End MkEval.