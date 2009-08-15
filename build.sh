set -e
wait="$1"
makeit() {
 for i in "$@"; do
   if test "$wait" = "$i"; then wait=""; fi
   if test -z "$wait"; then echo coqc "$i" ; coqc "$i" ; fi
 done; }
makeit Lib_Tactic Lib_ListFacts Lib_ListFactsMore
makeit Lib_MyFSetInterface Lib_FinSet Lib_FinSetImpl
makeit Metatheory_Var Metatheory_Fresh Metatheory_Env
makeit Metatheory_SP Metatheory
makeit ML_SP_Definitions ML_SP_Infrastructure
makeit ML_SP_Soundness ML_SP_Rename ML_SP_Eval
makeit Cardinal ML_SP_Unify_wf ML_SP_Inference_wf
makeit ML_SP_Domain
