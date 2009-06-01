set -e
makeit() { for i in "$@"; do echo coqc "$i".v ; coqc "$i".v ; done; }
makeit Lib_Tactic Lib_ListFacts Lib_ListFactsMore
makeit Lib_MyFSetInterface Lib_FinSet Lib_FinSetImpl
makeit Metatheory_Var Metatheory_Fresh Metatheory_Env
makeit Metatheory_SP Metatheory
makeit ML_SP_Definitions ML_SP_Infrastructure
makeit ML_SP_Soundness ML_SP_Eval
makeit Cardinal ML_SP_Unify ML_SP_Rename ML_SP_Inference
makeit ML_SP_Domain
