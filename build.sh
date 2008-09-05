makeit() { for i in "$@"; do echo coqc "$i"; coqc "$i"; done; }
makeit Lib_Tactic.v Lib_ListFacts.v Lib_ListFactsMore.v
makeit Lib_MyFSetInterface.v Lib_FinSet.v Lib_FinSetImpl.v
makeit Metatheory_Var.v Metatheory_Fresh.v Metatheory_Env.v Metatheory.v
makeit ML_SP_Definitions.v ML_SP_Infrastructure.v ML_SP_Soundness.v ML_SP_Domain.v
