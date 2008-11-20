Require Import Metatheory ML_SP_Domain.
Import Infer2.
Import Infer.Unify.Sound.Infra.
Import Defs.

Definition v  :=  Variables.var_default.
Definition min_vars := S.add v S.empty.
Definition typinf' trm :=
  match
    typinf Env.empty Env.empty trm (typ_fvar v)
      min_vars Env.empty (S (trm_depth trm))
  with (None, _) => None
  | (Some (kenv, subs), _) =>
    Some (Env.map (kind_subst subs) kenv, Env.get v subs)
  end.

Extraction "typinf" typinf'.