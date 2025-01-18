From Tealeaves Require Export
  Classes.Monoid
  Classes.Kleisli.Monad
  Classes.Categorical.Applicative
  Functors.Early.Subset.

Import Monad.Notations.
Import Product.Notations.
Import Applicative.Notations.
Import Subset.Notations.

#[local] Generalizable Variables A B.

#[export] Instance Compat_Map_Bind_subset :
  `{Compat_Map_Bind (Map_U := Map_subset) subset subset} := ltac:(reflexivity).

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind {A B f} :
  Monoid_Morphism (subset A) (subset B) (bind f) :=
  {| monmor_unit := @bind_set_nil A B f;
    monmor_op := @bind_set_add A B f;
  |}.


(** * Misc properties *)
(******************************************************************************)
