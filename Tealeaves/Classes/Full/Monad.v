From Tealeaves.Classes Require Import
  Categorical.Monad
  Kleisli.Monad.

#[local] Generalizable Variables T U A B.

(** * Derived Categorical operations *)
(******************************************************************************)
Class Compat_Join_Bind
  (T : Type -> Type)
  `{return_T: Return T}
  `{map_T: Map T}
  `{bind_T: Bind T T}
  `{join_T: Join T}
  : Prop :=
  { compat_join_bind: forall (A: Type),
      @join T join_T A = @bind T T bind_T (T A) A (@id (T A));
    compat_bind_join: forall (A B: Type) (f: A -> T B),
      @bind T T bind_T A B f = @join T join_T B ∘ @map T map_T A (T B) f;
  }.

(** ** Rewriting *)
(******************************************************************************)
Lemma join_to_bind:
  `{join_T: Join T}
  `{bind_T: Bind T T}
  `{compat: !Compat_Join_Bind T T}:
  forall `(f : A -> T B),
    @join T join_T A = @bind T U bind_U A B (@ret T ret_T B ∘ f).
Proof.
  rewrite compat_map_bind.
  reflexivity.
Qed.


Class Monad (T : Type -> Type)
  `{Return_inst: Return T}
  `{Bind_inst: Bind T T}
  `{Join_inst: Join T}
  `{Map_inst: Map T}
  :=
  { fmon_cat :> Categorical.Monad.Monad T;
    fmon_kleisli :> Kleisli.Monad.Monad T;
    fmon_compat :> Compat_Join_Bind T;
  }.

From Tealeaves Require Import
  Adapters.KleisliToCategorical.Monad.

Import KleisliToCategorical.Monad.Instance.

Print Instances Map.

#[export] Instance MonadFull_Kleisli {T} `{Kleisli.Monad.Monad T}:
  Full.Monad.Monad T :=
  {| fmon_cat := CategoricalFromKleisli_Monad T;
  |}.
