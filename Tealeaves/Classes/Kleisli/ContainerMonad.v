From Tealeaves Require Export
  Classes.Functor
  Classes.Categorical.ContainerFunctor
  Classes.Kleisli.Monad
  Functors.Early.Subset.

Import Subset.Notations.
Import ContainerFunctor.Notations.


(** * Typeclasses *)
(********************************************************************)
Class ContainerMonad
  (T : Type -> Type)
  `{Bind T T} `{Return T} `{ToSubset T} :=
  { contm_monad :> Monad T;
    contm_hom :> MonadHom T subset (@tosubset T _);
    contm_pointwise : forall (A B : Type) (t : T A) (f g : A -> T B),
      (forall a, a ∈ t -> f a = g a) -> bind f t = bind g t;
  }.

Class ContainerRightModule
  (T U : Type -> Type)
  `{Bind T T}
  `{Bind T U}
  `{Return T}
  `{ToSubset T}
  `{ToSubset U} :=
  { contmod_module :> RightModule T U;
    contmod_hom :> ParallelRightModuleHom T subset U subset
      (@tosubset T _)
      (@tosubset U _);
    contmod_pointwise : forall (A B : Type) (t : U A) (f g : A -> T B),
      (forall a, a ∈ t -> f a = g a) -> bind f t = bind g t;
  }.
