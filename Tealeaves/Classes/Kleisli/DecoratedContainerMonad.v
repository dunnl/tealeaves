From Tealeaves Require Export
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.DecoratedContainerFunctor.

Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variables A T U W.

(** * Decorated container monads *)
(******************************************************************************)

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedContainerMonad
  (W : Type) (T : Type -> Type)
  `{Monoid_op W} `{Monoid_unit W}
  `{Bindd W T T} `{Return T}
  `{ToCtxset W T} :=
  { dconm_functor :> DecoratedMonad W T;
    decom_hom :> DecoratedMonadHom W T (ctxset W) (@toctxset W T _);
    dconm_pointwise : forall (A B : Type) (t : T A) (f g : W * A -> T B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> bindd f t = bindd g t;
  }.

Class DecoratedContainerRightModule
  (W : Type) (T U : Type -> Type)
  `{Monoid_op W} `{Monoid_unit W}
  `{Bindd W T T} `{Return T}
  `{Bindd W T U}
  `{ToCtxset W T}
  `{ToCtxset W U} :=
  { dconmod_module :> DecoratedRightModule W T U;
    dconmod_hom :> ParallelDecoratedRightModuleHom T (ctxset W) U (ctxset W)
      (@toctxset W T _)
      (@toctxset W U _);
    dconmod_pointwise : forall (A B : Type) (t : U A) (f g : W * A -> T B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> bindd f t = bindd (U := U) g t;
  }.
