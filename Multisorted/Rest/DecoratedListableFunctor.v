From Tealeaves Require Export
     Monoid.

From Tealeaves.Multisorted Require Export
     Functors
     MSets
     Quantifiable
     MList
     Listable
     Decorated
     Properness.

(** Import notations *)
Import Monoid.Notations.
Import Multisorted.Category.Notations.
Import Multisorted.Functors.Notations.
Import Multisorted.Decorated.Notations.
Import Multisorted.Quantifiable.Notations.
Local Open Scope tealeaves_scope.
Local Open Scope tealeaves_multi_scope.

(** ** Notations module *)
(******************************************************************************)
Module Notations.

  Include Monoid.Notations.
  Include Multisorted.Category.Notations.
  Include Multisorted.Functors.Notations.
  Include Multisorted.Decorated.Notations.
  Include Multisorted.Quantifiable.Notations.

  Local Notation "x @ k ∈mr t" :=
    (tomsetr _ t (k, x)) (k at level 5, at level 50) : tealeaves_multi_scope.

End Notations.

Import Notations.

(** * Typeclasses for multisorted syntax functors *)
(** ** Syntax functors *)
(******************************************************************************)
Section syntax_functor_class.

  Context
    `{Index}
    (W : Type)
    (F : Type -> Type)
    {monoid_op : Monoid_op W}
    {monoid_unit : Monoid_unit W}
    `{! Mfmap F}
    `{Decorate (Row W) F}
    `{! Tomlist F}.

  Class SyntaxMFunctor : Type :=
    { synf_dec :> DecoratedMFunctor (Row W) F;
      synf_com :> ListableMFunctor F;
      synf_monoid : Monoid W;
    }.

End syntax_functor_class.

(** ** Syntax monads *)
(******************************************************************************)
Section syntax_monad_class.

  Context
    `{Index}
    (W : Type)
    {monoid_op : Monoid_op W}
    {monoid_unit : Monoid_unit W}
    (T : K -> Type -> Type)
    `{! Mreturn T}
    `{! forall k, Mbind (T k) T}
    `{forall k, Decorate (Row W) (T k)}
    `{! forall k, Tomlist (T k)}.

  Class SyntaxMMonad : Type :=
    { synm_dec :> DecoratedMMonad (Row W) T;
      synm_com :> ListableMMonad T;
      synm_monoid : Monoid W;
      synm_proper :> forall k, Mbind_proper (T k);
    }.

End syntax_monad_class.

(** ** Syntax modules *)
(******************************************************************************)
Section syntax_module_class.

  Context
    `{Index}
    (W : Type)
    (F : Type -> Type)
    (T : K -> Type -> Type)
    {monoid_op : Monoid_op W}
    {monoid_unit : Monoid_unit W}
    `{! Mreturn T}
    `{! forall k, Mbind (T k) T}
    `{forall k, Decorate (Row W) (T k)}
    `{! forall k, Tomlist (T k)}
    `{! Mbind F T}
    `{Decorate (Row W) F}
    `{! Tomlist F}.

  Class SyntaxModule : Type :=
    { synmod_dec :> DecoratedModule (Row W) F T;
      synmod_com :> ListableRightModule F T;
      synmod_monad :> SyntaxMMonad W T;
      synmod_proper :> Mbind_proper F;
    }.

  Existing Instance synm_monoid.

  #[global] Instance SyntaxMFunctor_module `{SyntaxModule} : SyntaxMFunctor W F.
  Proof.
    constructor; typeclasses eauto.
  Qed.

End syntax_module_class.

Section monad_to_module.

  Existing Instance synm_monoid.

  Instance SyntaxModule_Monad `{Hmon : SyntaxMMonad W T} k : SyntaxModule W (T k) T.
  Proof.
    constructor. all: try typeclasses eauto.
    - apply Decorated_Module_MMonad.
    - apply Listable_Module_MMonad.
  Qed.

End monad_to_module.
