From Tealeaves Require Export
  Functors.Writer.

Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W T A B C.

Definition preincr `{Monoid_op W} (w : W) `(f : W * A -> B) :=
  f ∘ incr w.

(** * The <<Bindd>> operation *)
(** A decorated monad is a decorated functor whose monad operations
    are compatible with the decorated structure. *)
(******************************************************************************)
Section operations.

  Context
    (W : Type)
    (T : Type -> Type)
    (F : Type -> Type).

  Class Bindd :=
    bindd : forall (A B : Type), (W * A -> T B) -> F A -> F B.

End operations.

(** ** Kleisli composition *)
(** This definition is such that more recently seen binders (those
    deeper in the AST, closer to the variable occurrence) are seen on
    the _left_. So @f@ gets called on @([β0, β1, ... βn], v)@
    where @βn@ is the outermost binder. *)
(******************************************************************************)
Definition kcompose_dm {A B C} `{Bindd W T T} `{Monoid_op W} :
  (W * B -> T C) ->
  (W * A -> T B) ->
  (W * A -> T C) :=
  fun g f '(w, a) => bindd W T T B C (preincr w g) (f (w, a)).

#[local] Notation "g ⋆dm f" := (kcompose_dm g f) (at level 40) : tealeaves_scope.

(** ** Decorated Monad *)
(******************************************************************************)
Section class.

  Context
    {W : Type}
    (T : Type -> Type)
    `{Return T}
    `{Bindd W T T}
    `{Monoid_op W} `{Monoid_unit W}.

  Class Monad :=
    { kmond_monoid :> Monoid W;
      kmond_bindd0 : forall `(f : W * A -> T B),
        bindd W T T A B f  ∘ ret T (A := A) = f ∘ ret ((W ×));
      kmond_bindd1 : forall (A : Type),
        bindd W T T A A (ret T ∘ extract (W ×)) = @id (T A);
      kmond_bindd2 : forall `(g : W * B -> T C) `(f : W * A -> T B),
        bindd W T T B C g ∘ bindd W T T A B f = bindd W T T A C (g ⋆dm f);
    }.

End class.

Arguments bindd {W}%type_scope {T}%function_scope (F)%function_scope
  {Bindd} {A B}%type_scope _%function_scope _.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "g ⋆dm f" := (kcompose_dm g f) (at level 40) : tealeaves_scope.

End Notations.
