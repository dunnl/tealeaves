(** This file implements "functors decorated by type <<E>>" and
    proves their basic properties.  *)

From Tealeaves Require Export
  Classes.Algebraic.Comonad
  Functors.Environment.

Import Product.Notations.
Import Functor.Notations.

#[local] Generalizable Variables E A.

(** * Decorated functors *)
(******************************************************************************)
Section DecoratedFunctor_operations.

  Context
    (E : Type)
    (F : Type -> Type).

  Class Decorate :=
    dec : F ⇒ F ○ (E ×).

End DecoratedFunctor_operations.

Section DecoratedFunctor.

  Context
    (E : Type)
    (F : Type -> Type)
    `{Fmap F}
    `{Decorate E F}.

  Class DecoratedFunctor :=
    { dfun_functor :> Functor F;
      dfun_dec_natural :> Natural (@dec E F _);
      dfun_dec_dec : forall (A : Type),
        dec E F (E * A) ∘ dec E F A = fmap F (cojoin (prod E)) ∘ dec E F A;
      dfun_dec_extract : forall (A : Type),
        fmap F (extract (E ×)) ∘ dec E F A = @id (F A);
    }.

End DecoratedFunctor.

(* Mark <<E>> and the type argument implicit *)
Arguments dec {E}%type_scope _%function_scope {Decorate} {A}%type_scope _.

(** ** Decoration-preserving natural transformations *)
(******************************************************************************)
Class DecoratePreservingTransformation
  {F G : Type -> Type}
  `{! Fmap F} `{Decorate E F}
  `{! Fmap G} `{Decorate E G}
  (ϕ : F ⇒ G) :=
  { dectrans_commute : `(ϕ (E * A) ∘ dec F = dec G ∘ ϕ A);
    dectrans_natural : Natural ϕ;
  }.
