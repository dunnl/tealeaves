From Tealeaves Require Export
  Classes.Functor
  Data.Strength
  Functors.Identity
  Functors.Compose.
From Tealeaves Require Import
  Classes.Kleisli.Monad.

Export Kleisli.Monad (Return, ret).

Import Functor.Notations.

#[local] Generalizable Variables W T A.

(** * Monads *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section monad_operations.

  Context
    (T : Type -> Type).

  Class Join := join : T ∘ T ⇒ T.

End monad_operations.

(** ** Monads *)
(******************************************************************************)
Section monad_class.

  Context
    (T : Type -> Type)
   `{Fmap T} `{Return T} `{Join T}.

  Class Monad :=
    { mon_functor :> Functor T;
      mon_ret_natural :> Natural (@ret T _);
      mon_join_natural :> Natural (join T);
      mon_join_ret : (* left unit law *)
      `(join T A ∘ ret T (A := T A) = @id (T A));
      mon_join_fmap_ret : (* right unit law *)
      `(join T A ∘ fmap T (ret T (A := A)) = @id (T A));
      mon_join_join : (* associativity *)
      `(join T A ∘ join T (T A) =
          join T A ∘ fmap T (join T _));
    }.

End monad_class.

#[global] Arguments join _%function_scope {Join} {A}%type_scope.
#[global] Arguments ret _%function_scope {Return} {A}%type_scope.

(** * Monad homomorphisms *)
(******************************************************************************)
Section monad_homomorphism.

  Context
    (T : Type -> Type)
    (U : Type -> Type)
    `{Monad T}
    `{Monad U}.

  Class Monad_Hom (ϕ : T ⇒ U) :=
    { mhom_domain : Monad T;
      mhom_codomain : Monad U;
      mhom_natural : Natural ϕ;
      mhom_ret :
        `(ϕ A ∘ ret T = ret U);
      mhom_join :
        `(ϕ A ∘ join T = join U ∘ ϕ (U A) ∘ fmap T (ϕ A));
    }.

End monad_homomorphism.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'μ'" := (join) : tealeaves_scope.
  Notation "'η'" := (ret) : tealeaves_scope.
End Notations.

(** * The identity monad *)
(******************************************************************************)
#[export] Instance Return_I : Return (fun A => A) := (fun A (a : A) => a).

#[export] Instance Join_I : Join (fun A => A) := (fun A (a : A) => a).

#[export, program] Instance Monad_I : Monad (fun A => A).

Solve All Obligations with
  (constructor; try typeclasses eauto; intros; now ext t).

(** * Miscellaneous properties *)
(******************************************************************************)
Section tensor_laws.

  Context
    `{Monad T}
    {W : Type}.

  Theorem strength_return  {A B} (a : A) (b : B) :
    strength T (b, ret T a) = ret T (b, a).
  Proof.
    unfold strength. compose near a on left.
    change (@compose ?B) with (@compose ((fun A => A) B)).
    now rewrite natural.
  Qed.

End tensor_laws.
