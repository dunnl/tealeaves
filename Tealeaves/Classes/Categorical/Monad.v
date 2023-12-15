From Tealeaves Require Export
  Classes.Functor
  Classes.Kleisli.Monad (Return, ret)
  Classes.Categorical.Applicative
  Functors.Identity
  Functors.Compose
  Misc.Strength.

Import Functor.Notations.
Import Product.Notations.
Import Functor.Notations.
Import Strength.Notations.

#[local] Generalizable Variables W T A.

#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

(** * Monads *)
(******************************************************************************)
Class Join (T : Type -> Type) :=
  join : T ∘ T ⇒ T.

Class Monad
  (T : Type -> Type)
  `{Map T} `{Return T} `{Join T} :=
  { mon_functor :> Functor T;
    mon_ret_natural :> Natural (@ret T _);
    mon_join_natural :> Natural (join);
    mon_join_ret : (* left unit law *)
    `(join A ∘ ret T (T A) = @id (T A));
    mon_join_map_ret : (* right unit law *)
    `(join A ∘ map T A (T A) (ret T A) = @id (T A));
    mon_join_join : (* associativity *)
    `(join A ∘ join (T A) =
        join A ∘ map T (T (T A)) (T A) (join A));
  }.

#[global] Arguments join {T}%function_scope {Join} {A}%type_scope.
#[local] Arguments join _%function_scope {Join} A%type_scope.

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
        `(ϕ A ∘ ret T A = ret U A);
      mhom_join :
        `(ϕ A ∘ join T A = join U A ∘ ϕ (U A) ∘ map T (T A) (U A) (ϕ A));
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
    strength (b, ret T A a) = ret T (B * A) (b, a).
  Proof.
    unfold strength. compose near a on left.
    change (@compose ?B) with (@compose ((fun A => A) B)).
    now rewrite natural.
  Qed.

End tensor_laws.
