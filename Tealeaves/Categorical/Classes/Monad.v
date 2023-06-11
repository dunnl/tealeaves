From Tealeaves Require Export
  Classes.Functor
  Definitions.Strength
  Functors.Identity
  Functors.Compose
  Classes.Kleisli (Return, ret).

Import Functor.Notations.

#[local] Generalizable Variables W T A.

(** * Monads *)
(******************************************************************************)
Section monad.

  Context
    (T : Type -> Type).

  Class Join := join : T ∘ T ⇒ T.

  Context
    `{Map T} `{Return T} `{Join}.

  Class Monad :=
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

End monad.

#[local] Arguments join _%function_scope {Join} A%type_scope.
#[local] Arguments ret _%function_scope {Return} A%type_scope.

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
    strength T (b, ret T A a) = ret T (B * A) (b, a).
  Proof.
    unfold strength. compose near a on left.
    change (@compose ?B) with (@compose ((fun A => A) B)).
    now rewrite natural.
  Qed.

End tensor_laws.

From Tealeaves Require Import Classes.Applicative.

(*
(** * Monadic applicative functors *)
(******************************************************************************)
Section Applicative_Monad.

  Context
    `{Monad T}.

  Import Monad.ToKleisli.
  Import Applicative.Notations.
  Import Data.Product.Notations.

  #[global] Instance Pure_Monad : Pure T := @ret T _.

  #[global] Instance Mult_Monad : Mult T :=
    fun A B (p : T A * T B) =>
      match p with (ta, tb) =>
                   bind T (fun a => strength T (a, tb)) ta
      end.

  Theorem app_pure_natural_Monad : forall (A B : Type) (f : A -> B) (x : A),
      map T f (pure T x) = pure T (f x).
  Proof.
    intros. unfold_ops @Pure_Monad.
    compose near x. now rewrite (natural (ϕ := @ret T _)).
  Qed.

  Theorem app_mult_natural_Monad : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : T A) (y : T B),
      map T f x ⊗ map T g y = map T (map_tensor f g) (x ⊗ y).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x.
    rewrite (bind_map T), (map_bind T).
    fequal. ext c; unfold compose; cbn. compose near y.
    now rewrite 2(fun_map_map T).
  Qed.

  Theorem app_assoc_Monad : forall (A B C : Type) (x : T A) (y : T B) (z : T C),
      map T α ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x on left. rewrite (kmon_bind2 T).
    compose near x on left. rewrite (map_bind T).
    fequal. ext a; unfold compose; cbn.
    compose near y on right. rewrite (map_bind T).
    unfold compose; cbn. compose near z on right.
    unfold kcompose. unfold compose; cbn.
    compose near y on left.
    rewrite (bind_map T). compose near y on left.
    rewrite (map_bind T). fequal. ext b. unfold compose; cbn.
    compose near z. now do 2 (rewrite (fun_map_map T)).
  Qed.

  Theorem app_unital_l_Monad : forall (A : Type) (x : T A),
      map T left_unitor (pure T tt ⊗ x) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near tt. rewrite (mon_bind_comp_ret T).
    unfold strength. compose near x.
    rewrite (fun_map_map T). change (left_unitor ∘ pair tt) with (@id A).
    now rewrite (fun_map_id T).
  Qed.

  Theorem app_unital_r_Monad : forall (A : Type) (x : T A),
      map T right_unitor (x ⊗ pure T tt) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near x. rewrite (map_bind T).
    replace (map T right_unitor ∘ (fun a : A => strength T (a, ret T tt)))
      with (ret T (A := A)).
    now rewrite (mon_bind_id T).
    ext a; unfold compose; cbn. compose near (ret T tt).
    rewrite (fun_map_map T). compose near tt.
    rewrite (natural (ϕ := @ret T _ )). now unfold compose; cbn.
  Qed.

  Theorem app_mult_pure_Monad : forall (A B : Type) (a : A) (b : B),
      pure T a ⊗ pure T b = pure T (a, b).
  Proof.
    intros. intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near a. rewrite (mon_bind_comp_ret T).
    now rewrite (strength_return).
  Qed.

  #[global] Instance Applicative_Monad : Applicative T :=
  { app_mult_pure := app_mult_pure_Monad;
    app_pure_natural := app_pure_natural_Monad;
    app_mult_natural := app_mult_natural_Monad;
    app_assoc := app_assoc_Monad;
    app_unital_l := app_unital_l_Monad;
    app_unital_r := app_unital_r_Monad;
  }.

End Applicative_Monad.
*)
