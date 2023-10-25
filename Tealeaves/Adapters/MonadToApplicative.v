From Tealeaves Require Import
  Classes.Categorical.Monad
  Classes.Categorical.Applicative
  Adapters.CategoricalToKleisli.Monad
  Misc.Product.

Import Misc.Product.Notations.

(** * Monadic applicative functors *)
(******************************************************************************)
Section Applicative_Monad.

  #[local] Generalizable Variable T.

  Import Applicative.Notations.

  Context
    `{Categorical.Monad.Monad T}.

  Import CategoricalToKleisli.Monad.ToKleisli.

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
    now rewrite 2(fun_map_map (F := T)).
  Qed.

  Theorem app_assoc_Monad : forall (A B C : Type) (x : T A) (y : T B) (z : T C),
      map T α ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x on left. rewrite (kmon_bind2 (T := T)).
    compose near x on left. rewrite (map_bind T).
    fequal. ext a; unfold compose; cbn.
    compose near y on right. rewrite (map_bind T).
    unfold compose; cbn. compose near z on right.
    unfold kc1. unfold compose; cbn.
    compose near y on left.
    rewrite (bind_map T). compose near y on left.
    rewrite (map_bind T). fequal. ext b. unfold compose; cbn.
    compose near z.
    now do 2 (rewrite (fun_map_map (F := T))).
  Qed.

  Theorem app_unital_l_Monad : forall (A : Type) (x : T A),
      map T left_unitor (pure T tt ⊗ x) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near tt. rewrite (mon_bind_comp_ret T).
    unfold strength. compose near x.
    rewrite (fun_map_map (F := T)). change (left_unitor ∘ pair tt) with (@id A).
    now rewrite (fun_map_id (F := T)).
  Qed.

  Theorem app_unital_r_Monad : forall (A : Type) (x : T A),
      map T right_unitor (x ⊗ pure T tt) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near x. rewrite (map_bind T).
    replace (map T right_unitor ∘ (fun a : A => strength T (a, ret T unit tt)))
      with (ret T A).
    now rewrite (mon_bind_id T).
    ext a; unfold compose; cbn. compose near (ret T unit tt).
    rewrite (fun_map_map (F := T)). compose near tt.
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
