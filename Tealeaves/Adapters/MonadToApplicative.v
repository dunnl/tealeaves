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

  Import Kleisli.Monad.
  Import CategoricalToKleisli.Monad.DerivedOperations.
  Import CategoricalToKleisli.Monad.DerivedInstances.

  #[global] Instance Pure_Monad : Pure T := @ret T _.

  #[global] Instance Mult_Monad : Mult T :=
    fun A B (p : T A * T B) =>
      match p with (ta, tb) =>
                   bind (fun a => strength (a, tb)) ta
      end.

  Theorem app_pure_natural_Monad : forall (A B : Type) (f : A -> B) (x : A),
      map f (pure x) = pure (f x).
  Proof.
    intros. unfold_ops @Pure_Monad.
    compose near x. now rewrite (natural (ϕ := @ret T _)).
  Qed.

  Theorem app_mult_natural_Monad : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : T A) (y : T B),
      map f x ⊗ map g y = map (map_tensor f g) (x ⊗ y).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x.
    rewrite bind_map.
    rewrite map_bind.
    fequal. ext c; unfold compose; cbn. compose near y.
    now rewrite 2(fun_map_map (F := T)).
  Qed.

  Theorem app_assoc_Monad : forall (A B C : Type) (x : T A) (y : T B) (z : T C),
      map α ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x on left.
    rewrite (kmon_bind2 (T := T)).
    compose near x on left.
    rewrite (map_bind).
    fequal. ext a; unfold compose; cbn.
    compose near y on right. rewrite (map_bind).
    unfold compose; cbn. compose near z on right.
    unfold kc. unfold compose; cbn.
    compose near y on left.
    rewrite (bind_map). compose near y on left.
    rewrite (map_bind). fequal. ext b. unfold compose; cbn.
    compose near z.
    now do 2 (rewrite (fun_map_map (F := T))).
  Qed.

  Theorem app_unital_l_Monad : forall (A : Type) (x : T A),
      map left_unitor (pure tt ⊗ x) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near tt. rewrite mon_bind_comp_ret.
    unfold strength. compose near x.
    rewrite (fun_map_map (F := T)). change (left_unitor ∘ pair tt) with (@id A).
    now rewrite (fun_map_id (F := T)).
  Qed.

  Theorem app_unital_r_Monad : forall (A : Type) (x : T A),
      map right_unitor (x ⊗ pure tt) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near x. rewrite (map_bind).
    replace (map right_unitor ∘ (fun a : A => strength (a, ret tt)))
      with (ret (T := T) (A := A)).
    now rewrite mon_bind_id.
    ext a; unfold compose; cbn. compose near (ret tt).
    rewrite (fun_map_map (F := T)). compose near tt.
    rewrite (natural (ϕ := @ret T _ )). now unfold compose; cbn.
  Qed.

  Theorem app_mult_pure_Monad : forall (A B : Type) (a : A) (b : B),
      pure a ⊗ pure b = pure (a, b).
  Proof.
    intros. intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near a. rewrite mon_bind_comp_ret.
    now rewrite strength_return.
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
