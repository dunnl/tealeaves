From Tealeaves Require Import
  Classes.Algebraic.Applicative
  Theory.Algebraic.Monad.Properties
  Classes.Kleisli.Monad
  Theory.Algebraic.Monad.ToKleisli.

Import Product.Notations.
Import Applicative.Notations.

#[local] Generalizable Variable T.

(** * Monadic applicative functors *)
(******************************************************************************)
Section Applicative_Monad.

  Context
    `{Algebraic.Monad.Monad T}.

  Import Monad.ToKleisli.Operation.
  Import Monad.ToKleisli.Instance.

  #[global] Instance Pure_Monad : Pure T := @ret T _.

  #[global] Instance Mult_Monad : Mult T :=
    fun A B (p : T A * T B) =>
      match p with (ta, tb) =>
                   bind T (fun a => strength T (a, tb)) ta
      end.

  Theorem app_pure_natural_Monad : forall (A B : Type) (f : A -> B) (x : A),
      fmap T f (pure T x) = pure T (f x).
  Proof.
    intros. unfold_ops @Pure_Monad.
    compose near x. now rewrite (natural (ϕ := @ret T _)).
  Qed.

  Theorem app_mult_natural_Monad : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : T A) (y : T B),
      fmap T f x ⊗ fmap T g y = fmap T (map_tensor f g) (x ⊗ y).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x.
    rewrite (bind_fmap T), (fmap_bind T).
    fequal. ext c; unfold compose; cbn. compose near y.
    now rewrite 2(fun_fmap_fmap T).
  Qed.

  Theorem app_assoc_Monad : forall (A B C : Type) (x : T A) (y : T B) (z : T C),
      fmap T α ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x on left. rewrite (kmon_bind2 T).
    compose near x on left. rewrite (fmap_bind T).
    fequal. ext a; unfold compose; cbn.
    compose near y on right. rewrite (fmap_bind T).
    unfold compose; cbn. compose near z on right.
    unfold kcompose. unfold compose; cbn.
    compose near y on left.
    rewrite (bind_fmap T). compose near y on left.
    rewrite (fmap_bind T). fequal. ext b. unfold compose; cbn.
    compose near z. now do 2 (rewrite (fun_fmap_fmap T)).
  Qed.

  Theorem app_unital_l_Monad : forall (A : Type) (x : T A),
      fmap T left_unitor (pure T tt ⊗ x) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near tt. rewrite (mon_bind_comp_ret T).
    unfold strength. compose near x.
    rewrite (fun_fmap_fmap T). change (left_unitor ∘ pair tt) with (@id A).
    now rewrite (fun_fmap_id T).
  Qed.

  Theorem app_unital_r_Monad : forall (A : Type) (x : T A),
      fmap T right_unitor (x ⊗ pure T tt) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near x. rewrite (fmap_bind T).
    replace (fmap T right_unitor ∘ (fun a : A => strength T (a, ret T tt)))
      with (ret T (A := A)).
    now rewrite (mon_bind_id T).
    ext a; unfold compose; cbn. compose near (ret T tt).
    rewrite (fun_fmap_fmap T). compose near tt.
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
