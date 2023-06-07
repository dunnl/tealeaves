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

(** * Algebraic monad to Kleisli monad *)
(******************************************************************************)

Module ToKleisli.

  Export Kleisli.Monad.
  Import Kleisli.Monad.Notations.

  Generalizable All Variables.

  Section operation.

    Context
      (T : Type -> Type)
      `{Fmap T} `{Join T}.

    #[export] Instance Bind_join : Bind T T :=
      fun {A B} (f : A -> T B) => join T ∘ fmap T f.

  End operation.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Classes.Monad.Monad T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma mon_bind_id :
      `(bind T (ret T) = @id (T A)).
    Proof.
      intros. unfold_ops @Bind_join.
      now rewrite (mon_join_fmap_ret T).
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma mon_bind_bind : forall `(g : B -> T C) `(f : A -> T B),
        bind T g ∘ bind T f = bind T (g ⋆ f).
    Proof.
      introv. unfold transparent tcs.
      unfold kcompose.
      unfold_ops @Bind_join.
      rewrite <- 2(fun_fmap_fmap T).
      reassociate <- on right.
      change (fmap ?T (fmap ?T g)) with (fmap (T ∘ T) g).
      reassociate <- on right.
      rewrite <- (mon_join_join T).
      reassociate -> near (fmap (T ∘ T) g).
      now rewrite <- (natural (ϕ := @join T _)).
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma mon_bind_comp_ret : forall (A B : Type) (f : A -> T B),
        bind T f ∘ ret T = f.
    Proof.
      intros. unfold transparent tcs.
      reassociate -> on left.
      unfold_compose_in_compose; (* these rewrites are not visible *)
        change (@compose A) with (@compose ((fun A => A) A)).
      rewrite natural.
      reassociate <- on left.
      now rewrite (mon_join_ret T).
    Qed.

    #[export] Instance Kleisli_Monad : Kleisli.Monad.Monad T :=
      {| kmon_bind0 := @mon_bind_comp_ret;
        kmon_bind1 := @mon_bind_id;
        kmon_bind2 := @mon_bind_bind;
      |}.

  End with_monad.

End ToKleisli.

(** ** Derived laws *)
(******************************************************************************)
Section ToKleisli_laws.

  Context
    (T : Type -> Type)
   `{Monad T}.

  Generalizable All Variables.
  Import Kleisli.Monad.Notations.
  Import ToKleisli.

  Lemma fmap_to_bind : forall `(f : A -> B),
      fmap T f = bind T (ret T ∘ f).
  Proof.
    intros. unfold_ops @Bind_join.
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

  Corollary bind_fmap : forall `(g : B -> T C) `(f : A -> B),
      bind T g ∘ fmap T f = bind T (g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

  Corollary fmap_bind : forall `(g : B -> C) `(f : A -> T B),
      fmap T g ∘ bind T f = bind T (fmap T g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    reassociate <- on left.
    rewrite (natural). unfold_ops @Fmap_compose.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

  (** ** Left identity law *)
  Theorem kleisli_id_l : forall `(f : A -> T B),
      (@ret T _ B) ⋆ f = f.
  Proof.
    intros. unfold kcompose. now rewrite (kmon_bind1 T).
  Qed.

  (** ** Right identity law *)
  Theorem kleisli_id_r : forall `(g : B -> T C),
      g ⋆ (@ret T _ B) = g.
  Proof.
    intros. unfold kcompose. now rewrite (kmon_bind0 T).
  Qed.

  (** ** Associativity law *)
  Theorem kleisli_assoc : forall `(h : C -> T D) `(g : B -> T C) `(f : A -> T B),
      h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f.
  Proof.
    intros. unfold kcompose at 3.
    now rewrite <- (kmon_bind2 T).
  Qed.

End ToKleisli_laws.

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

From Tealeaves Require Import Classes.Applicative.

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
