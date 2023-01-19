From Tealeaves Require Import
  Classes.Algebraic.Traversable.Monad
  Classes.Algebraic.Setlike.Functor
  Classes.Kleisli.Traversable.Monad
  Theory.Algebraic.Traversable.Functor.Properties
  Theory.Algebraic.Traversable.Functor.ToKleisli
  Theory.Algebraic.Monad.ToKleisli.

#[local] Generalizable Variables G T A B.

Import Setlike.Functor.Notations.
Import Kleisli.Traversable.Monad.Notations.

(** * Algebraic traversable monads to Kleisli traversable monads *)
(******************************************************************************)
Import Monad.ToKleisli.Operation.
Import Functor.ToKleisli.Operation.

(** ** Operations *)
(******************************************************************************)
Module Operation.
  Section with_algebraic.

    Context
      (T : Type -> Type)
      `{Fmap T} `{Join T} `{Dist T}.

    #[export] Instance Bindt_alg : Bindt T T :=
      fun (G : Type -> Type) (A B : Type) _ _ _ (f : A -> G (T B)) =>
        fmap G (join T) ∘ dist T G ∘ fmap T f.

  End with_algebraic.
End Operation.

(** ** Kleisli laws *)
(******************************************************************************)
Module Instance.

  Import Operation.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Algebraic.Traversable.Monad.TraversableMonad T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma ktm_bindt1_T :
      forall (A : Type), bindt T (fun A => A) (ret T) = @id (T A).
    Proof.
      intros. unfold bindt. unfold_ops @Bindt_alg.
      unfold_ops @Fmap_I. rewrite (dist_unit T).
      change (?g ∘ id ∘ ?f) with (g ∘ f).
      now rewrite (mon_join_fmap_ret T).
    Qed.


    (** *** Composition law *)
    (******************************************************************************)
    Lemma ktm_bindt2_T : forall
        (A B C : Type)
        (G1 : Type -> Type) `{Fmap G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
        (G2 : Type -> Type) `{Fmap G2} `{Pure G2} `{Mult G2} `{! Applicative G2}
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        fmap G1 (bindt T G2 g) ∘ bindt T G1 f =
          bindt T (G1 ∘ G2) (g ⋆tm f).
    Proof.
      intros. unfold bindt at 1 2 3.
      unfold_ops @Bindt_alg.
      reassociate -> on right. repeat reassociate <-.
      rewrite (fun_fmap_fmap G1).
      reassociate -> near (join T). rewrite (natural (ϕ := @join T _)).
      reassociate <-. reassociate -> near (join T).
      rewrite (trvmon_join T). reassociate <-.
      rewrite (fun_fmap_fmap G2). rewrite (mon_join_join T).
      rewrite <- (fun_fmap_fmap G1).
      reassociate -> near (dist T G1).
      change (fmap G1 (fmap (T ∘ T) g) ∘ dist T G1)
        with (fmap (G1 ∘ T) (fmap T g) ∘ dist T G1).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      #[local] Unset Keyed Unification.
      reassociate <-. rewrite <- (fun_fmap_fmap G1).
      reassociate -> near (dist T G1).
      unfold_ops @Dist_compose.
      rewrite <- (fun_fmap_fmap G1).
      reassociate <-. reassociate -> near (dist T G1).
      change (fmap G1 (fmap T (dist (A:=?A) T G2)))
        with (fmap (G1 ∘ T) (dist (A:=A) T G2)).
      reassociate -> near (dist T G1).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      #[local] Unset Keyed Unification.
      repeat reassociate <-. reassociate -> near (dist T G1).
      rewrite <- (dist_linear T).
      change (fmap G1 (fmap G2 ?f)) with (fmap (G1 ∘ G2) f).
      rewrite <- (fun_fmap_fmap (G1 ∘ G2)).
      reassociate -> near (dist T (G1 ∘ G2)).
      change (fmap (G1 ∘ G2) (fmap T ?f)) with (fmap ((G1 ∘ G2) ∘ T) f).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ (G1 ∘ G2) _ _ _)).
      reassociate <-. reassociate -> near (fmap T f).
      rewrite (fun_fmap_fmap T).
      reassociate -> near (fmap T (fmap G1 (fmap T g) ∘ f)).
      rewrite (fun_fmap_fmap T).
      reassociate ->.
      reassociate ->.
      rewrite (fun_fmap_fmap T).
      reassociate <-.
      reassociate <-.
      rewrite (fun_fmap_fmap G1).
      reassociate <-.
      rewrite (fun_fmap_fmap G1).
      #[local] Unset Keyed Unification.
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma ktm_bindt0_T : forall
        (A B: Type)
        (G1 : Type -> Type) `{Fmap G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
        (f : A -> G1 (T B)),
        bindt T G1 f ∘ ret T = f.
    Proof.
      intros. unfold_ops @Bindt_alg.
      reassociate -> on left.
      rewrite (natural (Natural := mon_ret_natural T)).
      unfold_ops @Fmap_I.
      reassociate <-; reassociate -> near (ret T).
      rewrite (trvmon_ret T).
      rewrite (fun_fmap_fmap G1).
      rewrite (mon_join_ret T).
      now rewrite (fun_fmap_id G1).
    Qed.

    (** *** Morphism law *)
    (******************************************************************************)
    Lemma ktm_morph_T : forall
        (G1 G2 : Type -> Type) `{Fmap G1} `{Pure G1} `{Mult G1}
        `{Fmap G2} `{Pure G2} `{Mult G2}
        (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : A -> G1 (T B)), ϕ (T B) ∘ bindt T G1 f = bindt T G2 (ϕ (T B) ∘ f).
    Proof.
      introv morph.
      inversion morph. intros.
      unfold_ops @Bindt_alg.
      do 2 reassociate <- on left.
      unfold compose. ext a.
      rewrite (appmor_natural _ (T B) (join T)).
      unfold compose. compose near (fmap T f a).
      rewrite <- (dist_morph T).
      unfold compose. compose near a on left.
      rewrite (fun_fmap_fmap T).
      reflexivity.
    Qed.

    (** *** Purity law *)
    (******************************************************************************)
    Theorem bindt_purity_T
      `{Applicative G1} `{Applicative G2} : forall `(f : A -> G1 (T B)),
        bindt T (G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ bindt T G1 f.
    Proof.
      intros. unfold_ops @Bindt_alg.
      reassociate -> on left.
      rewrite (fmap_purity_2 T (G2 := G2) f).
      do 2 reassociate <- on left.
      do 2 reassociate <- on right.
      do 2 fequal.
      unfold_ops @Fmap_compose.
      ext t; unfold compose.
      now rewrite (app_pure_natural G2).
    Qed.

    #[export] Instance TravMon_ToKleisli: Kleisli.Traversable.Monad.Monad T :=
      {| ktm_bindt0 := @ktm_bindt0_T;
        ktm_bindt1 := @ktm_bindt1_T;
        ktm_bindt2 := @ktm_bindt2_T;
        ktm_morph := @ktm_morph_T;
      |}.

  End with_monad.

End Instance.
