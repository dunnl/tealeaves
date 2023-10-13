From Tealeaves Require Import
  Classes.Categorical.TraversableMonad
  Classes.Kleisli.TraversableMonad
  Adapters.CategoricalToKleisli.TraversableFunctor.

Import Kleisli.TraversableMonad.Notations.

#[local] Generalizable Variables G ϕ.

#[local] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bindt (U T)%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(** * Traversable monads to Kleisli traversable monads *)
(******************************************************************************)
Module ToKleisli.

  (** ** Operation *)
  (******************************************************************************)
  #[export] Instance Bindt_distjoin
    (T : Type -> Type)
    `{Map T} `{Join T} `{ApplicativeDist T} : Bindt T T :=
  fun (G : Type -> Type) _ _ _ (A B : Type) (f : A -> G (T B)) =>
    map G (join T) ∘ dist T G ∘ map T f.


  Import CategoricalToKleisli.TraversableFunctor.ToKleisli.

  (** ** Laws *)
  (******************************************************************************)
  Section with_monad.

    Context
      (T : Type -> Type)
      `{Classes.Categorical.TraversableMonad.TraversableMonad T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma ktm_bindt1_T :
      forall (A : Type), bindt T T (fun A => A) A A (ret T A) = @id (T A).
    Proof.
      intros. unfold bindt. unfold_ops @Bindt_distjoin.
      unfold_ops @Map_I. rewrite (dist_unit (F := T)).
      change (?g ∘ id ∘ ?f) with (g ∘ f).
      now rewrite (mon_join_map_ret (T := T)).
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma ktm_bindt2_T : forall
        (G1 G2 : Type -> Type) `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
        `{Map G2} `{Pure G2} `{Mult G2} `{! Applicative G2}
        (A B C : Type)
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        map G1 (bindt T T G2 B C g) ∘ bindt T T G1 A B f =
          bindt T T (G1 ∘ G2) A C (g ⋆3 f).
    Proof.
      intros. unfold bindt at 1 2 3.
      unfold_ops @Bindt_distjoin.
      reassociate -> on right. repeat reassociate <-.
      rewrite (fun_map_map (F := G1)).
      reassociate -> near (join T). rewrite (natural (ϕ := @join T _)).
      reassociate <-. reassociate -> near (join T).
      rewrite (trvmon_join (T := T)).
      reassociate <-.
      reassociate <-.
      rewrite (fun_map_map (F := G2)).
      rewrite (mon_join_join (T := T)).
      rewrite <- (fun_map_map (F := G1)).
      reassociate -> near (dist T G1).
      change (map G1 (map (T ∘ T) g) ∘ dist T G1)
        with (map (G1 ∘ T) (map T g) ∘ dist T G1).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      #[local] Unset Keyed Unification.
      reassociate <-. rewrite <- (fun_map_map (F := G1)).
      reassociate -> near (dist T G1).
      (* unfold_ops @Dist_compose. *)
      rewrite <- (fun_map_map (F := G1)).
      reassociate <-. reassociate -> near (dist T G1).
      change (map G1 (map T (dist (A:=?A) T G2)))
        with (map (G1 ∘ T) (dist (A:=A) T G2)).
      (* reassociate -> near (dist T G1). *)
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      #[local] Unset Keyed Unification.
      repeat reassociate <-. reassociate -> near (dist T G1).
      rewrite <- (dist_linear (F := T)).
      change (map G1 (map G2 ?f)) with (map (G1 ∘ G2) f).
      rewrite <- (fun_map_map (F := G1 ∘ G2)).
      reassociate -> near (dist T (G1 ∘ G2)).
      change (map (G1 ∘ G2) (map T ?f)) with (map ((G1 ∘ G2) ∘ T) f).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ (G1 ∘ G2) _ _ _)).
      reassociate <-. reassociate -> near (map T f).
      rewrite (fun_map_map (F := T)).
      reassociate -> near (map T (map G1 (map T g) ∘ f)).
      rewrite (fun_map_map (F := T)).
      reassociate ->.
      reassociate ->.
      rewrite (fun_map_map (F := T)).
      reassociate <-.
      reassociate <-.
      rewrite (fun_map_map (F := G1)).
      reassociate <-.
      rewrite (fun_map_map (F := G1)).
      #[local] Unset Keyed Unification.
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma ktm_bindt0_T : forall
        (G1 : Type -> Type) `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
        (A B: Type) (f : A -> G1 (T B)),
        bindt T T G1 A B f ∘ ret T A = f.
    Proof.
      intros. unfold_ops @Bindt_distjoin.
      reassociate -> on left.
      rewrite (natural (Natural := mon_ret_natural)).
      unfold_ops @Map_I.
      reassociate <-; reassociate -> near (ret T (G1 (T B))).
      rewrite (trvmon_ret (T := T)).
      rewrite (fun_map_map (F := G1)).
      rewrite (mon_join_ret (T := T)).
      now rewrite (fun_map_id (F := G1)).
    Qed.

    (** *** Morphism law *)
    (******************************************************************************)
    Lemma ktm_morph_T : forall
        (G1 G2 : Type -> Type) `{Map G1} `{Pure G1} `{Mult G1}
        `{Map G2} `{Pure G2} `{Mult G2}
        (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : A -> G1 (T B)), ϕ (T B) ∘ bindt T T G1 A B f = bindt T T G2 A B (ϕ (T B) ∘ f).
    Proof.
      introv morph.
      inversion morph. intros.
      unfold_ops @Bindt_distjoin.
      do 2 reassociate <- on left.
      unfold compose. ext a.
      rewrite (appmor_natural _ (T B) (join T)).
      unfold compose. compose near (map T f a).
      rewrite <- (dist_morph (F := T)).
      unfold compose. compose near a on left.
      rewrite (fun_map_map (F := T)).
      reflexivity.
    Qed.

    (** *** Purity law *)
    (******************************************************************************)
    Theorem bindt_purity_T
      `{Applicative G1} `{Applicative G2} : forall (A B : Type) (f : A -> G1 (T B)),
        bindt T T (G2 ∘ G1) A B (pure G2 ∘ f) = pure G2 ∘ bindt T T G1 A B f.
    Proof.
      intros. unfold_ops @Bindt_distjoin.
      reassociate -> on left.
      rewrite (map_purity_2 T (G2 := G2) f).
      do 2 reassociate <- on left.
      do 2 reassociate <- on right.
      do 2 fequal.
      unfold_ops @Map_compose.
      ext t; unfold compose.
      now rewrite (app_pure_natural G2).
    Qed.

    #[export] Instance TravMon_ToKleisli: Kleisli.TraversableMonad.TraversableMonad T :=
      {| ktm_bindt0 := @ktm_bindt0_T;
        ktm_bindt1 := @ktm_bindt1_T;
        ktm_bindt2 := @ktm_bindt2_T;
        ktm_morph := @ktm_morph_T;
      |}.

  End with_monad.

End ToKleisli.
