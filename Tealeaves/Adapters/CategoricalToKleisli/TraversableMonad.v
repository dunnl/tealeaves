From Tealeaves Require Import
  Classes.Categorical.TraversableMonad
  Classes.Kleisli.TraversableMonad
  Adapters.CategoricalToKleisli.TraversableFunctor.

Import Kleisli.TraversableMonad.Notations.

#[local] Generalizable Variables T G ϕ.

(** * Kleisli Traversable Monads from Categorical Traversable Monads *)
(******************************************************************************)

(** ** Operation *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Bindt_Categorical
    (T: Type -> Type)
    `{Map_T: Map T} `{Join_T: Join T}
    `{Dist_T: ApplicativeDist T}
 : Bindt T T | 1000
  := fun (G: Type -> Type) _ _ _ (A B: Type)
       (f: A -> G (T B)) =>
       map (F := G) join ∘ dist T G ∘ map (F := T) f.

End DerivedOperations.

(** ** Derived Laws *)
(******************************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Section with_monad.

    Context
      `{Categorical.TraversableMonad.TraversableMonad T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma ktm_bindt1_T :
      forall (A: Type), bindt (G := fun A => A) (ret (T := T)) = @id (T A).
    Proof.
      intros. unfold bindt. unfold_ops @Bindt_Categorical.
      unfold_ops @Map_I. rewrite (dist_unit (F := T)).
      change (?g ∘ id ∘ ?f) with (g ∘ f).
      now rewrite (mon_join_map_ret (T := T)).
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma ktm_bindt2_T: forall
        `{Applicative G1} `{Applicative G2}
        (A B C: Type)
        (g: B -> G2 (T C)) (f: A -> G1 (T B)),
        map (bindt g) ∘ bindt f = bindt (G := G1 ∘ G2) (g ⋆6 f).
    Proof.
      intros. unfold bindt at 1 2 3.
      unfold_ops @Bindt_Categorical.
      reassociate -> on right. repeat reassociate <-.
      rewrite (fun_map_map (F := G1)).
      reassociate -> near join. rewrite (natural (ϕ := @join T _)).
      reassociate <-. reassociate -> near join.
      rewrite (trvmon_join (T := T)).
      reassociate <-.
      reassociate <-.
      rewrite (fun_map_map (F := G2)).
      rewrite (mon_join_join (T := T)).
      rewrite <- (fun_map_map (F := G1)).
      reassociate -> near (dist T G1).
      change (map (map (F := T ∘ T) g) ∘ dist T G1)
        with (map (F := G1 ∘ T) (map (F := T) g) ∘ dist T G1).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      #[local] Unset Keyed Unification.
      reassociate <-. rewrite <- (fun_map_map (F := G1)).
      reassociate -> near (dist T G1).
      (* unfold_ops @Dist_compose. *)
      rewrite <- (fun_map_map (F := G1)).
      reassociate <-. reassociate -> near (dist T G1).
      change (map (F := G1) (map (dist (A:=?A) T G2)))
        with (map (F := G1 ∘ T) (dist (A:=A) T G2)).
      (* reassociate -> near (dist T G1). *)
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      #[local] Unset Keyed Unification.
      repeat reassociate <-. reassociate -> near (dist T G1).
      rewrite <- (dist_linear (F := T)).
      change (map (F := G1) (map (F := G2) ?f)) with (map (F := G1 ∘ G2) f).
      rewrite <- (fun_map_map (F := G1 ∘ G2)).
      reassociate -> near (dist T (G1 ∘ G2)).
      change (map (F := G1 ∘ G2) (map (F := T) ?f)) with (map (F :=(G1 ∘ G2) ∘ T) f).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ (G1 ∘ G2) _ _ _)).
      reassociate <-. reassociate -> near (map f).
      rewrite (fun_map_map (F := T)).
      reassociate -> near (map (map (map g) ∘ f)).
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
    Lemma ktm_bindt0_T: forall
        (G1: Type -> Type) `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
        (A B: Type) (f: A -> G1 (T B)),
        bindt f ∘ ret = f.
    Proof.
      intros. unfold_ops @Bindt_Categorical.
      reassociate -> on left.
      rewrite (natural (Natural := Monad.mon_ret_natural)).
      unfold_ops @Map_I.
      reassociate <-; reassociate -> near ret.
      rewrite (trvmon_ret (T := T)).
      rewrite (fun_map_map (F := G1)).
      rewrite (mon_join_ret (T := T)).
      rewrite (fun_map_id (F := G1)).
      reflexivity.
    Qed.

    (** *** Morphism law *)
    (******************************************************************************)
    Lemma ktm_morph_T: forall `{ApplicativeMorphism G1 G2 ϕ},
        forall (A B: Type) (f: A -> G1 (T B)), ϕ (T B) ∘ bindt f = bindt (ϕ (T B) ∘ f).
    Proof.
      introv morph. intros.
      unfold_ops @Bindt_Categorical.
      do 2 reassociate <- on left.
      unfold compose. ext a.
      rewrite (appmor_natural _ (T B) join).
      unfold compose. compose near (map f a).
      rewrite <- (dist_morph (F := T)).
      unfold compose. compose near a on left.
      rewrite (fun_map_map (F := T)).
      reflexivity.
    Qed.

    (** *** Purity law *)
    (******************************************************************************)
    Theorem bindt_purity_T
      `{Applicative G1} `{Applicative G2}: forall (A B: Type) (f: A -> G1 (T B)),
        bindt (G := G2 ∘ G1) (pure (F := G2) ∘ f) = pure (F := G2) ∘ bindt f.
    Proof.
      intros. unfold_ops @Bindt_Categorical.
      reassociate -> on left.
      rewrite (map_purity_2 (T := T) (G2 := G2) f).
      do 2 reassociate <- on left.
      do 2 reassociate <- on right.
      do 2 fequal.
      unfold_ops @Map_compose.
      ext t; unfold compose.
      now rewrite app_pure_natural.
    Qed.

    #[export] Instance TravMon_ToKleisli:
      Kleisli.TraversableMonad.TraversableRightPreModule T T :=
      {|ktm_bindt1 := @ktm_bindt1_T;
        ktm_bindt2 := @ktm_bindt2_T;
        ktm_morph := @ktm_morph_T;
      |}.

    #[export] Instance:
      Kleisli.TraversableMonad.TraversableMonad T :=
      {| ktm_bindt0 := @ktm_bindt0_T;
      |}.

  End with_monad.

End DerivedInstances.
