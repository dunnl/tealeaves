From Tealeaves Require Import
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.TraversableFunctor.

#[local] Generalizable Variables T G ϕ.

(** * Kleisli Traversable Functors from Categorical Traversable Functors *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Traverse_Categorical
    (T: Type -> Type)
    `{Map_T: Map T}
    `{Dist_T: ApplicativeDist T}:
  Traverse T :=
  fun (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
    (A B: Type) (f: A -> G B) => dist T G ∘ map f.

End DerivedOperations.

(** ** Derived Laws *)
(******************************************************************************)
Module DerivedInstances.

  (* Alectryon doesn't like this
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
   *)
  Import DerivedOperations.

  Section with_functor.

    Context
      `{Categorical.TraversableFunctor.TraversableFunctor T}.

    Theorem traverse_id: forall (A: Type),
        traverse (G := fun A => A) id = @id (T A).
    Proof.
      intros. unfold traverse. unfold_ops @Traverse_Categorical. ext t.
      rewrite (dist_unit (F := T)).
      rewrite (fun_map_id (F := T)).
      reflexivity.
    Qed.

    Theorem traverse_id_purity: forall `{Applicative G} (A: Type),
        traverse (pure (F := G)) = @pure G _ (T A).
    Proof.
      intros. unfold traverse.
      unfold_ops @Traverse_Categorical.
      ext t. rewrite map_purity_1.
      reflexivity.
    Qed.

    Lemma traverse_traverse `{Applicative G1} `{Applicative G2}:
      forall (A B C: Type) (g: B -> G2 C) (f: A -> G1 B),
        map (F := G1) (traverse (G := G2) g) ∘ traverse (G := G1) f =
          traverse (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      introv. unfold traverse.
      unfold_ops @Traverse_Categorical.
      rewrite (dist_linear (F := T)).
      repeat reassociate <-.
      rewrite <- (fun_map_map (F := T)).
      repeat reassociate <-.
      reassociate -> near (map (map g)).
      change (map (map g)) with (map (F := T ∘ G1) g).
      rewrite <- (natural (ϕ := @dist T _ G1 _ _ _)).
      unfold_ops @Map_compose.
      reassociate <-.
      unfold_compose_in_compose.
      now rewrite (fun_map_map (F := G1)).
    Qed.

    Lemma traverse_morphism `{morph: ApplicativeMorphism G1 G2 ϕ}:
      forall (A B: Type) (f: A -> G1 B),
        ϕ (T B) ∘ traverse f = traverse (ϕ B ∘ f).
    Proof.
      intros. unfold traverse.
      unfold_ops @Traverse_Categorical.
      reassociate <-.
      rewrite <- (dist_morph (F := T)).
      reassociate ->.
      now rewrite (fun_map_map (F := T)).
    Qed.

    #[export] Instance: Classes.Kleisli.TraversableFunctor.TraversableFunctor T :=
      {| trf_traverse_id := @traverse_id;
        trf_traverse_traverse := @traverse_traverse;
        trf_traverse_morphism := @traverse_morphism;
      |}.

  End with_functor.

End DerivedInstances.
