From Tealeaves Require Import
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.TraversableFunctor.

#[local] Generalizable Variables T G ϕ.

(** * Kleisli Traversable Functors from Categorical Traversable Functors *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Traverse_Categorical
    (T: Type -> Type)
    `{Map_T: Map T}
    `{Dist_T: ApplicativeDist T}:
  Traverse T :=
  fun (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
    (A B: Type) (f: A -> G B) => dist T G ∘ map f.

  #[export] Instance Compat_Map_Traverse_Categorical
    (T: Type -> Type)
    `{Map_T: Map T}
    `{Dist_T: ApplicativeDist T}
    `{Categorical.TraversableFunctor.TraversableFunctor T}
    :
    Compat_Map_Traverse T.
  Proof.
    unfold Compat_Map_Traverse.
    unfold DerivedOperations.Map_Traverse.
    ext A B f.
    unfold traverse.
    unfold Traverse_Categorical.
    rewrite dist_unit.
    reflexivity.
  Qed.

End DerivedOperations.

(** ** Compatibility Classes *)
(**********************************************************************)
Class Compat_Traverse_Categorical
    (F: Type -> Type)
    `{Traverse_F: Traverse F}
    `{Map_F: Map F}
    `{Dist_F: ApplicativeDist F} :=
  compat_traverse_categorical:
    Traverse_F = @DerivedOperations.Traverse_Categorical F Map_F Dist_F.

#[export] Instance compat_traverse_categorical_self
    (F: Type -> Type)
    `{Map_F: Map F}
    `{Dist_F: ApplicativeDist F}:
  Compat_Traverse_Categorical F (Traverse_F := DerivedOperations.Traverse_Categorical F).
Proof.
  reflexivity.
Qed.


Lemma traverse_to_categorical {F}
    `{Traverse_F: Traverse F}
    `{Map_F: Map F}
    `{Dist_F: ApplicativeDist F}
    `{Compat: ! Compat_Traverse_Categorical F}:
  forall {G} `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G} (A B: Type) (t: F A) (f: A -> G B),
    @traverse F Traverse_F G Map_G Pure_G Mult_G A B f =dist F G ∘ map f.
Proof.
  now rewrite compat_traverse_categorical.
Qed.

(** ** Derived Laws *)
(**********************************************************************)
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

    #[export] Instance TraversableFunctor_Kleisli_Categorical:
      Classes.Kleisli.TraversableFunctor.TraversableFunctor T :=
      {| trf_traverse_id := @traverse_id;
         trf_traverse_traverse := @traverse_traverse;
         trf_traverse_morphism := @traverse_morphism;
      |}.

  End with_functor.

End DerivedInstances.
