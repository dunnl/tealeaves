From Tealeaves Require Import
  Classes.Categorical.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedTraversableFunctor.

Import Kleisli.DecoratedTraversableFunctor.Notations.
Import Product.Notations.

#[local] Generalizable Variables G ϕ.

(** * Kleisli Decorated Traversable Functors from Categorical Decorated Traversable Functors *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Mapdt_Categorical
    (E: Type)
    (T: Type -> Type)
    `{Map T}
    `{Decorate E T}
    `{ApplicativeDist T}:
  Mapdt E T :=
  fun (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
    (A B: Type) (f: E * A -> G B) =>
    (dist T G ∘ map f ∘ dec T: T A -> G (T B)).

End DerivedOperations.

(** ** Derived Instances *)
(**********************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Section with_functor.

    Context
      (E: Type)
      (T: Type -> Type)
      `{Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

    Theorem mapdt_id: forall (A: Type),
        mapdt (G := fun A => A) (extract (W := (E ×))) = @id (T A).
    Proof.
      introv. unfold_ops @Mapdt_Categorical.
      reassociate -> on left.
      rewrite (dfun_dec_extract (E := E) (F := T)).
      rewrite (dist_unit (F := T)).
      reflexivity.
    Qed.

    Theorem mapdt_mapdt:
      forall `{Applicative G1} `{Applicative G2}
        (A B C: Type) (g: E * B -> G2 C) (f: E * A -> G1 B),
        map (mapdt g) ∘ mapdt f = mapdt (G := G1 ∘ G2) (g ⋆3 f).
    Proof.
      intros. unfold transparent tcs. unfold kc3.
      rewrite <- (fun_map_map (F := G1)).
      repeat reassociate <- on left.
      change (?f ∘ map (dec T) ∘ dist T G1 ∘ ?g) with
        (f ∘ (map (F := G1) (dec T) ∘ dist T G1) ∘ g).
      rewrite <- (dtfun_compat (E := E) (F := T) B).
      rewrite <- (fun_map_map (F := G1)).
      repeat reassociate <- on left.
      change (?f ∘ map (map g) ∘ dist T G1 ∘ ?h) with
        (f ∘ (map (F := G1) (map (F := T) g) ∘ dist T G1) ∘ h).
      change (map (map g)) with (map (F := G1 ∘ T) g).
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      rewrite (dist_linear (F := T)).
      repeat reassociate <- on left.
      rewrite <- (fun_map_map (F := T)).
      unfold_ops @Map_compose.
      change (?f ∘ map (map g) ∘ ?x ∘ ?h) with
        (f ∘ (map (F := T) (map (F := G1) g) ∘ x) ∘ h).
      rewrite (fun_map_map (F := T)).
      reassociate -> near (map f).
      rewrite <- (natural (ϕ := @dec E T _)).
      repeat reassociate ->.
      repeat fequal.
      rewrite (dfun_dec_dec (E := E) (F := T)).
      reassociate <-. unfold_ops @Map_compose.
      rewrite (fun_map_map (F := T)).
      do 2 fequal. now ext [e a].
    Qed.

    Theorem mapdt_mapdt_morphism:
      forall `{ApplicativeMorphism G1 G2 ϕ}
             (A B: Type) (f: E * A -> G1 B),
        ϕ (T B) ∘ mapdt f = mapdt (ϕ B ∘ f).
    Proof.
      intros. unfold transparent tcs.
      do 2 reassociate <-.
      rewrite <- (fun_map_map (F := T)).
      rewrite <- (dist_morph (F := T)).
      reflexivity.
    Qed.

    (** ** Typeclass Instance *)
    (******************************************************************)
    #[local] Instance:
      Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T :=
      {| kdtf_mapdt1 := @mapdt_id;
         kdtf_mapdt2 := @mapdt_mapdt;
         kdtf_morph := @mapdt_mapdt_morphism;
      |}.

  End with_functor.

End DerivedInstances.
