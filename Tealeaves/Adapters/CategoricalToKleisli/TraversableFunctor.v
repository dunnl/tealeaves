From Tealeaves Require Import
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.TraversableFunctor.

#[local] Generalizable Variables G ϕ.

#[local] Arguments traverse (T)%function_scope {Traverse} G%function_scope
  {H H0 H1} (A B)%type_scope _%function_scope _.

(** * Kleisi presentation of traversable functors *)
(******************************************************************************)
Module ToKleisli.

  #[export] Instance Traverse_dist
    (T : Type -> Type) `{Map T} `{ApplicativeDist T}
  : Traverse T :=
  fun (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    (A B : Type) (f : A -> G B) => dist T G ∘ map T f.

  Section with_functor.

    Context
      (T : Type -> Type)
      `{Classes.Categorical.TraversableFunctor.TraversableFunctor T}.

    Theorem traverse_id : forall (A : Type),
        traverse T (fun A => A) A A id = @id (T A).
    Proof.
      intros. unfold traverse. unfold_ops @Traverse_dist.
      ext t. rewrite (dist_unit (F := T)).
      now rewrite (fun_map_id (F := T)).
    Qed.

    Theorem traverse_id_purity : forall `{Applicative G} (A : Type),
        traverse T G A A (pure G) = @pure G _ (T A).
    Proof.
      intros. unfold traverse.
      unfold_ops @Traverse_dist.
      ext t. now rewrite map_purity_1.
    Qed.

    Lemma traverse_traverse (G1 G2 : Type -> Type) `{Applicative G1} `{Applicative G2} :
      forall (A B C : Type) (g : B -> G2 C) (f : A -> G1 B),
        map G1 (traverse T G2 B C g) ∘ traverse T G1 A B f = traverse T (G1 ∘ G2) A C (map G1 g ∘ f).
    Proof.
      introv. unfold traverse.
      unfold_ops @Traverse_dist.
      rewrite (dist_linear (F := T)).
      repeat reassociate <-.
      rewrite <- (fun_map_map (F := T)).
      repeat reassociate <-.
      reassociate -> near (map T (map G1 g)).
      change (map T (map G1 g)) with (map (T ∘ G1) g).
      rewrite <- (natural (ϕ := @dist T _ G1 _ _ _)).
      unfold_ops @Map_compose.
      reassociate <-.
      unfold_compose_in_compose.
      now rewrite (fun_map_map (F := G1)).
    Qed.

    Lemma traverse_morphism `{morph : ApplicativeMorphism G1 G2 ϕ} : forall (A B : Type) (f : A -> G1 B),
        ϕ (T B) ∘ traverse T G1 A B f = traverse T G2 A B (ϕ B ∘ f).
    Proof.
      intros. unfold traverse.  unfold_ops @Traverse_dist.
      reassociate <-.
      inversion morph.
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

End ToKleisli.
