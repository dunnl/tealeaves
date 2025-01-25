From Tealeaves Require Export
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.TraversableFunctor.

#[local] Generalizable Variables ϕ G.

(** * Categorical Traversable Functors from Kleisli Traversable Functors *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Dist_Traverse (T: Type -> Type) `{Traverse T}
 : ApplicativeDist T := fun G _ _ _ A => traverse (@id (G A)).

End DerivedOperations.

(** ** Derived Instances *)
(**********************************************************************)
Module DerivedInstances.

  Section proofs.

    Context
      (T: Type -> Type)
      `{Kleisli.TraversableFunctor.TraversableFunctor T}.
      (* Alectryon doesn't like this
      Import KleisliToCategorical.TraversableFunctor.DerivedOperations.
      *)
      Import DerivedOperations.
      Import Kleisli.TraversableFunctor.DerivedOperations.
      Import Kleisli.TraversableFunctor.DerivedInstances.

    Lemma dist_natural_T:
      forall (G: Type -> Type)
        (H2: Map G) (H3: Pure G) (H4: Mult G),
        Applicative G -> Natural (@dist T _ G H2 H3 H4).
    Proof.
      intros. constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Map_compose @Dist_Traverse @Map_Traverse.
        rewrite (trf_traverse_traverse (G1 := G) (G2 := fun A => A)).
        change (traverse (@id (G B))) with (map (F := fun A => A) (traverse (@id (G B)))).
        rewrite (trf_traverse_traverse (G1 := fun A => A) (G2 := G)).
        (* TODO Cleanup this part *)
        fequal. rewrite (Mult_compose_identity1 G), (Mult_compose_identity2 G).
        reflexivity.
    Qed.

    Lemma dist_morph_T: forall G1 G2 `{ApplicativeMorphism G1 G2 ϕ},
      forall A: Type, dist T G2 ∘ map (ϕ A) = ϕ (T A) ∘ dist T G1.
    Proof.
      intros. unfold_ops @Dist_Traverse @Map_Traverse.
      change (traverse (@id (G2 A))) with (map (F := fun A => A) (traverse (@id (G2 A)))).
      infer_applicative_instances.
      rewrite (trf_traverse_traverse (G1 := fun A => A)).
      change (map (fun A => A) id ∘ ?f) with f.
      rewrite (trf_traverse_morphism (T := T)).
      fequal. now rewrite (Mult_compose_identity2 G2).
    Qed.

    Lemma dist_unit_T: forall A: Type,
        dist T (fun A0: Type => A0) = @id (T A).
    Proof.
      intros. unfold_ops @Dist_Traverse.
      apply (trf_traverse_id (T := T)).
    Qed.

    Lemma dist_linear_T: forall (G1: Type -> Type) (H2: Map G1) (H3: Pure G1) (H4: Mult G1),
        Applicative G1 ->
        forall (G2: Type -> Type) (H6: Map G2) (H7: Pure G2) (H8: Mult G2),
          Applicative G2 -> forall A: Type, dist T (G1 ∘ G2) (A := A) = map (F := G1) (dist T G2) ∘ dist T G1.
    Proof.
      intros. unfold_ops @Dist_Traverse.
      rewrite (trf_traverse_traverse).
      unfold kc2.
      rewrite (fun_map_id (F := G1)).
      reflexivity.
    Qed.

    #[export] Instance: Categorical.TraversableFunctor.TraversableFunctor T :=
      {| dist_natural := dist_natural_T;
         dist_morph := dist_morph_T;
         dist_unit := dist_unit_T;
         dist_linear := dist_linear_T;
      |}.

  End proofs.

End DerivedInstances.
