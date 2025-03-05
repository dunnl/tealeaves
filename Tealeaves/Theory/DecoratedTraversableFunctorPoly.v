From Tealeaves Require Export
  Functors.Batch
  Classes.Kleisli.DecoratedTraversableFunctorPoly
  Classes.Kleisli.Theory.DecoratedTraversableFunctorPoly
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.DecoratedShapelyFunctor
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Functors.Environment
  Functors.Batch2
  Functors.List_Telescoping_General
  Functors.Z2
  Classes.Kleisli.Theory.DecoratedTraversableFunctor
  Theory.TraversableFunctor.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables F M E T G A B C ϕ.

(** * Factoring through runBatch *)
(******************************************************************************)
Section decorated_traversable_monad_poly_toBatch.

  Context
    `{T: Type -> Type -> Type}
      `{DecoratedTraversableFunctorPoly T}.


  Import DecoratedTraversableFunctorPoly.DerivedOperations.

  Definition toBatchp {B1 B2 A1 A2: Type}:
      T B1 A1 ->
      Batch2
        (list B1 * B1) B2
        (list B1 * A1) A2
        (T B2 A2) :=
    mapdtp (G := Batch2 (list B1 * B1) B2 (list B1 * A1) A2) batch2B batch2A.

  Lemma mapdtp_through_toBatchp:
      forall (B1 A1 B2 A2: Type)
        (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
        `{! Applicative G}
        (ϕB: list B1 * B1 -> G B2)
        (ϕA: list B1 * A1 -> G A2),
        mapdtp ϕB ϕA =
          runBatch2 (C := T B2 A2) G ϕB ϕA ∘
            toBatchp (A1 := A1) (A2 := A2) (B1 := B1) (B2 := B2).
  Proof.
    intros.
    unfold toBatchp.
    rewrite (kdtfp_morphism
                 (ϕ := fun C => runBatch2 G ϕB ϕA (C := C))
                 (morph := ApplicativeMorphism_runBatch2)).
    fequal.
    - ext [w b]. cbn.
      rewrite ap1.
      reflexivity.
    - ext [w a]. cbn.
      unfold compose.
      rewrite <- map_to_ap.
      rewrite fun_map_id.
      reflexivity.
  Qed.

  (** ** Pointwise reasoning corollaries of factoring through runBatch *)
  (******************************************************************************)
  Section pointwise_corollaries.

    Context
      (B1 B2 A1 A2: Type)
        (ρ1: list B1 * B1 -> B2)
        (σ1: list B1 * A1 -> A2)
        (ρ2: list B1 * B1 -> B2)
        (σ2: list B1 * A1 -> A2)
        (t: T B1 A1).

    Lemma mapdtp_pw:
      (forall (b_occ: list B1 * B1),
          binder_of_ctx t b_occ -> ρ1 b_occ = ρ2 b_occ) ->
      (forall (v_occ: list B1 * A1),
          leaf_of_ctx t v_occ -> σ1 v_occ = σ2 v_occ) ->
      mapdtp (G := fun A => A) ρ1 σ1 t =
        mapdtp (G := fun A => A) ρ2 σ2 t.
    Proof.
      introv Hpwb Hpwv.
      unfold binder_of in *.
      unfold leaf_of in *.
      rewrite mapdtp_through_toBatchp in *.
      rewrite mapdtp_through_toBatchp in *.
      all: try typeclasses eauto.
      unfold compose in *.
      induction (@toBatchp B1 B2 A1 A2 t).
      - cbn. reflexivity.
      - cbn in *.
        rewrite IHb.
        fequal.
        unfold leaf_of_ctx in Hpwv.
        rewrite mapdtp_through_toBatchp in Hpwv; try typeclasses eauto.
        unfold compose in Hpwv.
        admit.
      - do 2 rewrite runBatch2_rw2.
        rewrite IHb.
        fequal.
        admit.
    Admitted.

  End pointwise_corollaries.

End decorated_traversable_monad_poly_toBatch.
