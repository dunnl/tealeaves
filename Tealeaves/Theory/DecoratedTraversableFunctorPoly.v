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

  Definition toBatchA {A1 A2 B1 B2: Type}:
      A1 -> Batch2 A1 A2 B1 B2 A2 :=
    fun a1 => StepA (Done2 (C := A2 -> A2) id) a1.

  Definition toBatchB {A1 A2 B1 B2: Type}:
      B1 -> Batch2 A1 A2 B1 B2 B2 :=
    fun b1 => StepB (Done2 (C := B2 -> B2) id) b1.

  Definition toBatchp {A1 A2 B1 B2: Type}:
      T B1 A1 ->
      Batch2
        (list B1 * A1) A2
        (list B1 * B1) B2
        (T B2 A2) :=
    mapdtp (G := Batch2 (list B1 * A1) A2 (list B1 * B1) B2) toBatchB toBatchA.

  Instance ApplicativeMorphism_runBatch2
    `{Applicative G}
    {A1 A2 B1 B2: Type}
    {ϕB : B1 -> G B2}
    {ϕA : A1 -> G A2}:
    ApplicativeMorphism (Batch2 A1 A2 B1 B2) G
      (fun C => runBatch2 G ϕB ϕA (C := C)).
  Proof.
    constructor.
    - admit.
    - assumption.
    - intros C1 C2 f b.
      generalize dependent C2.
      induction b; intros.
      + cbn.
        rewrite app_pure_natural.
        reflexivity.
      + cbn.
        rewrite map_ap.
        rewrite IHb.
        reflexivity.
      + cbn.
        rewrite map_ap.
        rewrite IHb.
        reflexivity.
    - intros C c.
      reflexivity.
    - intros C1 C2 b1 b2.
      cbn.
      admit.
  Admitted.

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
      (A1 A2 B1 B2: Type)
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
      assert (Hpwb': forall b_occ : list B1 * B1,
         @runBatch2 (list B1 * A1) A2 (list B1 * B1) B2 (@const Type Type (list B1 * B1 -> Prop))
           (@Map_const (list B1 * B1 -> Prop)) (@Mult_const (list B1 * B1 -> Prop) (@Monoid_op_subset (list B1 * B1)))
           (@Pure_const (list B1 * B1 -> Prop) (@Monoid_unit_subset (list B1 * B1))) (@eq (list B1 * B1))
           (@const (list B1 * A1) (list B1 * B1 -> Prop) (@const (list B1 * B1) Prop False)) (T B2 A2)
           (@toBatchp A1 A2 B1 B2 t) b_occ -> ρ1 b_occ = ρ2 b_occ).
      admit. clear Hpwb.
      assert (Hpwv': forall v_occ : list B1 * A1,
         @runBatch2 (list B1 * A1) A2 (list B1 * B1) B2 (@const Type Type (list B1 * A1 -> Prop))
           (@Map_const (list B1 * A1 -> Prop)) (@Mult_const (list B1 * A1 -> Prop) (@Monoid_op_subset (list B1 * A1)))
           (@Pure_const (list B1 * A1 -> Prop) (@Monoid_unit_subset (list B1 * A1)))
           (@const (list B1 * B1) (list B1 * A1 -> Prop) (@const (list B1 * A1) Prop False)) (@eq (list B1 * A1))
           (T B2 A2) (@toBatchp A1 A2 B1 B2 t) v_occ -> σ1 v_occ = σ2 v_occ).
      admit. clear Hpwv.
      induction (@toBatchp A1 A2 B1 B2 t).
      - cbn. reflexivity.
      - cbn in *.
        rewrite IHb.
        2:{ intros. apply Hpwb'.
            unfold monoid_op in *.
            unfold Monoid_op_subset in *.
            rewrite subset_in_add.
            tauto. }
        2:{ intros. apply Hpwv'.
            unfold monoid_op in *.
            unfold Monoid_op_subset in *.
            rewrite subset_in_add.
            tauto. }
        fequal. apply Hpwv'.
        now right.
      - cbn in *.
        rewrite IHb.
        2:{ intros. apply Hpwb'.
            unfold monoid_op in *.
            unfold Monoid_op_subset in *.
            rewrite subset_in_add.
            tauto. }
        2:{ intros. apply Hpwv'.
            unfold monoid_op in *.
            unfold Monoid_op_subset in *.
            rewrite subset_in_add.
            tauto. }
        fequal. apply Hpwb'.
        now right.
    Admitted.

  End pointwise_corollaries.

End decorated_traversable_monad_poly_toBatch.
