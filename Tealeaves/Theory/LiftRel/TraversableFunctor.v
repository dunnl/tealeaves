From Tealeaves Require Export
  Adapters.CategoricalToKleisli.TraversableFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Classes.Coalgebraic.TraversableFunctor
  Functors.Batch
  Functors.List
  Functors.VectorRefinement
  Theory.TraversableFunctor.

Import Coalgebraic.TraversableFunctor (ToBatch, toBatch).
Import KleisliToCoalgebraic.TraversableFunctor.DerivedInstances.

Import Subset.Notations.
Import Applicative.Notations.
Import ContainerFunctor.Notations.
Import ProductFunctor.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import Batch.Notations.
Import Monoid.Notations.
Import VectorRefinement.Notations.

#[local] Generalizable Variables F T G A B C M ϕ.

#[local] Arguments mapfst_Batch {B C A1 A2}%type_scope
  f%function_scope b.
#[local] Arguments mapsnd_Batch {A B1 B2 C}%type_scope
  f%function_scope b.




(** * Lifting relations over Traversable functors *)
(**********************************************************************)
Definition lift_relation {X} {A B:Type} `{Traverse X}
  (R: A -> B -> Prop): X A -> X B -> Prop :=
  traverse (G := subset) R.

Lemma lift_relation_rw {X} {A B:Type} `{Traverse X}
  (R: A -> B -> Prop) t1 t2:
  lift_relation R t1 t2 = traverse (G := subset) R t1 t2.
Proof.
  reflexivity.
Qed.

Section lifting_relations.

  Context
    `{Classes.Categorical.TraversableFunctor.TraversableFunctor T}.

  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.TraversableFunctor.DerivedInstances.
  Import KleisliToCoalgebraic.TraversableFunctor.DerivedOperations.
  Import KleisliToCoalgebraic.TraversableFunctor.DerivedInstances.

  Context
    `{ToSubset T}
    `{! Compat_ToSubset_Traverse T}.

  Lemma relation_spec:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u <->
        (exists b: Vector (plength t) B,
            traverse (G := subset) R (trav_contents t) b /\
              trav_make t b = u).
  Proof.
    intros.
    unfold lift_relation.
    rewrite traverse_repr.
    compose near (trav_contents t).
    rewrite (traverse_commutative (G := subset) (T := Vector (plength t))).
    reflexivity.
  Qed.

  (* Minor, not helpful  *)
  Lemma relation1:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Plen: plength u = plength t),
      lift_relation R t u ->
        trav_make t (coerce Plen in trav_contents u) = u.
  Proof.
    introv Hrel.
    rewrite relation_spec in Hrel.
    destruct Hrel as [trav_contents_u [Htrav Hmake]].
    assert (Hcontents: trav_contents u ~~ trav_contents_u).
    { apply trav_contents_unique in Hmake.
      symmetry. assumption. }
    rewrite <- Hmake.
    apply Vector_fun_sim_eq.
    - reflexivity.
    - vector_sim.
  Qed.

  Lemma relation2:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Hlen: plength u = plength t),
      lift_relation R t u ->
      traverse (G := subset) R
        (trav_contents t)
        (coerce Hlen in trav_contents u).
  Proof.
    introv Hrel.
    rewrite relation_spec in Hrel.
    destruct Hrel as [trav_contents_u [Hrel Hmake]].
    enough (Heq: coerce Hlen in trav_contents u =
                             trav_contents_u).
    { rewrite Heq.
      assumption. }
    apply Vector_sim_eq.
    vector_sim.
    symmetry.
    apply trav_contents_unique.
    assumption.
  Qed.

  Lemma relation3:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Hlen: plength u = plength t),
      trav_make (B := B) t ~!~ trav_make u ->
      traverse (G := subset) R
        (trav_contents t)
        (coerce Hlen in trav_contents u) ->
            lift_relation R t u.
  Proof.
    introv Htrav.
    rewrite relation_spec.
    exists (coerce Hlen in trav_contents u). split.
    assumption.
    change u with (id u) at 3.
    rewrite id_spec.
    apply Vector_fun_sim_eq.
    assumption.
    vector_sim.
  Qed.

  Lemma relation4:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u ->
      (forall C, trav_make (B := C) t ~!~ trav_make u).
  Proof.
    introv Hrel. intro C.
    rewrite relation_spec in Hrel.
    destruct Hrel as [trav_contents_u [Htrav Hmake]].
    eapply trav_make_unique.
    eassumption.
  Qed.

  (** ** Related terms have the same shape *)
  (********************************************************************)
  Lemma relation_implies_shape:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u -> shape t = shape u.
  Proof.
    introv Hrel.
    apply trav_same_shape_rev.
    eapply relation4.
    eassumption.
  Qed.

  (** ** Related terms have a related zip *)
  (********************************************************************)
  Lemma Monoid_op_Opposite_and:
    Monoid_op_Opposite Monoid_op_and = and.
  Proof.
    ext P1 P2; propext; cbv; tauto.
  Qed.

  (* Hshape is trying to use Derived.Map_Traverse
     so pass (H := H) to ensure the right Map F is chosen *)
  Lemma relation_to_zipped:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Hshape: shape (H := H) t = shape u),
      lift_relation R t u ->
      Forall (uncurry R)
        (same_shape_zip t u Hshape).
  Proof.
    intros.
    unfold Forall.
    unfold same_shape_zip.
    rewrite foldMap_trav_make.
    rewrite Monoid_op_Opposite_and.
    unfold same_shape_zip_contents.
    unfold Vector_zip.
    rewrite <- (traverse_zipped_vector
                 (R := R) (plength t) (trav_contents t)
                 (coerce eq_sym (same_shape_implies_plength t u Hshape)
                   in trav_contents u)).
    pose relation2.
    apply t0.
    assumption.
  Qed.

  Lemma foldMap_same_shape_zip `{Monoid M}:
    forall (A B: Type) (f: A * B -> M) (t: T A) (u: T B)
      (Hshape: shape (H := H) t = shape u),
      foldMap (T := T) f (same_shape_zip t u Hshape) =
        foldMap (op := Monoid_op_Opposite op) (T := Vector (plength t))
          f (same_shape_zip_contents t u Hshape).
  Proof.
    intros.
    unfold same_shape_zip.
    rewrite foldMap_trav_make.
    reflexivity.
  Qed.

  Lemma relation_to_zipped_iff:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Hshape: shape (H :=H) t = shape u),
      lift_relation R t u <->
        (forall C, trav_make (B := C) t ~!~ trav_make u) /\
          Forall (uncurry R)
            (same_shape_zip t u Hshape).
  Proof.
    intros.
    split.
    - introv Hrel. split.
      + eapply relation4.
        eassumption.
      + apply relation_to_zipped.
        assumption.
    - intros [Hmake Hzip].
      rewrite relation_spec.
      assert (Hlen: plength u = plength t).
      { apply same_shape_implies_plength.
        symmetry. assumption. }
      exists (coerce Hlen in trav_contents u).
      split.
      + unfold same_shape_zip in Hzip.
        unfold same_shape_zip_contents in Hzip.
        unfold Vector_zip in Hzip.
        unfold Forall in Hzip.
        rewrite foldMap_trav_make in Hzip.
        rewrite Monoid_op_Opposite_and in Hzip.
        rewrite <- (traverse_zipped_vector
                     (R := R) (plength t) (trav_contents t)
                     (coerce eq_sym (same_shape_implies_plength t u Hshape)
                       in trav_contents u)) in Hzip.
        enough (Hcoerce: (coerce eq_sym (same_shape_implies_plength t u Hshape)
                   in trav_contents u) =
                  coerce Hlen in trav_contents u).
        rewrite <- Hcoerce.
        assumption.
        apply Vector_sim_eq.
        vector_sim.
      + change u with (id u) at 3.
        rewrite id_spec.
        apply Vector_fun_sim_eq.
        * apply Hmake.
        * vector_sim.
  Qed.

  Lemma relation_natural1:
    forall (A B1 B2: Type) (R: B1 -> B2 -> Prop) (t: T A) (f: A -> B1),
      lift_relation R (map f t) = lift_relation (R ∘ map f) t.
  Proof.
    intros.
    unfold lift_relation.
    compose near t on left.
    rewrite (traverse_map (G2 := subset) R f).
    reflexivity.
  Qed.

  Lemma relation_natural2_lemma:
    forall (B1 A B2: Type) (R: B1 -> B2 -> Prop) (t: T B1) (u: T A) (f: A -> B2)
      (Hshape: shape (H := H) t = shape (map f u))
      (Hshape': shape (H := H)  t = shape u),
      Forall (uncurry R) (same_shape_zip t (map f u) Hshape) =
        Forall (uncurry (precompose f ∘ R)) (same_shape_zip t u Hshape').
  Proof.
    intros.
    unfold Forall.
    rewrite foldMap_same_shape_zip.
    rewrite foldMap_same_shape_zip.
    rewrite natural_snd_same_shape_zip_contents_rev.
    compose near (same_shape_zip_contents t u (same_shape_map_rev_r t u f Hshape)).
    rewrite (foldMap_map).
    fequal.
    - ext [x y]. reflexivity.
    - apply same_shape_zip_contents_proof_irrelevance.
  Qed.

  Lemma relation_natural2_core:
    forall (B1 A B2: Type) (R: B1 -> B2 -> Prop) (t: T B1) (u: T A) (f: A -> B2),
      shape t = shape u ->
      lift_relation R t (map f u) = lift_relation (precompose f ∘ R) t u.
  Proof.
    introv Hshape.
    assert (Hshape': shape t = shape (map f u)).
    { rewrite shape_map. assumption. }
    apply propositional_extensionality.
    rewrite (relation_to_zipped_iff _ _ R t (map f u) Hshape').
    rewrite (relation_to_zipped_iff _ _ (precompose f ∘ R) t u Hshape).
    erewrite relation_natural2_lemma.
    split.
    - intros [X1 X2]. split.
      + intros.
        apply trav_same_shape.
        assumption.
      + eassumption.
    - intros [X1 X2]. split.
      + apply trav_same_shape.
        assumption.
      + assumption.
  Qed.

  Lemma relation_natural2:
    forall (B1 A B2: Type) (R: B1 -> B2 -> Prop) (t: T B1) (u: T A) (f: A -> B2),
      lift_relation R t (map f u) = lift_relation (precompose f ∘ R) t u.
  Proof.
    intros.
    apply propositional_extensionality.
    split.
    - introv hyp.
      rewrite <- relation_natural2_core; try assumption.
      apply relation_implies_shape in hyp.
      rewrite shape_map in hyp.
      assumption.
    - introv hyp.
      rewrite relation_natural2_core; try assumption.
      apply relation_implies_shape in hyp.
      assumption.
  Qed.

  (* TODO This can actually be strengthed into an IFF *)
  Lemma relation_respectful:
    forall (A B1 B2: Type) (R: B1 -> B2 -> Prop) (t: T A) (f: A -> B1) (g: A -> B2),
    (forall (a: A), a ∈ t -> R (f a) (g a)) -> lift_relation R (map f t) (map g t).
  Proof.
    introv hyp.
    rewrite relation_natural1.
    rewrite relation_natural2.
    unfold lift_relation.
    rewrite traverse_through_runBatch.
    unfold compose.
    unfold element_of in hyp.
    rewrite tosubset_to_foldMap in hyp.
    change t with (id t) at 2.
    rewrite id_through_runBatch.
    unfold compose.
    rewrite (foldMap_through_toBatch A A) in hyp.
    (* induction (@toBatch T ToBatch_inst A A t). *) (* Generates a weird hypothesis *)
    apply (Batch_ind A A
      (fun (C: Type) (b: Batch A A C) =>
           (forall a: A, foldMap (T := BATCH1 A C) (ret (T := subset)) b a -> R (f a) (g a)) ->
           runBatch (G := subset) (fun a: A => precompose g (R (map f a))) b (runBatch id b))).
    - intros C c hyp'.
      reflexivity.
    - introv IH.
      introv hyp'.
      rewrite runBatch_rw2.
      rewrite runBatch_rw2.
      rewrite subset_ap_spec.
      unfold ap.
      unfold_ops @Map_I.
      unfold_ops @Mult_I.
      exists (runBatch id b) a.
      splits.
      { unfold precompose, compose.
        unfold_ops @Map_I.
        apply hyp'.
        now right. }
      { apply IH.
        intros.
        apply hyp'.
        rewrite foldMap_Batch_rw2.
        now left.
      }
      { reflexivity. }
    - assumption.
  Qed.

End lifting_relations.


(** * Properties of Relations *)
(**********************************************************************)
Section relprop.


End relprop.

(** * Diagonal *)
(**********************************************************************)
Section relprop.

  Context
    `{Classes.Categorical.TraversableFunctor.TraversableFunctor T}.

  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.TraversableFunctor.DerivedInstances.
  Import KleisliToCoalgebraic.TraversableFunctor.DerivedOperations.
  Import KleisliToCoalgebraic.TraversableFunctor.DerivedInstances.

  Lemma relation_diagonal1:
    forall (A: Type) (R: A -> A -> Prop) (t: T A),
      Forall (fun (a: A) => R a a) t -> lift_relation R t t.
  Proof.
    introv HF.
    unfold Forall in HF.
    rewrite (foldMap_to_traverse2 A) in HF.
    unfold lift_relation.
    rewrite traverse_through_runBatch in HF.
    rewrite traverse_through_runBatch.
    unfold compose.
    change t with (id t) at 2.
    rewrite (id_through_runBatch).
    unfold compose at 1.
    unfold compose at 1 in HF.
    generalize dependent HF.

    apply (Batch_ind A A
             (fun C (b: Batch A A C) =>
                runBatch (G := const Prop) (fun a: A => R a a) b ->
                runBatch (G := subset) R b (runBatch id b))).
    - cbv. tauto.
    - introv X1 X2.
      rewrite runBatch_rw2 in X2.
      unfold ap in X2.
      unfold map in X2.
      unfold Map_const in X2.
      unfold mult in X2.
      unfold Mult_const in X2.
      unfold monoid_op in X2.
      unfold Monoid_op_and in X2.
      destruct X2 as [Y1 Y2].
      rewrite runBatch_rw2.
      rewrite runBatch_rw2.
      rewrite subset_ap_spec.
      exists (runBatch id b).
      exists a.
      split; auto.
  Qed.

  Lemma Forall_vector:
    forall (A: Type) (R: A -> Prop) (t: T A),
      Forall R t = Forall R (trav_contents t).
  Proof.
    unfold Forall.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_repr.
    induction (trav_contents t) using Vector_induction.
    - cbn.
      reflexivity.
    - rewrite traverse_Vector_vcons.
      rewrite foldMap_to_traverse1.
      rewrite traverse_Vector_vcons.
      rewrite <- foldMap_to_traverse1.
      cbn.
      rewrite <- IHv.
      cbn.
      unfold transparent tcs.
      unfold transparent tcs.
      propext.
      + intros.
        preprocess.
        split; auto.
      + intros.
        preprocess.
        split; auto.
  Qed.

  Lemma relation_diagonal2:
    forall (A: Type) (R: A -> A -> Prop) (t: T A),
      lift_relation R t t -> Forall (fun (a: A) => R a a) t.
  Proof.
    introv.
    rewrite (relation_to_zipped_iff _ _ R t t (eq_refl)).
    intros [X1 X2].
    generalize dependent X2.
    unfold same_shape_zip.
    unfold same_shape_zip_contents.
    rewrite Vector_zip_proof_irrelevance2.
    rewrite Vector_zip_diagonal.
    unfold Forall.
    rewrite foldMap_trav_make.
    compose near (trav_contents t).
    rewrite foldMap_map.
    unfold compose.
    intro.
    change (Forall (fun a => R a a) t).
    rewrite Forall_vector.
    unfold uncurry in X2.
    induction (trav_contents t) using Vector_induction.
    - unfold Forall.
      rewrite foldMap_Vector_vnil.
      easy.
    - unfold Forall.
      rewrite foldMap_Vector_vcons.
      rewrite foldMap_Vector_vcons in X2.
      inversion X2.
      split.
      + assumption.
      + apply IHv. assumption.
  Qed.

  Lemma relation_diagonal_iff:
    forall (A: Type) (R: A -> A -> Prop) (t: T A),
      lift_relation R t t <-> Forall (fun (a: A) => R a a) t.
  Proof.
    introv; split; intro.
    apply relation_diagonal2; auto.
    apply relation_diagonal1; auto.
  Qed.

End relprop.


