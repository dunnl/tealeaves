
  Definition Batch_to_Vector'
    (b: Batch A B C): Vector.t A (length_Batch b).
  Proof.
    induction b.
    - apply Vector.nil.
    - cbn.
      apply Vector.cons;
      assumption.
  Defined.

  Definition Batch_to_makeFn'
    (b: Batch A B C): Vector.t B (length_Batch b) -> C.
  Proof.
    induction b.
    - intros ?; assumption.
    - cbn.
      intro X.
      apply VectorDef.uncons in X.
      destruct X.
      apply IHb; auto.
  Defined.

  Definition Batch_to_Vector''
    (b: Batch A B C): Vector.t A (length_Batch b).
  Proof.
    induction b.
    - apply Vector.nil.
    - cbn.
      apply Vector.cons;
      assumption.
  Defined.

  Definition Batch_to_makeFn''
    (b: Batch A B C): Vector.t B (length_Batch b) -> C.
  Proof.
    induction b.
    - intros ?; assumption.
    - cbn.
      intro X.
      apply VectorDef.uncons in X.
      destruct X.
      apply IHb; auto.
  Defined.

End batch_to.

Lemma Batch_to_Vector_step {A B C}: forall (a: A) (b: Batch A B (B -> C)),
    Batch_to_Vector' (b ⧆ a) =
      Vector.cons A a (length_Batch b) (Batch_to_Vector' b).
Proof.
  reflexivity.
Qed.

Lemma Batch_to_makeFn_step {A B C}: forall (a: A) (b: Batch A B (B -> C)),
    Batch_to_makeFn' (b ⧆ a) =
      fun (v:Vector.t B (S (length_Batch b))) =>
          match (Vector.uncons v) with
          | (b', v') => Batch_to_makeFn' b v' b'
          end.
Proof.
  reflexivity.
Qed.

From Tealeaves Require Import
               Classes.Coalgebraic.TraversableFunctor
               Adapters.KleisliToCoalgebraic.TraversableFunctor.

Section aksdjflasdf.

  Context
   T (A:Type) G `{Applicative G}
     `{Kleisli.TraversableFunctor.TraversableFunctor T}.

  Definition toLen: forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := A) (toBatch t)).
  Defined.

  Definition toMake: forall (t : T A),
      Vector.t A (toLen t) -> (T A).
  Proof.
    intros t B.
    unfold toLen.
    apply (Batch_to_makeFn' (toBatch t)).
    assumption.
  Defined.

  Definition toContents: forall (t : T A),
      Vector.t A (toLen t).
  Proof.
    intro t.
    unfold toLen.
    apply (Batch_to_Vector' (toBatch t)).
  Defined.

  Definition toLen' (B:Type): forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := B) (toBatch t)).
  Defined.

  Definition toMake' B: forall (t : T A),
      Vector.t B (toLen' B t) -> (T B).
  Proof.
    intros t.
    unfold toLen.
    apply (Batch_to_makeFn' (toBatch t)).
  Defined.

  Definition toContents' B: forall (t : T A),
      Vector.t A (toLen' B t).
  Proof.
    intro t.
    apply (Batch_to_Vector' (toBatch t)).
  Defined.


  Lemma repr: forall `(t : T A),
      t = toMake t (toContents t).
  Proof.
    intros.
    unfold toMake, toContents.
    change t with (id t) at 1.
    rewrite <- trf_extract.
    unfold compose at 1.
    eapply (
        Batch_ind A A
                  (fun (T1 : Type) (b0 : Batch A A T1) =>
                     extract_Batch b0 =
                       Batch_to_makeFn' b0 (Batch_to_Vector' b0))).
    - reflexivity.
    - intros.
      rewrite Batch_to_makeFn_step.
      rewrite Batch_to_Vector_step.
      cbn.
      rewrite H5.
      reflexivity.
  Qed.

  Lemma repr': forall `(t : T A) B (f : A -> G B),
      traverse f t = pure (toMake' B t) <⋆>
                       (traverse (T := VEC (toLen' B t)) f (toContents' B t)).
  Proof.
    intros.
    unfold toMake', toContents'.
    Search traverse toBatch.
    rewrite traverse_through_runBatch.
    unfold compose at 1.
  Admitted.

End aksdjflasdf.