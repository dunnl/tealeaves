From Tealeaves Require Import
  Classes.Coalgebraic.TraversableFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Functors.Batch
  Functors.Vector.

Import Applicative.Notations.

Module monomorphic.

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
      apply (Batch_to_makeFn (toBatch t)).
      assumption.
    Defined.

    Definition toContents: forall (t : T A),
        Vector.t A (toLen t).
    Proof.
      intro t.
      unfold toLen.
      apply (Batch_to_contents (toBatch t)).
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
                         Batch_to_makeFn b0 (Batch_to_contents b0))).
      - reflexivity.
      - intros.
        rewrite Batch_to_makeFn_rw2.
        rewrite Batch_to_contents_rw2.
        cbn.
        rewrite H5.
        reflexivity.
    Qed.

  End aksdjflasdf.

End monomorphic.

Section polymorphic.

  Context
    T G
      `{Applicative G}
      `{Kleisli.TraversableFunctor.TraversableFunctor T}
      `{Map T}
      `{ToBatch T}
      `{! Compat_Map_Traverse T}
      `{! Compat_ToBatch_Traverse}.

  Lemma toBatch_mapsnd : forall (A B B' : Type) (f : B -> B'),
      mapsnd_Batch B B' f ∘ toBatch (A := A) (A' := B') =
        map (F := Batch A B) (map f) ∘ toBatch (A := A) (A' := B).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism
               (G1 := Batch A B')
               (ϕ := fun A => mapsnd_Batch B B' f)).
    rewrite (map_traverse).
    rewrite ret_dinatural.
    reflexivity.
  Qed.

  Definition toLen {A} (B: Type): forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := B) (toBatch t)).
  Defined.

  Lemma toLen1: forall A B, toLen (A := A) B =
                         toLen (A := unit) B ∘ map (fun _ => tt).
  Proof.
    intros.
    ext t.
    unfold toLen.
    rewrite (batch_length_mapfst (fun _ => tt)
                                 (@toBatch T _ A B t)).
    compose near t on left.
    rewrite <- (toBatch_mapfst (T := T) A unit (fun _ => tt) B).
    unfold compose.
    reflexivity.
  Qed.

  Definition toMake {A}: forall (t : T A) (B: Type),
      Vector.t B (toLen B t) -> (T B).
  Proof.
    intros t B.
    unfold toLen.
    apply (Batch_to_makeFn (toBatch t)).
  Defined.

  Definition toContents {A B}: forall (t : T A),
      Vector.t A (toLen B t).
  Proof.
    intro t.
    apply (Batch_to_contents (toBatch t)).
  Defined.

  Lemma repr {A}: forall `(t : T A) B (f : A -> G B),
      traverse f t = pure (toMake t B) <⋆>
                       (traverse (T := VEC (toLen B t)) f (toContents t)).
  Proof.
    intros.
    unfold toMake, toContents.
    rewrite traverse_through_runBatch.
    unfold compose.
    rewrite runBatch_repr.
    reflexivity.
  Qed.

End polymorphic.
