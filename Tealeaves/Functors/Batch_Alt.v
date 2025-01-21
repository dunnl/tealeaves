From Tealeaves.Functors Require Import
  Early.Batch
  Functors.Batch
  Constant.

Import Early.Batch.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import Kleisli.TraversableFunctor.Notations.

(** * Deconstructing <<Batch A B C>> via Coq Stdlib <<Vector>> Type *)
(******************************************************************************)
From Tealeaves Require
  Functors.Vector
  Adapters.CategoricalToKleisli.TraversableFunctor.

Module DeconstructBatchStdlib.

  Import Functors.Vector.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.TraversableFunctor.DerivedInstances.

  (** ** <<Batch_contents>> and <<Batch_make>> *)
  (******************************************************************************)
  Fixpoint Batch_contents {A B C} (b: Batch A B C):
    Vector.t A (length_Batch b) :=
    match b return (Vector.t A (length_Batch b)) with
    | Done c => Vector.nil A
    | Step rest a =>
        Vector.cons A a (length_Batch rest) (Batch_contents rest)
    end.

  Fixpoint Batch_make {A B C} (b: Batch A B C):
    Vector.t B (length_Batch b) -> C :=
    match b return (Vector.t B (length_Batch b) -> C) with
    | Done c =>
        const c
    | Step rest a =>
        fun (v: Vector.t B (S (length_Batch rest))) =>
          match (Vector.uncons v) with
          | (b, v_rest) => Batch_make rest v_rest b
          end
    end.

  (** ** Rewriting Rules *)
  (******************************************************************************)
  Lemma Batch_contents_rw2: forall {A B C} (b: Batch A B (B -> C)) (a: A),
      Batch_contents (b ⧆ a) =
        Vector.cons A a (length_Batch b) (Batch_contents b).
  Proof.
    reflexivity.
  Qed.

  Lemma Batch_make_rw2: forall {A B C} (a: A) (b: Batch A B (B -> C)),
      Batch_make (b ⧆ a) =
        fun (v:Vector.t B (S (length_Batch b))) =>
          match (Vector.uncons v) with
          | (b', v') => Batch_make b v' b'
          end.
  Proof.
    reflexivity.
  Qed.

  (** ** Representation Theorem *)
  (******************************************************************************)
  Lemma Batch_repr {A C}:
    forall (b: Batch A A C),
      Batch_make b (Batch_contents b) = extract_Batch b.
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn.
      rewrite IHb.
      reflexivity.
  Qed.

  Lemma runBatch_repr `{Applicative G} {A B C}:
    forall (f: A -> G B) (b: Batch A B C),
      runBatch (G := G) f b =
        pure G (Batch_make b) <⋆>
          traverse (T := VEC (length_Batch b)) f (Batch_contents b).
  Proof.
    intros.
    induction b.
    - cbn.
      rewrite ap2.
      reflexivity.
    - rewrite runBatch_rw2.
      rewrite Batch_contents_rw2.
      rewrite Batch_make_rw2.
      cbn.
      rewrite <- ap4.
      rewrite ap2.
      rewrite <- ap4.
      rewrite ap2.
      rewrite ap2.
      rewrite IHb.
      reflexivity.
  Qed.

End DeconstructBatchStdlib.

(** * Deconstructing <<Batch A B C>> with Partial Operations *)
(******************************************************************************)
From Tealeaves Require Functors.Option.

Module DeconstructBatchPartial.

  Import Functors.Option.

  Fixpoint Batch_make {A B C} (b: Batch A B C) (l: list B): option C :=
    match b with
    | Done c =>
        match l with
        | nil => Some c
        | _ => None
        end
    | Step rest a =>
        match (List.rev l) with
        | (b' :: bs) =>
            map _ (evalAt  b') (Batch_make rest bs)
        | _ => None
        end
    end.

  Definition Batch_contents {A B C} (b: Batch A B C): list A :=
    runBatch (G := const (list A)) (ret list A) b.

  Fixpoint Batch_replace_contents `(b: Batch A B C) `(l: list A'):
    Batch (option A') B C :=
    match b with
    | Done c => Done c
    | Step rest a =>
      match l with
      | nil => Step (Batch_replace_contents rest nil) None
      | cons a l' => Step (Batch_replace_contents rest l') (Some a)
      end
    end.

  (** ** Rewriting Rules *)
  (******************************************************************************)
  Lemma Batch_make_rw11 {A B C}: forall c,
      Batch_make (@Done A B C c) nil = Some c.
  Proof.
    reflexivity.
  Qed.

  Lemma Batch_make_rw12 {A B C} b' l: forall c,
      Batch_make (@Done A B C c) (b' :: l) = None.
  Proof.
    reflexivity.
  Qed.

  Lemma Batch_make_rw21 {A B C}:
    forall (b: Batch A B (B -> C)) (a: A),
       Batch_make (b ⧆ a) nil = None.
  Proof.
    reflexivity.
  Qed.

  Lemma Batch_make_rw22 {A B C}:
    forall (b: Batch A B (B -> C)) (a: A) (l : list B) (b' : B),
       Batch_make (b ⧆ a) (l ++ b' :: nil) =
        Batch_make b (List.rev l) <⋆> pure option b'.
  Proof.
    intros.
    cbn.
    rewrite List.rev_unit.
    rewrite map_to_ap.
    rewrite ap3.
    reflexivity.
  Qed.

  (** ** Naturality *)
  (******************************************************************************)
  Lemma basic0 {A B C C'} (b: Batch A B C) (l: list B) (f: C -> C'):
    map _ f (Batch_make b l) = Batch_make (map _ f b) l.
  Proof.
    induction b; induction l.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn in *.
      rename a0 into b'.
      specialize (IHb (f ∘ evalAt b')).
      destruct b.
  Abort.

  Lemma basic1 {A B C} (b: Batch A B C) (l: list B):
    length l = length_Batch b ->
    {c | Batch_make b l = Some c}.
  Proof.
    intros.
    generalize dependent l.
    induction b; intros l.
    - destruct l.
      + cbn. exists c. reflexivity.
      + cbn. inversion 1.
    - destruct l.
      + inversion 1.
      + intro Heq.
        specialize (IHb (List.rev l)).
        assert (length (List.rev l) = length_Batch b).
        { rewrite List.rev_length.
          apply S_uncons.
          assumption. }
        specialize (IHb H).
        destruct IHb as [c pf].
        rewrite <- (List.rev_involutive l).
        rewrite <- List.rev_unit.
        rewrite List.rev_app_distr.
        destruct l.
        { cbn. exists (c b0).
          cbn in pf. rewrite pf.
          reflexivity. }
  Abort.

  Lemma Batch_repr {A C}:
    forall (b: Batch A A C),
      Batch_make b (List.rev (Batch_contents b)) = Some (extract_Batch b).
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn.
      assert (forall {A B C} (b: Batch A B (B -> C)) (a: A) (l : list B) (b': B),
      Batch_make (b ⧆ a) (l ++ b' :: nil) =
        Batch_make b (List.rev l) <⋆> pure _ b').
      { intros.
        rewrite Batch_make_rw22.
        reflexivity. }
      unfold_ops @Monoid_op_list.
      rewrite List.rev_app_distr.
      cbn.
      rewrite List.rev_involutive.
      remember (runBatch (G := const (list A)) (ret list A) b).
      destruct c.
  Abort.

End DeconstructBatchPartial.
