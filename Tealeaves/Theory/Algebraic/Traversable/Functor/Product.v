From Tealeaves Require Import
  Classes.Algebraic.Traversable.Functor
  Theory.Algebraic.Traversable.Functor.ToKleisli
  Functors.Product.

Import Functors.Product.Notations.

#[local] Generalizable Variables A B F G.

Definition traversal_combine `(f : A -> F B) `(g : A -> G B) : A -> (F ◻ G) B :=
  fun a => product (f a) (g a).

#[local] Notation "f <◻> g" := (traversal_combine f g) (at level 60) : tealeaves_scope.

(** * Characterization of distribution w.r.t. (F ◻ G) *)
(******************************************************************************)
Section traversable_product.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G1}
    `{Applicative G2}.

  Import Traversable.Functor.ToKleisli.Operation.

  Variables
    (A B : Type)
    (f : A -> G1 B) (g : A -> G2 B).

  Lemma dist_combine1 : forall (t : T A),
    pi1 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G1 f t.
  Proof.
    intros. pose (ApplicativeMorphism_pi1 G1 G2).
    compose near t on left.
    now rewrite (traverse_morphism T).
  Qed.

  Lemma dist_combine2 : forall (t : T A),
    pi2 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G2 g t.
  Proof.
    intros. pose (ApplicativeMorphism_pi2 G1 G2).
    compose near t on left.
    now rewrite (traverse_morphism T).
  Qed.

  Theorem dist_combine : forall (t : T A),
    dist T (G1 ◻ G2) (fmap T (f <◻> g) t) =
    product (traverse T G1 f t) (traverse T G2 g t).
  Proof.
    intros. compose near t on left.
    erewrite <- (dist_combine1).
    erewrite <- (dist_combine2).
    now rewrite <- product_eta.
  Qed.

  Theorem traverse_combine :
    traverse T (G1 ◻ G2) (f <◻> g) = (traverse T G1 f) <◻> (traverse T G2 g).
  Proof.
    intros. unfold_ops Traverse_alg.
    ext t. unfold compose.
    now rewrite dist_combine.
  Qed.

End traversable_product.

Module Notations.

  Notation "f <◻> g" := (traversal_combine f g) (at level 60) : tealeaves_scope.

End Notations.

