From Tealeaves Require Export
  Classes.Kleisli.Traversable.Functor
  Classes.Algebraic.Traversable.Functor
  Theory.Kleisli.Traversable.Functor.Container
  Theory.Algebraic.Traversable.Functor.ToKleisli.

Import Traversable.Functor.ToKleisli.Operation.

Import Batch.Notations.

#[local] Generalizable Variable T G A B.

(** * Decomposing <<dist>> in terms of <<iterate>> *)
(******************************************************************************)
Section traversal_iterate.

  Context
    `{Algebraic.Traversable.Functor.TraversableFunctor T}.

  Import ToKleisli.Instance.

  Lemma dist_to_runBatch `{Applicative G} {A : Type} :
    dist T G (A := A) = runBatch (@id (G A)) ∘ iterate T A.
  Proof.
    ext t.
    replace t with (fmap T id t) at 1 by (now rewrite (fun_fmap_id T)).
    change_left (traverse T G (@id (G A)) t).
    now rewrite (traverse_to_runBatch T).
  Qed.

End traversal_iterate.
