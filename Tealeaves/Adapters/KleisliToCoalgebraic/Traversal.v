

(** * Decomposing <<dist>> in terms of <<iterate>> *)
(******************************************************************************)
Section traversal_iterate.

  Import Classes.Kleisli.Traversable.Functor.

  Context
    `{Classes.Traversable.Functor.TraversableFunctor T}.

  Import Traversable.Functor.ToKleisli.

  Lemma dist_to_runBatch `{Applicative G} {A : Type} :
    dist T G (A := A) = runBatch (@id (G A)) ∘ Functor.toBatch T A.
  Proof.
    ext t.
    replace t with (map T id t) at 1 by (now rewrite (fun_map_id T)).
    change_left (traverse T G (@id (G A)) t).
    now rewrite (traverse_to_runBatch T).
  Qed.

End traversal_iterate.
