From Tealeaves Require Import
  Classes.Kleisli.Monad (Return, ret)
  Classes.Kleisli.TraversableMonad
  Classes.Categorical.Applicative
  Functors.Batch.

Import Applicative.Notations.

#[local] Arguments Done : clear implicits.
#[local] Arguments Step : clear implicits.

(** * Traversable monads as coalgebras *)
(******************************************************************************)
Class ToBatchM (T : Type -> Type) :=
  toBatchM : forall A B, T A -> Batch A (T B) (T B).

#[global] Arguments toBatchM (T)%function_scope {ToBatchM} (A B)%type_scope _.

Fixpoint cojoin_BatchM (T : Type -> Type) `{ToBatchM T} (A B B' C : Type)
  (b : Batch A (T B) C) : Batch A (T B') (Batch B' (T B) C) :=
  match b with
  | Done _ _ _ c => Done A (T B') (Batch B' (T B) C) (Done B' (T B) C c)
  | Step _ _ _ rest (*:Batch A (T B) (T B -> C)*) a(*:A*) =>
      Step A (T B') (Batch B' (T B) C)
        (map (Batch A (T B'))
           (fun (x : Batch B' (T B) (T B -> C)) (t : T B') =>
              x <⋆> (toBatchM T B' B t : Batch B' (T B) (T B))
           )
           (cojoin_BatchM T A B B' (T B -> C) rest))
        (a : A)
  end.

Section spec.

  Context
    (T : Type -> Type)
    `{ToBatchM T}.

  Definition double_BatchM (A B C : Type) :
      A -> Batch A (T B) (Batch B (T C) (T C)) :=
    map (Batch A (T B)) (toBatchM T B C) ∘ batch (T B) A.

  Lemma cojoin_BatchM_spec : forall (A B B' C : Type),
      cojoin_BatchM T A B B' C =
        runBatch (Batch A (T B') ∘ Batch B' (T B)) (double_BatchM A B' B) C.
  Proof.
    intros. ext b. induction b.
    - cbn. reflexivity.
    - cbn. rewrite IHb.
      fequal.
      compose near ((runBatch (Batch A (T B') ∘ Batch B' (T B))
                (double_BatchM A B' B) (T B -> C) b)) on right.
      rewrite (fun_map_map (F := Batch A (T B'))).
      compose near ((runBatch (Batch A (T B') ∘ Batch B' (T B))
                (double_BatchM A B' B) (T B -> C) b)) on right.
      rewrite (fun_map_map (F := Batch A (T B'))).
      compose near ((runBatch (Batch A (T B') ∘ Batch B' (T B))
                (double_BatchM A B' B) (T B -> C) b)) on right.
      rewrite (fun_map_map (F := Batch A (T B'))).
      reflexivity.
  Qed.

End spec.

Section experiment.

  Context (A B B' C : Type) T `{ToBatchM T}.
  Check toBatchM T A B.
  Check map (Batch A (T B)) (toBatchM T B C).
  Check map (Batch A (T B)) (toBatchM T B C) ∘ toBatchM T A B.
  (* T A -> Batch A (T B) (Batch B (T C) (T C)) *)

  Check toBatchM T A C. (* T A -> Batch A (T C) (T C) *)
  Check cojoin_BatchM T A C B' (T C).
  Check cojoin_BatchM T A C B' (T C) ∘ toBatchM T A C.
  (*  T A -> Batch A (T B') (Batch B' (T C) (T C)) *)
  Check cojoin_BatchM T A (T C) B' C.
  Check toBatchM T A C.

  Check cojoin_Batch (B := B) ∘ toBatchM T A C.
  Check cojoin_Batch (B := B) ∘ toBatchM T A C.

End experiment.

Class TraversableMonad
  (T : Type -> Type) `{Return T} `{ToBatchM T} :=
  { trfm_ret : forall (A B : Type),
      toBatchM T A B ∘ ret T A = batch (T B) A;
    trfm_extract : forall (A : Type),
      extract_Batch ∘ mapfst_Batch A (T A) (ret T A) ∘ toBatchM T A A = @id (T A);
    trfm_duplicate : forall (A B C : Type),
      cojoin_BatchM T A C B (T C) ∘ toBatchM T A C =
        map (Batch A (T B)) (toBatchM T B C) ∘ toBatchM T A B;
  }.
