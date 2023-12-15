From Tealeaves Require Import
  Classes.Kleisli.TraversableFunctor
  Functors.Batch.

(** * Traversable functors as <<Batch>> coalgebras *)
(******************************************************************************)
Class ToBatch (T : Type -> Type) :=
  toBatch : forall A B, T A -> Batch A B (T B).

#[global] Arguments toBatch (T)%function_scope {ToBatch} (A B)%type_scope _.

Class TraversableFunctor
  (T : Type -> Type) `{ToBatch T} :=
  { trf_extract : forall (A : Type),
      extract_Batch ∘ toBatch T A A = @id (T A);
    trf_duplicate : forall (A B C : Type),
      cojoin_Batch ∘ toBatch T A C =
        map (F := Batch A B) (toBatch T B C) ∘ toBatch T A B;
  }.
