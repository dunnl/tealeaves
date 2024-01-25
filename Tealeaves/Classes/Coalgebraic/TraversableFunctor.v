From Tealeaves Require Import
  Classes.Kleisli.TraversableFunctor
  Functors.Batch.

(** * Traversable functors as <<Batch>> coalgebras *)
(******************************************************************************)
Class ToBatch (T : Type -> Type) :=
  toBatch : forall A A', T A -> Batch A A' (T A').

#[global] Arguments toBatch {T}%function_scope {ToBatch} {A A'}%type_scope _.

Class TraversableFunctor
  (T : Type -> Type) `{ToBatch T} :=
  { trf_extract : forall (A : Type),
      extract_Batch ∘ toBatch = @id (T A);
    trf_duplicate : forall (A B C : Type),
      cojoin_Batch ∘ toBatch =
        map (toBatch (A' := C)) ∘ toBatch (A := A) (A' := B)
  }.
