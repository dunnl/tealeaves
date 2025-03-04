From Tealeaves Require Export
  Classes.Functor
  Functors.Batch2.

(** * Coalgebraic Traversable Functors *)
(**********************************************************************)

(** ** <<toBatch>> Operation *)
(**********************************************************************)
Class ToBatch2 (T: Type -> Type -> Type) :=
  toBatch2: forall B B' A A', T B A -> Batch2 B B' A A' (T B' A').

#[global] Arguments toBatch2 {T}%function_scope {ToBatch2}
  {B B' A A'}%type_scope _.

(** ** Typeclass *)
(**********************************************************************)
Class TraversableFunctor2
  (T: Type -> Type -> Type)
  `{ToBatch_T: ToBatch2 T} :=
  { trf_extract: forall (A: Type),
      extract_Batch2 ∘ toBatch = @id (T A);
    trf_duplicate: forall (A B C: Type),
      cojoin_Batch ∘ toBatch =
        map (toBatch (A' := C)) ∘ toBatch (A := A) (A' := B)
  }.
