From Tealeaves Require Export
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Kleisli.TraversableFunctor.

#[local] Generalizable Variable T G A B C ϕ M.

Import TraversableFunctor.Notations.

(** * Commutative/Idempotent-Traversable Functors *)
(******************************************************************************)

(** ** The <<traverse>> Operation *)
(** The operation is Classes.Kleisli.TraversableFunctor.Traverse *)
(******************************************************************************)

(** ** Kleisli Composition *)
(** The operation is Classes.Kleisli.TraversableFunctor.kc2 *)
(******************************************************************************)

(** ** Typeclass *)
(******************************************************************************)
Class TraversableCommIdemFunctor (T: Type -> Type) `{Traverse T} :=
  { trfci_traverse_id: forall (A: Type),
      traverse (G := fun A => A) id = @id (T A);
    trfci_traverse_traverse :
    forall `{ApplicativeCommutativeIdempotent G1}
      `{ApplicativeCommutativeIdempotent G2}
      (A B C: Type) (g: B -> G2 C) (f: A -> G1 B),
      map (traverse g) ∘ traverse f = traverse (T := T) (G := G1 ∘ G2) (g ⋆2 f);
    trfci_traverse_morphism :
    forall `{morphism: ApplicativeMorphism G1 G2 ϕ} (A B: Type) (f: A -> G1 B),
      ϕ (T B) ∘ traverse f = traverse (ϕ B ∘ f);
  }.
