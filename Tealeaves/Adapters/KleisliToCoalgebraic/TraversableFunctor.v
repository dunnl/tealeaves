From Tealeaves Require Import
  Functors.Early.Batch
  Classes.Kleisli.TraversableFunctor
  Classes.Coalgebraic.TraversableFunctor.

Import Batch.Notations.
Import Kleisli.TraversableFunctor.Notations.

#[local] Generalizable Variables G T M A B.

#[local] Arguments batch {A} (B)%type_scope _.

(** * Coalgebraic Traversable Functors From Kleisli Traversable Functors *)
(******************************************************************************)

(** ** Derived <<ToBatch>> Operation *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance ToBatch_Traverse `{Traverse T}:
    Coalgebraic.TraversableFunctor.ToBatch T :=
  (fun A B => traverse (G := Batch A B) (batch B) :
     T A -> Batch A B (T B)).

End DerivedOperations.

Class Compat_ToBatch_Traverse
  (T: Type -> Type)
  `{Traverse_inst: Traverse T}
  `{ToBatch_inst: ToBatch T} :=
  compat_toBatch_traverse :
  forall A B, @toBatch T ToBatch_inst A B =
           @traverse T Traverse_inst (Batch A B) _ _ _ A B (batch B).

Lemma toBatch_to_traverse
  `{Compat_ToBatch_Traverse T} :
  forall A B, toBatch (T := T) =
           traverse (G := Batch A B) (batch B).
Proof.
  intros.
  rewrite compat_toBatch_traverse.
  reflexivity.
Qed.

#[export] Instance Compat_ToBatch_Traverse_Self
  `{Traverse T}: Compat_ToBatch_Traverse T
                   (ToBatch_inst := DerivedOperations.ToBatch_Traverse)
  := ltac:(hnf; reflexivity).

(** ** Derived Laws *)
(******************************************************************************)
Module DerivedInstances.
  Section instances.


    Context
      `{Traverse T}
      `{ToBatch T}
      `{! Kleisli.TraversableFunctor.TraversableFunctor T}
      `{! Compat_ToBatch_Traverse T}.

    (** *** Coalgebra laws *)
    (******************************************************************************)
    Lemma toBatch_extract_Kleisli: forall (A: Type),
        extract_Batch ∘ toBatch = @id (T A).
    Proof.
      intros.
      rewrite toBatch_to_traverse.
      rewrite (trf_traverse_morphism (ϕ := @extract_Batch A)).
      rewrite extract_Batch_batch.
      rewrite trf_traverse_id.
      reflexivity.
    Qed.

    Lemma toBatch_duplicate_Kleisli: forall (A B C: Type),
        cojoin_Batch ∘ toBatch =
          map (F := Batch A B) (toBatch (A' := C)) ∘ toBatch (A' := B).
    Proof.
      intros.
      rewrite toBatch_to_traverse.
      rewrite (trf_traverse_morphism (ϕ := @cojoin_Batch A B C)).
      rewrite cojoin_Batch_batch.
      rewrite toBatch_to_traverse.
      rewrite toBatch_to_traverse.
      rewrite (trf_traverse_traverse (G1 := Batch A B) (G2 := Batch B C)).
      reflexivity.
    Qed.

    #[export] Instance Coalgebraic_Traversable_of_Kleisli :
      Coalgebraic.TraversableFunctor.TraversableFunctor T :=
      {| trf_extract := toBatch_extract_Kleisli;
         trf_duplicate := toBatch_duplicate_Kleisli;
      |}.

  End instances.
End DerivedInstances.
