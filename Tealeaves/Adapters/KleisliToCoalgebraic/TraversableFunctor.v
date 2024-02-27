From Tealeaves Require Import
  Functors.Batch
  Classes.Kleisli.TraversableFunctor
  Classes.Coalgebraic.TraversableFunctor.

Import Batch.Notations.
Import Kleisli.TraversableFunctor.Notations.

#[local] Generalizable Variables G T M A B.

(* TODO : Standardize the Arguments *)
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch {T}%function_scope {ToBatch} {A A'}%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Traversable functors as <<Batch>> coalgebras *)
(******************************************************************************)

(** ** <<ToBatch>> instance *)
(******************************************************************************)
#[export] Instance ToBatch_Traverse `{Traverse T}
  : Coalgebraic.TraversableFunctor.ToBatch T :=
  (fun A B => traverse (G := Batch A B) (batch B) :
     T A -> Batch A B (T B)).

Class Compat_ToBatch_Traverse
  `{Traverse_inst : Traverse T}
  `{ToBatch_inst : ToBatch T} :=
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
  `{Traverse T} : Compat_ToBatch_Traverse := ltac:(hnf; reflexivity).

(** ** Laws *)
(******************************************************************************)
Section laws.

  Context
    `{Kleisli.TraversableFunctor.TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  (** *** Factoring operations through <<toBatch>> *)
  (******************************************************************************)
  Lemma traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse f = runBatch f ∘ toBatch.
  Proof.
    rewrite toBatch_to_traverse.
    rewrite trf_traverse_morphism.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary map_through_runBatch {A B : Type} (f : A -> B) :
    map f = runBatch (F := fun A => A) f ∘ toBatch.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch : forall (A : Type),
      id = runBatch (F := fun A => A) id ∘ toBatch (T := T) (A' := A).
  Proof.
    intros.
    rewrite <- trf_traverse_id.
    rewrite (traverse_through_runBatch (G := fun A => A)).
    reflexivity.
  Qed.

  (** *** Naturality of <<toBatch>> *)
  (******************************************************************************)
  Lemma toBatch_mapfst : forall (A B : Type) (f : A -> B) (C : Type),
    toBatch (A' := C) ∘ map f = mapfst_Batch f ∘ toBatch.
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite traverse_map.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism (morphism := mapfst_Batch1_Hom f)).
    rewrite ret_natural.
    reflexivity.
  Qed.

  (** *** Coalgebra laws *)
  (******************************************************************************)
  Lemma toBatch_extract_Kleisli : forall (A : Type),
      extract_Batch ∘ toBatch = @id (T A).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism (ϕ := @extract_Batch A)).
    rewrite extract_Batch_batch.
    rewrite trf_traverse_id.
    reflexivity.
  Qed.

  Lemma toBatch_duplicate_Kleisli : forall (A B C : Type),
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

  (** *** Representation theorem *)
  (******************************************************************************)

  Definition length_gen {A B}: T A -> nat :=
    length_Batch ∘ toBatch (A' := B).

  Lemma length_gen1: forall {A B B'} (t: T A),
      length_gen (B := B) t = length_gen (B := B') t.
  Proof.
    intros.
    unfold length_gen.
    unfold compose.
  Abort.

  Definition to_contents_gen {A B}:
    forall (t: T A), Vector.t A (length_gen (B := B) t) :=
    fun t => Batch_to_contents (toBatch (A' := B) t).

  Definition to_makeFn_gen {A B}:
    forall (t: T A), Vector.t B (length_gen (B := B) t) -> T B :=
    fun t => Batch_to_makeFn (toBatch (A' := B) t).

  Import Applicative.Notations.
  Import Functors.Vector.

  Theorem traverse_repr `{Applicative G} {A B C : Type}:
    forall (f: A -> G B) (t: T A),
      traverse f t =
        pure (to_makeFn_gen t) <⋆>
            traverse (T := VEC (length_gen (B := B) t)) f
                     (to_contents_gen t).
  Proof.
    intros.
    rewrite traverse_through_runBatch.
    unfold compose at 1.
    rewrite runBatch_repr.
    reflexivity.
  Qed.

End laws.
