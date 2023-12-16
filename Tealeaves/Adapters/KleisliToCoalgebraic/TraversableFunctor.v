From Tealeaves Require Export
  Misc.Prop
  Functors.Subset
  Functors.List
  Functors.Batch
  Classes.Kleisli.TraversableFunctor.

From Tealeaves Require Import
  Classes.Coalgebraic.TraversableFunctor.

Import TraversableFunctor.Notations.
Import Batch.Notations.

#[local] Generalizable Variables G T M A B.
#[local] Existing Instances TraversableFunctor.TraversableFunctorMakeFull.

#[local] Arguments map {F}%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments traverse {T}%function_scope {Traverse} {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch {T}%function_scope {ToBatch} {A} (B)%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Traversable functors as <<Batch>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatch_Traverse `{Traverse T}
  : Coalgebraic.TraversableFunctor.ToBatch T :=
  (fun A B => traverse (G := Batch A B) (batch B) : T A -> Batch A B (T B)).

Section with_functor.

  Context
    `{Kleisli.TraversableFunctor.TraversableFunctorFull T}.

  (** ** Factoring operations through <<toBatch>> *)
  (******************************************************************************)
  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse f = runBatch f ∘ toBatch B.
  Proof.
    unfold_ops @ToBatch_Traverse.
    rewrite (trf_traverse_morphism (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary map_to_runBatch {A B : Type} (f : A -> B) :
    map f = runBatch (F := fun A => A) f ∘ toBatch B.
  Proof.
    rewrite trff_map_to_traverse.
    rewrite (traverse_to_runBatch (G := fun A => A)).
    reflexivity.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
      id (A := T A) = runBatch id ∘ toBatch A.
  Proof.
    intros. rewrite <- (trf_traverse_id (T := T)).
    rewrite (traverse_to_runBatch (G := fun A => A)).
    reflexivity.
  Qed.

  (** ** Naturality of <<toBatch>> *)
  (******************************************************************************)
  Lemma toBatch_mapfst
    {A B : Type} (f : A -> B) {C : Type} :
    toBatch C ∘ map f = mapfst_Batch f ∘ toBatch C.
  Proof.
    unfold_ops @ToBatch_Traverse.
    rewrite (traverse_map T (Batch B C)).
    rewrite (traverse_to_runBatch (G := Batch B C)).
    rewrite (traverse_to_runBatch (G := Batch A C)).
    ext t.
    unfold compose.
    induction (toBatch C t).
    - cbv. reflexivity.
    - do 2 rewrite runBatch_rw2. rewrite IHb.
      now rewrite mapfst_Batch2.
  Qed.

  (** ** Coalgebra laws *)
  (******************************************************************************)
  Lemma toBatch_extract_Kleisli : forall (A : Type),
      extract_Batch ∘ toBatch A = @id (T A).
  Proof.
    intros.
    unfold_ops @ToBatch_Traverse.
    rewrite (trf_traverse_morphism (ϕ := @extract_Batch A)).
    rewrite trf_traverse_id.
    reflexivity.
  Qed.

  Lemma toBatch_duplicate_Kleisli : forall (A B C : Type),
      cojoin_Batch ∘ toBatch C =
        map (F := Batch A B) (toBatch C) ∘ toBatch B.
  Proof.
    intros.
    unfold_ops @ToBatch_Traverse.
    rewrite (trf_traverse_morphism (ϕ := @cojoin_Batch A B C)).
    rewrite cojoin_Batch_batch.
    rewrite (trf_traverse_traverse (G1 := Batch A B) (G2 := Batch B C)).
    reflexivity.
  Qed.

  #[export] Instance Coalgebraic_Traversable_of_Kleisli :
    Coalgebraic.TraversableFunctor.TraversableFunctor T :=
    {| trf_extract := toBatch_extract_Kleisli;
       trf_duplicate := toBatch_duplicate_Kleisli;
    |}.

End with_functor.
