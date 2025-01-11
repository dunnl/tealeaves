From Tealeaves Require Import
  Functors.Batch
  Functors.Subset
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Coalgebraic.TraversableFunctor.

Import Batch.Notations.
Import Subset.Notations.
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
#[local] Instance ToBatch_Traverse `{Traverse T}
  : Coalgebraic.TraversableFunctor.ToBatch T :=
  (fun A B => traverse (G := Batch A B) (batch B) :
     T A -> Batch A B (T B)).

Class Compat_ToBatch_Traverse (T: Type -> Type)
  `{Traverse_inst : Traverse T}
  `{ToBatch_inst : ToBatch T} :=
  compat_toBatch_traverse:
    @ToBatch_inst = @ToBatch_Traverse T Traverse_inst.

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
  `{Traverse T} : Compat_ToBatch_Traverse T := ltac:(hnf; reflexivity).

(** ** Laws *)
(******************************************************************************)
Section laws.

  Context
    `{Map T}
      `{ToBatch T}
      `{Traverse T}
      `{! Kleisli.TraversableFunctor.TraversableFunctor T}
      `{! Compat_Map_Traverse T}
      `{! Compat_ToBatch_Traverse T}.

  (** *** Factoring operations through <<toBatch>> *)
  (******************************************************************************)
  Lemma traverse_through_runBatch
    `{Applicative G} `(f : A -> G B) :
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

  (** *** Factoring derived operations through <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMap_through_runBatch1 {A : Type} `{Monoid M} : forall `(f : A -> M),
      foldMap f = runBatch (F:= const M) f (B := False) ∘
                    toBatch (A := A) (A' := False).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_through_runBatch2 `{Monoid M} : forall (A fake : Type) `(f : A -> M),
      foldMap f = runBatch (F := const M) f (B := fake) ∘
                    toBatch (A' := fake).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    change (fun _ : Type => M) with (const (A := Type) M).
    rewrite (traverse_const1 fake).
    rewrite (traverse_through_runBatch (G := const M)).
    reflexivity.
  Qed.


  Corollary tolist_through_runBatch {A : Type} (tag : Type) `(t : T A) :
    tolist t =
      runBatch (F := const (list A))
        (ret (T := list) : A -> const (list A) tag)
        (B := tag) (toBatch (A' := tag) t).
  Proof.
    rewrite (tolist_to_traverse2 A tag).
    rewrite (traverse_through_runBatch (G := const (list A))).
    reflexivity.
  Qed.

  Context
    `{ToSubset T}
      `{! Compat_ToSubset_Traverse T}.

  Lemma tosubset_through_runBatch1 : forall (A : Type),
      tosubset =
        runBatch (F := const (A -> Prop))
          (ret (T := subset) (A := A)) (B := False) ∘
          toBatch (A' := False).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_through_runBatch1.
    reflexivity.
  Qed.

  Lemma tosubset_through_runBatch2 : forall (A tag : Type),
      tosubset =
        runBatch (F := const (A -> Prop))
          (ret (T := subset)) (B := tag) ∘
          toBatch (A' := tag).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite (foldMap_through_runBatch2 A tag).
    reflexivity.
  Qed.

  (** *** Naturality of <<toBatch>> *)
  (******************************************************************************)
  Lemma toBatch_mapfst : forall (A B A' : Type) (f : A -> B),
      toBatch (A := B) (A' := A') ∘ map f =
        mapfst_Batch f ∘ toBatch (A := A) (A' := A').
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite traverse_map.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism (morphism := mapfst_Batch1_Hom f)).
    rewrite ret_natural.
    reflexivity.
  Qed.

  Lemma toBatch_mapsnd: forall (X A A' : Type) (f : A -> A'),
      mapsnd_Batch f ∘ toBatch =
        map (map f) ∘ toBatch (A := X) (A' := A).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism (morphism := mapsnd_Batch2_Hom f)).
    rewrite ret_dinatural.
    rewrite toBatch_to_traverse.
    rewrite map_traverse.
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

End laws.
