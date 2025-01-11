From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.Theory.DecoratedTraversableFunctor
  Classes.Coalgebraic.DecoratedTraversableFunctor.
From Tealeaves Require Export
  Classes.Coalgebraic.TraversableFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor.

Import Product.Notations.
Import Kleisli.DecoratedTraversableFunctor.Notations.
Import Batch.Notations.
Import Monoid.Notations.
Import Subset.Notations.

#[local] Generalizable Variables E G T M A B.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Decorated traversable functors as coalgebras *)
(******************************************************************************)
#[export] Instance ToBatch6_Mapdt `{Mapdt E T}
    : Coalgebraic.DecoratedTraversableFunctor.ToBatch6 E T :=
  (fun A B => mapdt (G := Batch (E * A) B) (batch B) : T A -> Batch (E * A) B (T B)).

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    `{Map_inst: Map T}
     `{Mapd_inst: Mapd E T}
     `{Traverse_inst: Traverse T}
     `{Mapdt_inst: Mapdt E T}
     `{Subset_inst: ToSubset T}
     `{! Compat_Map_Mapdt}
     `{! Compat_Mapd_Mapdt}
     `{! Compat_Traverse_Mapdt}
     `{! Compat_ToSubset_Traverse T}
     `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

  Theorem toBatch6_toBatch
    {A B} `{ToBatch T} `{! Compat_ToBatch_Traverse T}:
    toBatch (T := T) (A := A) (A' := B) =
      mapfst_Batch extract ∘ toBatch6 (T := T) (A := A).
  Proof.
    rewrite toBatch_to_traverse.
    rewrite traverse_to_mapdt.
    unfold toBatch6, ToBatch6_Mapdt.
    rewrite <- (kdtfun_morph (T := T)
                 (ϕ := fun X =>
                         mapfst_Batch (B := B) (C := X)
                           (A1 := E * A) (A2 := A)
                           (extract (W := prod E) (A := A)))
                 (batch B)).
    reflexivity.
  Qed.

  Theorem mapdt_through_runBatch `{Applicative G} `(f : E * A -> G B) :
    mapdt f = runBatch f ∘ toBatch6.
  Proof.
    intros. unfold_ops @ToBatch6_Mapdt.
    rewrite <- kdtfun_morph.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse f = runBatch (f ∘ extract (W := (E ×))) ∘ toBatch6.
  Proof.
    rewrite traverse_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapd_through_runBatch `(f : E * A -> B) :
      mapd f = runBatch (F := fun A => A) f ∘ toBatch6.
  Proof.
    intros.
    rewrite mapd_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
      map f = runBatch (F := fun A => A) (f ∘ extract) ∘ toBatch6.
  Proof.
    intros.
    rewrite map_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  (** *** <<foldMapd>> a special case of <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMapd_through_runBatch1 {A} `{Monoid M} : forall `(f : E * A -> M),
      foldMapd f = runBatch (F := const M) f (C := T False) ∘ toBatch6 (B := False).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_through_runBatch (G := const M)).
    reflexivity.
  Qed.

  Lemma foldMapd_through_runBatch2 `{Monoid M} : forall (A fake : Type) `(f : E * A -> M),
      foldMapd f = runBatch (F := const M) f (C := T fake) ∘ toBatch6 (B := fake).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_constant_applicative2 False False fake).
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  (** *** Factoring through <<runBatch>> *)
  (******************************************************************************)
  Corollary toctxlist_through_runBatch6 {A : Type} (tag : Type) :
    toctxlist = runBatch (B := tag) (F := const (list (E * A))) (ret (T := list))
                  ∘ toBatch6.
  Proof.
    rewrite (toctxlist_to_mapdt2 A tag).
    now rewrite mapdt_through_runBatch.
  Qed.


  Corollary toctxset_through_runBatch1 {A : Type} :
    toctxset (F := T) = runBatch (B := False) (F := const (subset (E * A)))
                                (ret (T := subset)) ∘ toBatch6.
  Proof.
    rewrite (toctxset_to_mapdt1 A).
    now rewrite (mapdt_through_runBatch).
  Qed.

  Corollary toctxset_through_runBatch2 {A tag : Type} :
    toctxset (F := T) = runBatch (B := tag) (F := const (subset (E * A)))
                                (ret (T := subset)) ∘ toBatch6.
  Proof.
    rewrite (toctxset_to_mapdt2 A tag).
    now rewrite (mapdt_through_runBatch).
  Qed.

  Corollary ctx_elements_through_runBatch1 {A : Type} {p:E * A}:
    element_ctx_of (T := T) p =
      runBatch (B := False) (F := const Prop)
        (H0 := @Mult_const _ Monoid_op_or)
        (H1 := @Pure_const _ Monoid_unit_false)
        {{p}} ∘ toBatch6.
  Proof.
    rewrite element_ctx_of_to_foldMapd.
    rewrite foldMapd_through_runBatch1.
    reflexivity.
  Qed.

End runBatch.

From Tealeaves Require Import
  Classes.Coalgebraic.TraversableFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor.

(** ** Relating <<toBatch6>> with <<toBatch>> *)
(******************************************************************************)
(*
Lemma toBatch6_toBatch
  `{Traverse_inst: Traverse T}
  `{Mapdt_inst: Mapdt E T}
  `{ToBatch_inst: ToBatch T}
  `{! Compat_Traverse_Mapdt}
  `{! Compat_ToBatch_Traverse}
  `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  {A B : Type} :
  toBatch (A := A) (A' := B) = mapfst_Batch extract ∘ toBatch6.
Proof.
  intros.
  unfold_ops @ToBatch6_Mapdt.
  rewrite toBatch_to_traverse.
  rewrite traverse_to_mapdt.
  rewrite <- (kdtfun_morph
               (G1 := Batch (E * A) B)
               (G2 := Batch A B)
               (ϕ := fun C => mapfst_Batch extract)).
  rewrite ret_natural.
  reflexivity.
Qed.
*)

Lemma runBatch_toBatch6
  `{Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  `{Applicative G} `(f : E * A -> G B) :
  runBatch f ∘ toBatch6 = mapdt (E := E) (T := T) f.
Proof.
  intros.
  unfold_ops @ToBatch6_Mapdt.
  rewrite <- kdtfun_morph.
  rewrite (runBatch_batch G).
  reflexivity.
Qed.

(** ** Naturality of <<toBatchDM>> *)
(******************************************************************************)Lemma toBatch6_mapdt
  `{Mapdt_inst: Mapdt E T}
  `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  `{Applicative G}
  {A A' B : Type} (f : E * A -> G A') :
  map (F := G) (toBatch6 (A := A') (B := B)) ∘ mapdt (T := T) f =
    traverse (T := BATCH1 B (T B)) (strength ∘ cobind f) ∘ toBatch6.
Proof.
  rewrite (traverse_spec G).
  rewrite (runBatch_toBatch6 (A := A) (E := E) (T := T)
             (B := B) (G := G ∘ Batch (E * A') B)).
  unfold_ops @ToBatch6_Mapdt.
  rewrite kdtfun_mapdt2.
  unfold kc6.
  reflexivity.
Qed.

Lemma toBatch6_mapd
  `{Mapd_inst: Mapd E T}
  `{Mapdt_inst: Mapdt E T}
  `{! Compat_Mapd_Mapdt}
  `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  {A A' B : Type} (f : E * A -> A') :
  toBatch6 ∘ mapd (T := T) f =
    mapfst_Batch (cobind f) ∘ toBatch6 (A := A) (B := B).
Proof.
  unfold_ops @ToBatch6_Mapdt.
  rewrite mapdt_mapd.
  rewrite <- (kdtfun_morph
             (G1 := Batch (E * A) B)
             (G2 := Batch (E * A') B)
             (ϕ := fun C => mapfst_Batch (cobind f))).
  reflexivity.
Qed.

Lemma toBatch6_map
  `{Map_inst: Map T}
  `{Mapdt_inst: Mapdt E T}
  `{! Compat_Map_Mapdt}
  `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  {A A' B : Type} (f : A -> A') {C : Type} :
  toBatch6 ∘ map (F := T) f = mapfst_Batch (map f) ∘ toBatch6 (A := A) (B := B).
Proof.
  unfold_ops @ToBatch6_Mapdt.
  rewrite mapdt_map.
  rewrite <- (kdtfun_morph (H6 := mapfst_Batch1_Hom (map f))
               (ϕ := fun C => mapfst_Batch (map f))).
  rewrite ret_natural.
  reflexivity.
Qed.

Lemma toBatch6_mapfst3
  `{Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctorFull E T}
  `{ToBatch_inst: ToBatch T}
  `{! Compat_ToBatch_Traverse T}
  {A A' B : Type} (f : E * A -> A') :
  toBatch (A := A') (A' := B) ∘ mapd (T := T) f =
    mapfst_Batch f ∘ toBatch6 (T := T) (A := A) (B := B).
Proof.
  rewrite toBatch6_toBatch.
  reassociate -> on left.
  rewrite toBatch6_mapd.
  reassociate <-.
  rewrite (mapfst_mapfst_Batch).
  rewrite (kcom_cobind0).
  reflexivity.
Qed.

(** ** Coalgebra laws *)
(******************************************************************************)
Section to_coalgebraic.

  Context
    `{Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctorFull E T}
      `{ToBatch_inst: ToBatch T}
      `{! Compat_ToBatch_Traverse T}.

  Lemma double_Batch6_spec : forall A B C,
      double_batch6 (E := E) (A := A) (B := B) C = batch C ⋆6 batch B.
  Proof.
    intros. unfold double_batch6. now ext [e a].
  Qed.

  Lemma toBatch6_extract_Kleisli : forall (A : Type),
      extract_Batch ∘ mapfst_Batch (extract (W := (E ×))) ∘ toBatch6 = @id (T A).
  Proof.
    intros.
    reassociate -> on left.
    rewrite <- toBatch6_toBatch.
    rewrite trf_extract.
    reflexivity.
  Qed.

  Lemma toBatch6_duplicate_Kleisli : forall (A B C : Type),
      cojoin_Batch6 ∘ toBatch6 (A := A) (B := C) =
        map (F := Batch (E * A) B) (toBatch6) ∘ toBatch6.
    intros.
    unfold_ops @ToBatch6_Mapdt.
    erewrite <- (kdtfun_morph (T := T) (E := E) (B := C)
               (G1 := Batch (E * A) C)
               (G2 := Batch (E * A) B ∘ Batch (E * B) C)
               (ϕ := @cojoin_Batch6 E _ _ A C B)).
    - rewrite (kdtfun_mapdt2 _ _).
      rewrite <- double_Batch6_spec.
      rewrite <- (cojoin_Batch6_batch (E := E) (T := T)).
      reflexivity.
      Unshelve.
      all:eauto with typeclass_instances.
  Qed.

  #[export] Instance Coalgebraic_DecoratedTraversableFunctor_of_Kleisli :
    Coalgebraic.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T :=
    {| dtf_extract := toBatch6_extract_Kleisli;
       dtf_duplicate := toBatch6_duplicate_Kleisli;
    |}.

End to_coalgebraic.
