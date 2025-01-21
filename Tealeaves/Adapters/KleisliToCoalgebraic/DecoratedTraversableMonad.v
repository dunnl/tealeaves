From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Coalgebraic.DecoratedTraversableMonad
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Functors.Early.Batch.

Import Product.Notations.
Import Kleisli.DecoratedTraversableMonad.Notations.
Import Kleisli.Comonad.Notations.
Import Batch.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables U W G T M A B.

#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch7 {W}%type_scope {T U}%function_scope {ToBatch7} {A B}%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * DecoratedTraversableMonads as <<Batch7>> coalgebras *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance ToBatch7_Binddt
    `{Binddt_WTU: Binddt W T U}:
  Coalgebraic.DecoratedTraversableMonad.ToBatch7 W T U :=
  (fun A B => binddt (G := Batch (W * A) (T B))
             (batch (T B)): U A -> Batch (W * A) (T B) (U B)).

End DerivedOperations.

(** ** Specification for <<binddt>> via <<toBatch7>> *)
(******************************************************************************)
Section binddt_spec.

  Import DerivedOperations.

  Context
    `{Binddt W T T}
    `{Binddt W T U}
    `{Monoid W}
    `{Return T}
    `{! DecoratedTraversableRightPreModule W T U}.

  Lemma binddt_toBatch7_spec:
    forall (G: Type -> Type) `{Applicative G}
      (A B: Type) (f: W * A -> G (T B)),
      binddt (T := T) (U := U) f =
        map (F := G) (extract_Batch) ∘
          traverse (T := BATCH1 (T B) (U B)) f ∘ toBatch7.
  Proof.
    intros.
    unfold_ops @ToBatch7_Binddt.
    rewrite <- runBatch_via_traverse.
    rewrite (kdtm_morph (Batch (W * A) (T B)) G
               (morph := ApplicativeMorphism_runBatch)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary bindd_toBatch7_spec:
    forall (A B: Type) (f: W * A -> T B),
      binddt (G := fun A => A) (T := T) (U := U) f =
        extract_Batch ∘ mapfst_Batch f ∘ toBatch7.
  Proof.
    intros.
    rewrite (binddt_toBatch7_spec (fun A => A)).
    unfold_ops @Map_I.
    fequal.
    fequal.
    rewrite <- TraversableFunctor.map_to_traverse.
    reflexivity.
  Qed.

End binddt_spec.

(** ** Coalgebra laws *)
(******************************************************************************)
Section to_coalgebraic.

  Import DerivedOperations.

  Context
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

  Lemma double_Batch7_spec: forall (A B C: Type),
      double_batch7 (A := A) (A' := B) =
        batch (T C) ⋆7 (batch (T B)).
  Proof.
    intros.
    unfold double_batch7.
    ext [w a].
    cbn.
    change (?f ∘ id) with f.
    unfold_ops @ToBatch7_Binddt.
    rewrite (kdtm_morph
               (Batch (W * B) (T C))
               (Batch (W * B) (T C))
               (ϕ := fun C => mapfst_Batch (incr w))).
    rewrite ret_natural.
    reflexivity.
  Qed.

  Lemma toBatch7_ret_Kleisli: forall A B: Type,
      toBatch7 ∘ ret (T := T) (A := A) = batch (T B) ∘ ret (T := (W ×)).
  Proof.
    intros.
    unfold_ops @ToBatch7_Binddt.
    rewrite kdtm_binddt0.
    reflexivity.
  Qed.

  Lemma toBatch7_extract_Kleisli: forall (A: Type),
      extract_Batch ∘ mapfst_Batch (ret ∘ extract (W := (W ×)))
        ∘ toBatch7 = @id (T A).
  Proof.
    intros.

    rewrite <- bindd_toBatch7_spec.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma toBatch7_duplicate_Kleisli: forall (A B C: Type),
      cojoin_Batch7 ∘ toBatch7 (A := A) (B := C) =
        map (F := Batch (W * A) (T B)) toBatch7 ∘ toBatch7.
  Proof.
    intros.
    rewrite cojoin_Batch7_to_runBatch.
    unfold toBatch7 at 1.
    unfold ToBatch7_Binddt.
    rewrite (kdtm_morph (U := T) (T := T) (W := W) (A := A) (B := C)
               (Batch (W * A) (T C))
               (Batch (W * A) (T B) ∘ Batch (W * B) (T C))
               (morph := ApplicativeMorphism_runBatch)).
    rewrite (runBatch_batch _).
    rewrite double_Batch7_spec.
    unfold toBatch7 at 1 2.
    rewrite (kdtm_binddt2 _ _).
    reflexivity.
  Qed.

  #[export] Instance Coalgebraic_DecoratedTraversableMonad_of_Kleisli :
    Coalgebraic.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
    {| dtm_ret := toBatch7_ret_Kleisli;
       dtm_extract := toBatch7_extract_Kleisli;
       dtm_duplicate := toBatch7_duplicate_Kleisli;
    |}.

End to_coalgebraic.
