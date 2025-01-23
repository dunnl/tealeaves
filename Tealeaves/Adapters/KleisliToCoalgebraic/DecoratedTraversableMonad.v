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

Class Compat_ToBatch7_Binddt
  (W: Type)
  (T: Type -> Type)
  (U: Type -> Type)
  `{Binddt_inst: Binddt W T U}
  `{ToBatch7_inst: ToBatch7 W T U} :=
  compat_toBatch7_binddt:
    ToBatch7_inst = DerivedOperations.ToBatch7_Binddt.

Lemma toBatch7_to_binddt
  `{Compat_ToBatch7_Binddt W T U} :
  forall A B, toBatch7 (W := W) (T := T) (U := U) =
           binddt (G := Batch (W * A) (T B)) (batch (T B)).
Proof.
  intros.
  rewrite compat_toBatch7_binddt.
  reflexivity.
Qed.

#[export] Instance Compat_ToBatch7_Binddt_Self
  `{Binddt W T U}:
  Compat_ToBatch7_Binddt W T U
    (ToBatch7_inst := DerivedOperations.ToBatch7_Binddt)
  := ltac:(hnf; reflexivity).

Section dtm_coalgebraic_laws.

  Context
    `{Binddt W T T}
    `{Binddt W T U}
    `{Monoid W}
    `{Return T}
    `{! Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}
    `{! DecoratedTraversableRightPreModule W T U}.

  Context
    `{ToBatch7_WTT: ToBatch7 W T T}
    `{ToBatch7_WTU: ToBatch7 W T U}
    `{! Compat_ToBatch7_Binddt W T T}
    `{! Compat_ToBatch7_Binddt W T U}.

  (** ** Coalgebra laws *)
  (******************************************************************************)
  Lemma double_Batch7_spec: forall (A B C: Type),
      double_batch7 (A := A) (A' := B) =
        batch (T C) ⋆7 (batch (T B)).
  Proof.
    intros.
    unfold double_batch7.
    ext [w a].
    cbn.
    change (?f ∘ id) with f.
    rewrite toBatch7_to_binddt.
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
    rewrite toBatch7_to_binddt.
    rewrite kdtm_binddt0.
    reflexivity.
  Qed.

  Lemma toBatch7_extract_Kleisli: forall (A: Type),
      extract_Batch ∘ mapfst_Batch (ret ∘ extract (W := (W ×)))
        ∘ toBatch7 = @id (T A).
  Proof.
    intros.
    rewrite toBatch7_to_binddt.
    reassociate -> on left.
    rewrite (kdtm_morph (U := T) (B := A)
               (Batch (W * A) (T A))
               (Batch (T A) (T A))
               (ϕ := fun C => mapfst_Batch (ret ∘ extract))).
    rewrite (kdtm_morph (U := T) (B := A)
               (Batch (T A) (T A))
               (fun A => A)
               (ϕ := fun C => extract_Batch)).
    rewrite ret_natural.
    reassociate <- on left.
    rewrite extract_Batch_batch.
    change (id ∘ ?f) with f.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma toBatch7_duplicate_Kleisli: forall (A B C: Type),
      cojoin_Batch7 ∘ toBatch7 (A := A) (B := C) =
        map (F := Batch (W * A) (T B)) toBatch7 ∘ toBatch7.
  Proof.
    intros.
    rewrite cojoin_Batch7_to_runBatch.
    rewrite toBatch7_to_binddt.
    rewrite toBatch7_to_binddt.
    rewrite toBatch7_to_binddt.
    rewrite double_Batch7_spec.
    rewrite (kdtm_morph (U := U) (T := T) (W := W) (A := A) (B := C)
               (Batch (W * A) (T C))
               (Batch (W * A) (T B) ∘ Batch (W * B) (T C))
               (morph := ApplicativeMorphism_runBatch)).
    rewrite (runBatch_batch _).
    rewrite (kdtm_binddt2 _ _).
    reflexivity.
  Qed.

End dtm_coalgebraic_laws.

Module DerivedInstances.
  Section instances.

    Context
      `{Binddt W T T}
      `{Binddt W T U}
      `{Monoid W}
      `{Return T}
      `{! Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}
      `{! DecoratedTraversableRightPreModule W T U}.

    Context
      `{ToBatch7_WTT: ToBatch7 W T T}
      `{ToBatch7_WTU: ToBatch7 W T U}
      `{! Compat_ToBatch7_Binddt W T T}
      `{! Compat_ToBatch7_Binddt W T U}.

    #[export] Instance Coalgebraic_DecoratedTraversableMonad_of_Kleisli :
      Coalgebraic.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
      {| dtm_ret := toBatch7_ret_Kleisli;
         dtm_extract := toBatch7_extract_Kleisli;
         dtm_duplicate := toBatch7_duplicate_Kleisli;
      |}.


  (*
  #[export] Instance Coalgebraic_DecoratedTraversableMonad_of_Kleisli :
    Coalgebraic.DecoratedTraversableMonad.DecoratedTraversableRightModule W T U :=
    {| dtm_ret := toBatch7_ret_Kleisli;
       dtm_extract := toBatch7_extract_Kleisli;
       dtm_duplicate := toBatch7_duplicate_Kleisli;
    |}.
   *)

  End instances.
End DerivedInstances.
