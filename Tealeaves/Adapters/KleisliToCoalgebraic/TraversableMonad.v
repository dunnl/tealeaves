From Tealeaves Require Import
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableMonad
  Functors.Early.Batch.

Import Functors.Early.Batch.Notations.
Import Kleisli.TraversableMonad.Notations.

#[local] Generalizable Variables G U T M A B.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch6 {T U}%function_scope {ToBatch6} {A} (B)%type_scope _.

(** * Coalgebraic Traversable Monads *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance ToBatch6_Bindt `{Bindt T U}
 : Coalgebraic.TraversableMonad.ToBatch6 T U :=
  (fun A B => bindt (G := Batch A (T B)) (batch (T B)): U A -> Batch A (T B) (U B)).

End DerivedOperations.

(** ** Derived Laws *)
(******************************************************************************)
Module DerivedInstances.

  Import DerivedOperations.

  Section to_coalgebraic.

    Context
      `{Kleisli.TraversableMonad.TraversableMonad T}
      `{Map U}
      `{Bindt T U}
      `{! Compat_Map_Bindt T U}
      `{! Kleisli.TraversableMonad.TraversableRightPreModule T U}.

    Lemma double_batch6_spec: forall A B C,
        double_batch6 (A := A) = batch (T C) ⋆6 batch (T B).
    Proof.
      reflexivity.
    Qed.

    Lemma toBatch6_ret_Kleisli: forall A B: Type,
        toBatch6 B ∘ ret (T := T) (A := A) = batch (T B).
    Proof.
      intros.
      unfold_ops @ToBatch6_Bindt.
      rewrite (ktm_bindt0 A).
      reflexivity.
    Qed.

    Lemma toBatch6_extract_Kleisli: forall (A: Type),
        extract_Batch ∘ mapfst_Batch _ _ ret ∘ toBatch6 A = @id (U A).
    Proof.
      intros.
      reassociate -> on left.
      unfold_ops @ToBatch6_Bindt.
      rewrite (ktm_morph
                 (G1 := Batch A (T A))
                 (G2 := Batch (T A) (T A))
                 (morphism := ApplicativeMorphism_mapfst_Batch
                                (ret (T := T) (A := A)))
                 A A
                 (batch (T A))).
      rewrite (ktm_morph
                 (G1 := Batch (T A) (T A))
                 (G2 := fun A => A)
                 (morphism := ApplicativeMorphism_extract_Batch (T A))).
      reassociate <- on left.
      assert (cut: extract_Batch ∘ mapfst_Batch A (T A) ret ∘ batch (T A)
              = ret).
      { ext a. unfold compose. reflexivity. }
      rewrite cut.
      rewrite ktm_bindt1.
      reflexivity.
    Qed.

    Lemma toBatch6_duplicate_Kleisli: forall (A B C: Type),
        cojoin_Batch6 A B C (R := U C) ∘ toBatch6 (T := T) C =
          map (F := Batch A (T B)) (toBatch6 C) ∘ toBatch6 (U := U) B.
    Proof.
      intros.
      unfold_ops @ToBatch6_Bindt.
      change (Batch A (T B) (Batch B (T C) ?x))
        with ((Batch A (T B) ∘ Batch B (T C)) x).
      erewrite (ktm_morph (T := T)
                  (G1 := Batch A (T C))
                  (G2 := Batch A (T B) ∘ Batch B (T C))
                  (morphism := ApplicativeMorphism_cojoin_Batch6 _ _ _)
                  (ϕ := @cojoin_Batch6 T _ A B C)).
      unfold_compose_in_compose.
      rewrite (cojoin_Batch6_batch).
      rewrite (ktm_bindt2 _ _).
      rewrite double_batch6_spec.
      reflexivity.
    Qed.

  End to_coalgebraic.

  (** ** Typeclass Instances *)
  (******************************************************************************)
    Section instances.

      Context
        `{Return T}
        `{Map T}
        `{Bindt T T}
        `{! Compat_Map_Bindt T T}
        `{! Kleisli.TraversableMonad.TraversableMonad T}
        `{Map U}
        `{Bindt T U}
        `{! Compat_Map_Bindt T U}
        `{! Kleisli.TraversableMonad.TraversableRightPreModule T U}.

      #[export] Instance:
        Coalgebraic.TraversableMonad.TraversableRightPreModule T T :=
        {| trfm_extract := toBatch6_extract_Kleisli;
          trfm_duplicate := toBatch6_duplicate_Kleisli;
        |}.

      #[export] Instance Coalgebraic_TraversableRightPreModule_of_Kleisli :
        Coalgebraic.TraversableMonad.TraversableRightPreModule T U :=
        {| trfm_extract := toBatch6_extract_Kleisli;
          trfm_duplicate := toBatch6_duplicate_Kleisli;
        |}.

      #[export] Instance Coalgebraic_TraversableMonad_of_Kleisli :
        Coalgebraic.TraversableMonad.TraversableMonad T :=
        {| trfm_ret := toBatch6_ret_Kleisli;
        |}.

      #[export] Instance Coalgebraic_TraversableRightModule_of_Kleisli :
        Coalgebraic.TraversableMonad.TraversableRightModule T U :=
        {| trfmod_monad := _
        |}.

    End instances.

End DerivedInstances.

