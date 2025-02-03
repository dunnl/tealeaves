From Tealeaves Require Import
  Classes.Categorical.Applicative
  Classes.Categorical.Monad (Return, ret)
  Classes.Kleisli.TraversableMonad
  Functors.Early.Batch.

Import Batch.Notations.
Import Applicative.Notations.
Import TraversableMonad.Notations.

#[local] Generalizable Variables T U.

(** * Coalgebraic Traversable Monads *)
(**********************************************************************)

(** ** Operation <<toBatch6>> *)
(**********************************************************************)
Class ToBatch6 (T U: Type -> Type) :=
  toBatch6: forall A B, U A -> Batch A (T B) (U B).

#[global] Arguments toBatch6 {T U}%function_scope {ToBatch6}
  {A B}%type_scope _.

(** ** Operation <<cojoin_Batch6>> *)
(**********************************************************************)
Section cojoin6.

  Context
    `{ToBatch6 T T}
    (A A' A'': Type).

  Section auxiliary.

    Variable (R: Type).

    Definition key_function:
      Batch A' (T A'') (T A'' -> R) ->
      T A' ->
      Batch A' (T A'') R :=
      fun next_batch t =>
        next_batch <⋆> toBatch6 t.

    Definition cojoin_Batch6_leaf_case:
      Batch A (T A') (Batch A' (T A'') (T A'' -> R)) ->
      (* ^ recursive call on cojoin of continuation *)
      Batch A (T A') (T A' -> Batch A' (T A'') R) :=
      (* new continuation *)
      fun rec_continue =>
        map (F := Batch A (T A')) key_function rec_continue.

  End auxiliary.

  Fixpoint cojoin_Batch6 {R: Type}
    (b: Batch A (T A'') R):
    Batch A (T A') (Batch A' (T A'') R) :=
    match b with
    | Done r => Done (Done r)
    | Step continuation a =>
        let new_continuation :=
          cojoin_Batch6_leaf_case R (cojoin_Batch6 continuation)
        in Step new_continuation a
    end.

End cojoin6.

(** ** <<cojoin_Batch6>> Alternate Definition *)
(**********************************************************************)
Section cojoin6_alt.

  Context
    `{ToBatch6 T T}.

  Definition double_batch6 {A B C: Type}:
    A -> Batch A (T B) (Batch B (T C) (T C)) :=
    map (F := Batch A (T B)) toBatch6 ∘ batch A (T B).

  Lemma double_batch6_rw {A B C: Type} (a: A):
    double_batch6 (B := B) (C := C) a =
      Done toBatch6 ⧆ a.
  Proof.
    reflexivity.
  Qed.

  (** ** <<cojoin_Batch6>> as <<runBatch double_batch6>> *)
  (********************************************************************)
  Lemma cojoin_Batch6_to_runBatch: forall (A B B': Type),
      @cojoin_Batch6 _ _ A B B' =
        @runBatch A (T B') (Batch A (T B) ∘ Batch B (T B')) _ _ _
          (double_batch6 (B := B) (C := B')).
  Proof.
    intros.
    ext C. ext b.
    induction b as [R r |R rest IHrest a].
    - cbn. reflexivity.
    - cbn.
      rewrite IHrest.
      do 3
        (compose near
           (@runBatch A (T B') (Batch A (T B) ∘ Batch B (T B'))
              _ _ _
              (double_batch6) (T B' -> R) rest) on right;
         rewrite (fun_map_map (F := Batch A (T B)))).
      reflexivity.
  Qed.

  Lemma cojoin_Batch6_batch: forall (A B C: Type),
      cojoin_Batch6 A B C ∘ batch A (T C) =
        double_batch6.
  Proof.
    intros.
    rewrite cojoin_Batch6_to_runBatch.
    rewrite (runBatch_batch (Batch A (T B) ∘ Batch B (T C)) A (T C)).
    reflexivity.
  Qed.

  #[export] Instance ApplicativeMorphism_cojoin_Batch6:
    forall (A B C: Type),
      ApplicativeMorphism (Batch A (T C))
        (Batch A (T B) ∘ Batch B (T C))
        (@cojoin_Batch6 T _ A B C).
  Proof.
    intros.
    rewrite (@cojoin_Batch6_to_runBatch A B C).
    apply ApplicativeMorphism_runBatch.
  Qed.

End cojoin6_alt.

(*
  Section experiment.

  Context (A B B' C: Type) T `{ToBatch6 T}.
  Check toBatch6 T A B.
  Check map (Batch A (T B)) (toBatch6 T B C).
  Check map (Batch A (T B)) (toBatch6 T B C) ∘ toBatch6 T A B.
  (* T A -> Batch A (T B) (Batch B (T C) (T C)) *)

  Check toBatch6 T A C. (* T A -> Batch A (T C) (T C) *)
  Check cojoin_Batch6 T A C B' (T C).
  Check cojoin_Batch6 T A C B' (T C) ∘ toBatch6 T A C.
  (*  T A -> Batch A (T B') (Batch B' (T C) (T C)) *)
  Check cojoin_Batch6 T A (T C) B' C.
  Check toBatch6 T A C.

  Check cojoin_Batch (B := B) ∘ toBatch6 T A C.
  Check cojoin_Batch (B := B) ∘ toBatch6 T A C.

  End experiment.
 *)

(** ** Typeclasses *)
(**********************************************************************)
Class TraversableRightPreModule
  (T U: Type -> Type) `{Return T}
  `{ToBatch6 T T} `{ToBatch6 T U} :=
  { trfm_extract: forall (A: Type),
      extract_Batch ∘ mapfst_Batch ret ∘ toBatch6 = @id (U A);
    trfm_duplicate: forall (A A' A'': Type),
      cojoin_Batch6 A A' A'' ∘ toBatch6 (U := U) =
        map (F := Batch A (T A')) (toBatch6) ∘ toBatch6;
  }.

Class TraversableMonad
  (T: Type -> Type) `{Return T} `{ToBatch6 T T} :=
  { trfm_ret: forall (A B: Type),
      toBatch6 ∘ ret = batch A (T B);
    trfm_premod :> TraversableRightPreModule T T;
  }.

Class TraversableRightModule
  (T U: Type -> Type) `{Return T}
  `{ToBatch6 T T} `{ToBatch6 T U} :=
  { trfmod_monad :> TraversableMonad T;
    trfmod_premod :> TraversableRightPreModule T U;
  }.
