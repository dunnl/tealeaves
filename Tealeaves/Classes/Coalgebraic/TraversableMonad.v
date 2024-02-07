From Tealeaves Require Import
  Classes.Kleisli.Monad (Return, ret)
  Classes.Kleisli.TraversableMonad
  Classes.Categorical.Applicative
  Functors.Batch.

Import Applicative.Notations.

#[local] Generalizable Variables T.

(** * Traversable Monads, coalgebraically *)
(******************************************************************************)

(** ** <<ToBatch3>> operation *)
(******************************************************************************)
Class ToBatch3 (T : Type -> Type) :=
  toBatch3 : forall A B, T A -> Batch A (T B) (T B).

#[global] Arguments toBatch3 {T}%function_scope {ToBatch3} {A B}%type_scope _.

(** ** <<cojoin_Batch3>> operation *)
(******************************************************************************)
Section cojoin.

  Context
    `{ToBatch3 T}
      (A A' A'' : Type).

  Section auxiliary.

    Variable (R : Type).

    Definition key_function :
      Batch A' (T A'') (T A'' -> R) ->
      T A' ->
      Batch A' (T A'') R :=
      fun next_batch t =>
        next_batch <⋆> toBatch3 t.

    Definition cojoin_Batch3_leaf_case :
      Batch A (T A') (Batch A' (T A'') (T A'' -> R)) -> (* recursive call on cojoin of continuation *)
      Batch A (T A') (T A' -> Batch A' (T A'') R) := (* new continuation *)
      fun rec_continue =>
        map (F := Batch A (T A')) key_function rec_continue.

  End auxiliary.

  Fixpoint cojoin_Batch3 {R : Type}
    (b : Batch A (T A'') R) :
    Batch A (T A') (Batch A' (T A'') R) :=
    match b with
    | Done r => Done (Done r)
    | Step continuation a =>
        let new_continuation :=
          cojoin_Batch3_leaf_case R (cojoin_Batch3 continuation)
        in Step new_continuation a
    end.

End cojoin.

(** ** <<cojoin_Batch3>> alternate specification *)
(******************************************************************************)
Section spec.

  Context
    `{ToBatch3 T}.

  Definition double_Batch3 (A B C : Type) :
      A -> Batch A (T B) (Batch B (T C) (T C)) :=
    map (F := Batch A (T B)) toBatch3 ∘ batch A (T B).

  Lemma cojoin_Batch3_spec : forall (A B B' : Type),
      @cojoin_Batch3 _ _ A B B' =
        runBatch (Batch A (T B) ∘ Batch B (T B'))
          (double_Batch3 A B B').
  Proof.
    intros. ext C. ext b.
    induction b as [R r |R rest IHrest a].
    - cbn. reflexivity.
    - cbn.
      rewrite IHrest.
      do 3
        (compose near
           (runBatch (Batch A (T B) ∘ Batch B (T B'))
              (double_Batch3 A B B') (T B' -> R) rest) on right;
         rewrite (fun_map_map (F := Batch A (T B)))).
      reflexivity.
  Qed.

  Lemma cojoin_Batch3_batch : forall (A B C : Type),
      cojoin_Batch3 A B C ∘ batch A (T C) =
        double_Batch3 A B C.
  Proof.
    intros.
    rewrite cojoin_Batch3_spec.
    rewrite (runBatch_batch (Batch A (T B) ∘ Batch B (T C)) A (T C)).
    reflexivity.
  Qed.

  #[export] Instance AppMor_cojoin_Batch3 : forall (A B C : Type),
      ApplicativeMorphism
        (Batch A (T C))
        (Batch A (T B) ∘ Batch B (T C))
        (@cojoin_Batch3 T _ A B C).
  Proof.
    intros.
    Set Printing All.
    rewrite (@cojoin_Batch3_spec A B C).
    apply ApplicativeMorphism_runBatch.
  Qed.

End spec.

(*
Section experiment.

  Context (A B B' C : Type) T `{ToBatch3 T}.
  Check toBatch3 T A B.
  Check map (Batch A (T B)) (toBatch3 T B C).
  Check map (Batch A (T B)) (toBatch3 T B C) ∘ toBatch3 T A B.
  (* T A -> Batch A (T B) (Batch B (T C) (T C)) *)

  Check toBatch3 T A C. (* T A -> Batch A (T C) (T C) *)
  Check cojoin_Batch3 T A C B' (T C).
  Check cojoin_Batch3 T A C B' (T C) ∘ toBatch3 T A C.
  (*  T A -> Batch A (T B') (Batch B' (T C) (T C)) *)
  Check cojoin_Batch3 T A (T C) B' C.
  Check toBatch3 T A C.

  Check cojoin_Batch (B := B) ∘ toBatch3 T A C.
  Check cojoin_Batch (B := B) ∘ toBatch3 T A C.

End experiment.
*)

Class TraversableMonad
  (T : Type -> Type) `{Return T} `{ToBatch3 T} :=
  { trfm_ret : forall (A B : Type),
      toBatch3 ∘ ret = batch A (T B);
    trfm_extract : forall (A : Type),
      extract_Batch ∘ mapfst_Batch A (T A) (ret) ∘ toBatch3 = @id (T A);
    trfm_duplicate : forall (A A' A'' : Type),
      cojoin_Batch3 A A' A'' ∘ toBatch3 =
        map (F := Batch A (T A')) toBatch3 ∘ toBatch3;
  }.
