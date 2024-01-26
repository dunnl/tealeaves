From Tealeaves Require Export
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableFunctor
  Classes.Coalgebraic.TraversableMonad
  Functors.Batch.

Import Kleisli.TraversableMonad.Notations.
Import Batch.Notations.

#[local] Generalizable Variables G T M A B.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch {T}%function_scope {ToBatch} {A} (A')%type_scope _.
#[local] Arguments toBatchM {T}%function_scope {ToBatchM} {A} (B)%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Traversals as <<BatchM>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatchM_Bindt `{Bindt T T}
    : Coalgebraic.TraversableMonad.ToBatchM T :=
  (fun A B => bindt (G := Batch A (T B)) (batch (T B)) : T A -> Batch A (T B) (T B)).

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    `{Kleisli.TraversableMonad.TraversableMonadFull T}.

  Lemma bindt_through_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt f = runBatch f ∘ toBatchM B.
  Proof.
    unfold_ops @ToBatchM_Bindt.
    rewrite (ktm_morph (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Lemma traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse (T := T) f = runBatch (map ret ∘ f) ∘ toBatchM B.
  Proof.
    rewrite ktmf_traverse_to_bindt.
    rewrite bindt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
    map (F := T) f = runBatch (F := fun A => A) (ret (T := T) ∘ f) ∘ toBatchM B.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch : forall (A : Type),
      id (A := T A) = runBatch (F := fun A => A) (ret (T := T)) ∘ toBatchM A.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := T)).
    rewrite map_through_runBatch.
    reflexivity.
  Qed.

End runBatch.

From Tealeaves Require Import Adapters.KleisliToCoalgebraic.TraversableFunctor.

(** ** Relating <<toBatchM>> with <<toBatch>> *)
(******************************************************************************)
Lemma toBatchM_toBatch
  `{Kleisli.TraversableMonad.TraversableMonadFull T}
  {A B : Type} (t : T A) :
  toBatch B t = mapsnd_Batch (ret (T := T)) (toBatchM B t).
Proof.
  intros.
  unfold_ops @ToBatch_Traverse.
  rewrite ktmf_traverse_to_bindt.
  unfold_ops @ToBatchM_Bindt.
  compose near t on right.
  rewrite (ktm_morph (G1 := Batch A (T B)) (G2 := Batch A B)
                     (ϕ := fun C => mapsnd_Batch (ret (T := T)))).
  rewrite ret_dinatural.
  reflexivity.
Qed.

(** ** Naturality of <<toBatch>> *)
(******************************************************************************)
Lemma toBatchM_mapfst (T : Type -> Type)
  `{Kleisli.TraversableMonad.TraversableMonadFull T}
  {A B : Type} (f : A -> B) {C : Type} :
  toBatchM C ∘ map (F := T) f = mapfst_Batch f ∘ toBatchM C.
Proof.
  unfold_ops @ToBatchM_Bindt.
  rewrite (bindt_map (G2 := Batch B (T C))).
  rewrite (bindt_through_runBatch (G := Batch B (T C))).
  rewrite (bindt_through_runBatch (G := Batch A (T C))).
  ext t.
  unfold compose.
  induction (toBatchM C t).
  - cbn. reflexivity.
  - do 2 rewrite runBatch_rw2.
    rewrite IHb.
    rewrite mapfst_Batch2.
    reflexivity.
Qed.

(** ** Coalgebra laws *)
(******************************************************************************)
Section to_coalgebraic.

  Context
    `{Kleisli.TraversableMonad.TraversableMonadFull T}.

  Lemma double_BatchM_spec : forall A B C,
      double_BatchM T A B C = batch (T C) ⋆3 batch (T B).
  Proof.
    reflexivity.
  Qed.

  Lemma toBatchM_ret_Kleisli : forall A B : Type,
      toBatchM B ∘ ret (T := T) (A := A) = batch (T B).
  Proof.
    intros.
    unfold_ops @ToBatchM_Bindt.
    rewrite (ktm_bindt0 _).
    reflexivity.
  Qed.

  Lemma toBatchM_extract_Kleisli : forall (A : Type),
      extract_Batch ∘ mapfst_Batch ret ∘ toBatchM A = @id (T A).
  Proof.
    intros.
    reassociate -> on left.
    rewrite <- (toBatchM_mapfst T).
    unfold_ops @ToBatchM_Bindt.
    rewrite (bindt_map (G2 := Batch (T A) (T A))).
    rewrite (ktm_morph (ϕ := @extract_Batch (T A))).
    reassociate <- on left.
    rewrite extract_Batch_batch.
    change (id ∘ ?f) with f.
    now rewrite ktm_bindt1.
  Qed.

  Lemma toBatchM_duplicate_Kleisli : forall (A B C : Type),
      cojoin_BatchM T A C B (T C) ∘ toBatchM C =
        map (F := Batch A (T B)) (toBatchM C) ∘ toBatchM B.
  Proof.
    intros.
    unfold_ops @ToBatchM_Bindt.
    change (Batch A (T B) (Batch B (T C) ?x))
      with ((Batch A (T B) ∘ Batch B (T C)) x).
    erewrite (ktm_morph (T := T)
               (G1 := Batch A (T C))
               (G2 := Batch A (T B) ∘ Batch B (T C))
               (ϕ := @cojoin_BatchM T _ A C B)).
    unfold_compose_in_compose.
    rewrite (cojoin_BatchM_batch).
    rewrite (ktm_bindt2 _ _).
    rewrite double_BatchM_spec.
    reflexivity.
    Unshelve.
    all:eauto with typeclass_instances.
  Qed.

  #[export] Instance Coalgebraic_TraversableMonad_of_Kleisli :
    Coalgebraic.TraversableMonad.TraversableMonad T :=
    {| trfm_ret := toBatchM_ret_Kleisli;
      trfm_extract := toBatchM_extract_Kleisli;
      trfm_duplicate := toBatchM_duplicate_Kleisli;
    |}.

End to_coalgebraic.
