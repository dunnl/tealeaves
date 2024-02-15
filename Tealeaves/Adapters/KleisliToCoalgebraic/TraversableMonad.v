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
#[local] Arguments toBatch3 {T}%function_scope {ToBatch3} {A} (B)%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Traversals as <<Batch3>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatch3_Bindt `{Bindt T T}
    : Coalgebraic.TraversableMonad.ToBatch3 T :=
  (fun A B => bindt (G := Batch A (T B)) (batch (T B)) : T A -> Batch A (T B) (T B)).

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    `{ret_inst : Return T}
    `{Map_T_inst : Map T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Bindt_T_inst : Bindt T T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! Kleisli.TraversableMonad.TraversableMonad T}.

  Lemma bindt_through_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt f = runBatch f ∘ toBatch3 B.
  Proof.
    unfold_ops @ToBatch3_Bindt.
    rewrite (ktm_morph (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Lemma traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse (T := T) f = runBatch (map ret ∘ f) ∘ toBatch3 B.
  Proof.
    rewrite traverse_to_bindt.
    rewrite bindt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
    map (F := T) f = runBatch (F := fun A => A) (ret (T := T) ∘ f) ∘ toBatch3 B.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch : forall (A : Type),
      id (A := T A) = runBatch (F := fun A => A) (ret (T := T)) ∘ toBatch3 A.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := T)).
    rewrite map_through_runBatch.
    reflexivity.
  Qed.

End runBatch.

From Tealeaves Require Import
  Adapters.KleisliToCoalgebraic.TraversableFunctor.

(** ** Relating <<toBatch3>> with <<toBatch>> *)
(******************************************************************************)
Lemma toBatch3_toBatch
  `{Traverse_inst : Traverse T}
  `{Bindt_inst : Bindt T T}
  `{Return_inst : Return T}
  `{! Compat_Traverse_Bindt T T}
  `{! Kleisli.TraversableMonad.TraversableMonad T}
  {A B: Type} (t: T A) :
  toBatch B t = mapsnd_Batch (ret (T := T)) (toBatch3 B t).
Proof.
  intros.
  unfold_ops @ToBatch_Traverse.
  rewrite traverse_to_bindt.
  unfold_ops @ToBatch3_Bindt.
  compose near t on right.
  rewrite (ktm_morph (G1 := Batch A (T B)) (G2 := Batch A B)
                     (ϕ := fun C => mapsnd_Batch (ret (T := T)))).
  rewrite ret_dinatural.
  reflexivity.
Qed.

(** ** Naturality of <<toBatch>> *)
(******************************************************************************)
Lemma toBatch3_mapfst (T : Type -> Type)
  `{Map_inst : Map T}
  `{Bindt_inst : Bindt T T}
  `{Return_inst : Return T}
  `{! Compat_Map_Bindt T T}
  `{! Kleisli.TraversableMonad.TraversableMonad T}
  {A B : Type} (f : A -> B) {C : Type} :
  toBatch3 C ∘ map (F := T) f = mapfst_Batch f ∘ toBatch3 C.
Proof.
  unfold_ops @ToBatch3_Bindt.
  About bindt_map.
  rewrite (bindt_map (Module_inst := TraversableRightModule_TraversableMonad T)
             (G2 := Batch B (T C))).
  rewrite (bindt_through_runBatch (G := Batch B (T C))).
  rewrite (bindt_through_runBatch (G := Batch A (T C))).
  ext t.
  unfold compose.
  induction (toBatch3 C t).
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
    `{Map_inst : Map T}
    `{Compat_Map_Bindt T T}
    `{! Kleisli.TraversableMonad.TraversableMonad T}.

  Lemma double_batch3_spec : forall A B C,
      double_batch3 (A := A) = batch (T C) ⋆3 batch (T B).
  Proof.
    reflexivity.
  Qed.

  Lemma toBatch3_ret_Kleisli : forall A B : Type,
      toBatch3 B ∘ ret (T := T) (A := A) = batch (T B).
  Proof.
    intros.
    unfold_ops @ToBatch3_Bindt.
    rewrite (ktm_bindt0 _).
    reflexivity.
  Qed.

  Lemma toBatch3_extract_Kleisli : forall (A : Type),
      extract_Batch ∘ mapfst_Batch ret ∘ toBatch3 A = @id (T A).
  Proof.
    intros.
    reassociate -> on left.
    rewrite <- (toBatch3_mapfst T).
    unfold_ops @ToBatch3_Bindt.
    rewrite (bindt_map (Module_inst := TraversableRightModule_TraversableMonad T)
               (G2 := Batch (T A) (T A))).
    rewrite (ktm_morph (ϕ := @extract_Batch (T A))).
    reassociate <- on left.
    rewrite extract_Batch_batch.
    change (id ∘ ?f) with f.
    now rewrite ktm_bindt1.
  Qed.

  Lemma toBatch3_duplicate_Kleisli : forall (A B C : Type),
      cojoin_Batch3 A B C (R := T C) ∘ toBatch3 (T := T) C =
        map (F := Batch A (T B)) (toBatch3 C) ∘ toBatch3 B.
  Proof.
    intros.
    unfold_ops @ToBatch3_Bindt.
    change (Batch A (T B) (Batch B (T C) ?x))
      with ((Batch A (T B) ∘ Batch B (T C)) x).
    erewrite (ktm_morph (T := T)
               (G1 := Batch A (T C))
               (G2 := Batch A (T B) ∘ Batch B (T C))
               (ϕ := @cojoin_Batch3 T _ A B C)).
    unfold_compose_in_compose.
    rewrite (cojoin_Batch3_batch).
    rewrite (ktm_bindt2 _ _).
    rewrite double_batch3_spec.
    reflexivity.
    Unshelve.
    all:eauto with typeclass_instances.
  Qed.

  #[export] Instance Coalgebraic_TraversableMonad_of_Kleisli :
    Coalgebraic.TraversableMonad.TraversableMonad T :=
    {| trfm_ret := toBatch3_ret_Kleisli;
      trfm_extract := toBatch3_extract_Kleisli;
      trfm_duplicate := toBatch3_duplicate_Kleisli;
    |}.

End to_coalgebraic.
