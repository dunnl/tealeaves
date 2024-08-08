From Tealeaves Require Export
  Classes.Coalgebraic.TraversableFunctor
  Classes.Coalgebraic.TraversableMonad
  Classes.Kleisli.TraversableMonad
  Functors.Batch.

Import Kleisli.TraversableMonad.Notations.
Import Batch.Notations.

#[local] Generalizable Variables G U T M A B.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch {T}%function_scope {ToBatch} {A} (A')%type_scope _.
#[local] Arguments toBatch3 {T U}%function_scope {ToBatch3} {A} (B)%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Traversals as <<Batch3>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatch3_Bindt `{Bindt T U}
    : Coalgebraic.TraversableMonad.ToBatch3 T U :=
  (fun A B => bindt (G := Batch A (T B)) (batch (T B)) : U A -> Batch A (T B) (U B)).

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    `{ret_inst : Return T}
    `{Map_inst : Map U}
    `{Traverse_inst : Traverse U}
    `{Bind_inst : Bind T U}
    `{Bindt_inst : Bindt T U}
    `{Bindt_T_inst : Bindt T T}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{! Functor U}
    `{! TraversableRightPreModule T U}.

  Lemma bindt_through_runBatch `{Applicative G} `(f : A -> G (T B)):
    bindt (U := U) f = runBatch f ∘ toBatch3 B.
  Proof.
    unfold_ops @ToBatch3_Bindt.
    rewrite (ktm_morph (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary bind_through_runBatch `{Applicative G} `(f : A -> T B):
    bind (U := U) f = runBatch (F := fun A => A) f ∘ toBatch3 B.
  Proof.
    unfold_ops @ToBatch3_Bindt.
    rewrite bind_to_bindt.
    rewrite bindt_through_runBatch.
    reflexivity.
  Qed.

  Corollary traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse (T := U) f = runBatch (map ret ∘ f) ∘ toBatch3 B.
  Proof.
    rewrite traverse_to_bindt.
    rewrite bindt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
    map (F := U) f = runBatch (F := fun A => A) (ret (T := T) ∘ f) ∘ toBatch3 B.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch : forall (A : Type),
      id (A := U A) = runBatch (F := fun A => A) (ret (T := T)) ∘ toBatch3 A.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := U)).
    rewrite map_through_runBatch.
    reflexivity.
  Qed.

End runBatch.

From Tealeaves Require Import
  Adapters.KleisliToCoalgebraic.TraversableFunctor.

(** ** Relating <<toBatch3>> with <<toBatch>> *)
(******************************************************************************)
Lemma toBatch3_toBatch
  `{Kleisli.TraversableMonad.TraversableMonad T}
  `{Traverse_inst : Traverse U}
  `{Bindt_U_inst : Bindt T U}
  `{ToBatch_U_inst : ToBatch U}
  `{! Compat_Traverse_Bindt T U}
  `{! Compat_ToBatch_Traverse}
  `{! Kleisli.TraversableMonad.TraversableRightPreModule T U}
  {A B: Type} (t: U A) :
  toBatch B t = mapsnd_Batch (ret (T := T)) (toBatch3 B t).
Proof.
  intros.
  rewrite toBatch_to_traverse.
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
Lemma toBatch3_mapfst (U : Type -> Type)
  `{Map_inst : Map U}
  `{Bindt_T_inst : Bindt T T}
  `{Bindt_U_inst : Bindt T U}
  `{Return_inst : Return T}
  `{! Compat_Map_Bindt T U}
  `{! TraversableMonad T}
  `{! Kleisli.TraversableMonad.TraversableRightPreModule T U}
  {A B : Type} (f : A -> B) {C : Type} :
  toBatch3 C ∘ map (F := U) f = mapfst_Batch f ∘ toBatch3 C.
Proof.
  unfold_ops @ToBatch3_Bindt.
  rewrite (bindt_map (G2 := Batch B (T C))).
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
    `{Kleisli.TraversableMonad.TraversableMonad T}
    `{Map U}
    `{Bindt T U}
    `{! Compat_Map_Bindt T U}
    `{! TraversableRightPreModule T U}.

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
      extract_Batch ∘ mapfst_Batch ret ∘ toBatch3 A = @id (U A).
  Proof.
    intros.
    reassociate -> on left.
    rewrite <- (toBatch3_mapfst U).
    unfold_ops @ToBatch3_Bindt.
    rewrite (bindt_map (G2 := Batch (T A) (T A))).
    rewrite (ktm_morph (ϕ := @extract_Batch (T A))).
    reassociate <- on left.
    rewrite extract_Batch_batch.
    change (id ∘ ?f) with f.
    now rewrite ktm_bindt1.
  Qed.

  Lemma toBatch3_duplicate_Kleisli : forall (A B C : Type),
      cojoin_Batch3 A B C (R := U C) ∘ toBatch3 (T := T) C =
        map (F := Batch A (T B)) (toBatch3 C) ∘ toBatch3 (U := U) B.
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

End to_coalgebraic.

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
    `{! TraversableRightPreModule T U}.

  #[export] Instance:
    Coalgebraic.TraversableMonad.TraversableRightPreModule T T :=
    {| trfm_extract := toBatch3_extract_Kleisli;
       trfm_duplicate := toBatch3_duplicate_Kleisli;
    |}.

  #[export] Instance Coalgebraic_TraversableRightPreModule_of_Kleisli :
    Coalgebraic.TraversableMonad.TraversableRightPreModule T U :=
    {| trfm_extract := toBatch3_extract_Kleisli;
       trfm_duplicate := toBatch3_duplicate_Kleisli;
    |}.

  #[export] Instance Coalgebraic_TraversableMonad_of_Kleisli :
    Coalgebraic.TraversableMonad.TraversableMonad T :=
    {| trfm_ret := toBatch3_ret_Kleisli;
    |}.

  #[export] Instance Coalgebraic_TraversableRightModule_of_Kleisli :
    Coalgebraic.TraversableMonad.TraversableRightModule T U :=
    {| trfmod_monad := _
    |}.

End instances.
