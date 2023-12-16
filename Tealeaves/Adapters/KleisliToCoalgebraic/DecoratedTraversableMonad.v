From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Coalgebraic.DecoratedTraversableMonad
  Functors.Batch.

Import Product.Notations.
Import Kleisli.DecoratedTraversableMonad.Notations.
Import Batch.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W G T M A B.

#[local] Arguments map {F}%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments traverse {T}%function_scope {Traverse} {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatchDM {W}%type_scope {T}%function_scope {ToBatchDM} {A B}%type_scope _.
#[local] Arguments bindt {U} {T}%function_scope {Bindt} {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments binddt {W}%type_scope {U} {T}%function_scope {Binddt} {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments traverse {T}%function_scope {Traverse} {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Traversals as <<BatchM>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatchDM_Binddt `{Binddt W T T}
    : Coalgebraic.DecoratedTraversableMonad.ToBatchDM W T :=
  (fun A B => binddt (G := Batch (W * A) (T B)) (batch (T B)) : T A -> Batch (W * A) (T B) (T B)).

Import Kleisli.TraversableMonad.DerivedOperations.

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

  Lemma binddt_to_runBatch `{Applicative G} `(f : W * A -> G (T B)) :
    binddt f = runBatch f ∘ toBatchDM.
  Proof.
    unfold_ops @ToBatchDM_Binddt.
    rewrite (kdtm_morph _ _ (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  (*
  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse (T := T) f = runBatch (map ret ∘ f) ∘ toBatchM B.
  Proof.
    rewrite ktmf_traverse_to_bindt.
    rewrite bindt_to_runBatch.
    reflexivity.
  Qed.

  Corollary map_to_runBatch `(f : A -> B) :
    map (F := T) f = runBatch (F := fun A => A) (ret (T := T) ∘ f) ∘ toBatchM B.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_to_runBatch.
    reflexivity.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
      id (A := T A) = runBatch (F := fun A => A) (ret (T := T)) ∘ toBatchM A.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := T)).
    rewrite map_to_runBatch.
    reflexivity.
  Qed.
  *)
End runBatch.

Import Kleisli.DecoratedTraversableMonad.DerivedInstances.
Require Import Tealeaves.Adapters.KleisliToCoalgebraic.TraversableMonad.

(** ** Relating <<toBatchDM>> with <<toBatch>> *)
(******************************************************************************)
Lemma toBatchMD_toBatchM
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}
  {A B : Type} :
  toBatchM T A B = mapfst_Batch (extract) ∘ toBatchDM.
Proof.
  intros.
  unfold_ops @ToBatchM_Bindt.
  unfold_ops @ToBatchDM_Binddt.
  rewrite (kdtm_morph (Batch (W * A) (T B)) (Batch A (T B))
             (ϕ := fun C => mapfst_Batch (extract))).
  reflexivity.
Qed.

(** ** Naturality of <<toBatchDM>> *)
(******************************************************************************)
Lemma toBatchDM_mapfst1
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}
  {A A' B : Type} (f : W * A -> A') :
  toBatchDM ∘ mapd (T := T) f = mapfst_Batch (cobind f) ∘ toBatchDM (A := A) (B := B).
Proof.
  unfold_ops @ToBatchDM_Binddt.
  rewrite (binddt_mapd W T).
  rewrite (kdtm_morph
             (Batch (W * A) (T B))
             (Batch (W * A') (T B))
             (ϕ := fun C => mapfst_Batch (cobind f))).
  reflexivity.
Qed.

Lemma toBatchDM_mapfst2
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}
  {A A' B : Type} (f : A -> A') {C : Type} :
  toBatchDM ∘ map (F := T) f = mapfst_Batch (map f) ∘ toBatchDM (A := A) (B := B).
Proof.
  rewrite (map_to_cobind W).
  rewrite <- toBatchDM_mapfst1.
  reflexivity.
Qed.

Lemma toBatchDM_mapfst3
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}
  {A A' B : Type} (f : W * A -> A') :
  toBatchM T _ _ ∘ mapd (T := T) f = mapfst_Batch f ∘ toBatchDM (A := A) (B := B).
Proof.
  rewrite toBatchMD_toBatchM.
  unfold_ops @ToBatchDM_Binddt.
  reassociate ->.
  rewrite (binddt_mapd W T).
  rewrite (kdtm_morph (Batch (W * A) (T B)) (Batch A' (T B))
             (ϕ := fun C => mapfst_Batch f)).
  rewrite (kdtm_morph (Batch (W * A') (T B)) (Batch A' (T B))
             (ϕ := fun C => mapfst_Batch (extract))).
  fequal. now ext [w a].
Qed.

(** ** Coalgebra laws *)
(******************************************************************************)
Section to_coalgebraic.

  Context
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

  Lemma double_BatchDM_spec : forall A B C,
      double_batchDM (A := A) (B := B) C = batch (T C) ⋆7 (batch (T B)).
  Proof.
    intros.
    unfold double_batchDM.
    ext [w a].
    cbn.
    change (?f ∘ id) with f.
    unfold_ops @ToBatchDM_Binddt.
    rewrite (kdtm_morph
               (Batch (W * B) (T C))
               (Batch (W * B) (T C))
               (ϕ := fun C => mapfst_Batch (incr w))).
    rewrite ret_natural.
    reflexivity.
  Qed.

  Lemma toBatchDM_ret_Kleisli : forall A B : Type,
      toBatchDM ∘ ret (T := T) (A := A) = batch (T B) ∘ ret (T := (W ×)).
  Proof.
    intros.
    unfold_ops @ToBatchDM_Binddt.
    rewrite kdtm_binddt0.
    reflexivity.
  Qed.

  Lemma toBatchDM_extract_Kleisli : forall (A : Type),
      extract_Batch ∘ mapfst_Batch (ret ∘ extract (W := (W ×))) ∘ toBatchDM = @id (T A).
  Proof.
    intros.
    reassociate -> on left.
    rewrite <- mapfst_mapfst_Batch.
    do 2 reassociate <-; reassociate ->.
    rewrite <- toBatchDM_mapfst3.
    reassociate <-.
    rewrite dfun_mapd1.
    rewrite toBatchM_extract_Kleisli.
    reflexivity.
  Qed.

  Lemma toBatchDM_duplicate_Kleisli : forall (A B C : Type),
      cojoin_BatchDM ∘ toBatchDM (A := A) (B := C) =
        map (F := Batch (W * A) (T B)) (toBatchDM) ∘ toBatchDM.
    intros.
    unfold_ops @ToBatchDM_Binddt.
    change (Batch ?A (T B) (Batch ?B' (T C) ?x))
      with ((Batch A (T B) ∘ Batch B' (T C)) x).
    erewrite (kdtm_morph (T := T)
               (Batch (W * A) (T C))
               (Batch (W * A) (T B) ∘ Batch (W * B) (T C))
               (ϕ := @cojoin_BatchDM W _ _ _ A C B)).
    - unfold_compose_in_compose.
      rewrite (kdtm_binddt2 _ _).
      rewrite (cojoin_BatchDM_batch).
      rewrite double_BatchDM_spec.
      reflexivity.
      Unshelve.
      all:eauto with typeclass_instances.
  Qed.

  #[export] Instance Coalgebraic_DecoratedTraversableMonad_of_Kleisli :
    Coalgebraic.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
    {| dtm_ret := toBatchDM_ret_Kleisli;
      dtm_extract := toBatchDM_extract_Kleisli;
      dtm_duplicate := toBatchDM_duplicate_Kleisli;
    |}.

End to_coalgebraic.
