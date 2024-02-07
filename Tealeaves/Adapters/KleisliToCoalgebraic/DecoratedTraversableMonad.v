From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Coalgebraic.DecoratedTraversableMonad
  Functors.Batch.

Import Product.Notations.
Import Kleisli.DecoratedTraversableMonad.Notations.
Import Batch.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W G T M A B.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch7 {W}%type_scope {T}%function_scope {ToBatch7} {A B}%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * Traversals as <<Batch3>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatch7_Binddt `{Binddt W T T}
    : Coalgebraic.DecoratedTraversableMonad.ToBatch7 W T :=
  (fun A B => binddt (G := Batch (W * A) (T B)) (batch (T B)) : T A -> Batch (W * A) (T B) (T B)).

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

  Lemma binddt_to_runBatch `{Applicative G} `(f : W * A -> G (T B)) :
    binddt f = runBatch f ∘ toBatch7.
  Proof.
    unfold_ops @ToBatch7_Binddt.
    rewrite (kdtm_morph _ _ (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  (*
  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse (T := T) f = runBatch (map ret ∘ f) ∘ toBatch3 B.
  Proof.
    rewrite ktmf_traverse_to_bindt.
    rewrite bindt_to_runBatch.
    reflexivity.
  Qed.

  Corollary map_to_runBatch `(f : A -> B) :
    map (F := T) f = runBatch (F := fun A => A) (ret (T := T) ∘ f) ∘ toBatch3 B.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_to_runBatch.
    reflexivity.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
      id (A := T A) = runBatch (F := fun A => A) (ret (T := T)) ∘ toBatch3 A.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := T)).
    rewrite map_to_runBatch.
    reflexivity.
  Qed.
  *)
End runBatch.

(** * Batch *)
  (******************************************************************************)
  (*
    Definition toBatch7 W T `{Binddt W T T} {A : Type} (B : Type) : T A -> @Batch (W * A) (T B) (T B) :=
  binddt W T T (Batch (W * A) (T B)) A B (batch (W * A) (T B)).

Section with_functor.

  Context
    `{DecTravMonad W T}.

  About runBatch.

  Lemma runBatch_batch7 : forall `{Applicative G} (A B : Type) (f : W * A -> G (T B)),
      runBatch G f (T B) ∘ (@batch (W * A) (T B)) = f.
  Proof.
    intros. apply (runBatch_batch G).
  Qed.

  Lemma extract_to_runBatch : forall (A X : Type) (b : Batch A A X),
      extract_Batch b = runBatch (fun A => A) (@id A) X b.
  Proof.
    intros. induction b.
    - reflexivity.
    - cbn. now rewrite <- IHb.
  Qed.

End with_functor.
   *)


Require Import
  Tealeaves.Adapters.KleisliToCoalgebraic.TraversableMonad.

(** ** Relating <<toBatch7>> with <<toBatch>> *)
(******************************************************************************)
Lemma toBatch3D_toBatch3
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A B : Type} :
  toBatch3 (A := A) (B := B) = mapfst_Batch extract ∘ toBatch7.
Proof.
  intros.
  unfold_ops @ToBatch3_Bindt.
  unfold_ops @ToBatch7_Binddt.
  rewrite (kdtm_morph (Batch (W * A) (T B)) (Batch A (T B))
             (ϕ := fun C => mapfst_Batch extract)).
  rewrite kdtmf_bindt_compat.
  reflexivity.
Qed.

(** ** Naturality of <<toBatch7>> *)
(******************************************************************************)
Lemma toBatch7_mapfst1
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A A' B : Type} (f : W * A -> A') :
  toBatch7 ∘ mapd (T := T) f = mapfst_Batch (cobind f) ∘ toBatch7 (A := A) (B := B).
Proof.
  unfold_ops @ToBatch7_Binddt.
  (*
  rewrite (binddt_mapd W T).
  rewrite (kdtm_morph
             (Batch (W * A) (T B))
             (Batch (W * A') (T B))
             (ϕ := fun C => mapfst_Batch (cobind f))).
  reflexivity.
Qed.
   *)
Admitted.

Lemma toBatch7_mapfst2
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A A' B : Type} (f : A -> A') {C : Type} :
  toBatch7 ∘ map (F := T) f = mapfst_Batch (map f) ∘ toBatch7 (A := A) (B := B).
Proof.
  rewrite (map_to_cobind W).
  rewrite <- toBatch7_mapfst1.
Admitted.

Lemma toBatch7_mapfst3
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A A' B : Type} (f : W * A -> A') :
  toBatch3 ∘ mapd (T := T) f = mapfst_Batch f ∘ toBatch7 (A := A) (B := B).
Proof.
  rewrite toBatch3D_toBatch3.
  unfold_ops @ToBatch7_Binddt.
  reassociate ->.
  (*
  rewrite (binddt_mapd W T).
  rewrite (kdtm_morph (Batch (W * A) (T B)) (Batch A' (T B))
             (ϕ := fun C => mapfst_Batch f)).
  rewrite (kdtm_morph (Batch (W * A') (T B)) (Batch A' (T B))
             (ϕ := fun C => mapfst_Batch extract)).
  fequal. now ext [w a].
Qed.
   *)
Admitted.

(** ** Coalgebra laws *)
(******************************************************************************)
Section to_coalgebraic.

  Context
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}.

  Lemma double_Batch7_spec : forall A B C,
      double_batch7 (A := A) (A' := B) = batch (T C) ⋆7 (batch (T B)).
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

  Lemma toBatch7_ret_Kleisli : forall A B : Type,
      toBatch7 ∘ ret (T := T) (A := A) = batch (T B) ∘ ret (T := (W ×)).
  Proof.
    intros.
    unfold_ops @ToBatch7_Binddt.
    rewrite kdtm_binddt0.
    reflexivity.
  Qed.

  Lemma toBatch7_extract_Kleisli : forall (A : Type),
      extract_Batch ∘ mapfst_Batch (ret ∘ extract (W := (W ×))) ∘ toBatch7 = @id (T A).
  Proof.
    intros.
    reassociate -> on left.
    rewrite <- mapfst_mapfst_Batch.
    do 2 reassociate <-; reassociate ->.
    rewrite <- toBatch7_mapfst3.
    reassociate <-.
    (*
    rewrite dfun_mapd1.
    rewrite toBatch3_extract_Kleisli.
    reflexivity.
  Qed.
     *)
  Admitted.

  Lemma toBatch7_duplicate_Kleisli : forall (A B C : Type),
      cojoin_Batch7 ∘ toBatch7 (A := A) (B := C) =
        map (F := Batch (W * A) (T B)) toBatch7 ∘ toBatch7.
    intros.
    unfold_ops @ToBatch7_Binddt.
    change (Batch ?A (T B) (Batch ?B' (T C) ?x))
      with ((Batch A (T B) ∘ Batch B' (T C)) x).
    erewrite (kdtm_morph (T := T)
               (Batch (W * A) (T C))
               (Batch (W * A) (T B) ∘ Batch (W * B) (T C))
               (ϕ := @cojoin_Batch7 W _ _ _ A C B)).
    - unfold_compose_in_compose.
      rewrite (kdtm_binddt2 _ _).
      rewrite cojoin_Batch7_batch.
      rewrite double_Batch7_spec.
      reflexivity.
      Unshelve.
      all:eauto with typeclass_instances.
  Qed.

  #[export] Instance Coalgebraic_DecoratedTraversableMonad_of_Kleisli :
    Coalgebraic.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
    {| dtm_ret := toBatch7_ret_Kleisli;
      dtm_extract := toBatch7_extract_Kleisli;
      dtm_duplicate := toBatch7_duplicate_Kleisli;
    |}.

End to_coalgebraic.
