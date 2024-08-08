From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Coalgebraic.DecoratedTraversableMonad
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Functors.Batch.

Import Product.Notations.
Import Kleisli.DecoratedTraversableMonad.Notations.
Import Kleisli.Comonad.Notations.
Import Batch.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables U W G T M A B.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments batch {A} (B)%type_scope _.
#[local] Arguments toBatch7 {W}%type_scope {T U}%function_scope {ToBatch7} {A B}%type_scope _.
#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.

(** * DecoratedTraversableMonads as <<Batch7>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatch7_Binddt `{Binddt W T U}
  : Coalgebraic.DecoratedTraversableMonad.ToBatch7 W T U :=
  (fun A B => binddt (G := Batch (W * A) (T B)) (batch (T B)) : U A -> Batch (W * A) (T B) (U B)).

Lemma toBatch6_to_toBatch7
  `{Monoid_op W}
  `{Monoid_unit W}
  `{Return T}
  `{Mapdt W U}
  `{Binddt W T U}
  `{Binddt W T T}
  `{! Compat_Mapdt_Binddt W T U}
  `{! DecoratedTraversableRightPreModule W T U}:
  forall A A' t,
    toBatch6 (A := A) (B := A') t =
      mapsnd_Batch (B1 := A') (B2 := T A')
        (ret (T := T) (A := A')) (toBatch7 (A := A) (B := A') t).
Proof.
  intros.
  unfold_ops @ToBatch6_Mapdt.
  unfold_ops @ToBatch7_Binddt.
  rewrite mapdt_to_binddt.
  compose near t on right.
  rewrite (kdtm_morph (A := A) (T := T)
             (Batch _ (T A'))
             (Batch _ A')
             (ϕ := fun C => mapsnd_Batch (B1 := A') (B2 := T A') ret)
             (batch (A := W * A) (T A'))).
  reflexivity.
Qed.

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.


  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Monoid_inst: Monoid W}.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Mapd_T_inst : Mapd W T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Mapdt_T_inst : Mapdt W T}
      `{Bindd_T_inst : Bindd W T T}
      `{Bindt_T_inst : Bindt T T}
      `{Binddt_T_inst : Binddt W T T}
      `{ToSubset_T_inst: ToSubset T}
      `{! Compat_Map_Binddt W T T}
      `{! Compat_Mapd_Binddt W T T}
      `{! Compat_Traverse_Binddt W T T}
      `{! Compat_Bind_Binddt W T T}
      `{! Compat_Mapdt_Binddt W T T}
      `{! Compat_Bindd_Binddt W T T}
      `{! Compat_Bindt_Binddt W T T}.

  Context
    `{Map_U_inst : Map U}
      `{Mapd_U_inst : Mapd W U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Mapdt_U_inst : Mapdt W U}
      `{Bindd_U_inst : Bindd W T U}
      `{Bindt_U_inst : Bindt T U}
      `{Binddt_U_inst : Binddt W T U}
      `{ToSubset_U_inst: ToSubset U}
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Mapd_Binddt W T U}
      `{! Compat_Traverse_Binddt W T U}
      `{! Compat_Bind_Binddt W T U}
      `{! Compat_Mapdt_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U}
      `{! Compat_Bindt_Binddt W T U}
      `{! Compat_ToSubset_Traverse T}
      `{! Compat_ToSubset_Traverse U}.

  Context
    `{Monad_inst : ! DecoratedTraversableMonad W T}
      `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  Lemma binddt_through_runBatch `{Applicative G} `(f : W * A -> G (T B)) :
    binddt (U := U) f = runBatch f ∘ toBatch7.
  Proof.
    unfold_ops @ToBatch7_Binddt.
    rewrite (kdtm_morph _ _ (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Lemma bindt_through_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt (U := U) f = runBatch (f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite bindt_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Lemma bindd_through_runBatch `(f : W * A -> T B) :
    bindd (U := U) f = runBatch (F := fun A => A) f ∘ toBatch7.
  Proof.
    rewrite bindd_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Lemma traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse (T := U) f = runBatch (map ret ∘ f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite traverse_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapdt_through_runBatch `{Applicative G} `(f : W * A -> G B) :
    mapdt (T := U) f = runBatch (F := G) (map ret ∘ f) ∘ toBatch7.
  Proof.
    rewrite mapdt_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapd_through_runBatch `(f : W * A -> B) :
    mapd (T := U) f = runBatch (F := fun A => A) (ret (T := T) ∘ f) ∘ toBatch7.
  Proof.
    rewrite mapd_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
    map (F := U) f = runBatch (F := fun A => A) (ret (T := T) ∘ f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch : forall (A : Type),
      id (A := U A) = runBatch (F := fun A => A) (ret (T := T) ∘ extract) ∘ toBatch7.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := U)).
    rewrite map_through_runBatch.
    reflexivity.
  Qed.

End runBatch.

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
  rewrite (binddt_mapd).
  rewrite (kdtm_morph (T := T) (U := T)
                      (Batch (W * A) _)
                      (Batch (W * A') _)
                      (ϕ := fun A => mapfst_Batch (cobind f)) (batch (T B))).
  rewrite ret_natural.
  reflexivity.
Qed.

Lemma toBatch7_mapfst2
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A A' B : Type} (f : A -> A') {C : Type} :
  toBatch7 ∘ map (F := T) f = mapfst_Batch (map f) ∘ toBatch7 (A := A) (B := B).
Proof.
  rewrite (map_to_cobind W).
  rewrite <- toBatch7_mapfst1.
  rewrite map_to_mapd.
  reflexivity.
Qed.

Lemma toBatch7_mapfst3
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A A' B : Type} (f : W * A -> A') :
  toBatch3 ∘ mapd (T := T) f = mapfst_Batch f ∘ toBatch7 (A := A) (B := B).
Proof.
  rewrite toBatch3D_toBatch3.
  unfold_ops @ToBatch7_Binddt.
  reassociate ->.
  rewrite (binddt_mapd).
  rewrite (kdtm_morph (T := T) (U := T)
                      (Batch (W * A') _)
                      (Batch A' _)
                      (ϕ := fun A => mapfst_Batch extract) (_)).
  rewrite (kdtm_morph (T := T) (U := T)
                      (Batch (W * A) _)
                      (Batch A' _)
                      (ϕ := fun A => mapfst_Batch f) (batch (T B))).
  rewrite ret_natural.
  unfold kc4.
  reassociate <- on left.
  rewrite ret_natural.
  reassociate -> on left.
  rewrite kcom_cobind0.
  reflexivity.
Qed.

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
    reassociate <- on left.
    rewrite dfun_mapd1.
    rewrite trfm_extract.
    reflexivity.
  Qed.

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
