From Tealeaves Require Import
  Classes.Coalgebraic.TraversableMonad
  Classes.Coalgebraic.DecoratedTraversableFunctor
  Classes.Coalgebraic.DecoratedTraversableMonad
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Adapters.KleisliToCoalgebraic.DecoratedTraversableMonad
  Classes.Kleisli.Theory.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedContainerMonad.

From Tealeaves Require Export
  Theory.DecoratedTraversableFunctor
  Theory.TraversableMonad
  Classes.Monoid
  Functors.List
  Functors.Subset
  Functors.Constant
  Classes.Categorical.Applicative.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.
Import DecoratedTraversableMonad.Notations.

#[local] Generalizable Variables M U W T G A B C.

(** * Theory of Decorated Traversable Monads *)
(**********************************************************************)
Section decorated_traversable_monad_theory.

  Context
    `{op: Monoid_op W}
    `{unit: Monoid_unit W}
    `{Monoid_inst: Monoid W}.

  Context
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Mapd_T_inst: Mapd W T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Mapdt_T_inst: Mapdt W T}
    `{Bindd_T_inst: Bindd W T T}
    `{Bindt_T_inst: Bindt T T}
    `{Binddt_T_inst: Binddt W T T}
    `{! Compat_Map_Binddt W T T}
    `{! Compat_Mapd_Binddt W T T}
    `{! Compat_Traverse_Binddt W T T}
    `{! Compat_Bind_Binddt W T T}
    `{! Compat_Mapdt_Binddt W T T}
    `{! Compat_Bindd_Binddt W T T}
    `{! Compat_Bindt_Binddt W T T}.

  Context
    `{Map_U_inst: Map U}
    `{Mapd_U_inst: Mapd W U}
    `{Traverse_U_inst: Traverse U}
    `{Bind_U_inst: Bind T U}
    `{Mapdt_U_inst: Mapdt W U}
    `{Bindd_U_inst: Bindd W T U}
    `{Bindt_U_inst: Bindt T U}
    `{Binddt_U_inst: Binddt W T U}
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Mapd_Binddt W T U}
    `{! Compat_Traverse_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    `{! Compat_Mapdt_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    `{! Compat_Bindt_Binddt W T U}.

  Context
    `{Monad_inst: ! DecoratedTraversableMonad W T}
    `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  Context
    `{ToBatch7_WTT: ToBatch7 W T T}
    `{ToBatch7_WTU: ToBatch7 W T U}
    `{! Compat_ToBatch7_Binddt W T T}
    `{! Compat_ToBatch7_Binddt W T U}.

  Context
    `{ToSubset_U_inst: ToSubset U}
    `{ToSubset_T_inst: ToSubset T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToSubset_Traverse U}.

  Context
    `{ToCtxset_T_inst: ToCtxset W T}
    `{ToCtxset_U_inst: ToCtxset W U}
    `{! Compat_ToCtxset_Mapdt W T}
    `{! Compat_ToCtxset_Mapdt W U}.

  Context
    `{ToCtxlist_T_inst: ToCtxlist W T}
    `{ToCtxlist_U_inst: ToCtxlist W U}
    `{! Compat_ToCtxlist_Mapdt W T}
    `{! Compat_ToCtxlist_Mapdt W U}.

  Context
    `{ToBatch3_TU: ToBatch3 W U}
    `{! Compat_ToBatch3_Mapdt W U}
    `{ToBatch6_TU: ToBatch6 T U}
    `{! Compat_ToBatch6_Bindt T U}.

  Import
    Kleisli.TraversableMonad.DerivedInstances
    Kleisli.DecoratedTraversableMonad.DerivedInstances.

  (** ** Relating <<toBatch7>> to <<toBatch3>> and <<toBatch6>> *)
  (********************************************************************)
  Lemma toBatch3_to_toBatch7 {A B: Type}:
    forall (t: U A),
      toBatch3 (B := B) t =
        mapsnd_Batch (B1 := B) (B2 := T B) ret (toBatch7 (B := B) t).
  Proof.
    intros.
    rewrite toBatch3_to_mapdt.
    rewrite toBatch7_to_binddt.
    rewrite mapdt_to_binddt.
    compose near t on right.
    rewrite (kdtm_morph
               (Batch _ (T B))
               (Batch _ B)
               (ϕ := fun C => mapsnd_Batch (B1 := B) (B2 := T B) ret)
               (batch (W * A) (T B))).
    reflexivity.
  Qed.

  Lemma toBatch6_toBatch7
    {A B: Type}:
    toBatch6 (A := A) (B := B) = mapfst_Batch extract ∘ toBatch7.
  Proof.
    intros.
    rewrite toBatch6_to_bindt.
    rewrite bindt_to_binddt.
    rewrite toBatch7_to_binddt.
    rewrite (kdtm_morph (Batch (W * A) (T B)) (Batch A (T B))
               (ϕ := fun C => mapfst_Batch extract)).
    reflexivity.
  Qed.

  (** ** Specification for <<binddt>> via <<toBatch7>> *)
  (********************************************************************)
  Lemma binddt_through_toBatch7:
    forall (G: Type -> Type) `{Applicative G}
      (A B: Type) (f: W * A -> G (T B)),
      binddt (T := T) (U := U) f =
        map (F := G) (extract_Batch) ∘
          traverse (T := BATCH1 (T B) (U B)) f ∘ toBatch7.
  Proof.
    intros.
    rewrite toBatch7_to_binddt.
    rewrite <- runBatch_via_traverse.
    rewrite (kdtm_morph (Batch (W * A) (T B)) G
               (morph := ApplicativeMorphism_runBatch)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Lemma binddt_through_runBatch `{Applicative G} `(f: W * A -> G (T B)):
    binddt (U := U) f = runBatch f ∘ toBatch7.
  Proof.
    rewrite toBatch7_to_binddt.
    rewrite (kdtm_morph (Batch (W * A) (T B)) G
               (morph := ApplicativeMorphism_runBatch)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Lemma bindt_through_runBatch `{Applicative G} `(f: A -> G (T B)):
    bindt (U := U) f = runBatch (f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite bindt_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Lemma bindd_through_runBatch `(f: W * A -> T B):
    bindd (U := U) f = runBatch (G := fun A => A) f ∘ toBatch7.
  Proof.
    rewrite bindd_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Lemma traverse_through_runBatch `{Applicative G} `(f: A -> G B):
    traverse (T := U) f = runBatch (map ret ∘ f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite traverse_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapdt_through_runBatch `{Applicative G} `(f: W * A -> G B):
    mapdt (T := U) f = runBatch (G := G) (map ret ∘ f) ∘ toBatch7.
  Proof.
    rewrite mapdt_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapd_through_runBatch `(f: W * A -> B):
    mapd (T := U) f =
      runBatch (G := fun A => A) (ret (T := T) ∘ f) ∘ toBatch7.
  Proof.
    rewrite mapd_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f: A -> B):
    map (F := U) f = runBatch (G := fun A => A)
                       (ret (T := T) ∘ f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch: forall (A: Type),
      id (A := U A) =
        runBatch (G := fun A => A) (ret (T := T) ∘ extract) ∘ toBatch7.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := U)).
    rewrite map_through_runBatch.
    reflexivity.
  Qed.

  (** ** Naturality of <<toBatch7>> *)
  (********************************************************************)
  Lemma toBatch7_mapfst1
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}
    {A A' B: Type} (f: W * A -> A'):
    toBatch7 ∘ mapd (T := T) f =
      mapfst_Batch (cobind f) ∘ toBatch7 (A := A) (B := B).
  Proof.
    rewrite toBatch7_to_binddt.
    rewrite (binddt_mapd).
    rewrite toBatch7_to_binddt.
    rewrite
      (kdtm_morph (T := T) (U := T)
         (Batch (W * A) _)
         (Batch (W * A') _)
         (ϕ := fun A => mapfst_Batch (cobind f)) (batch (W * A) (T B))).
    rewrite ret_natural.
    reflexivity.
  Qed.

  Lemma toBatch7_mapfst2
    {A A' B: Type} (f: A -> A') {C: Type}:
    toBatch7 ∘ map (F := T) f =
      mapfst_Batch (map f) ∘ toBatch7 (A := A) (B := B).
  Proof.
    rewrite (map_to_cobind (W := prod W)).
    rewrite <- toBatch7_mapfst1.
    rewrite map_to_mapd.
    reflexivity.
  Qed.

  Lemma toBatch7_mapfst3
    {A A' B: Type} (f: W * A -> A'):
    mapfst_Batch f ∘ toBatch7 (U := U) (A := A) (B := B) =
      toBatch6 ∘ mapd (T := U) f.
  Proof.
    rewrite toBatch6_toBatch7.
    rewrite toBatch7_to_binddt.
    rewrite toBatch7_to_binddt.
    reassociate ->.
    rewrite (binddt_mapd).
    rewrite (kdtm_morph (T := T) (U := U)
               (Batch (W * A') _)
               (Batch A' _)
               (ϕ := fun A => mapfst_Batch extract)).
    rewrite (kdtm_morph (T := T) (U := U)
               (Batch (W * A) (T B))
               (Batch A' (T B))
               (ϕ := fun A => mapfst_Batch f)
               (batch (W * A) (T B))).
    rewrite ret_natural.
    unfold kc1.
    reassociate <- on right.
    rewrite ret_natural.
    reassociate -> on right.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  (** ** Respectfulness for <<binddt>> *)
  (********************************************************************)
  Lemma binddt_respectful_core
    {G} `{Mult G} `{Map G} `{Pure G}:
    forall (A B: Type) (t: U A) (f g: W * A -> G (T B)),
      (forall (w: W) (a: A), (w, a) ∈d t -> f (w, a) = g (w, a)) =
        Forall_ctx (fun '(w, a) => f (w, a) = g (w, a)) t.
  Proof.
    intros.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.

  Theorem binddt_respectful
    {G} `{Mult G} `{Map G} `{Pure G} `{! Applicative G}:
    forall (A B: Type) (t: U A)
      (f g: W * A -> G (T B)),
      (forall (w: W) (a: A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> binddt f t = binddt (U := U) g t.
  Proof.
    introv.
    rewrite (binddt_respectful_core).
    unfold Forall_ctx.
    rewrite (foldMapd_through_runBatch2 A B).
    do 2 rewrite binddt_through_runBatch.
    unfold compose.
    rewrite toBatch3_to_toBatch7.
    rewrite <- runBatch_mapsnd.
    induction (toBatch7 t).
    - cbn. reflexivity.
    - destruct a as [w a].
      cbn.
      intros [hyp1 hyp2].
      rewrite hyp2.
      rewrite IHb; auto.
  Qed.

  Theorem binddt_respectful_pure
    {G} `{Mult G} `{Map G} `{Pure G} `{! Applicative G}:
    forall (A: Type) (t: U A)
      (f: W * A -> G (T A)),
      (forall (w: W) (a: A),
          (w, a) ∈d t ->
          f (w, a) = pure (F := G) (ret (T := T) a))
      -> binddt f t = pure t.
  Proof.
    intros.
    rewrite <- (binddt_pure A).
    apply binddt_respectful;
    assumption.
  Qed.

  (** ** Respectfulness for <<bindd>> *)
  (********************************************************************)
  Lemma bindd_respectful_core:
    forall (A B: Type) (t: U A) (f g: W * A -> T B),
      (forall (w: W) (a: A), (w, a) ∈d t -> f (w, a) = g (w, a)) =
        Forall_ctx (fun '(w, a) => f (w, a) = g (w, a)) t.
    intros.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.

  Theorem bindd_respectful:
    forall (A B: Type) (t: U A) (f g: W * A -> T B),
      (forall (w: W) (a: A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd f t = bindd (U := U) g t.
  Proof.
    introv.
    rewrite (bindd_respectful_core A B t f g).
    unfold Forall_ctx.
    rewrite (foldMapd_through_runBatch2 A B).
    do 2 rewrite bindd_through_runBatch.
    unfold compose.
    rewrite toBatch3_to_toBatch7.
    rewrite <- runBatch_mapsnd.
    induction (toBatch7 t).
    - cbn. reflexivity.
    - destruct a as [w a].
      cbn.
      intros [hyp1 hyp2].
      rewrite hyp2.
      rewrite IHb; auto.
  Qed.

End decorated_traversable_monad_theory.

Section instances.

  Context
    `{op: Monoid_op W}
    `{unit: Monoid_unit W}
    `{Monoid_inst: Monoid W}.

  Context
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Mapd_T_inst: Mapd W T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Mapdt_T_inst: Mapdt W T}
    `{Bindd_T_inst: Bindd W T T}
    `{Bindt_T_inst: Bindt T T}
    `{Binddt_T_inst: Binddt W T T}
    `{ToSubset_T_inst: ToSubset T}
    `{! Compat_Map_Binddt W T T}
    `{! Compat_Mapd_Binddt W T T}
    `{! Compat_Traverse_Binddt W T T}
    `{! Compat_Bind_Binddt W T T}
    `{! Compat_Mapdt_Binddt W T T}
    `{! Compat_Bindd_Binddt W T T}
    `{! Compat_Bindt_Binddt W T T}.

  Context
    `{Map_U_inst: Map U}
    `{Mapd_U_inst: Mapd W U}
    `{Traverse_U_inst: Traverse U}
    `{Bind_U_inst: Bind T U}
    `{Mapdt_U_inst: Mapdt W U}
    `{Bindd_U_inst: Bindd W T U}
    `{Bindt_U_inst: Bindt T U}
    `{Binddt_U_inst: Binddt W T U}
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
    `{ToCtxset_T_inst: ToCtxset W T}
    `{ToCtxset_U_inst: ToCtxset W U}
    `{! Compat_ToCtxset_Mapdt W T}
    `{! Compat_ToCtxset_Mapdt W U}.

  Context
    `{ToCtxlist_T_inst: ToCtxlist W T}
    `{ToCtxlist_U_inst: ToCtxlist W U}
    `{! Compat_ToCtxlist_Mapdt W T}
    `{! Compat_ToCtxlist_Mapdt W U}.

  Context
    `{Monad_inst: ! DecoratedTraversableMonad W T}
    `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  Import
    Kleisli.TraversableMonad.DerivedInstances
    Kleisli.DecoratedTraversableMonad.DerivedInstances
    KleisliToCoalgebraic.TraversableMonad.DerivedOperations
    KleisliToCoalgebraic.DecoratedTraversableFunctor.DerivedOperations
    KleisliToCoalgebraic.DecoratedTraversableMonad.DerivedOperations.

  #[export] Instance DecoratedContainerFunctor_DTM:
    DecoratedContainerFunctor W U.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      apply mapd_respectful.
      auto.
  Qed.

  #[export] Instance DecoratedContainerMonad_DTM:
    DecoratedContainerMonad W T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      apply bindd_respectful.
      auto.
  Qed.

  #[export] Instance DecoratedContainerModule_DTM:
    DecoratedContainerRightModule W T U.
  Proof.
    constructor.
    - apply (DecoratedRightModule_DecoratedTraversableRightPreModule W T U).
    - typeclasses eauto.
    - intros; apply bindd_respectful; auto.
  Qed.

End instances.

(** * Deriving All Other Typeclass Instances from a DTM *)
(**********************************************************************)
Module UsefulInstances.

  Export Classes.Coalgebraic.TraversableFunctor.
  Export Classes.Coalgebraic.TraversableMonad.
  Export Classes.Coalgebraic.DecoratedTraversableFunctor.
  Export Classes.Coalgebraic.DecoratedTraversableMonad.

  Export Classes.Kleisli.TraversableFunctor.
  Export Classes.Kleisli.TraversableMonad.
  Export Classes.Kleisli.DecoratedTraversableFunctor.
  Export Classes.Kleisli.DecoratedTraversableMonad.


  Export KleisliToCoalgebraic.TraversableFunctor.
  Export KleisliToCoalgebraic.TraversableFunctor.DerivedOperations.
  Export KleisliToCoalgebraic.TraversableFunctor.DerivedInstances.

  Export KleisliToCoalgebraic.TraversableMonad.
  Export KleisliToCoalgebraic.TraversableMonad.DerivedOperations.
  Export KleisliToCoalgebraic.TraversableMonad.DerivedInstances.

  Export KleisliToCoalgebraic.DecoratedTraversableFunctor.
  Export KleisliToCoalgebraic.DecoratedTraversableFunctor.DerivedOperations.
  Export KleisliToCoalgebraic.DecoratedTraversableFunctor.DerivedInstances.

  Export KleisliToCoalgebraic.DecoratedTraversableMonad.
  Export KleisliToCoalgebraic.DecoratedTraversableMonad.DerivedOperations.
  Export KleisliToCoalgebraic.DecoratedTraversableMonad.DerivedInstances.

  (*
  Export Kleisli.DecoratedTraversableFunctor.DerivedOperations.
  Export Kleisli.DecoratedTraversableFunctor.DerivedInstances.
   *)

  Export Kleisli.DecoratedTraversableMonad.DerivedOperations.
  Export Kleisli.DecoratedTraversableMonad.DerivedInstances.

  #[export] Existing Instance Tolist_Traverse.
  #[export] Existing Instance ToSubset_Traverse.
  #[export] Existing Instance ToCtxlist_Mapdt.
  #[export] Existing Instance ToCtxset_Mapdt.

End UsefulInstances.
