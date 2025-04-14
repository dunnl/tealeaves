From Tealeaves Require Import
  Adapters.KleisliToCategorical.TraversableFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Adapters.KleisliToCategorical.DecoratedTraversableFunctor
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Classes.Coalgebraic.TraversableFunctor
  Classes.Coalgebraic.DecoratedTraversableFunctor.

From Tealeaves Require Export
  Functors.Batch
  Functors.Environment
  Functors.Option
  Theory.TraversableFunctor
  Kleisli.Theory.DecoratedTraversableFunctor.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.
Import VectorRefinement.Notations.

#[local] Generalizable Variables F M E T G A B C ϕ.

(** * Properties of <<toBatch3>> *)
(**********************************************************************)
Section theory.

  Context
    `{Mapdt_inst: Mapdt E T}
    `{Traverse_inst: Traverse T}
    `{Mapd_inst: Mapd E T}
    `{Map_inst: Map T}
    `{ToBatch_inst: ToBatch T}
    `{ToBatch3_inst: ToBatch3 E T}
    `{ToCtxset_inst: ToCtxset E T}
    `{ToCtxlist_inst: ToCtxlist E T}
    `{! Compat_Traverse_Mapdt E T}
    `{! Compat_Mapd_Mapdt E T}
    `{! Compat_Map_Mapdt E T}
    `{! Compat_ToBatch_Traverse T}
    `{! Compat_ToBatch3_Mapdt E T}
    `{! Compat_ToCtxset_Mapdt E T}
    `{! Compat_ToCtxlist_Mapdt E T}
    `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

  (** ** Relating <<toBatch3>> with <<toBatch>> *)
  (********************************************************************)
  Lemma toBatch_to_toBatch3 {A B: Type}:
    toBatch (A := A) (A' := B) = mapfst_Batch extract ∘ toBatch3.
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite traverse_to_mapdt.
    rewrite toBatch3_to_mapdt.
    rewrite (kdtf_morph
               (G1 := Batch (E * A) B)
               (G2 := Batch A B)
               (ϕ := fun C => mapfst_Batch extract)).
    rewrite ret_natural.
    reflexivity.
  Qed.

  (** ** Factoring <<mapdt>> via <<toBatch3>>  *)
  (********************************************************************)
  Lemma mapdt_through_toBatch3
    `{Applicative G} `(f: E * A -> G B):
    mapdt (E := E) (T := T) f = runBatch f ∘ toBatch3.
  Proof.
    intros.
    rewrite toBatch3_to_mapdt.
    rewrite kdtf_morph.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  (** ** Naturality of <<toBatch3>> *)
  (********************************************************************)
  Lemma toBatch3_mapdt
    `{Applicative G}
    {A A' B: Type} (f: E * A -> G A'):
    map (F := G) (toBatch3 (A := A') (B := B)) ∘ mapdt (T := T) f =
      traverse (T := BATCH1 B (T B)) (strength ∘ cobind f) ∘ toBatch3.
  Proof.
    rewrite toBatch3_to_mapdt.
    rewrite kdtf_mapdt2.
    rewrite (traverse_via_runBatch G).
    rewrite <- (mapdt_through_toBatch3
                 (A := A) (B := B)
                 (G := G ∘ Batch (E * A') B)).
    reflexivity.
  Qed.

  Lemma toBatch3_mapd
    {A A' B: Type} (f: E * A -> A'):
    toBatch3 ∘ mapd (T := T) f =
      mapfst_Batch (cobind f) ∘ toBatch3 (A := A) (B := B).
  Proof.
    rewrite toBatch3_to_mapdt.
    rewrite mapdt_mapd.
    rewrite toBatch3_to_mapdt.
    rewrite (kdtf_morph
               (G1 := Batch (E * A) B)
               (G2 := Batch (E * A') B)
               (ϕ := fun C => mapfst_Batch (cobind f))).
    reflexivity.
  Qed.

  Lemma toBatch3_map
    {A A' B: Type} (f: A -> A') {C: Type}:
    toBatch3 ∘ map (F := T) f =
      mapfst_Batch (map f) ∘ toBatch3 (A := A) (B := B).
  Proof.
    rewrite toBatch3_to_mapdt.
    rewrite mapdt_map.
    rewrite toBatch3_to_mapdt.
    rewrite (kdtf_morph
               (morphism := ApplicativeMorphism_mapfst_Batch (map f))

               (ϕ := fun C => mapfst_Batch (map f))).
    rewrite ret_natural.
    reflexivity.
  Qed.

  Lemma toBatch_mapd
    {A A' B: Type} (f: E * A -> A'):
    toBatch (A := A') (A' := B) ∘ mapd (T := T) f =
      mapfst_Batch f ∘ toBatch3 (T := T) (A := A) (B := B).
  Proof.
    rewrite toBatch_to_toBatch3.
    reassociate -> on left.
    rewrite toBatch3_mapd.
    reassociate <-.
    rewrite (mapfst_mapfst_Batch).
    rewrite (kcom_cobind0).
    reflexivity.
  Qed.

  (** * Factoring Operations Through <<toBatch3>> *)
  (********************************************************************)
  Section runBatch.

    (** ** Core Operations *)
    (******************************************************************)
    Theorem mapdt_through_runBatch `{Applicative G} `(f: E * A -> G B):
      mapdt f = runBatch f ∘ toBatch3.
    Proof.
      intros.
      rewrite toBatch3_to_mapdt.
      rewrite kdtf_morph.
      rewrite (runBatch_batch G).
      reflexivity.
    Qed.

    Corollary traverse_through_runBatch `{Applicative G} `(f: A -> G B):
      traverse f = runBatch (f ∘ extract (W := (E ×))) ∘ toBatch3.
    Proof.
      rewrite traverse_to_mapdt.
      rewrite mapdt_through_runBatch.
      reflexivity.
    Qed.

    Corollary mapd_through_runBatch `(f: E * A -> B):
      mapd f = runBatch (G := fun A => A) f ∘ toBatch3.
    Proof.
      intros.
      rewrite mapd_to_mapdt.
      rewrite mapdt_through_runBatch.
      reflexivity.
    Qed.

    Corollary map_through_runBatch `(f: A -> B):
      map f = runBatch (G := fun A => A) (f ∘ extract) ∘ toBatch3.
    Proof.
      intros.
      rewrite map_to_mapdt.
      rewrite mapdt_through_runBatch.
      reflexivity.
    Qed.

    (** ** <<mapdReduce>> Through <<toBatch3>> *)
    (******************************************************************)
    Lemma mapdReduce_through_runBatch1 {A} `{Monoid M}: forall `(f: E * A -> M),
        mapdReduce f = runBatch (G := const M) f (C := T False) ∘ toBatch3 (B := False).
    Proof.
      intros.
      rewrite mapdReduce_to_mapdt1.
      rewrite (mapdt_through_runBatch (G := const M)).
      reflexivity.
    Qed.

    Lemma mapdReduce_through_runBatch2 `{Monoid M}: forall (A fake: Type) `(f: E * A -> M),
        mapdReduce f = runBatch (G := const M) f (C := T fake) ∘ toBatch3 (B := fake).
    Proof.
      intros.
      rewrite mapdReduce_to_mapdt1.
      rewrite (mapdt_constant_applicative2 False False fake).
      rewrite mapdt_through_runBatch.
      reflexivity.
    Qed.

    (** ** <<toctxlist>> Through <<toBatch3>> *)
    (******************************************************************)
    Corollary toctxlist_through_runBatch3 {A: Type} (tag: Type):
      toctxlist = runBatch (B := tag)
                    (G := const (list (E * A)))
                    (ret (T := list))
                    ∘ toBatch3.
    Proof.
      rewrite (toctxlist_to_mapdt2 A tag).
      now rewrite mapdt_through_runBatch.
    Qed.


    Corollary toctxset_through_runBatch1 {A: Type}:
      toctxset (F := T) = runBatch (B := False)
                            (G := const (subset (E * A)))
                            (ret (T := subset)) ∘ toBatch3.
    Proof.
      rewrite (toctxset_to_mapdt1 A).
      now rewrite (mapdt_through_runBatch).
    Qed.

    Corollary toctxset_through_runBatch2 {A tag: Type}:
      toctxset (F := T) = runBatch (B := tag)
                            (G := const (subset (E * A)))
                            (ret (T := subset)) ∘ toBatch3.
    Proof.
      rewrite (toctxset_to_mapdt2 A tag).
      now rewrite (mapdt_through_runBatch).
    Qed.

    Corollary element_ctx_of_through_runBatch1
      `{ToSubset T}
      `{! Compat_ToSubset_Traverse T}
      {A: Type} {p: E * A}:
      element_ctx_of (T := T) p =
        runBatch (B := False) (G := const Prop)
          (H0 := @Mult_const _ Monoid_op_or)
          (H1 := @Pure_const _ Monoid_unit_false)
          {{p}} ∘ toBatch3.
    Proof.
      rewrite element_ctx_of_to_mapdReduce.
      rewrite mapdReduce_through_runBatch1.
      reflexivity.
    Qed.

  End runBatch.

  (** * Respectfulness Properties *)
  (********************************************************************)
  Section decorated_traversable_functor_theory.

    (** ** Purity *)
    (******************************************************************)
    Theorem mapdt_purity1:
      forall `{Applicative G},
        `(mapdt (G := G) (pure ∘ extract) = @pure G _ (T A)).
    Proof.
      intros.
      rewrite <- (kdtf_morph (G1 := fun A => A) (G2 := G)).
      rewrite kdtf_mapdt1.
      reflexivity.
    Qed.

    (** ** Characterizing <<∈d>> and <<mapd>> *)
    (******************************************************************)
    Lemma mapdt_respectful:
      forall A B `{Applicative G} (t: T A) (f g: E * A -> G B),
        (forall (e: E) (a: A), (e, a) ∈d t -> f (e, a) = g (e, a))
        -> mapdt f t = mapdt g t.
    Proof.
      introv Happl hyp.
      do 2 rewrite mapdt_through_runBatch.
      unfold element_ctx_of in hyp.
      rewrite (toctxset_through_runBatch2 (tag := B)) in hyp.
      unfold compose in *.
      induction (toBatch3 (B := B) t).
      - reflexivity.
      - destruct a as [e a]. cbn.
        rewrite IHb.
        rewrite hyp.
        reflexivity.
        + cbn. now right.
        + introv hyp2.
          apply hyp.
          now left.
    Qed.


    Corollary mapdt_respectful_pure:
      forall A `{Applicative G} (t: T A) (f: E * A -> G A),
        (forall (e: E) (a: A), (e, a) ∈d t -> f (e, a) = pure (F := G) a)
        -> mapdt f t = pure t.
    Proof.
      intros.
      rewrite <- mapdt_purity1.
      now apply mapdt_respectful.
    Qed.

    Corollary mapdt_respectful_id:
      forall A (t: T A) (f: E * A -> A),
        (forall (e: E) (a: A), (e, a) ∈d t -> f (e, a) = a)
        -> mapdt (G := fun A => A) f t = t.
    Proof.
      intros.
      change t with (id t) at 2.
      rewrite <- kdtf_mapdt1.
      apply (mapdt_respectful A A (G := fun A => A)).
      assumption.
    Qed.

    Lemma mapd_respectful:
      forall A B (t: T A) (f g: E * A -> B),
        (forall (e: E) (a: A), (e, a) ∈d t -> f (e, a) = g (e, a))
        -> mapd f t = mapd g t.
    Proof.
      introv hyp.
      rewrite mapd_through_runBatch.
      rewrite mapd_through_runBatch.
      unfold element_ctx_of in hyp.
      rewrite (toctxset_through_runBatch2 (tag := B)) in hyp.
      unfold compose in *.
      induction (toBatch3 (B := B) t).
      - reflexivity.
      - destruct a as [e a]. cbn.
        rewrite IHb.
        rewrite hyp.
        reflexivity.
        + cbn. now right.
        + introv hyp2.
          apply hyp.
          now left.
    Qed.

    Lemma mapd_eq_iff:
      forall A B (t: T A) (f g: E * A -> B),
        mapd f t = mapd g t ->
        mapfst_Batch f (toBatch3 (B := B) t) = mapfst_Batch g (toBatch3 t).
    Proof.
      intros.
      assert (cut: mapfst_Batch (cobind f) (toBatch3 (B := B) t) = mapfst_Batch (cobind g) (toBatch3 t)).
      - compose near t.
        rewrite <- toBatch3_mapd.
        rewrite <- toBatch3_mapd.
        unfold compose. rewrite H0.
        reflexivity.
      - induction (toBatch3 t).
        + reflexivity.
        + cbn. fequal.
          { apply IHb.
            assumption.
            inversion cut.
            eauto. }
          { inversion cut.
            destruct a as [e a].
            cbn in H3.
            inversion H3; auto.
          }
    Qed.

    Lemma mapd_respectful_iff
      `{! ToSubset T} `{! Compat_ToSubset_Traverse T}:
      forall A B (t: T A) (f g: E * A -> B),
        (forall (e: E) (a: A), (e, a) ∈d t -> f (e, a) = g (e, a))
        <-> mapd f t = mapd g t.
    Proof.
      split.
      - apply mapd_respectful.
      - introv Heq Hf.
        apply mapd_eq_iff in Heq.
        rewrite element_ctx_of_to_mapdReduce in Hf.
        rewrite (mapdReduce_through_runBatch2 A B) in Hf.
        unfold compose in *.
        pose (Batch_ind (E * A) B
                (fun (C: Type) (b: Batch (E * A) B C) =>
                   mapfst_Batch f b = mapfst_Batch g b ->
                   runBatch
                     (H := Map_const)
                     (H0 := (@Mult_const Prop Monoid_op_or))
                     (H1 := (@Pure_const Prop Monoid_unit_false))
                     (C := C) (G := const Prop) {{(e, a)}} b
                   -> f (e, a) = g (e, a))).
        eapply e0.
        + introv X Y.
          inversion Y.
        + intros C b Hb [e' a'].
          rewrite mapfst_Batch_rw2.
          rewrite mapfst_Batch_rw2.
          rewrite runBatch_rw2.
          unfold ap.
          unfold_ops @Map_const.
          unfold_ops @Mult_const.
          unfold transparent tcs.
          intros X [Case1 | Case2].
          { apply Hb; inversion X; auto. }
          { inversion X.
            inversion Case2; subst.
            assumption. }
          Unshelve.
          exact (T B).
          exact (toBatch3 t).
        + assumption.
        + assumption.
    Qed.

    Import Kleisli.DecoratedTraversableFunctor.DerivedInstances.

    #[export] Instance
      DecoratedContainerFunctor_DecoratedTraversableFunctor:
      DecoratedContainerFunctor E T.
    Proof.
      constructor.
      - typeclasses eauto.
      - constructor.
        intros.
        rewrite toctxset_mapd.
        reflexivity.
      - intros.
        apply mapd_respectful.
        assumption.
    Qed.

  End decorated_traversable_functor_theory.

  (** * Shapeliness *)
  (********************************************************************)
  Section shapeliness.

    Import Kleisli.DecoratedTraversableFunctor.DerivedInstances.

    Lemma mapd_shape {A B}: forall (f: E * A -> B) t,
        shape (mapd f t) = shape t.
    Proof.
      intros.
      unfold shape.
      compose near t on left.
      rewrite map_mapd.
      rewrite map_to_mapd.
      reflexivity.
    Qed.

    Lemma mapd_ctxlist_injective {A B}:
      forall (f: E * A -> B) (t1 t2: T A),
        (forall p q: E * A, f p = f q -> p = q) ->
        mapd f (toctxlist t1) = mapd f (toctxlist t2) ->
        tolist t1 = tolist t2.
    Proof.
      introv Hinj.
      rewrite tolist_to_toctxlist.
      unfold compose.
      generalize dependent (toctxlist t2).
      induction (toctxlist t1) as [| [e a] rest IHrest];
        intros toctxlist_t2 premise.
      - destruct (toctxlist_t2) as [| [e' a'] rest'].
        + reflexivity.
        + exfalso. inversion premise.
      - destruct (toctxlist_t2) as [| [e' a'] rest'].
        + exfalso. inversion premise.
        + cbn in *.
          fequal.
          * assert (Heq: f (e, a) = f (e', a')) by
              now inversion premise.
            specialize (Hinj (e, a) (e', a') Heq).
            now inversion Hinj.
          * apply IHrest.
            now inversion premise.
    Qed.

    Lemma mapd_ctxlist_injective_restricted1 {A B}:
      forall (f: E * A -> B) (t1 t2: T A),
        (forall p q: E * A,
            p ∈d (toctxlist t1) ->
            q ∈d (toctxlist t2) ->
            f p = f q -> p = q) ->
        mapd f (toctxlist t1) = mapd f (toctxlist t2) ->
        tolist t1 = tolist t2.
    Proof.
      introv Hinj.
      rewrite tolist_to_toctxlist.
      unfold compose.
      generalize dependent (toctxlist t2).
      induction (toctxlist t1) as [| [e a] rest IHrest];
        intros toctxlist_t2 Hinj premise.
      - destruct (toctxlist_t2) as [| [e' a'] rest'].
        + reflexivity.
        + exfalso. inversion premise.
      - destruct (toctxlist_t2) as [| [e' a'] rest'].
        + exfalso. inversion premise.
        + cbn in *.
          fequal.
          * assert (Heq: f (e, a) = f (e', a')) by
              now inversion premise.
            enough (X: (e, a) = (e', a'))
              by now inversion X.
            apply Hinj; auto.
          * apply IHrest.
            { intros p q Hinp Hinq Heq.
              apply Hinj; eauto. }
            { now inversion premise. }
    Qed.

    Lemma mapd_ctxlist_injective_restricted2 {A B}:
      forall (f: E * A -> B) (t1 t2: T A),
        (forall (e: E) (a1: A) (a2: A),
            (e, a1) ∈d (toctxlist t1) ->
            (e, a2) ∈d (toctxlist t2) ->
            f (e, a1) = f (e, a2) -> a1 = a2) ->
        mapd f (toctxlist t1) = mapd f (toctxlist t2) ->
        tolist t1 = tolist t2.
    Proof.
      introv Hinj.
      rewrite tolist_to_toctxlist.
      unfold compose.
      generalize dependent (toctxlist t2).
      induction (toctxlist t1) as [| [e a] rest IHrest];
        intros toctxlist_t2 Hinj premise.
      - destruct (toctxlist_t2) as [| [e' a'] rest'].
        + reflexivity.
        + exfalso. inversion premise.
      - destruct (toctxlist_t2) as [| [e' a'] rest'].
        + exfalso. inversion premise.
        + cbn in *.
          fequal.
          * assert (e = e') by now inversion premise; subst.
            assert (Heq: f (e, a) = f (e, a')) by
              now inversion premise.
            eapply Hinj; auto.
            subst; now left.
          * apply IHrest.
            { intros e'' a1 a2 Hinp Hinq Heq.
              eapply Hinj; eauto. }
            { now inversion premise. }
    Qed.

    Theorem mapd_injective1 {A B}: forall (f: E * A -> B) (t1 t2: T A),
        (forall p q, f p = f q -> p = q) ->
        mapd f t1 = mapd f t2 ->
        t1 = t2.
    Proof.
      introv Hinj Heq.
      assert (cut: (toctxlist ∘ mapd f) t1 = (toctxlist ∘ mapd f) t2).
      { unfold compose. fequal. auto. }
      rewrite <- mapd_toctxlist in cut.
      unfold compose in cut.
      apply Traversable_shapeliness.
      split.
      - (* Same shape *)
        enough (cut2: shape (mapd f t1) = shape (mapd f t2)).
        do 2 rewrite mapd_shape in cut2; auto.
        now rewrite Heq.
      - (* Same contents *)
        eapply mapd_ctxlist_injective; eassumption.
    Qed.

    Theorem mapd_injective2 {A B}:
      forall (f: E * A -> B) (t1 t2: T A),
        (forall e a1 a2,
            (e, a1) ∈d t1 ->
            (e, a2) ∈d t2 ->
            f (e, a1) = f (e, a2) -> a1 = a2) ->
        mapd f t1 = mapd f t2 ->
        t1 = t2.
    Proof.
      introv Hinj Heq.
      setoid_rewrite ind_iff_in_toctxlist1 in Hinj.
      assert (Heq2: (toctxlist ∘ mapd f) t1 = (toctxlist ∘ mapd f) t2).
      { unfold compose. fequal. auto. }
      rewrite <- mapd_toctxlist in Heq2.
      unfold compose in Heq2.
      apply Traversable_shapeliness.
      split.
      - (* Same shape *)
        enough (cut2: shape (mapd f t1) = shape (mapd f t2)).
        do 2 rewrite mapd_shape in cut2; auto.
        now rewrite Heq.
      - eapply mapd_ctxlist_injective_restricted2; eauto.
        intros.
        eapply Hinj; eauto.
        + repeat rewrite toctxlist_to_mapdt in *.
          assumption.
        + repeat rewrite toctxlist_to_mapdt in *.
          assumption.
    Qed.

  End shapeliness.

  (** * Deconstructing with refinement-type vectors *)
  (********************************************************************)
  Section deconstruction.

    Import Kleisli.DecoratedTraversableFunctor.DerivedInstances.

    #[local] Generalizable Variables v.

    (** ** Relating <<plength>> and <<toBatch3>> *)
    (******************************************************************)
    Lemma plength_toBatch3:
      forall {A} {B} (t: T A),
        plength t = length_Batch (toBatch3 (A := A) (B := B) t).
    Proof.
      intros.
      unfold plength.
      rewrite (mapReduce_through_runBatch2 A B).
      rewrite toBatch_to_toBatch3.
      unfold compose.
      induction (toBatch3 t).
      - reflexivity.
      - cbn.
        rewrite IHb.
        unfold_ops @NaturalNumbers.Monoid_op_plus.
        lia.
    Qed.

    Lemma length_toBatch3_toBatch:
      forall {A B} (t: T A),
        length_Batch (toBatch3 (A := A) (B := B) t) =
          length_Batch (toBatch (A := A) (A' := B) t).
    Proof.
      intros.
      rewrite toBatch_to_toBatch3.
      unfold compose. induction (toBatch3 t).
      - reflexivity.
      - cbn. now rewrite IHb.
    Qed.

    (** ** <<mapdt_contents>> and <<mapdt_make>> *)
    (******************************************************************)
    Definition mapdt_contents {A} (t: T A):
      Vector (plength t) (E * A) :=
      let v: Vector
               (length_Batch (toBatch3 (B := False) (A := A) t))
               (E * A)
        := Batch_contents (toBatch3 t)
      in coerce_Vector_length (eq_sym (plength_toBatch3 t)) v.

    Definition mapdt_make {A B} (t: T A):
      Vector (plength t) B -> T B := trav_make t.

    (** ** Relation <<toctxlist>> and <<mapdt_contents>> *)
    (******************************************************************)
    Lemma Batch3_contents_toctxlist:
      forall {A B} (t: T A),
        Vector_to_list (E * A) (Batch_contents (toBatch3 (B := B) t)) =
          List.rev (toctxlist t).
    Proof.
      intros.
      rewrite toctxlist_to_mapdReduce.
      rewrite (mapdReduce_through_runBatch2 A B).
      unfold compose.
      induction (toBatch3 t).
      - cbn. reflexivity.
      - cbn.
        rewrite Vector_to_list_vcons.
        rewrite IHb.
        unfold_ops @Monoid_op_list @Return_list.
        rewrite List.rev_unit.
        reflexivity.
    Qed.

    Corollary mapdt_contents_toctxlist:
      forall {A} (t: T A),
        Vector_to_list (E * A) (mapdt_contents t) =
          List.rev (toctxlist t).
    Proof.
      intros.
      unfold mapdt_contents.
      unfold Vector_to_list.
      rewrite <- coerce_Vector_contents.
      apply Batch3_contents_toctxlist.
    Qed.

    (** ** <<_sim>> Properties *)
    (******************************************************************)
    Lemma Batch_contents_toBatch3_sim:
      forall {A B B'} (t: T A),
        Batch_contents (toBatch3 (B := B) t) ~~
          Batch_contents (toBatch3 (B := B') t).
    Proof.
      intros.
      unfold Vector_sim.
      change (proj1_sig ?v) with (Vector_to_list _ v).
      rewrite Batch3_contents_toctxlist.
      rewrite Batch3_contents_toctxlist.
      reflexivity.
    Qed.

    Lemma Batch_make_toBatch3 {A B} (t: T A):
      Batch_make (toBatch3 t) =
        (fun v => Batch_make (B := B)
                 (toBatch t) (coerce (length_toBatch3_toBatch t) in v)).
    Proof.
      ext v.
      generalize dependent (length_toBatch3_toBatch (B := B) t).
      intro e.
      apply Batch_make_sim3.
      2: { vector_sim. }
      { rewrite toBatch_to_toBatch3.
        unfold compose.
        clear e v.
        induction (toBatch3 t).
        + reflexivity.
        + unfold shape in *. cbn.
          fequal. apply IHb.
      }
    Qed.


    (** * Miscellaneous *)
    (******************************************************************)
    Lemma toBatch_mapdt_make {A A' B} {t: T A} {v: Vector (plength t) B}:
      toBatch (A' := A') (mapdt_make t v) =
        Batch_replace_contents
          (toBatch (A' := A') t)
          (coerce eq_sym (plength_eq_length t) in v).
    Proof.
      apply toBatch_trav_make_to_replace_contents.
    Qed.

    Lemma mapdt_same_shape
      `(t1: T A) `(t2: T A'):
      shape t1 = shape t2 ->
      forall B, mapdt_make (B := B) t1 ~!~ mapdt_make t2.
    Proof.
      intros.
      now apply trav_same_shape.
    Qed.

    Lemma plength_mapdt_make: forall `(t: T A) `(v: Vector _ B),
        plength (mapdt_make t v) = plength t.
    Proof.
      intros.
      unfold mapdt_make.
      symmetry. apply plength_trav_make.
    Qed.

    (** * Lens Laws *)
    (******************************************************************)
    Section lens_laws.

      Import KleisliToCoalgebraic.DecoratedTraversableFunctor.DerivedInstances.
      Import KleisliToCoalgebraic.TraversableFunctor.DerivedInstances.

      (** ** get-put *)
      (****************************************************************)
      Lemma mapdt_get_put `{t: T A}:
        mapdt_make t (map extract (mapdt_contents t)) = t.
      Proof.
        unfold mapdt_make, trav_make, mapdt_contents.
        hide_lhs;
          change t with (id t);
          rewrite Heqlhs; clear Heqlhs lhs.
        rewrite <- trf_extract.
        unfold compose.
        rewrite <- Batch_make_contents.
        apply Batch_make_sim1.
        vector_sim.
        unfold Vector_sim.
        rewrite Batch_contents_natural.
        compose near t on left.
        rewrite <- toBatch_to_toBatch3.
        apply Batch_contents_toBatch_sim.
      Qed.

      (** ** put-get *)
      (****************************************************************)
      (* Ill-typed, needs clarification of statement *)
      (*
        Lemma mapdt_contents_make {A} {t: T A}
        {v: Vector (plength t) A}:
        mapdt_contents (trav_make t v) ~~ v.
        Proof.
        unfold trav_contents.
        vector_sim.
        rewrite toBatch_trav_make.
        rewrite Batch_put_get.
        vector_sim.
        Qed.
       *)

      (** ** put-put *)
      (****************************************************************)
      Lemma mapdt_make_make
        `(t: T A) `(v: Vector (plength t) B)
        `(v1: Vector _ B')
        (v2: Vector _ B')
        (pf: v1 ~~ v2):
        mapdt_make (mapdt_make t v) v1 =
          mapdt_make t v2.
      Proof.
        unfold mapdt_make at 1 2 3.
        apply trav_make_make.
        assumption.
      Qed.

    End lens_laws.

    (** * Representation theorems *)
    (******************************************************************)
    Lemma mapdt_repr:
      forall `{Applicative G} (A B: Type) (t: T A) (f: E * A -> G B),
        mapdt f t =
          map (mapdt_make t)
            (forwards (traverse (mkBackwards ∘ f) (mapdt_contents t))).
    Proof.
      intros.
      unfold mapdt_make.
      unfold mapdt_contents.
      unfold trav_make.
      change  (map (?f ○ ?g)) with (map (f ∘ g)).
      rewrite <- (fun_map_map (F := G)).
      unfold compose at 1.
      do 2 change (map ?f (forwards ?x)) with (forwards (map f x)).
      rewrite traverse_Vector_coerce_natural;[|typeclasses eauto].

      rewrite mapdt_through_runBatch.
      unfold compose at 1.
      rewrite runBatch_repr2.
      change (map ?f (forwards ?x)) with (forwards (map f x)).
      fequal.
      rewrite Batch_make_toBatch3.
      change  (map (?f ○ ?g) ?t) with (map (f ∘ g) t).
      rewrite <- (fun_map_map (F := Backwards G)).
      unfold compose at 1.
      rewrite traverse_Vector_coerce_natural;
        [| typeclasses eauto ].
      fequal.
      fequal.
      apply Vector_sim_eq.
      vector_sim.
      apply Batch_contents_toBatch3_sim.
    Qed.

  End deconstruction.

  (** ** Specialized to option *)
  (**********************************************************************)
  Lemma map_None_eq_iff: forall (A B: Type) (f: A -> B) (o: option A),
      map f o = None <-> o = None.
  Proof.
    intros; destruct o; easy.
  Qed.

  Import Applicative.Notations.

  Lemma ap_None_eq_None1: forall (A B: Type) (o: option A),
      (None: option (A -> B)) <⋆> o = None.
  Proof.
    now destruct o.
  Qed.

  Lemma ap_None_eq_None1_iff: forall (A B: Type) (f: option (A -> B)) (a: A),
      f <⋆> Some a = None <-> f = None.
  Proof.
    intros.
    now destruct f.
  Qed.

  Lemma ap_None_eq_None2: forall (A B: Type) (f: option (A -> B)),
      f <⋆> None = None.
  Proof.
    now destruct f.
  Qed.

  Lemma ap_None_eq_None2_iff: forall (A B: Type) (f: A -> B) (o: option A),
      Some f <⋆> o = None <-> o = None.
  Proof.
    now destruct o.
  Qed.

  Lemma list_rev_cons: forall (A: Type) (a: A) (l: list A),
      List.rev (a :: l) = List.rev l ++ [a].
  Proof.
    reflexivity.
  Qed.

  Lemma in_list_rev_spec: forall (A: Type) (l: list A) (a: A),
      a ∈ l <-> a ∈ List.rev l.
  Proof.
    induction l.
    - reflexivity.
    - setoid_rewrite element_of_list_cons.
      setoid_rewrite IHl.
      rewrite list_rev_cons.
      setoid_rewrite element_of_list_app.
      setoid_rewrite element_of_list_one.
      tauto.
  Qed.

  Lemma list_traverse_None_iff: forall (A B: Type) (f: A -> option B) (l: list A),
      traverse f l = None <-> exists (a: A), a ∈ l /\ f a = None.
  Proof.
    intros; induction l.
    - cbn. split; intro Hyp.
      + false.
      + destruct Hyp as [a [contra _]].
        false.
    - rewrite traverse_list_cons.
      remember (f a) as Fa.
      destruct Fa.
      + cbn. split; intro Hyp.
        { apply ap_None_eq_None2_iff in Hyp.
          rewrite IHl in Hyp.
          destruct Hyp as [a' [Hain Hfa]].
          + exists a'. split; auto.
        }
        { rewrite ap_None_eq_None2_iff.
          rewrite IHl.
          destruct Hyp as [a' [Hain Hfa]].
          destruct Hain as [Case1 | Case2].
          - false.
          - exists a'; auto.
        }
      + split; intro Hyp.
        { exists a. split; [now left|].
          now rewrite HeqFa. }
        { apply ap_None_eq_None1. }
  Qed.

  Lemma traverse_Vector_None_spec1 {A B} (n: nat) (f: E * A -> option B):
    forall (l: list (E * A)) (e: length l = n),
      (forwards (traverse_Vector_core (mkBackwards ∘ f) l e) = None) -> traverse f l = None.
  Proof.
    introv HeqNone.
    destruct e.
    induction l.
    - cbn in HeqNone. false.
    - assert (cut: f a = None \/ forwards (traverse_Vector_core (mkBackwards ∘ f) l eq_refl) = None).
      { cbn in HeqNone.
        rewrite map_None_eq_iff in HeqNone.
        rewrite map_None_eq_iff in HeqNone.
        destruct (f a).
        right.
        cbn in HeqNone.
        remember (@forwards option (Vector (@length (prod E A) l) B)
                    ((fix go (vl : list (prod E A)) (n : nat) {struct vl} :
                       forall _ : @eq nat (@length (prod E A) vl) n, Backwards option (Vector n B) :=
                        match
                          vl as vl0 return (forall _ : @eq nat (@length (prod E A) vl0) n, Backwards option (Vector n B))
                        with
                        | nil =>
                            fun vlen : @eq nat O n =>
                              @pure (Backwards option) (@Pure_Backwards option Pure_option)
                                (@sig (list B) (fun l : list B => @eq nat (@length B l) n))
                                (@exist (list B) (fun l : list B => @eq nat (@length B l) n) (@nil B) vlen)
                        | cons a rest =>
                            fun vlen : @eq nat (S (@length (prod E A) rest)) n =>
                              match
                                n as n0
                                return (forall _ : @eq nat (S (@length (prod E A) rest)) n0, Backwards option (Vector n0 B))
                              with
                              | O =>
                                  fun vlen' : @eq nat (S (@length (prod E A) rest)) O =>
                                    @zero_not_S
                                      ((fix length (l : list (prod E A)) : nat :=
                                          match l return nat with
                                          | nil => O
                                          | cons _ l' => S (length l')
                                          end) rest) (Backwards option (Vector O B))
                                      (@eq_sym nat (S (@length (prod E A) rest)) O vlen')
                              | S m =>
                                  fun vlen' : @eq nat (S (@length (prod E A) rest)) (S m) =>
                                    @ap (Backwards option) (@Map_Backwards option Map_option)
                                      (@Mult_Backwards option Map_option Mult_option) (Vector m B) (Vector (S m) B)
                                      (@ap (Backwards option) (@Map_Backwards option Map_option)
                                         (@Mult_Backwards option Map_option Mult_option) B
                                         (forall _ : Vector m B, Vector (S m) B)
                                         (@pure (Backwards option) (@Pure_Backwards option Pure_option)
                                            (forall (_ : B) (_ : Vector m B), Vector (S m) B) (@vcons m B))
                                         (@compose (prod E A) (option B) (Backwards option B) (@mkBackwards option B) f a))
                                      (go rest m
                                         (@S_uncons
                                            ((fix length (l : list (prod E A)) : nat :=
                                                match l return nat with
                                                | nil => O
                                                | cons _ l' => S (length l')
                                                end) rest) m vlen'))
                              end vlen
                        end) l (@length (prod E A) l) (@eq_refl nat (@length (prod E A) l)))) as X.
        destruct X.
        + false.
        + symmetry in HeqX.
          exact HeqX.
        + now left.
      }
      rewrite traverse_list_cons.
      destruct cut as [Case1 | Case2].
      + rewrite Case1.
        cbn.
        now rewrite ap_None_eq_None1.
      + rewrite IHl; auto.
        rewrite ap_None_eq_None2.
        reflexivity.
  Qed.

  Lemma traverse_Vector_None_spec2 {A B} (n: nat) (f: E * A -> option B):
    forall (l: list (E * A)) (e: length l = n),
      traverse f l = None -> (forwards (traverse_Vector_core (mkBackwards ∘ f) l e) = None).
  Proof.
    introv HeqNone.
    destruct e.
    induction l.
    - cbn in HeqNone. false.
    - assert (cut: f a = None \/
                     (exists b, f a = Some b /\ forwards (traverse_Vector_core (mkBackwards ∘ f) l eq_refl) = None)).
      { cbn in HeqNone.
        destruct (f a).
        right.
        cbn in HeqNone.
        destruct (traverse f l).
        + cbn in HeqNone. false.
        + rewrite ap_None_eq_None2 in HeqNone.
          specialize (IHl HeqNone).
          exists b; split; auto.
        + now left.
      }
      destruct cut as [Case1 | Case2].
      { (* Case 1 *)
        cbn.
        rewrite Case1.
        cbn.
        rewrite map_None_eq_iff.
        rewrite map_None_eq_iff.
        remember (@forwards option (Vector (@length (prod E A) l) B)
                    ((fix go (vl : list (prod E A)) (n : nat) {struct vl} :
                       forall _ : @eq nat (@length (prod E A) vl) n, Backwards option (Vector n B) :=
                        match
                          vl as vl0 return (forall _ : @eq nat (@length (prod E A) vl0) n, Backwards option (Vector n B))
                        with
                        | nil =>
                            fun vlen : @eq nat O n =>
                              @pure (Backwards option) (@Pure_Backwards option Pure_option)
                                (@sig (list B) (fun l : list B => @eq nat (@length B l) n))
                                (@exist (list B) (fun l : list B => @eq nat (@length B l) n) (@nil B) vlen)
                        | cons a rest =>
                            fun vlen : @eq nat (S (@length (prod E A) rest)) n =>
                              match
                                n as n0
                                return (forall _ : @eq nat (S (@length (prod E A) rest)) n0, Backwards option (Vector n0 B))
                              with
                              | O =>
                                  fun vlen' : @eq nat (S (@length (prod E A) rest)) O =>
                                    @zero_not_S
                                      ((fix length (l : list (prod E A)) : nat :=
                                          match l return nat with
                                          | nil => O
                                          | cons _ l' => S (length l')
                                          end) rest) (Backwards option (Vector O B))
                                      (@eq_sym nat (S (@length (prod E A) rest)) O vlen')
                              | S m =>
                                  fun vlen' : @eq nat (S (@length (prod E A) rest)) (S m) =>
                                    @ap (Backwards option) (@Map_Backwards option Map_option)
                                      (@Mult_Backwards option Map_option Mult_option) (Vector m B) (Vector (S m) B)
                                      (@ap (Backwards option) (@Map_Backwards option Map_option)
                                         (@Mult_Backwards option Map_option Mult_option) B
                                         (forall _ : Vector m B, Vector (S m) B)
                                         (@pure (Backwards option) (@Pure_Backwards option Pure_option)
                                            (forall (_ : B) (_ : Vector m B), Vector (S m) B) (@vcons m B))
                                         (@compose (prod E A) (option B) (Backwards option B) (@mkBackwards option B) f a))
                                      (go rest m
                                         (@S_uncons
                                            ((fix length (l : list (prod E A)) : nat :=
                                                match l return nat with
                                                | nil => O
                                                | cons _ l' => S (length l')
                                                end) rest) m vlen'))
                              end vlen
                        end) l (@length (prod E A) l) (@eq_refl nat (@length (prod E A) l)))) as X.
        destruct X.
        + reflexivity.
        + reflexivity.
      }
      { (* Case 2 *)
        destruct Case2 as [b [Hfa rest]].
        cbn.
        rewrite map_None_eq_iff.
        rewrite map_None_eq_iff.
        Set Keyed Unification.
        rewrite rest.
        Unset Keyed Unification.
        rewrite Hfa.
        cbn.
        reflexivity.
      }
  Qed.

  Lemma traverse_Vector_None_spec {A B} (n: nat) (f: E * A -> option B):
    forall (l: list (E * A)) (e: length l = n),
      (forwards (traverse_Vector_core (mkBackwards ∘ f) l e) = None) <-> traverse f l = None.
  Proof.
    intros. split.
    apply traverse_Vector_None_spec1.
    apply traverse_Vector_None_spec2.
  Qed.

  Lemma mapdt_option_None_spec:
    forall (A B: Type) (t: T A) (f: E * A -> option B),
      (mapdt f t = None) <->
        exists (e: E) (a: A), (e, a) ∈d t /\ f (e, a) = None.
  Proof.
    intros.
    rewrite mapdt_repr.
    setoid_rewrite ind_iff_in_toctxlist1.
    remember (mapdt_contents t).
    destruct v.
    assert (list_spec: List.rev (toctxlist t) = x).
    { symmetry.
      enough (x = Vector_to_list _ (exist (fun l : list (E * A) => length l = plength t) x e)).
      rewrite H0.
      rewrite Heqv.
      apply mapdt_contents_toctxlist.
      reflexivity. }
    cbn in *.
    rewrite map_None_eq_iff.
    clear Heqv.
    destruct e.
    rewrite traverse_Vector_None_spec.
    rewrite list_traverse_None_iff.
    rewrite <- list_spec.
    setoid_rewrite <- in_list_rev_spec at 1.
    rewrite <- compat_toctxlist_mapdt.
    split.
    { intros [[e a] rest]; eauto. }
    { intros [e [a rest]]; eauto. }
  Qed.

End theory.



