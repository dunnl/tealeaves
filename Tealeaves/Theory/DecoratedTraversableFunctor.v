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
(******************************************************************************)
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
  (******************************************************************************)
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
  (******************************************************************************)
  Lemma mapdt_through_toBatch3
    `{Applicative G} `(f: E * A -> G B) :
    mapdt (E := E) (T := T) f = runBatch f ∘ toBatch3.
  Proof.
    intros.
    rewrite toBatch3_to_mapdt.
    rewrite kdtf_morph.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  (** ** Naturality of <<toBatch3>> *)
  (******************************************************************************)
  Lemma toBatch3_mapdt
    `{Applicative G}
    {A A' B: Type} (f: E * A -> G A') :
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
    {A A' B: Type} (f: E * A -> A') :
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
    {A A' B: Type} (f: A -> A') {C: Type} :
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
  (******************************************************************************)
  Section runBatch.

  (** ** Core Operations *)
  (******************************************************************************)
  Theorem mapdt_through_runBatch `{Applicative G} `(f: E * A -> G B) :
    mapdt f = runBatch f ∘ toBatch3.
  Proof.
    intros.
    rewrite toBatch3_to_mapdt.
    rewrite kdtf_morph.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary traverse_through_runBatch `{Applicative G} `(f: A -> G B) :
    traverse f = runBatch (f ∘ extract (W := (E ×))) ∘ toBatch3.
  Proof.
    rewrite traverse_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapd_through_runBatch `(f: E * A -> B) :
      mapd f = runBatch (G := fun A => A) f ∘ toBatch3.
  Proof.
    intros.
    rewrite mapd_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f: A -> B) :
      map f = runBatch (G := fun A => A) (f ∘ extract) ∘ toBatch3.
  Proof.
    intros.
    rewrite map_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  (** ** <<foldMapd>> Through <<toBatch3>> *)
  (******************************************************************************)
  Lemma foldMapd_through_runBatch1 {A} `{Monoid M}: forall `(f: E * A -> M),
      foldMapd f = runBatch (G := const M) f (C := T False) ∘ toBatch3 (B := False).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_through_runBatch (G := const M)).
    reflexivity.
  Qed.

  Lemma foldMapd_through_runBatch2 `{Monoid M}: forall (A fake: Type) `(f: E * A -> M),
      foldMapd f = runBatch (G := const M) f (C := T fake) ∘ toBatch3 (B := fake).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_constant_applicative2 False False fake).
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  (** ** <<toctxlist>> Through <<toBatch3>> *)
  (******************************************************************************)
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
    rewrite element_ctx_of_to_foldMapd.
    rewrite foldMapd_through_runBatch1.
    reflexivity.
  Qed.

(** * Respectfulness Properties *)
(******************************************************************************)
Section decorated_traversable_functor_theory.

  (** ** Purity *)
  (******************************************************************************)
  Theorem mapdt_purity1 :
    forall `{Applicative G},
      `(mapdt (G := G) (pure ∘ extract) = @pure G _ (T A)).
  Proof.
    intros.
    rewrite <- (kdtf_morph (G1 := fun A => A) (G2 := G)).
    rewrite kdtf_mapdt1.
    reflexivity.
  Qed.

  (** ** Characterizing <<∈d>> and <<mapd>> *)
  (******************************************************************************)
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

  Lemma mapd_respectful :
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
(******************************************************************************)
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
(******************************************************************************)
Section deconstruction.

  Import Kleisli.DecoratedTraversableFunctor.DerivedInstances.

  #[local] Generalizable Variables v.

  (** ** Relating <<plength>> and <<toBatch3>> *)
  (******************************************************************************)
  Lemma plength_toBatch3:
    forall {A} {B} (t: T A),
      plength t = length_Batch (toBatch3 (A := A) (B := B) t).
  Proof.
    intros.
    unfold plength.
    rewrite (foldMap_through_runBatch2 A B).
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
  (******************************************************************************)
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
  (******************************************************************************)
  Lemma Batch3_contents_toctxlist:
    forall {A B} (t: T A),
      Vector_to_list (E * A) (Batch_contents (toBatch3 (B := B) t)) =
        List.rev (toctxlist t).
  Proof.
    intros.
    rewrite toctxlist_to_foldMapd.
    rewrite (foldMapd_through_runBatch2 A B).
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
  (******************************************************************************)
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

  (** ** Lemmas regarding <<trav_make>> *)
  (******************************************************************************)
  (*
  Section trav_make_lemmas.

    Context
      {A B: Type}.

    Lemma trav_make_sim1:
      forall (t: T A) `{v1 ~~ v2},
        trav_make (B := B) t v1 = trav_make t v2.
    Proof.
      intros.
      unfold trav_make.
      apply Batch_make_sim1.
      vector_sim.
    Qed.

    Lemma trav_make_sim2:
      forall `(t1: T A) (t2: T A)
        `(v1: Vector (plength t1) B)
        `(v2: Vector (plength t2) B),
        t1 = t2 ->
        Vector_sim v1 v2 ->
        trav_make t1 v1 = trav_make t2 v2.
    Proof.
      intros.
      subst.
      now apply trav_make_sim1.
    Qed.

  End trav_make_lemmas.
   *)

  (** * Miscellaneous *)
  (******************************************************************************)
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
  (******************************************************************************)
  Section lens_laws.

    Import KleisliToCoalgebraic.DecoratedTraversableFunctor.DerivedInstances.
    Import KleisliToCoalgebraic.TraversableFunctor.DerivedInstances.

    (** ** get-put *)
    (******************************************************************************)
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
    (******************************************************************************)
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
    (******************************************************************************)
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
  (******************************************************************************)
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

  End runBatch.
End theory.
