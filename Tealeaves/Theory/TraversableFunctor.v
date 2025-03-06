From Tealeaves Require Export
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Functors.Batch
  Functors.List
  Functors.VectorRefinement.

Import Coalgebraic.TraversableFunctor (ToBatch, toBatch).
Import KleisliToCoalgebraic.TraversableFunctor.DerivedInstances.

Import Subset.Notations.
Import Applicative.Notations.
Import ContainerFunctor.Notations.
Import ProductFunctor.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import Batch.Notations.
Import Monoid.Notations.
Import VectorRefinement.Notations.

#[local] Generalizable Variables F T G A B C M ϕ.

#[local] Arguments mapfst_Batch {B C A1 A2}%type_scope
  f%function_scope b.
#[local] Arguments mapsnd_Batch {A B1 B2 C}%type_scope
  f%function_scope b.


(** * Miscellaneous Properties Concerning <<toBatch>> *)
(**********************************************************************)
Section stuff.

  Import Adapters.KleisliToCoalgebraic.TraversableFunctor.

  Context
    `{Kleisli.TraversableFunctor.TraversableFunctor T}
    `{Map T}
    `{ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  (** ** Relating <<tolist>> and <<Batch_contents ∘ toBatch>> *)
  (********************************************************************)
  Lemma Batch_contents_tolist:
    forall {A B} (t: T A),
      proj1_sig (Batch_contents (toBatch (A' := B) t)) =
        List.rev (tolist t).
  Proof.
    intros.
    rewrite tolist_Batch_contents.
    rewrite <- tolist_through_toBatch.
    reflexivity.
  Qed.

  (** ** Naturality of <<toBatch>> *)
  (********************************************************************)
  Corollary shape_natural_toBatch {A A'}: forall (t: T A),
      toBatch (A' := A') (shape t) =
        shape (F := BATCH1 A' (T A')) (toBatch (A' := A') t).
  Proof.
    intros. unfold shape. compose near t.
    now rewrite toBatch_mapfst.
  Qed.

  Corollary shape_toBatch_spec {A}: forall (t: T A),
      shape t = runBatch (G := fun A => A) (const tt)
                  (toBatch (A' := unit) (T := T) t).
  Proof.
    intros.
    unfold shape.
    rewrite map_through_runBatch.
    reflexivity.
  Qed.

  (* This statement holds without a A' universally quantified
     inside the iff, but this is harder to prove. *)
  Lemma toBatch_injective_univ {A}: forall (t u: T A),
      (forall (A': Type), toBatch (A' := A') t = toBatch u) <-> t = u.
  Proof.
    intros. split.
    - intro HBatch.
      change (id t = id u).
      rewrite id_through_runBatch.
      unfold compose.
      rewrite HBatch.
      reflexivity.
    - intro; now subst.
  Qed.

  (** ** <<Batch_contents ∘ toBatch>> is Independent of <<B>> *)
  (********************************************************************)
  Lemma Batch_contents_toBatch_sim:
    forall {A B B': Type} (t: T A),
      Batch_contents (toBatch (A' := B) t)
      ~~ Batch_contents (toBatch (A' := B') t).
  Proof.
    intros.
    unfold Vector_sim.
    rewrite Batch_contents_tolist.
    rewrite Batch_contents_tolist.
    reflexivity.
  Qed.

  (** *** Terms with the same <<shape>> have <<toBatch>> of the same shape *)
  (********************************************************************)
  Lemma same_shape_toBatch:
    forall {A' B} `(t1: T A) (t2: T A'),
      shape t1 = shape t2 ->
      shape (F := BATCH1 B (T B))
        (toBatch (A' := B) t1) =
        shape (F := BATCH1 B (T B))
          (toBatch (A' := B) t2).
  Proof.
    introv Hshape.
    rewrite <- shape_natural_toBatch.
    rewrite <- shape_natural_toBatch.
    rewrite Hshape.
    reflexivity.
  Qed.

  (** *** Terms with the same <<tolist>> terms have <<toBatch>> of the same <<tolist>>s*)
  (********************************************************************)
  Lemma same_tolist_toBatch:
    forall {B1 B2: Type} `(t1: T A) (t2: T A),
      tolist t1 = tolist t2 ->
      tolist (toBatch (A' := B1) t1) =
        tolist (toBatch (A' := B2) t2).
  Proof.
    introv Hshape.
    rewrite (tolist_through_toBatch B1) in Hshape.
    rewrite (tolist_through_toBatch (T := T) B2) in Hshape.
    assumption.
  Qed.


  (** ** Equal <<toBatch>> Implies Equal <<tolist>> *)
  (********************************************************************)
  Lemma toBatch_injective_tolist:
    forall {A B} `(t1: T A) (t2: T A),
      (toBatch (A' := B) t1) =
        (toBatch (A' := B) t2) ->
      tolist t1 = tolist t2.
  Proof.
    introv Heq.
    rewrite (tolist_through_toBatch B).
    rewrite (tolist_through_toBatch (T := T) B).
    rewrite Heq.
    reflexivity.
  Qed.

  (** ** Similar <<shape>>d <<toBatch>> implies similar <<shape>>s*)
  (********************************************************************)
  Lemma toBatch_shape_inv:
    forall {A' B} `(t1: T A) (t2: T A'),
      shape (F := BATCH1 B (T B))
        (toBatch (A' := B) t1) =
        shape (F := BATCH1 B (T B))
          (toBatch (A' := B) t2) ->
      shape t1 = shape t2.
  Proof.
    introv.
    intro HBatch.
    rewrite <- shape_natural_toBatch in HBatch.
    rewrite <- shape_natural_toBatch in HBatch.
    unfold shape.
  Abort.

  Lemma toBatch_injective_shape:
    forall {A B} `(t1: T A) (t2: T A),
      (toBatch (A' := B) t1) =
        (toBatch (A' := B) t2) ->
      shape t1 = shape t2.
  Proof.
    introv Heq.
    unfold shape at 1 2.
  Abort.


  Lemma toBatch_injective_tolist2:
    forall {A B} `(t1: T A) (t2: T A),
      (toBatch (A' := B) t1) =
        (toBatch (A' := B) t2) <->
        tolist t1 = tolist t2.
  Proof.
    intros. split.
    - apply toBatch_injective_tolist.
    - rewrite (tolist_through_toBatch B).
      rewrite (tolist_through_toBatch (T := T) B).
  Abort.

  Lemma toBatch_injective:
    forall {A B} `(t1: T A) (t2: T A),
        (toBatch (A' := B) t1) =
          (toBatch (A' := B) t2) ->
        t1 = t2.
  Proof.
    introv Heq.
    change (id t1 = id t2).
    rewrite id_through_runBatch.
    unfold compose.
  Abort.

End stuff.

(** * Length of <<toBatch>> is polymorphic *)
(**********************************************************************)
Lemma length_Batch_independent
  `{TraversableFunctor T}
  `{ToBatch T}
  `{Map T}
  `{! Compat_Map_Traverse T}
  `{! Compat_ToBatch_Traverse T}
 : forall `(t: T A) B C,
    length_Batch (toBatch (A' := B) t) =
      length_Batch (toBatch (A' := C) t).
Proof.
Abort.

(** * Traversable Functors are Containers *)
(**********************************************************************)

(** ** Traversable Functors are Shapely *)
(**********************************************************************)
Section shapeliness.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Theorem Traversable_shapeliness: forall A (t1 t2: T A),
      shape t1 = shape t2 /\ tolist t1 = tolist t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    change (id t1 = id t2).
    rewrite id_through_runBatch.
    unfold compose.
    enough (cut: toBatch (A' := A) t1 = toBatch t2)
      by now rewrite cut.
    specialize (same_shape_toBatch (B := A) t1 t2 hyp1).
    specialize (same_tolist_toBatch (B1 := A) (B2 := A) t1 t2 hyp2).
    intros. apply Batch_shapeliness; assumption.
  Qed.

End shapeliness.

(** ** Pointwise Reasoning *)
(**********************************************************************)
Section pointwise.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{ToMap_inst: Map T}
    `{ToSubset_inst: ToSubset T}
    `{ToBatch_inst: ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Lemma traverse_respectful:
    forall `{Applicative G} `(f1: A -> G B) `(f2: A -> G B) (t: T A),
      (forall (a: A), a ∈ t -> f1 a = f2 a) -> traverse f1 t = traverse f2 t.
  Proof.
    introv ? hyp.
    do 2 rewrite traverse_through_runBatch.
    unfold element_of in hyp.
    rewrite (tosubset_through_runBatch2 A B) in hyp.
    unfold compose in *.
    unfold ret in *.
    induction (toBatch t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros.
        apply hyp. now left.
      + apply hyp. now right.
  Qed.

  (** *** Corollaries *)
  (********************************************************************)
  Corollary traverse_respectful_pure:
    forall `{Applicative G} `(f1: A -> G A) (t: T A),
      (forall (a: A), a ∈ t -> f1 a = pure a) -> traverse f1 t = pure t.
  Proof.
    intros.
    rewrite <- traverse_purity1.
    now apply traverse_respectful.
  Qed.

  Corollary traverse_respectful_map {A B}:
    forall `{Applicative G} (t: T A) (f: A -> G B) (g: A -> B),
      (forall a, a ∈ t -> f a = pure (g a)) -> traverse f t = pure (map g t).
  Proof.
    intros. rewrite <- (traverse_purity1 (G := G)).
    compose near t on right.
    rewrite traverse_map.
    apply traverse_respectful.
    assumption.
  Qed.

  Corollary traverse_respectful_id {A}:
    forall (t: T A) (f: A -> A),
      (forall a, a ∈ t -> f a = id a) -> traverse (G := fun A => A) f t = t.
  Proof.
    intros.
    change t with (pure (F := fun A => A) t) at 2.
    apply (traverse_respectful_pure (G := fun A => A)).
    assumption.
  Qed.

  Corollary map_respectful: forall `(f1: A -> B) `(f2: A -> B) (t: T A),
      (forall (a: A), a ∈ t -> f1 a = f2 a) -> map f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite map_to_traverse.
    rewrite map_to_traverse.
    apply (traverse_respectful (G := fun A => A)).
    assumption.
  Qed.

  (** ** Typeclass Instances *)
  (********************************************************************)
  #[export] Instance ContainerFunctor_Traverse:
    ContainerFunctor T.
  Proof.
    constructor.
    - rewrite compat_tosubset_traverse.
      typeclasses eauto.
    - apply DerivedInstances.Functor_TraversableFunctor.
    - intros. now apply map_respectful.
  Qed.

  #[export] Instance ShapelyFunctor_Traverse:
    ShapelyFunctor T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - unfold shapeliness.
      apply Traversable_shapeliness.
  Qed.

End pointwise.

(** * <<plength>> *)
(**********************************************************************)
Section length.

  Context
    `{Map T}
    `{ToBatch T}
    `{Traverse T}
    `{! TraversableFunctor T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Lemma plength_eq_length:
    forall {A} {B} (t: T A),
      length_Batch (toBatch (A' := B) t) = plength t.
  Proof.
    intros.
    unfold plength.
    rewrite (foldMap_through_runBatch2 A B).
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn.
      rewrite IHb.
      unfold_ops @NaturalNumbers.Monoid_op_plus.
      lia.
  Qed.

  Lemma plength_eq_length': forall {A} (t: T A),
      plength t = length_Batch (toBatch (A' := False) t).
  Proof.
    intros.
    symmetry.
    apply plength_eq_length.
  Qed.

End length.

(** * Factorizing Terms into <<shape>> and <<contents>> *)
(**********************************************************************)
Section deconstruction.

  Definition trav_contents
    {T: Type -> Type} {toBatch_T: ToBatch T} {traverse_T: Traverse T} {map_T: Map T}
    {cmt: Compat_Map_Traverse T}
    {cbt: Compat_ToBatch_Traverse T}
    {Trav_T: TraversableFunctor T}
    {A} (t: T A): Vector (plength t) A :=
    let v: Vector
             (length_Batch (toBatch (ToBatch := toBatch_T) (A' := False) t)) A
      := Batch_contents (toBatch t)
    in coerce_Vector_length (plength_eq_length t) v.

  Definition trav_make
    {T: Type -> Type}
    {map_T: Map T}
    {traverse_T: Traverse T}
    {toBatch_T: ToBatch T}
    {cmt: Compat_Map_Traverse T}
    {cmt: Compat_ToBatch_Traverse T}
    {Trav_T: TraversableFunctor T}
    {A B: Type} (t: T A):
    Vector (plength t) B -> T B :=
    (fun v =>
       let v' := coerce_Vector_length (eq_sym (plength_eq_length t)) v
       in Batch_make (toBatch t) v').

  Context
    `{Traverse T}
    `{Map T}
    `{ToBatch T}
    `{! TraversableFunctor T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  #[local] Generalizable Variables v.


  (** ** Operations on Vectors *)
  (********************************************************************)
  Section traverse_vector.

    Lemma trav_contents_Vector {n: nat} {A: Type}:
      forall (v: Vector n A),
        trav_contents v ~~ reverse_Vector v.
    Proof.
      intros.
      unfold Vector_sim.
      unfold trav_contents.
      rewrite <- coerce_Vector_contents.
      induction v using Vector_induction.
      - reflexivity.
      - rewrite toBatch_to_traverse.
        rewrite traverse_Vector_vcons.
        rewrite Batch_contents_rw_app.
        rewrite proj_Vector_append.
        rewrite Batch_contents_rw_app.
        rewrite proj_Vector_append.
        rewrite Batch_contents_rw_pure.
        rewrite proj_reverse_Vector.
        rewrite proj_vcons.
        cbn.
        rewrite <- proj_reverse_Vector.
        rewrite <- IHv.
        reflexivity.
    Qed.

    Lemma trav_make_Vector {n: nat} {A B: Type}:
      forall (v1: Vector n A) (v2: Vector (plength v1) B),
        (trav_make (B := B) v1 v2) ~~ v2.
    Proof.
      intros.
      induction v1 using Vector_induction.
      - assert (Hey: v2 = vnil).
        { apply Vector_nil_eq. }
        rewrite Hey.
        reflexivity.
      - cbn in v2.
        unfold trav_make.
        pose (toBatch_to_traverse (T := Vector (S m)) A B).
    Abort.

  End traverse_vector.

  (** ** Lemmas regarding <<trav_make>> *)
  (********************************************************************)
  Section trav_make_lemmas.

    Context
      {A B: Type}.

    Lemma trav_make_sim_refl:
      forall (t: T A), trav_make (B := B) t ~!~ trav_make t.
    Proof.
      intros.
      unfold trav_make.
      unfold Vector_fun_sim. split.
      - reflexivity.
      - intros.
        apply Batch_make_sim1.
        apply Vector_coerce_sim_l'.
        apply Vector_coerce_sim_r'.
        assumption.
    Qed.

    Lemma toBatch_trav_make_to_replace_contents
      {A'} {t: T A} {v: Vector (plength t) B}:
      toBatch (A' := A') (trav_make t v) =
        Batch_replace_contents (toBatch (A' := A') t)
          (coerce eq_sym (plength_eq_length t) in v).
    Proof.
      unfold trav_make.
      rewrite Batch_make_natural_rw1.
      rewrite Batch_replace_contents_spec.
      apply Batch_make_sim2.
      - compose near t.
        rewrite (TraversableFunctor.trf_duplicate (T := T)).
        rewrite compat_toBatch_traverse.
        reflexivity.
      - vector_sim.
    Qed.

    (** ** Naturality of <<trav_contents>> and <<trav_make>> *)
    (******************************************************************)
    Lemma trav_contents_natural:
      forall (A B: Type) (t: T A) (f: A -> B),
        trav_contents (map f t) ~~ map f (trav_contents t).
    Proof.
      intros.
      unfold Vector_sim.
      unfold trav_contents.
      rewrite <- coerce_Vector_contents.
      rewrite <- map_coerce_Vector.
      compose near t on left.
      rewrite toBatch_mapfst.
      unfold compose at 2.
      rewrite Batch_contents_natural.
      reflexivity.
    Qed.

    Lemma trav_make_natural:
      forall (A B C: Type) (t: T A) (f: B -> C) (v: Vector (plength t) B),
        trav_make t (map f v) = map f (trav_make t v).
    Proof.
      intros.
      unfold trav_make.
      rewrite (Batch_make_natural_rw1 (toBatch t) (map f)).
      assert (cut: map (map f) (toBatch t) =
                     mapsnd_Batch f (toBatch t)).
      { compose near t.
        now rewrite (toBatch_mapsnd). }
      rewrite (Batch_make_rw
                 (map (map f) (toBatch t))
                 (mapsnd_Batch f (toBatch t))
                 cut).
      rewrite coerce_Vector_compose.
      rewrite coerce_Vector_compose.
      rewrite Batch_make_natural2.
      apply Batch_make_sim1.
      apply Vector_coerce_sim_r'.
      apply Vector_coerce_sim_l'.
      apply map_coerce_Vector.
    Qed.

  End trav_make_lemmas.

  (** ** Relating <<tolist>> and <<trav_contents>> *)
  (********************************************************************)
  Lemma tolist_trav_contents `{t: T A}:
    Vector_to_list A (trav_contents t) = List.rev (tolist t).
  Proof.
    intros.
    unfold Vector_to_list.
    unfold trav_contents.
    rewrite <- coerce_Vector_contents.
    rewrite tolist_Batch_contents.
    rewrite <- tolist_through_toBatch.
    reflexivity.
  Qed.

  (** ** Lens-like laws *)
  (********************************************************************)
  Section lens_laws.

    (** *** get-put *)
    (******************************************************************)
    Lemma trav_get_put `{t: T A}:
      trav_make t (trav_contents t) = t.
    Proof.
      unfold trav_make, trav_contents.
      rewrite coerce_Vector_compose.
      hide_lhs;
        change t with (id t);
        rewrite <- TraversableFunctor.trf_extract;
        rewrite Heqlhs; clear Heqlhs lhs;
        unfold compose at 1.
      rewrite <- Batch_make_contents.
      apply Batch_make_sim1.
      vector_sim.
      apply Batch_contents_toBatch_sim.
    Qed.

    (** *** put-get *)
    (******************************************************************)
    Lemma trav_contents_make {A B} {t: T A} {v: Vector (plength t) B}:
      trav_contents (trav_make t v) ~~ v.
    Proof.
      unfold trav_contents.
      vector_sim.
      rewrite toBatch_trav_make_to_replace_contents.
      rewrite Batch_put_get.
      vector_sim.
    Qed.

    (** *** put-put *)
    (******************************************************************)
    Lemma trav_make_make_
            `(t: T A) `(v: Vector (plength t) B)
            `(v1: Vector (plength (trav_make t v)) B')
            (v2: Vector (plength t) B')
            (pf: v1 ~~ v2):
      trav_make (trav_make t v) v1 =
        trav_make t v2.
    Proof.
      unfold trav_make at 1.
      unfold trav_make at 7.
      apply Batch_make_sim3.
      - symmetry.
        rewrite toBatch_trav_make_to_replace_contents.
        apply Batch_shape_replace_contents.
      - vector_sim.
    Qed.

    Lemma plength_trav_make: forall `(t: T A) `(v: Vector _ B),
        plength t = plength (trav_make t v).
    Proof.
      intros.
      unfold plength at 1 2.
      do 2 change (fun (x:?X) => 1) with (const (A := X) 1).
      do 2 rewrite (foldMap_through_runBatch2 _ B).
      unfold compose.
      rewrite (@toBatch_trav_make_to_replace_contents A B B t v).
      rewrite <- (runBatch_const_contents (G := @const Type Type nat)).
      reflexivity.
    Qed.

    Lemma trav_make_make:
      forall `(t: T A) `(v: Vector (plength t) B) (C: Type),
      trav_make (B := C) (trav_make t v) ~!~
        trav_make t.
    Proof.
      intros.
      unfold Vector_fun_sim. split.
      - rewrite <- plength_trav_make.
        reflexivity.
      - intros.
        now rewrite (trav_make_make_ t v v1 v2).
    Qed.

    (** ** Lemmas regarding <<shape>> and <<trav_make>> *)
    (******************************************************************)
    Lemma trav_same_shape {A1 A2: Type}
      {t1: T A1} {t2: T A2}:
      shape t1 = shape t2 ->
      forall B, trav_make (B := B) t1 ~!~ trav_make t2.
    Proof.
      intros.
      unfold trav_make.
      apply Vector_coerce_fun_sim_l'.
      apply Vector_coerce_fun_sim_r'.
      apply Batch_make_shape.
      apply same_shape_toBatch.
      assumption.
    Qed.

  End lens_laws.

  (** ** Representation theorems *)
  (********************************************************************)
  Lemma traverse_repr:
    forall `{Applicative G} (A B: Type) (t: T A) (f: A -> G B),
      traverse f t =
        map (trav_make t) (forwards (traverse (mkBackwards ∘ f) (trav_contents t))).
  Proof.
    intros.
    rewrite traverse_through_runBatch.
    unfold compose at 1.
    rewrite runBatch_repr2.
    unfold trav_make, trav_contents.
    rewrite (traverse_Vector_coerce _ _ _ (plength_eq_length t)).
    change_left (
        map (Batch_make (toBatch t))
          (map
             (fun v: Vector (plength t) B =>
                coerce eq_sym (plength_eq_length (B := B) t) in v)
             (forwards
                (traverse (mkBackwards ∘ f)
                   (coerce (plength_eq_length (B := B) t) in
                     Batch_contents (toBatch t)))))).
    compose near ((forwards
                     (traverse (mkBackwards ∘ f)
                        (coerce (plength_eq_length (B := B) t)
                          in Batch_contents (toBatch t))))).
    rewrite (fun_map_map).
    fequal.
    fequal.
    fequal.
    apply Vector_eq.
    apply Vector_coerce_sim_l'.
    apply Vector_coerce_sim_r'.
    eapply Batch_contents_toBatch_sim.
  Qed.

  (** ** Corollary: Spec for <<traverse>> After Applying <<trav_make>> *)
  (********************************************************************)
  Corollary traverse_trav_make:
    forall `{Applicative G} (X A B: Type)
      (t: T X) (f: A -> G B) (v: Vector (plength t) A),
      traverse (T := T) f (trav_make t v) =
        map (trav_make t) (forwards (traverse (mkBackwards ∘ f) v)).
  Proof.
    intros.
    rewrite traverse_repr.
    assert (Hlen: plength (trav_make t v) = plength t).
    { now rewrite <- plength_trav_make. }
    rewrite (map_sim_function B (T B) _ _ (trav_make (trav_make t v))
               (trav_make t (B := B)) Hlen).
    2: { apply trav_make_make. }
    change (?f ○ ?pre) with (f ∘ pre).
    rewrite <- (fun_map_map).
    unfold compose at 1.
    fequal.
    compose near (traverse (mkBackwards ∘ f) (trav_contents (trav_make t v))).
    rewrite (natural (Natural := Natural_forwards)).
    unfold compose.
    fequal.
    apply map_sim_function_traverse_Vector.
    apply trav_contents_make.
  Qed.

  Lemma foldMap_opposite_traverse {A}:
    forall `{Monoid M} `{TraversableFunctor T'}
      `{ToBatch T'} `{! Compat_ToBatch_Traverse T'} (t: T' A) (f: A -> M),
      foldMap (op := Monoid_op_Opposite op) f t =
        forwards (traverse (B := False) (T := T') (G := Backwards (const M)) (mkBackwards ∘ f) t).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_through_runBatch.
    rewrite traverse_through_runBatch.
    unfold compose.
    induction (@toBatch T' _ A False t).
    - reflexivity.
    - rewrite runBatch_rw2.
      rewrite IHb.
      rewrite runBatch_rw2.
      reflexivity.
  Qed.

  Corollary foldMap_trav_make:
    forall `{Monoid M} (X A: Type)
      (t: T X) (f: A -> M) (v: Vector (plength t) A),
      foldMap (T := T) f (trav_make t v) =
        foldMap (op := Monoid_op_Opposite op) f v.
  Proof.
    intros.
    unfold foldMap.
    rewrite traverse_trav_make.
    unfold_ops @Map_const.
    setoid_rewrite <- (foldMap_opposite_traverse (T' := Vector (plength t))).
    reflexivity.
  Qed.

  (** ** Corollary: Specs for Functor Operations in Terms of Lens Operations *)
  (********************************************************************)
  Lemma id_spec:
    forall (A: Type) (t: T A),
      id t = trav_make t (trav_contents t).
  Proof.
    intros.
    rewrite trav_get_put.
    reflexivity.
  Qed.

  Lemma map_spec:
    forall (A B: Type) (t: T A) (f: A -> B),
      map f t = trav_make t (map f (trav_contents t)).
  Proof.
    intros A B t f.
    rewrite <- trav_get_put at 1.
    apply Vector_fun_sim_eq.
    - apply trav_same_shape.
      rewrite shape_map.
      reflexivity.
    - apply trav_contents_natural.
  Qed.

  (** ** Corollary: Specification for <<shape>> *)
  (********************************************************************)
  Lemma trav_contents_shape:
    forall (A: Type) (t: T A),
      trav_contents (shape t) ~~ Vector_tt (plength t).
  Proof.
    intros.
    (* LHS *)
    unfold trav_contents.
    apply Vector_coerce_sim_l'.
    unfold shape.
    replace (toBatch (A' := False) (map (const tt) t))
      with (mapfst_Batch (B := False) (const tt) (toBatch t)).
    2:{ compose near t.
        now rewrite toBatch_mapfst. }
    unfold Vector_tt.
    unfold plength.
    rewrite foldMap_through_runBatch1.
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn.
      unfold_ops @NaturalNumbers.Monoid_op_plus.
      rewrite PeanoNat.Nat.add_1_r.
      cbn.
      apply vcons_sim.
      assumption.
  Qed.

  Lemma shape_spec:
    forall (A: Type) (t: T A),
      shape t = trav_make (B := unit) t (Vector_tt (plength t)).
  Proof.
    intros A t.
    unfold shape.
    rewrite map_spec.
    fequal.
    apply Vector_sim_eq.
    unfold Vector_sim.
    rewrite <- (trav_contents_natural A unit t (const tt)).
    change (map (const tt) t) with (shape t).
    rewrite trav_contents_shape.
    reflexivity.
  Qed.

  Lemma trav_same_shape_rev {A1 A2: Type}
    {t1: T A1} {t2: T A2}:
    (forall B, trav_make (B := B) t1 ~!~ trav_make t2) ->
    shape t1 = shape t2.
  Proof.
    introv Hmake.
    rewrite shape_spec.
    rewrite shape_spec.
    destruct (Hmake unit) as
      [Hlen Hmake'].
    apply Vector_fun_sim_eq.
    - apply Hmake.
    - now inversion Hlen.
  Qed.

  Lemma trav_same_shape_iff {A1 A2: Type}
    {t1: T A1} {t2: T A2}:
    shape t1 = shape t2 <->
      (forall B, trav_make (B := B) t1 ~!~ trav_make t2).
  Proof.
    split.
    - apply trav_same_shape.
    - apply trav_same_shape_rev.
  Qed.

  Corollary trav_make_sim_map:
    forall `(t: T A)
      `(f: A -> B) (C: Type),
      trav_make (B := C) t ~!~
        (trav_make (B := C) (map (F := T) f t)).
  Proof.
    intros.
    apply trav_same_shape_iff.
    rewrite shape_map.
    reflexivity.
  Qed.

  (** ** <<trav_make>> is Preserved by <<shape>> *)
  (********************************************************************)
  Lemma trav_make_shape_spec {A B: Type}: forall (t: T A),
      trav_make (B := B) t ~!~ trav_make (B := B) (shape t).
  Proof.
    intros t.
    apply trav_same_shape.
    rewrite shape_shape.
    reflexivity.
  Qed.

  (** ** <<tosubset>> is Preserved by <<trav_contents>> *)
  (********************************************************************)
  Lemma tosubset_spec `{ToSubset T} `{! Compat_ToSubset_Traverse T}:
    forall (A: Type) (t: T A),
      tosubset t = tosubset (trav_contents t).
  Proof.
    intros A t.
    rewrite tosubset_through_tolist.
    unfold compose at 1.
    rewrite (tosubset_through_tolist (T := Vector (plength t))).
    unfold compose at 1.
    rewrite <- Vector_to_list_tolist.
    rewrite tolist_trav_contents.
    rewrite tosubset_to_foldMap.
    apply foldMap_comm_list.
  Qed.

End deconstruction.

(** * Lemmas about <<shape>> *)
(**********************************************************************)
Section misc.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{ToMap_inst: Map T}
    `{ToSubset_inst: ToSubset T}
    `{ToBatch_inst: ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

    (*
  (** ** Same <<shape>> Implies Same <<trav_make>> *)
  (********************************************************************)
  Lemma same_shape_implies_make_sim:
    forall (A B C: Type) (t: T A) (u: T B),
      shape t = shape u ->
      trav_make (B := C) t ~!~ trav_make u.
  Proof.
    intros. apply trav_same_shape.
    assumption.
    introv Hshape.
    eapply (transitive_Vector_fun_sim).
    apply (trav_make_shape_spec t).
    rewrite Hshape.
    apply symmetric_Vector_fun_sim.
    apply (trav_make_shape_spec u).
  Qed.
   *)

  (** ** Specification for <<id>> given two terms with the same <<shape>> *)
  (********************************************************************)
  Lemma same_shape_implies_other_make:
    forall (A B: Type) (t: T A) (u: T B)
      (Hshape: shape t = shape u),
      t = trav_make u
            (coerce (same_shape_implies_plength t u Hshape)
              in (trav_contents t)).
  Proof.
    intros.
    change t with (id t) at 1.
    rewrite id_spec.
    pose (cut := trav_same_shape Hshape A).
    destruct cut as [Hlen H_make_eq].
    apply H_make_eq.
    vector_sim.
  Qed.

End misc.

(** * Zipping Terms *)
(**********************************************************************)
From Tealeaves Require Import Functors.Pair.

Section traversable_functors_zipping.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{ToMap_inst: Map T}
    `{ToSubset_inst: ToSubset T}
    `{ToBatch_inst: ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  (** ** Operation to Zip Contents of Same-<<shape>> Terms *)
  (********************************************************************)
  Definition same_shape_zip_contents
    (A B: Type) (t: T A) (u: T B)
      (Hshape: shape t = shape u):
    Vector (plength t) (A * B) :=
      Vector_zip A B (plength t) (plength u) (trav_contents t) (trav_contents u)
        (same_shape_implies_plength t u Hshape).

  #[global] Arguments same_shape_zip_contents {A B}%type_scope t u Hshape.

  (** ** Proof Irrelevance *)
  (********************************************************************)
  Lemma same_shape_zip_contents_proof_irrelevance:
    forall (A B: Type) (t: T A) (u: T B)
      (Hshape1: shape t = shape u)
      (Hshape2: shape t = shape u),
      same_shape_zip_contents t u Hshape1 =
        same_shape_zip_contents t u Hshape2.
  Proof.
    intros.
    unfold same_shape_zip_contents.
    fequal.
    apply proof_irrelevance.
  Qed.

  (* useful when <<u>> can't be rewritten due to Hshape proofs *)
  Lemma same_shape_zip_contents_proof_irrelevance2:
    forall (A B: Type)
      (t: T A) (u: T B) (u': T B)
      (Hshape1: shape t = shape u)
      (Hshape2: shape t = shape u'),
      u = u' ->
      same_shape_zip_contents t u Hshape1 =
        same_shape_zip_contents t u' Hshape2.
  Proof.
    introv Heq.
    subst.
    apply same_shape_zip_contents_proof_irrelevance.
  Qed.

  (* useful when <<u>> can't be rewritten due to Hshape proofs *)
  Lemma same_shape_zip_contents_proof_irrelevance3:
    forall (A B: Type)
      (t: T A) (t': T A) (u: T B) (u': T B)
      (Hshape1: shape t = shape u)
      (Hshape2: shape t' = shape u'),
      t = t' ->
      u = u' ->
      (same_shape_zip_contents t u Hshape1 ~~
        same_shape_zip_contents t' u' Hshape2).
  Proof.
    introv Heqt Hequ.
    subst.
    erewrite same_shape_zip_contents_proof_irrelevance.
    reflexivity.
  Qed.

  (** ** Roundtrip Properties *)
  (********************************************************************)
  Lemma same_shape_zip_contents_fst
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    map fst (same_shape_zip_contents t u Hshape) = trav_contents t.
  Proof.
    unfold same_shape_zip_contents.
    rewrite Vector_zip_fst.
    reflexivity.
  Qed.

  Lemma same_shape_zip_contents_snd
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    map snd (same_shape_zip_contents t u Hshape) ~~ trav_contents u.
  Proof.
    unfold same_shape_zip_contents.
    apply (Vector_zip_snd A B
            (plength t) (plength u)
            (trav_contents t) (trav_contents u)
            (same_shape_implies_plength t u Hshape)).
  Qed.

  (** ** Naturality Properties *)
  (********************************************************************)
  Lemma same_shape_map {A1 A2 B1 B2}:
    forall (t: T A1) (u: T B1) (Hshape: shape t = shape u)
      (f: A1 -> A2) (g: B1 -> B2),
      shape (map f t) = shape (map g u).
  Proof.
    intros.
    rewrite (shape_map).
    rewrite (shape_map).
    assumption.
  Qed.

  Lemma same_shape_map_l {A1 A2 B}:
    forall (t: T A1) (u: T B) (Hshape: shape t = shape u)
      (f: A1 -> A2),
      shape (map f t) = shape u.
  Proof.
    intros.
    rewrite (shape_map).
    assumption.
  Qed.

  Lemma same_shape_map_r {A B1 B2}:
    forall (t: T A) (u: T B1) (Hshape: shape t = shape u)
      (g: B1 -> B2),
      shape t = shape (map g u).
  Proof.
    intros.
    rewrite (shape_map).
    assumption.
  Qed.

  Lemma same_shape_map_rev {A1 A2 B1 B2}:
    forall (t: T A1) (u: T B1)
      (f: A1 -> A2) (g: B1 -> B2)
      (Hshape: shape (map f t) = shape (map g u)),
      shape t = shape u.
  Proof.
    introv.
    rewrite (shape_map).
    rewrite (shape_map).
    easy.
  Qed.

  Lemma same_shape_map_rev_l {A1 A2 B}:
    forall (t: T A1) (u: T B)
      (f: A1 -> A2)
      (Hshape: shape (map f t) = shape u),
      shape t = shape u.
  Proof.
    introv.
    rewrite (shape_map).
    easy.
  Qed.

  Lemma same_shape_map_rev_r {A B1 B2}:
    forall (t: T A) (u: T B1)
      (g: B1 -> B2)
      (Hshape: shape t = shape (map g u)),
      shape t = shape u.
  Proof.
    introv.
    rewrite (shape_map).
    easy.
  Qed.

  Lemma natural_same_shape_zip_contents
    {A1 A2 B1 B2: Type}:
    forall (t: T A1) (u: T B1) (Hshape: shape t = shape u)
      (f: A1 -> A2) (g: B1 -> B2),
      map (map_pair f g) (same_shape_zip_contents t u Hshape)=
        coerce (natural_plength f t) in
      same_shape_zip_contents (map f t) (map g u) (same_shape_map t u Hshape _ _).
  Proof.
    intros.
    apply Vector_sim_eq.
    vector_sim.
    unfold same_shape_zip_contents.
    unfold Vector_zip.
    rewrite natural_Vector_zip_eq.
    apply Vector_zip_eq_sim_poly_both.
    - apply symmetric_Vector_sim.
      apply trav_contents_natural.
    - vector_sim.
      apply symmetric_Vector_sim.
      apply trav_contents_natural.
  Qed.

  Lemma natural_same_shape_zip_contents_op
    {A1 A2 B1 B2: Type}:
    forall (t: T A1) (u: T B1)
      (f: A1 -> A2) (g: B1 -> B2)
      (Hshape: shape (map f t) = shape (map g u)),
      same_shape_zip_contents (map f t) (map g u) Hshape =
        coerce (eq_sym (natural_plength f t)) in
      map (map_pair f g) (same_shape_zip_contents t u (same_shape_map_rev t u _ _ Hshape)).
  Proof.
    intros.
    rewrite natural_same_shape_zip_contents.
    apply Vector_sim_eq.
    vector_sim.
    vector_sim.
    fequal.
    fequal.
    apply proof_irrelevance.
  Qed.

  Corollary natural_fst_same_shape_zip_contents
    {A1 A2 B: Type}:
    forall (t: T A1) (u: T B) (Hshape: shape t = shape u)
      (f: A1 -> A2),
      map (map_fst f) (same_shape_zip_contents t u Hshape) =
        coerce (natural_plength f t) in
      same_shape_zip_contents (map f t) u (same_shape_map_l t u Hshape f).
  Proof.
    intros.
    rewrite map_fst_to_pair.
    rewrite natural_same_shape_zip_contents.
    apply Vector_sim_eq.
    vector_sim.
    fequal.
    apply same_shape_zip_contents_proof_irrelevance2.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Corollary natural_fst_same_shape_zip_contents_rev
    {A1 A2 B: Type}:
    forall (t: T A1) (u: T B)
      (f: A1 -> A2)
      (Hshape: shape (map f t) = shape u),
      same_shape_zip_contents (map f t) u Hshape =
        coerce (eq_sym (natural_plength f t)) in
        map (map_fst f) (same_shape_zip_contents t u (same_shape_map_rev_l _ _ _ Hshape)).

  Proof.
    intros.
    rewrite map_fst_to_pair.
    rewrite natural_same_shape_zip_contents.
    apply Vector_sim_eq.
    vector_sim.
    fequal.
    apply same_shape_zip_contents_proof_irrelevance2.
    rewrite fun_map_id.
    reflexivity.
  Qed.


  Corollary natural_snd_same_shape_zip_contents
    {A B1 B2: Type}:
    forall (t: T A) (u: T B1) (Hshape: shape t = shape u)
      (g: B1 -> B2),
      map (map_snd g) (same_shape_zip_contents t u Hshape) =
      same_shape_zip_contents t (map g u) (same_shape_map_r t u Hshape g).
  Proof.
    intros.
    rewrite map_snd_to_pair.
    rewrite natural_same_shape_zip_contents.
    apply Vector_sim_eq.
    vector_sim.
    apply same_shape_zip_contents_proof_irrelevance3.
    rewrite fun_map_id.
    reflexivity.
    reflexivity.
  Qed.

  Corollary natural_snd_same_shape_zip_contents_rev
    {A B1 B2: Type}:
    forall (t: T A) (u: T B1)
      (g: B1 -> B2)
      (Hshape: shape t = shape (map g u)),
      same_shape_zip_contents t (map g u) Hshape =
        map (map_snd g) (same_shape_zip_contents t u (same_shape_map_rev_r _ _ _ Hshape)).
  Proof.
    intros.
    rewrite map_snd_to_pair.
    rewrite natural_same_shape_zip_contents.
    apply Vector_sim_eq.
    vector_sim.
    apply same_shape_zip_contents_proof_irrelevance3.
    rewrite fun_map_id.
    reflexivity.
    reflexivity.
  Qed.

  (** ** Operation to Zip Same-<<shape>> Terms *)
  (********************************************************************)
  Definition same_shape_zip
    (A B: Type) (t: T A) (u: T B)
      (Hshape: shape t = shape u):
      T (A * B) :=
    trav_make t (same_shape_zip_contents t u Hshape).

  #[global] Arguments same_shape_zip {A B}%type_scope t u Hshape.

  Lemma same_shape_zip_fst
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    map fst (same_shape_zip t u Hshape) = t.
  Proof.
    unfold same_shape_zip.
    rewrite <- (trav_make_natural A (A * B) A t (@fst A B)
                 (same_shape_zip_contents t u Hshape)).
    rewrite same_shape_zip_contents_fst.
    rewrite trav_get_put.
    reflexivity.
  Qed.

  Lemma same_shape_zip_snd
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    map snd (same_shape_zip t u Hshape) = u.
  Proof.
    unfold same_shape_zip.
    rewrite <- (trav_make_natural A (A * B) B t (@snd A B)
                 (same_shape_zip_contents t u Hshape)).
    change u with (id u) at 2.
    rewrite id_spec.
    apply Vector_fun_sim_eq.
    - apply trav_same_shape.
      assumption.
    - apply same_shape_zip_contents_snd.
  Qed.

  (** ** Proof Irrelevance *)
  (********************************************************************)
  (* useful when <<u>> can't be rewritten due to Hshape proofs *)
  Lemma same_shape_zip_proof_irrelevance:
    forall (A B: Type)
      (t: T A) (t': T A) (u: T B) (u': T B)
      (Hshape1: shape t = shape u)
      (Hshape2: shape t' = shape u'),
      t = t' ->
      u = u' ->
      same_shape_zip t u Hshape1 =
        same_shape_zip t' u' Hshape2.
  Proof.
    introv Heqt Hequ.
    subst.
    fequal.
    apply proof_irrelevance.
  Qed.

  (** ** Naturality Properties *)
  (********************************************************************)
  Lemma natural_same_shape_zip
    {A1 A2 B1 B2: Type}:
    forall (t: T A1) (u: T B1) (Hshape: shape t = shape u)
      (f: A1 -> A2) (g: B1 -> B2),
      map (map_pair f g) (same_shape_zip t u Hshape) =
        same_shape_zip (map f t) (map g u) (same_shape_map t u Hshape _ _).
  Proof.
    intros.
    unfold same_shape_zip.
    rewrite <- trav_make_natural.
    rewrite natural_same_shape_zip_contents.
    apply Vector_fun_sim_eq.
    - apply trav_same_shape.
      rewrite shape_map.
      reflexivity.
    - vector_sim.
  Qed.

  Corollary natural_fst_same_shape_zip
    {A1 A2 B: Type}:
    forall (t: T A1) (u: T B) (Hshape: shape t = shape u)
      (f: A1 -> A2),
      map (map_fst f) (same_shape_zip t u Hshape) =
        same_shape_zip (map f t) u (same_shape_map_l t u Hshape f).
  Proof.
    intros.
    rewrite map_fst_to_pair.
    rewrite natural_same_shape_zip.
    apply same_shape_zip_proof_irrelevance.
    - reflexivity.
    - now rewrite fun_map_id.
  Qed.

  Corollary natural_snd_same_shape_zip
    {A B1 B2: Type}:
    forall (t: T A) (u: T B1) (Hshape: shape t = shape u)
      (g: B1 -> B2),
      map (map_snd g) (same_shape_zip t u Hshape) =
      same_shape_zip t (map g u) (same_shape_map_r t u Hshape g).
  Proof.
    intros.
    rewrite map_snd_to_pair.
    rewrite natural_same_shape_zip.
    apply same_shape_zip_proof_irrelevance.
    - rewrite fun_map_id.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma same_shape_zip_same_shape {A B}:
    forall (t: T A) (u: T B)
    (Hshape: shape t = shape u),
      shape (same_shape_zip t u Hshape) = shape t.
  Proof.
    intros.
    apply (same_shape_map_rev _ _ fst id).
    rewrite fun_map_id.
    rewrite same_shape_zip_fst.
    reflexivity.
  Qed.

  (** ** Traversals over the zip *)
  (**********************************************************************)
  Lemma map_sim_fns:
    forall (n m: nat) (A B C: Type) `{Applicative G}
      (mk1: Vector n B -> C) (v1: Vector n A)
      (mk2: Vector m B -> C) (v2: Vector m A)
      (f: A -> G B),
      mk1 ~!~ mk2 ->
      v1 ~~ v2 ->
      map (F := G) mk1 (traverse (G := G) (T := Vector n) f v1) = map (F := G) mk2 (traverse (T := Vector m) f v2).
  Proof.
    intros.
    assert (Heq: n = m) by (now apply Vector_sim_length in H2).
    generalize dependent v2.
    generalize dependent m.
    induction n; intros; subst.
    - rewrite (Vector_nil_eq v1).
      rewrite (Vector_nil_eq v2).
      rewrite traverse_Vector_vnil.
      fequal. ext v.
      apply Vector_fun_sim_eq.
      assumption. reflexivity.
    - rewrite (Vector_surjective_pairing2 (v := v2)) in *.
      rewrite (Vector_surjective_pairing2 (v := v1)) in *.
      rewrite traverse_Vector_vcons.
      rewrite traverse_Vector_vcons.
      inversion H2.
      do 2 rewrite proj_vcons in H4.
      inversion H4.
      fequal.
      { ext v. apply Vector_fun_sim_eq.
        assumption. reflexivity. }
      fequal.
      fequal.
      apply Vector_sim_eq.
      apply H6.
  Qed.

  Definition traverse_same_shape_zip
    `{Applicative G}
    (A B C: Type) (t: T A) (u: T B)
    (f: A * B -> G C)
    (Hshape: shape t = shape u)
    :
    traverse (T := T) f (same_shape_zip t u Hshape) =
      map (F := G) (trav_make t)
        (forwards (traverse (T := Vector (plength t)) (mkBackwards ∘ f) (same_shape_zip_contents t u Hshape))).
  Proof.
    assert (trav_make (B := C) (same_shape_zip t u Hshape) ~!~ trav_make t).
    { apply trav_same_shape.
      apply same_shape_zip_same_shape.
    }
    rewrite traverse_repr.
    assert (trav_contents (same_shape_zip t u Hshape) ~~
              (same_shape_zip_contents t u Hshape)).
    {  unfold same_shape_zip.
       unfold Vector_sim.
       rewrite trav_contents_make.
       reflexivity. }
    { compose near (traverse (mkBackwards ∘ f) (trav_contents (same_shape_zip t u Hshape))).
      compose near (traverse (mkBackwards ∘ f) (same_shape_zip_contents t u Hshape)).
      rewrite natural.
      rewrite natural.
      unfold compose.
      fequal.
      apply map_sim_fns; auto.
      typeclasses eauto.
    }
  Qed.

  Instance ApplicativeMorphism_const_op `{op: Monoid_op M} `{unit: Monoid_unit M} `{! Monoid M}:
    @ApplicativeMorphism (@const Type Type M) (Backwards (@const Type Type M))
      (@Map_const M) (@Mult_const M (@Monoid_op_Opposite M op)) (@Pure_const M unit)
      (@Map_Backwards (const M) _) (@Mult_Backwards (const M) (@Map_const M) (@Mult_const M op))
      (@Pure_Backwards (const M) (@Pure_const M unit)) (@mkBackwards (const M)).
  Proof.
    constructor; try typeclasses eauto.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Instance ApplicativeMorphism_const_op_inv `{op: Monoid_op M} `{unit: Monoid_unit M} `{! Monoid M}:
    @ApplicativeMorphism (Backwards (@const Type Type M))(@const Type Type M)
      (@Map_Backwards (const M) _) (@Mult_Backwards (const M) (@Map_const M) (@Mult_const M op))
      (@Pure_Backwards (const M) (@Pure_const M unit))
      (@Map_const M) (@Mult_const M (@Monoid_op_Opposite M op)) (@Pure_const M unit)
      (@forwards (const M)).
  Proof.
    constructor; try typeclasses eauto.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Definition foldmap_same_shape_zip
    `{Monoid M}
    (A B C: Type) (t: T A) (u: T B)
    (f: A * B -> M)
    (Hshape: shape t = shape u)
    :
    foldMap f (same_shape_zip t u Hshape) =
      foldMap (op := Monoid_op_Opposite op) f (same_shape_zip_contents t u Hshape).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_same_shape_zip.
    rewrite foldMap_to_traverse1.
    unfold_ops @Map_const.
    compose near (same_shape_zip_contents t u Hshape) on left.
    change ((fun (X Y : Type) (_ : X -> Y) (t0 : @const Type Type M X) => t0))
             with (@Map_const M).
    rewrite (trf_traverse_morphism (T := Vector (@plength T Traverse_T A t))
               (morphism := ApplicativeMorphism_const_op_inv (M := M))).
    reflexivity.
  Qed.

  Lemma traverse_const_opposite `{Monoid M} {A B: Type} (f: A -> M):
    traverse (T := T) (G := const M)
      (@Mult_const M (@Monoid_op_Opposite M op))

    Search traverse same_shape_zip_contents.
    rewrite t
              .
    unfold foldMap.
    rewrite traverse_same_shape_zip.
    rewrite <- traverse_repr.
    rewrite traverse_same_shape_zip.

    reflexivity.
  Qed.

End traversable_functors_zipping.


(** ** Folding over a Vector of pairs *)
(**********************************************************************)
Section fold_over_vector_pairs.

  Context {A B A0 B0: Type} `{Monoid M} `(f: A * B -> M).

  Lemma foldMap_vector_pair_natural:
    forall (fl: A0 -> A) (fr: B0 -> B),
    forall (n: nat) (v: Vector n (A0 * B0)),
      foldMap (T := Vector n) f (map (F := Vector n) (map_tensor fl fr) v) =
        foldMap (T := Vector n) (f ∘ map_tensor fl fr) v.
  Proof.
    intros.
    compose near v on left.
    rewrite foldMap_map.
    reflexivity.
  Qed.

  Lemma foldMap_vector_pair_natural_l:
    forall (fl: A0 -> A) (n: nat) (v: Vector n (A0 * B)),
      foldMap (T := Vector n) f (map (F := Vector n) (map_fst fl) v) =
        foldMap (T := Vector n) (f ∘ map_fst fl) v.
  Proof.
    intros.
    compose near v on left.
    rewrite foldMap_map.
    reflexivity.
  Qed.

  Lemma foldMap_vector_pair_natural_r:
    forall (fr: B0 -> B) (n: nat) (v: Vector n (A * B0)),
      foldMap (T := Vector n) f (map (F := Vector n) (map_snd fr) v) =
        foldMap (T := Vector n) (f ∘ map_snd fr) v.
  Proof.
    intros.
    compose near v on left.
    rewrite foldMap_map.
    reflexivity.
  Qed.

End fold_over_vector_pairs.

(** * Uniqueness *)
(**********************************************************************)

Section uniqueness_lemmas.

  Context {A B: Type}.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{ToMap_inst: Map T}
    `{ToBatch_inst: ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Lemma trav_contents_unique:
    forall (t: T A) (u: T B) (v: Vector (plength t) B),
      trav_make t v = u -> v ~~ trav_contents u.
  Proof.
    introv Hmake.
    rewrite <- Hmake.
    unfold Vector_sim.
    rewrite trav_contents_make.
    reflexivity.
  Qed.

  Lemma trav_make_unique:
    forall (t: T A) (u: T B) (v: Vector (plength t) B),
      trav_make t v = u ->
      forall (C: Type), trav_make (B := C) t ~!~ trav_make u.
  Proof.
    introv Hmake. intro C.
    rewrite <- Hmake.
    rewrite symmetric_Vector_fun_sim.
    apply trav_make_make.
  Qed.

  Corollary trav_decomposition_unique:
    forall (t: T A) (u: T B) (v: Vector (plength t) B),
      trav_make t v = u ->
      (forall C, trav_make (B := C) t ~!~ trav_make u) /\
        v ~~ trav_contents u.
  Proof.
    introv Hmake; split.
    eauto using trav_make_unique.
    auto using trav_contents_unique.
  Qed.


  Corollary trav_decomposition_unique_iff:
    forall (t: T A) (u: T B) (v: Vector (plength t) B),
      trav_make t v = u <->
        (forall C, trav_make (B := C) t ~!~ trav_make u) /\
          v ~~ trav_contents u.
  Proof.
    intros. split.
    - apply trav_decomposition_unique.
    - intros [Hmake Hcontents].
      rewrite <- (trav_get_put (t := u)).
      apply Vector_fun_sim_eq; auto.
  Qed.

  Corollary trav_decomposition_same_shape:
    forall (t: T A) (u: T B) (v: Vector (plength t) B),
      trav_make t v = u ->
      shape t = shape u.
  Proof.
    introv Hmake.
    apply trav_same_shape_rev.
    eapply trav_make_unique.
    eassumption.
  Qed.

  Corollary trav_decomposition_same_length:
    forall (t: T A) (u: T B) (v: Vector (plength t) B),
      trav_make t v = u ->
      plength t = plength u.
  Proof.
    introv Hmake.
    apply same_shape_implies_plength.
    eapply trav_decomposition_same_shape.
    eassumption.
  Qed.

End uniqueness_lemmas.


(** * Lifting relations over Traversable functors *)
(**********************************************************************)
Definition lift_relation {X} {A B:Type} `{Traverse X}
  (R: A -> B -> Prop): X A -> X B -> Prop :=
  traverse (G := subset) R.

Section lifting_relations.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{ToMap_inst: Map T}
    `{ToSubset_inst: ToSubset T}
    `{ToBatch_inst: ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Lemma relation_spec:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u <->
        (exists b: Vector (plength t) B,
            traverse (G := subset) R (trav_contents t) b /\
              trav_make t b = u).
  Proof.
    intros.
    unfold lift_relation.
    rewrite traverse_repr.
    compose near (trav_contents t).
    rewrite (traverse_commutative (G := subset) (T := Vector (plength t))).
    reflexivity.
  Qed.

  (* Minor, not helpful  *)
  Lemma relation1:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Plen: plength u = plength t),
      lift_relation R t u ->
        trav_make t (coerce Plen in trav_contents u) = u.
  Proof.
    introv Hrel.
    rewrite relation_spec in Hrel.
    destruct Hrel as [trav_contents_u [Htrav Hmake]].
    assert (Hcontents: trav_contents u ~~ trav_contents_u).
    { apply trav_contents_unique in Hmake.
      symmetry. assumption. }
    rewrite <- Hmake.
    apply Vector_fun_sim_eq.
    - reflexivity.
    - vector_sim.
  Qed.

  Lemma relation2:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Hlen: plength u = plength t),
      lift_relation R t u ->
      traverse (G := subset) R
        (trav_contents t)
        (coerce Hlen in trav_contents u).
  Proof.
    introv Hrel.
    rewrite relation_spec in Hrel.
    destruct Hrel as [trav_contents_u [Hrel Hmake]].
    enough (Heq: coerce Hlen in trav_contents u =
                             trav_contents_u).
    { rewrite Heq.
      assumption. }
    apply Vector_sim_eq.
    vector_sim.
    symmetry.
    apply trav_contents_unique.
    assumption.
  Qed.

  Lemma relation3:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Hlen: plength u = plength t),
      trav_make (B := B) t ~!~ trav_make u ->
      traverse (G := subset) R
        (trav_contents t)
        (coerce Hlen in trav_contents u) ->
            lift_relation R t u.
  Proof.
    introv Htrav.
    rewrite relation_spec.
    exists (coerce Hlen in trav_contents u). split.
    assumption.
    change u with (id u) at 3.
    rewrite id_spec.
    apply Vector_fun_sim_eq.
    assumption.
    vector_sim.
  Qed.

  Lemma relation4:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u ->
      (forall C, trav_make (B := C) t ~!~ trav_make u).
  Proof.
    introv Hrel. intro C.
    rewrite relation_spec in Hrel.
    destruct Hrel as [trav_contents_u [Htrav Hmake]].
    eapply trav_make_unique.
    eassumption.
  Qed.

  (** ** Related terms have the same shape *)
  (********************************************************************)
  Lemma relation_implies_shape:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u -> shape t = shape u.
  Proof.
    introv Hrel.
    apply trav_same_shape_rev.
    eapply relation4.
    eassumption.
  Qed.

  (** ** Related terms have a related zip *)
  (********************************************************************)
  Lemma Monoid_op_Opposite_and:
    Monoid_op_Opposite Monoid_op_and = and.
  Proof.
    ext P1 P2; propext; cbv; tauto.
  Qed.

  Lemma relation_to_zipped:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Hshape: shape t = shape u),
      lift_relation R t u ->
      Forall (uncurry R)
        (same_shape_zip t u Hshape).
  Proof.
    introv Hrel.
    unfold Forall.
    unfold same_shape_zip.
    rewrite foldMap_trav_make.
    rewrite Monoid_op_Opposite_and.
    unfold same_shape_zip_contents.
    unfold Vector_zip.
    rewrite <- (traverse_zipped_vector
                 (R := R) (plength t) (trav_contents t)
                 (coerce eq_sym (same_shape_implies_plength t u Hshape)
                   in trav_contents u)).
    apply relation2.
    assumption.
  Qed.

  Lemma foldMap_same_shape_zip `{Monoid M}:
    forall (A B: Type) (f: A * B -> M) (t: T A) (u: T B)
      (Hshape: shape t = shape u),
      foldMap (T := T) f (same_shape_zip t u Hshape) =
        foldMap (op := Monoid_op_Opposite op) (T := Vector (plength t))
          f (same_shape_zip_contents t u Hshape).
  Proof.
    intros.
    unfold same_shape_zip.
    rewrite foldMap_trav_make.
    reflexivity.
  Qed.

  Lemma relation_to_zipped_iff:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Hshape: shape t = shape u),
      lift_relation R t u <->
        (forall C, trav_make (B := C) t ~!~ trav_make u) /\
          Forall (uncurry R)
            (same_shape_zip t u Hshape).
  Proof.
    intros.
    split.
    - introv Hrel. split.
      + eapply relation4.
        eassumption.
      + apply relation_to_zipped.
        assumption.
    - intros [Hmake Hzip].
      rewrite relation_spec.
      assert (Hlen: plength u = plength t).
      { apply same_shape_implies_plength.
        symmetry. assumption. }
      exists (coerce Hlen in trav_contents u).
      split.
      + unfold same_shape_zip in Hzip.
        unfold same_shape_zip_contents in Hzip.
        unfold Vector_zip in Hzip.
        unfold Forall in Hzip.
        rewrite foldMap_trav_make in Hzip.
        rewrite Monoid_op_Opposite_and in Hzip.
        rewrite <- (traverse_zipped_vector
                     (R := R) (plength t) (trav_contents t)
                     (coerce eq_sym (same_shape_implies_plength t u Hshape)
                       in trav_contents u)) in Hzip.
        enough (Hcoerce: (coerce eq_sym (same_shape_implies_plength t u Hshape)
                   in trav_contents u) =
                  coerce Hlen in trav_contents u).
        rewrite <- Hcoerce.
        assumption.
        apply Vector_sim_eq.
        vector_sim.
      + change u with (id u) at 3.
        rewrite id_spec.
        apply Vector_fun_sim_eq.
        * apply Hmake.
        * vector_sim.
  Qed.

  Lemma relation_natural1:
    forall (A B1 B2: Type) (R: B1 -> B2 -> Prop) (t: T A) (f: A -> B1),
      lift_relation R (map f t) = lift_relation (R ∘ map f) t.
  Proof.
    intros.
    unfold lift_relation.
    compose near t on left.
    rewrite (traverse_map (G2 := subset) R f).
    reflexivity.
  Qed.

  Lemma relation_natural2_lemma:
    forall (B1 A B2: Type) (R: B1 -> B2 -> Prop) (t: T B1) (u: T A) (f: A -> B2)
      (Hshape: shape t = shape (map f u))
      (Hshape': shape t = shape u),
      Forall (uncurry R) (same_shape_zip t (map f u) Hshape) =
        Forall (uncurry (precompose f ∘ R)) (same_shape_zip t u Hshape').
  Proof.
    intros.
    unfold Forall.
    rewrite foldMap_same_shape_zip.
    rewrite foldMap_same_shape_zip.
    rewrite natural_snd_same_shape_zip_contents_rev.
    compose near (same_shape_zip_contents t u (same_shape_map_rev_r t u f Hshape)).
    rewrite (foldMap_map).
    fequal.
    - ext [x y]. reflexivity.
    - apply same_shape_zip_contents_proof_irrelevance.
  Qed.

  Lemma relation_natural2_core:
    forall (B1 A B2: Type) (R: B1 -> B2 -> Prop) (t: T B1) (u: T A) (f: A -> B2),
      shape t = shape u ->
      lift_relation R t (map f u) = lift_relation (precompose f ∘ R) t u.
  Proof.
    introv Hshape.
    assert (Hshape': shape t = shape (map f u)).
    { rewrite shape_map. assumption. }
    apply propositional_extensionality.
    rewrite (relation_to_zipped_iff _ _ R t (map f u) Hshape').
    rewrite (relation_to_zipped_iff _ _ (precompose f ∘ R) t u Hshape).
    erewrite relation_natural2_lemma.
    split.
    - intros [X1 X2]. split.
      + intros.
        apply trav_same_shape.
        assumption.
      + eassumption.
    - intros [X1 X2]. split.
      + apply trav_same_shape.
        assumption.
      + assumption.
  Qed.

  Lemma relation_natural2:
    forall (B1 A B2: Type) (R: B1 -> B2 -> Prop) (t: T B1) (u: T A) (f: A -> B2),
      lift_relation R t (map f u) = lift_relation (precompose f ∘ R) t u.
  Proof.
    intros.
    apply propositional_extensionality.
    split.
    - introv hyp.
      rewrite <- relation_natural2_core; try assumption.
      apply relation_implies_shape in hyp.
      rewrite shape_map in hyp.
      assumption.
    - introv hyp.
      rewrite relation_natural2_core; try assumption.
      apply relation_implies_shape in hyp.
      assumption.
  Qed.

  (* This can actually be strengthed into an IFF *)
  Lemma relation_respectful:
    forall (A B1 B2: Type) (R: B1 -> B2 -> Prop) (t: T A) (f: A -> B1) (g: A -> B2),
    (forall (a: A), a ∈ t -> R (f a) (g a)) -> lift_relation R (map f t) (map g t).
  Proof.
    introv hyp.
    rewrite relation_natural1.
    rewrite relation_natural2.
    unfold lift_relation.
    rewrite traverse_through_runBatch.
    unfold compose.
    unfold element_of in hyp.
    rewrite tosubset_to_foldMap in hyp.
    change t with (id t) at 2.
    rewrite id_through_runBatch.
    unfold compose.
    rewrite (foldMap_through_toBatch A A) in hyp.
    (* induction (@toBatch T ToBatch_inst A A t). *) (* Generates a weird hypothesis *)
    apply (Batch_ind A A
      (fun (C: Type) (b: Batch A A C) =>
           (forall a : A, foldMap (T := BATCH1 A C) (ret (T := subset)) b a -> R (f a) (g a)) ->
           runBatch (G := subset) (fun a : A => precompose g (R (map f a))) b (runBatch id b))).
    - intros C c hyp'.
      reflexivity.
    - introv IH.
      introv hyp'.
      rewrite runBatch_rw2.
      rewrite runBatch_rw2.
      rewrite subset_ap_spec.
      unfold ap.
      unfold_ops @Map_I.
      unfold_ops @Mult_I.
      exists (runBatch id b) a.
      splits.
      { unfold precompose, compose.
        unfold_ops @Map_I.
        apply hyp'.
        now right. }
      { apply IH.
        intros.
        apply hyp'.
        rewrite foldMap_Batch_rw2.
        now left.
      }
      { reflexivity. }
    - assumption.
  Qed.

End lifting_relations.

