From Tealeaves Require Export
  Functors.Batch
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.DecoratedShapelyFunctor
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Functors.Environment
  Theory.TraversableFunctor.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variables F M E T G A B C ϕ.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.


Section decorated_traversable_functor_theory.

  Context
    `{DecoratedTraversableFunctor E T}
      `{Map T}
      `{Mapd E T}
      `{! Compat_Map_Mapdt}
      `{! Compat_Mapd_Mapdt}.

  (** ** Characterizing <<∈d>> and <<mapd>> *)
  (******************************************************************************)
  Theorem ind_mapd_iff_core:
    forall `(f : E * A -> B),
      mapd f ∘ toctxset = toctxset ∘ mapd (T := T) f.
  Proof.
    intros.
    rewrite toctxset_through_toctxlist.
    rewrite toctxset_through_toctxlist.
    reassociate -> on right.
    change (list (prod ?E ?X)) with (env E X). (* hidden *)
    rewrite <- (mapd_toctxlist f).
    rewrite env_mapd_spec.
    reassociate <- on right.
    rewrite ctxset_mapd_spec.
    change (env ?E ?X) with (list (prod E X)). (* hidden *)
    unfold ctxset.
    rewrite <- (natural (ϕ := @tosubset list _)).
    reflexivity.
  Qed.

  Lemma mapdt_respectful:
    forall A B `{Applicative G} (t : T A) (f g : E * A -> G B),
      (forall (e : E) (a : A), (e, a) ∈d t -> f (e, a) = g (e, a))
      -> mapdt f t = mapdt g t.
  Proof.
    introv Happl hyp.
    do 2 rewrite mapdt_through_runBatch.
    unfold element_ctx_of in hyp.
    rewrite (toctxset_through_runBatch2 (tag := B)) in hyp.
    unfold compose in *.
    induction (toBatch6 (B := B) t).
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

  Theorem mapdt_purity1 :
    forall `{Applicative G},
      `(mapdt (G := G) (pure ∘ extract) = @pure G _ (T A)).
  Proof.
    intros.
    rewrite (kdtfun_morph (G1 := fun A => A) (G2 := G)).
    rewrite kdtfun_mapdt1.
    reflexivity.
  Qed.

  Corollary mapdt_respectful_pure:
    forall A `{Applicative G} (t : T A) (f : E * A -> G A),
      (forall (e : E) (a : A), (e, a) ∈d t -> f (e, a) = pure (F := G) a)
      -> mapdt f t = pure t.
  Proof.
    intros.
    rewrite <- mapdt_purity1.
    now apply mapdt_respectful.
  Qed.

  Corollary mapdt_respectful_id:
    forall A (t : T A) (f : E * A -> A),
      (forall (e : E) (a : A), (e, a) ∈d t -> f (e, a) = a)
      -> mapdt (G := fun A => A) f t = t.
  Proof.
    intros.
    change t with (id t) at 2.
    rewrite <- kdtfun_mapdt1.
    apply (mapdt_respectful A A (G := fun A => A)).
    assumption.
  Qed.

    Lemma mapd_respectful :
      forall A B (t : T A) (f g : E * A -> B),
        (forall (e : E) (a : A), (e, a) ∈d t -> f (e, a) = g (e, a))
        -> mapd f t = mapd g t.
    Proof.
      introv hyp.
      do 2 rewrite mapd_through_runBatch.
      unfold element_ctx_of in hyp.
      rewrite (toctxset_through_runBatch2 (tag := B)) in hyp.
      unfold compose in *.
      induction (toBatch6 (B := B) t).
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


  #[export] Instance: DecoratedContainerFunctor E T.
  Proof.
    constructor.
    - typeclasses eauto.
    - constructor.
      intros.
      apply ind_mapd_iff_core.
    - intros.
      apply mapd_respectful.
      assumption.
  Qed.

End decorated_traversable_functor_theory.


(** * Shapeliness *)
(******************************************************************************)
Section shapeliness.

  Context
    `{DecoratedTraversableFunctor E T}
      `{Map T}
      `{Mapd E T}
      `{Traverse T}
      `{ToBatch T}
      `{! Compat_Map_Mapd}
      `{! Compat_Map_Traverse T}
      `{! Compat_Mapd_Mapdt}
      `{! Compat_ToBatch_Traverse T}
      `{! Compat_Traverse_Mapdt}.

  Lemma mapd_shape {A B}: forall (f: E * A -> B) t,
      shape (mapd f t) = shape t.
  Proof.
    intros.
    unfold shape.
    compose near t on left.
    rewrite map_mapd.
    rewrite DecoratedFunctor.map_to_mapd.
    fequal.
  Qed.

  Theorem mapd_injective1 {A B}: forall (f: E * A -> B) (t1 t2 : T A),
      (forall p q, f p = f q -> p = q) ->
      mapd f t1 = mapd f t2 ->
      t1 = t2.
  Proof.
    introv Hinj Heq.
    assert (cut: (toctxlist ∘ mapd f) t1 = (toctxlist ∘ mapd f) t2).
    { unfold compose. fequal. auto. }
    rewrite <- mapd_toctxlist in cut.
    unfold compose in cut.
    apply shapeliness.
    split.
    - enough (cut2: shape (mapd f t1) = shape (mapd f t2)).
      do 2 rewrite mapd_shape in cut2; auto.
      now rewrite Heq.
    - rewrite tolist_to_toctxlist.
      unfold compose.
      generalize dependent (toctxlist t2).
      induction (toctxlist t1); intros otherlist premise.
      + induction (otherlist).
        * reflexivity.
        * destruct a as [e' a].
          inversion premise.
      + destruct a as [e' a].
        destruct otherlist.
        * inversion premise.
        * destruct p as [e'' a'].
          cbn in *.
          inversion premise.
          fequal.
          { specialize (Hinj (e'', a) (e'', a') H10).
            now inversion Hinj. }
          { apply IHe. auto. }
  Qed.

  Theorem mapd_injective2 {A B}: forall (f: E * A -> B) (t1 t2 : T A),
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
    apply shapeliness.
    split.
    - enough (cut2: shape (mapd f t1) = shape (mapd f t2)).
      do 2 rewrite mapd_shape in cut2; auto.
      now rewrite Heq.
    - rewrite tolist_to_toctxlist.
      unfold compose.
      generalize dependent (toctxlist t2).
      induction (toctxlist t1);
        intros otherlist Hinj Heq_list.
      + induction (otherlist).
        * reflexivity.
        * destruct a as [e' a].
          inversion Heq_list.
      + destruct a as [e' a].
        destruct otherlist.
        * inversion Heq_list.
        * destruct p as [e'' a'].
          inversion Heq_list; subst.
          cbn. fequal.
          { eapply Hinj.
            now left. now left. auto. }
          { apply IHe; auto.
            intros. eapply Hinj.
            rewrite element_of_list_cons.
            right. eassumption.
            rewrite element_of_list_cons.
            right. assumption.
            auto.
          }
  Qed.

End shapeliness.

(** * Deconstructing with refinement-type vectors *)
(******************************************************************************)
Section deconstruction.

  Context
    `{DecoratedTraversableFunctor E T}
      `{Traverse T}
      `{Map T}
      `{toBatch_inst: ToBatch T}
      `{ToSubset T}
      `{! TraversableFunctor T}
      `{! Compat_Map_Mapdt}
      `{! Compat_ToBatch_Traverse T}
      `{! Compat_ToSubset_Traverse T}
      `{! Compat_Traverse_Mapdt}.

  #[local] Generalizable Variables v.

  Lemma plength_toBatch6:
    forall {A} {B} (t: T A),
      plength t = length_Batch (toBatch6 (A := A) (B := B) t).
  Proof.
    intros.
    unfold plength.
    rewrite (foldMap_through_runBatch2 A B).
    rewrite toBatch6_toBatch.
    unfold compose.
    induction (toBatch6 t).
    - reflexivity.
    - cbn.
      rewrite IHb.
      unfold_ops @NaturalNumbers.Monoid_op_plus.
      lia.
  Qed.

  Lemma plength_toBatch6':
    forall {A B} (t: T A),
      length_Batch (toBatch6 (A := A) (B := B) t) = plength t.
  Proof.
    symmetry.
    apply plength_toBatch6.
  Qed.

  Lemma length_toBatch6_toBatch:
    forall {A B} (t: T A),
      length_Batch (toBatch6 (A := A) (B := B) t) =
        length_Batch (toBatch (A := A) (A' := B) t).
  Proof.
    intros.
    rewrite toBatch6_toBatch.
    unfold compose. induction (toBatch6 t).
    - reflexivity.
    - cbn. now rewrite IHb.
  Qed.

  Definition mapdt_contents {A} (t: T A):
    Vector (plength t) (E * A) :=
    let v : Vector
              (length_Batch (toBatch6 (B := False) (A := A) t))
              (E * A)
      := Batch_contents (toBatch6 t)
    in coerce_Vector_length (plength_toBatch6' t) v.

  Definition mapdt_make {A B} (t: T A):
    Vector (plength t) B -> T B := trav_make t.
  (*
    (fun v =>
       let v' := coerce_Vector_length (eq_sym (plength_eq_length t)) v
       in Batch_make (toBatch t) v').
   *)


  Lemma Batch_contents_toctxlist:
    forall {A B} (t: T A),
      Vector_to_list (E*A) (Batch_contents (toBatch6 (B := B) t)) =
        List.rev (toctxlist t).
  Proof.
    intros.
    unfold toctxlist.
    unfold ToCtxlist_Mapdt.
    rewrite (foldMapd_through_runBatch2 A B).
    unfold compose.
    induction (toBatch6 t).
    - cbn. reflexivity.
    - cbn.
      rewrite Vector_to_list_vcons.
      rewrite IHb.
      unfold_ops @Monoid_op_list @Return_list.
      rewrite List.rev_unit.
      reflexivity.
  Qed.

  Lemma Batch_contents_toBatch6_sim:
    forall {A B B'} (t: T A),
      Batch_contents
        (toBatch6 (B := B) t) ~~
        Batch_contents (toBatch6 (B := B') t).
  Proof.
    intros.
    unfold Vector_sim.
    change (proj1_sig ?v) with (Vector_to_list _ v).
    rewrite Batch_contents_toctxlist.
    rewrite Batch_contents_toctxlist.
    reflexivity.
  Qed.

  Lemma Batch_make6 {A B} (t: T A):
    Batch_make (toBatch6 t) =
      (fun v => Batch_make (B := B)
               (toBatch t) (coerce (length_toBatch6_toBatch t) in v)).
  Proof.
    ext v.
    generalize dependent (length_toBatch6_toBatch (B:=B) t).
    intro e.
    apply Batch_make_sim3.
    2: { vector_sim. }
    { rewrite toBatch6_toBatch.
      unfold compose.
      clear e v.
      induction (toBatch6 t).
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
      {A B : Type}.

    Lemma trav_make_sim1:
      forall (t : T A) `{v1 ~~ v2},
        trav_make (B := B) t v1 = trav_make t v2.
    Proof.
      intros.
      unfold trav_make.
      apply Batch_make_sim1.
      vector_sim.
    Qed.

    Lemma trav_make_sim2:
      forall `(t1 : T A) (t2: T A)
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

  (** ** Miscellaneous *)
  (******************************************************************************)
  Section ctxlist.

    Lemma tolist_trav_contents `{t: T A}:
      Vector_to_list (E * A) (mapdt_contents t) =
        List.rev (toctxlist t).
    Proof.
      intros.
      unfold mapdt_contents.
    Abort.

  End ctxlist.

  (** ** Lens-like laws *)
  (******************************************************************************)
  Section lens_laws.

    (** *** get-put *)
    (******************************************************************************)
    Lemma mapdt_get_put `{t: T A}:
      mapdt_make t (map extract (mapdt_contents t)) = t.
    Proof.
      unfold mapdt_make, trav_make, mapdt_contents.
      change t with (id t) at 13.
      rewrite <- trf_extract.
      unfold compose.
      rewrite <- Batch_make_contents.
      apply Batch_make_sim1.
      apply Vector_coerce_sim_l'.
      rewrite toBatch6_toBatch.
      unfold compose.
      apply (transitive_Vector_sim
               (v2 := map extract (Batch_contents (B := False) (toBatch6 t)))).
      { vec_symmetry.
        unfold Vector_sim.
        rewrite Batch_contents_natural.
        rewrite <- map_coerce_Vector.
        compose near t on left.
        rewrite <- toBatch6_toBatch.
        admit.
      }
      try apply Batch_contents_toBatch_sim.
      admit.
    Admitted.

    Lemma toBatch_mapdt_make {A A' B} {t: T A} {v: Vector (plength t) B}:
      toBatch (A' := A') (mapdt_make t v) =
        Batch_replace_contents
          (toBatch (A' := A') t)
          (coerce eq_sym (plength_eq_length t) in v).
    Proof.
      apply toBatch_trav_make.
    Qed.

    (** *** put-get *)
    (******************************************************************************)
    (*
    Lemma mapdt_contents_make {A} {t: T A} {v: Vector (plength t) A}:
      mapdt_contents (trav_make t v) ~~ v.
    Proof.
      unfold trav_contents.
      vector_sim.
      rewrite toBatch_trav_make.
      rewrite Batch_put_get.
      vector_sim.
    Qed.
     *)

    (** *** put-put *)
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

    Notation "'precoerce' Hlen 'in' F" :=
      (F ○ coerce_Vector_length Hlen)
        (at level 10, F at level 20).

    Lemma mapdt_same_shape
      `(t1: T A) `(t2: T A'):
      shape t1 = shape t2 ->
      forall B, mapdt_make (B := B) t1 ~!~ mapdt_make t2.
    Proof.
      intros.
      now apply trav_same_shape.
    Qed.

  End lens_laws.

  (** ** Representation theorems *)
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
    assert (Functor G) by now inversion H9.
    rewrite <- (fun_map_map (F := G)).
    unfold compose at 1.
    do 2 change (map ?f (forwards ?x)) with (forwards (map f x)).
    rewrite traverse_Vector_coerce_natural;[|typeclasses eauto].

    rewrite mapdt_through_runBatch.
    unfold compose at 1.
    rewrite runBatch_repr2.
    change (map ?f (forwards ?x)) with (forwards (map f x)).
    fequal.
    rewrite Batch_make6.
    change  (map (?f ○ ?g) ?t) with (map (f ∘ g) t).
    rewrite <- (fun_map_map (F := Backwards G)).
    unfold compose at 1.
    rewrite traverse_Vector_coerce_natural;[|typeclasses eauto].
    fequal.
    fequal.
    apply Vector_eq.
    apply Vector_coerce_sim_l'.
    apply Vector_coerce_sim_r'.
    apply Vector_coerce_sim_r'.
    eapply Batch_contents_toBatch6_sim.
  Qed.

  (** ** Lemmas regarding <<plength>> *)
  (******************************************************************************)
  Lemma plength_trav_make: forall `(t: T A) `(v: Vector _ B),
      plength t = plength (mapdt_make t v).
  Proof.
    intros.
    unfold mapdt_make.
    apply plength_trav_make.
  Qed.

End deconstruction.

(** * Lifting context-sensitive relations over Decorated-Traversable functors *)
(******************************************************************************)

From Tealeaves Require
  Adapters.KleisliToCategorical.DecoratedTraversableFunctor.

Section lifting_relations.

  Context
    `{DecoratedTraversableFunctor E T}
      `{Map T}
      `{Mapd E T}
      `{Traverse T}
      `{ToBatch T}
      `{! Compat_Map_Mapdt}
      `{! Compat_Mapd_Mapdt}
      `{! Compat_ToBatch_Traverse T}
      `{! Compat_Traverse_Mapdt}.

  Import Adapters.KleisliToCategorical.DecoratedTraversableFunctor.
  Import ToCategorical.


  Lemma shape_decorate1
    (A: Type) (t: T A):
    shape (F := T) (dec T t) = shape t.
  Proof.
    unfold dec.
    unfold_ops @Decorate_Mapdt.
    unfold shape.
  Abort.

  Lemma Hshape_decorate
    (A B: Type) (t : T A) (u: T B)
    (Hshape: shape t = shape u):
    shape (dec T t) = shape (dec T u).
  Proof.
    Set Printing Implicit.
    unfold dec.
    unfold Decorate_Mapdt.
    unfold shape.
    compose near t.
    unfold_ops @Map_compose.
  Abort.

  (*
  Definition zip_decorate
    (A B: Type) (t : T A) (u: T B)
    (Hshape: shape t = shape u):
    map (cojoin (E ×)) (dec T (same_shape_zip A B t u Hshape)) =
      dec T (same_shape_zip (E * A) (E * B) (dec T t) (dec T u) _).
  *)


End lifting_relations.
