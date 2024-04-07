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
