From Tealeaves Require Export
  Classes.Decorated.Functor
  Classes.Traversable.Functor.

Import Strength.Notations.

#[local] Generalizable Variables T E G A B C W op zero F ϕ.

(** * Decorated-traversable functors *)
(******************************************************************************)
Section DecoratedTraversableFunctor.

  Context
    (E : Type)
    (F : Type -> Type)
    `{Fmap F} `{Decorate E F} `{Dist F}.

  Class DecoratedTraversableFunctor :=
    { dtfun_decorated :> DecoratedFunctor E F;
      dtfun_traversable :> TraversableFunctor F;
      dtfun_compat : forall `{Applicative G},
        `(dist F G ∘ fmap F (σ G) ∘ dec F (A := G A) =
            fmap G (dec F) ∘ dist F G);
    }.

End DecoratedTraversableFunctor.

Import Monoid.Notations.
Import Strength.Notations.
Import Product.Notations.
Import Traversable.Functor.Notations.

(** * Monoid structure of D-T functors *)
(******************************************************************************)
Section DecoratedTraversableFunctor_monoid.

  Context
    `{@Monoid W op zero}.

  Section identity.

    Existing Instance DecoratedFunctor_zero.
    Existing Instance Traversable_I.

    (** ** The identity functor is D-T *)
    (******************************************************************************)
    #[program] Instance DecoratedTraversable_I : DecoratedTraversableFunctor W (fun A => A).

    Remove Hints DecoratedFunctor_zero : typeclass_instances.

  End identity.

  (** ** D-T functors are closed under composition *)
  (******************************************************************************)
  Section compose.

    #[local] Set Keyed Unification.

    Context
      `{Monoid W}
      (U T : Type -> Type)
      `{DecoratedTraversableFunctor W T}
      `{DecoratedTraversableFunctor W U}.

    (** Push the applicative wire underneath a <<shift>> operation *)
    Lemma strength_shift : forall (A : Type) `{Applicative G},
        δ T G ∘ fmap T (σ G) ∘ shift T (A := G A) =
          fmap G (shift T) ∘ σ G ∘ fmap (W ×) (δ T G ∘ fmap T (σ G)).
    Proof.
      intros. unfold shift. ext [w t].
      unfold compose; cbn; unfold id.
      compose near t on left. rewrite (fun_fmap_fmap T).
      compose near t on left. rewrite (fun_fmap_fmap T).
      compose near ((δ T G (fmap T (σ G) t))) on right.
      rewrite (fun_fmap_fmap G).
      reassociate <- on left.
      rewrite (strength_join_l (F := G) (W := W)).
      do 2 reassociate -> on left;
      rewrite <- (fun_fmap_fmap T);
      reassociate <- on left.
      change (fmap T (fmap G ?f)) with (fmap (T ∘ G) f).
      change (δ T G ((fmap (T ∘ G) (join (prod W)) ∘ ?f) t))
        with ((δ T G ∘ fmap (T ∘ G) (join (prod W))) (f t)).
      rewrite <- (natural (ϕ := @dist T _ G _ _ _ )).
      (* now focus on the RHS *)
      unfold id.
      change (fmap T (join (prod W) (A := ?A)) ○ σ T ∘ pair w)
        with  (fmap T (join (prod W) (A := A)) ∘ (σ T ∘ pair w)).
      rewrite (strength_2).
      rewrite <- (fun_fmap_fmap G).
      compose near (fmap T (σ G) t) on right.
      reassociate -> on right.
      change (fmap G (fmap T ?f)) with (fmap (G ∘ T) f).
      rewrite (natural (ϕ := @dist T _ G _ _ _) (pair w)).
      unfold compose. compose near t on right.
      now rewrite (fun_fmap_fmap T).
    Qed.

    (** Push the applicative wire underneath a <<dec (U ∘ T)>> operation *)
    Lemma strength_shift2 : forall (A : Type) `{Applicative G},
        δ U G ∘ fmap U (σ G ∘ fmap (prod W) (δ T G ∘ fmap T (σ G)))
          ∘ (dec U ∘ fmap U (dec T (A := G A))) =
          fmap G (dec U ∘ fmap U (dec T)) ∘ δ (U ∘ T) G.
    Proof.
      intros. rewrite <- (natural (ϕ := @dec W U _)).
      reassociate <- on left; reassociate -> near (fmap (U ○ prod W) (dec T)).
      rewrite (fun_fmap_fmap U). do 2 reassociate -> on left.
      rewrite (fun_fmap_fmap (prod W)).
      rewrite (dtfun_compat _ T); auto.
      rewrite <- (fun_fmap_fmap U).
      change (fmap U (fmap (W ×) ?f)) with (fmap (U ∘ (W ×)) f).
      reassociate -> on left. rewrite (natural (ϕ := @dec W U _)).
      do 2 reassociate <- on left.
      rewrite (dtfun_compat _ U); auto.
      rewrite <- (fun_fmap_fmap U). reassociate <- on left.
      change (fmap U (fmap G ?f)) with (fmap (U ∘ G) f).
      reassociate -> near (fmap (U ∘ G) (dec T)).
      rewrite <- (natural (ϕ := @dist U _ G _ _ _)).
      reassociate <- on left.
      rewrite (fun_fmap_fmap G). reflexivity.
    Qed.

    Theorem dtfun_compat_compose : forall `{Applicative G} {A : Type},
        δ (U ∘ T) G ∘ fmap (U ∘ T) (σ G) ∘ dec (U ∘ T) (A := G A) =
        fmap G (dec (U ∘ T)) ∘ dist (U ∘ T) G.
    Proof.
      intros. reassociate -> on left.
      unfold dec at 1, Decorate_compose.
      unfold dist at 1, Dist_compose.
      (* bring <<strength G >> and <<shift T>> together*)
      do 3 reassociate <- on left;
        reassociate -> near (fmap U (shift T));
      rewrite (fun_fmap_fmap U).
      reassociate -> near (fmap U (fmap T (σ G) ∘ shift T)).
      rewrite (fun_fmap_fmap U).
      reassociate <- on left.
      rewrite (strength_shift); auto.
      (* move <<δ U G>> under <<shift>> *)
      do 3 reassociate -> on left;
      rewrite <- (fun_fmap_fmap U);
      do 3 reassociate <- on left.
      change (fmap U (fmap G ?f)) with (fmap (U ∘ G) f).
      rewrite <- (natural (ϕ := @dist U _ G _ _ _) (shift T)).
      do 3 reassociate -> on left.
      reassociate <- near (δ U G).
      rewrite strength_shift2; auto.
      reassociate <- on left.
      now rewrite (fun_fmap_fmap G).
    Qed.

    (* TODO Investigate why DecoratedFunctor_compose solve the next instance automatically.
       It seems like <<dtfun_decorated>> needs extra help here.
       It seems like it doesn't want to pick up on the Dist instance or something.
     *)
    Lemma composition_is_decorated : DecoratedFunctor W (U ∘ T).
    Proof.
      inversion H4.
      inversion H8.
      apply DecoratedFunctor_compose.
    Qed.

    #[program, global] Instance DecoratedTraversableFunctor_compose :
      DecoratedTraversableFunctor W (U ∘ T) :=
      {| dtfun_decorated := composition_is_decorated;
        dtfun_compat := @dtfun_compat_compose; |}.

  End compose.

End DecoratedTraversableFunctor_monoid.

(** ** Zero-decorated traversable functors are decorated-traversable *)
(******************************************************************************)
Section TraversableFunctor_zero_DT.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Monoid W}.

  Existing Instance Decorate_zero.
  Existing Instance DecoratedFunctor_zero.

  Theorem dtfun_compat_zero : forall `{Applicative G} {A : Type},
      dist T G ∘ fmap T (strength G) ∘ dec T =
      fmap G (dec T) ∘ dist T G (A := A).
  Proof.
    intros. unfold_ops @Decorate_zero.
    reassociate -> on left. rewrite (fun_fmap_fmap T).
    change_right (fmap (G ∘ T) (pair Ƶ) ∘ δ T G (A := A)).
    rewrite (natural (ϕ := @dist T _ G _ _ _) (@pair W A Ƶ)).
    now unfold_ops @Fmap_compose.
  Qed.

  Instance DecoratedTraversableFunctor_zero :
    DecoratedTraversableFunctor W T :=
    {| dtfun_compat := @dtfun_compat_zero |}.

End TraversableFunctor_zero_DT.

From Tealeaves Require
  Classes.Decorated.Setlike
  Kleisli.DT.Functor.

(** * Kleisli presentation of decorated-traversable functors *)
(******************************************************************************)
Module ToKleisli.

  Import Kleisli.DT.Functor.

  Import Product.Notations.
  Import Kleisli.DT.Functor.Notations.

  Section operation.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Fmap T} `{Decorate E T} `{Dist T}.

  #[export] Instance Fmapdt_distdec : Fmapdt E T :=
      fun (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
        `(f : E * A -> G B) => (dist T G ∘ fmap T f ∘ dec T : T A -> G (T B)).

  End operation.

  Section with_functor.

    Context
      (T : Type -> Type)
      `{Classes.DT.Functor.DecoratedTraversableFunctor E T}.

    Theorem fmapdt_id : forall (A : Type), fmapdt T (fun A => A) (extract _) = @id (T A).
    Proof.
      introv. unfold_ops @Fmapdt_distdec.
      reassociate -> on left.
      rewrite (dfun_dec_extract E T). now rewrite (dist_unit T).
    Qed.

    Theorem fmapdt_fmapdt : forall `{Applicative G1} `{Applicative G2}
                              `(g : E * B -> G2 C) `(f : E * A -> G1 B),
        fmap G1 (fmapdt T G2 g) ∘ fmapdt T G1 f = fmapdt T (G1 ∘ G2) (g ⋆dt f).
    Proof.
      intros. unfold transparent tcs. unfold kcompose_dt.
      rewrite <- (fun_fmap_fmap G1).
      repeat reassociate <- on left.
      change (?f ∘ fmap G1 (dec T) ∘ dist T G1 ∘ ?g) with
        (f ∘ (fmap G1 (dec T) ∘ dist T G1) ∘ g).
      rewrite <- (dtfun_compat E T B).
      rewrite <- (fun_fmap_fmap G1).
      repeat reassociate <- on left.
      change (?f ∘ fmap G1 (fmap T g) ∘ dist T G1 ∘ ?h) with
        (f ∘ (fmap G1 (fmap T g) ∘ dist T G1) ∘ h).
      change (fmap G1 (fmap T g)) with (fmap (G1 ∘ T) g).
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      rewrite (dist_linear T).
      repeat reassociate <- on left.
      rewrite <- (fun_fmap_fmap T).
      unfold_ops @Fmap_compose.
      change (?f ∘ fmap T (fmap G1 g) ∘ ?x ∘ ?h) with
        (f ∘ (fmap T (fmap G1 g) ∘ x) ∘ h).
      rewrite (fun_fmap_fmap T). reassociate -> near (fmap T f).
      rewrite <- (natural (ϕ := @dec E T _)).
      repeat reassociate ->.
      repeat fequal. rewrite (dfun_dec_dec E T).
      reassociate <-. unfold_ops @Fmap_compose.
      now rewrite (fun_fmap_fmap T).
    Qed.

    Theorem fmapdt_fmapdt_morphism : forall `{ApplicativeMorphism G1 G2 ϕ} `(f : E * A -> G1 B),
        fmapdt T G2 (ϕ B ∘ f) = ϕ (T B) ∘ fmapdt T G1 f.
    Proof.
      intros. unfold transparent tcs.
      do 2 reassociate <-.
      rewrite <- (fun_fmap_fmap T).
      rewrite <- (dist_morph T).
      reflexivity.
    Qed.

    #[local] Instance: Kleisli.DT.Functor.DecoratedTraversableFunctor E T :=
      {| kdtfun_fmapdt1 := @fmapdt_id;
        kdtfun_fmapdt2 := @fmapdt_fmapdt;
        kdtfun_morph := @fmapdt_fmapdt_morphism;
      |}.

  End with_functor.

End ToKleisli.

(*|
At this stage we make sure our typeclass hierarchy works as expected. Given a `DecoratedTraversableFunctor`, Coq should infer the following classes.
|*)
Section test_typeclasses.

  Context
    `{DecoratedTraversableFunctor E T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal DecoratedFunctor E T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
  (* Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal SetlikeFunctor T. typeclasses eauto. Qed.  *)

End test_typeclasses.
