From Tealeaves Require Export
  Classes.Monoid
  Classes.Algebraic.DT.Functor
  Theory.Algebraic.Decorated.Shift
  Theory.Algebraic.Decorated.Functor.Category
  Theory.Algebraic.Traversable.Functor.Category
  Functors.Writer.

Import Monoid.Notations.
Import Strength.Notations.
Import Product.Notations.
Import Traversable.Functor.Notations.

#[local] Generalizable Variables T W op zero G.

(** * Monoid structure of D-T functors *)
(******************************************************************************)
Section DecoratedTraversableFunctor_monoid.

  Context
    `{@Monoid W op zero}.

  Existing Instance DecoratedFunctor_zero.
  Existing Instance Traversable_I.

  (** ** The identity functor is D-T *)
  (******************************************************************************)
  #[program] Instance DecoratedTraversable_I : DecoratedTraversableFunctor W (fun A => A).

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
      compose near ((δ T G (fmap T (σ G) t))) on right;
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

    #[local] Unset Keyed Unification.

    #[global] Instance DecoratedTraversableFunctor_compose :
      DecoratedTraversableFunctor W (U ∘ T) :=
      {| dtfun_compat := @dtfun_compat_compose; |}.

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
