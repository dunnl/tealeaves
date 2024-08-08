From Tealeaves Require Import
  Classes.Categorical.DecoratedTraversableFunctor
  Categories.DecoratedFunctor
  Categories.TraversableFunctor.

#[local] Generalizable Variables W T F U G X Y ϕ op zero.

Import TraversableFunctor.Notations.
Import Monad.Notations.
Import Strength.Notations.
Import Product.Notations.
Import Monoid.Notations.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.

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
        δ T G ∘ map T σ ∘ shift T (A := G A) =
          map G (shift T) ∘ σ ∘ map (W ×) (δ T G ∘ map T σ).
    Proof.
      intros. unfold shift. ext [w t].
      unfold compose; cbn; unfold id.
      compose near t on left. rewrite (fun_map_map (F := T)).
      compose near t on left. rewrite (fun_map_map (F := T)).
      compose near ((δ T G (map T σ t))) on right.
      rewrite (fun_map_map (F := G)).
      reassociate <- on left.
      rewrite 2(incr_spec).
      rewrite (strength_join_l (F := G) (W := W)).
      do 2 reassociate -> on left;
      rewrite <- (fun_map_map (F := T));
      reassociate <- on left.
      change (map T (map G ?f)) with (map (T ∘ G) f).
      change (δ T G ((map (T ∘ G) (join (prod W)) ∘ ?f) t))
        with ((δ T G ∘ map (T ∘ G) (join (prod W))) (f t)).
      rewrite <- (natural (ϕ := @dist T _ G _ _ _ )).
      (* now focus on the RHS *)
      unfold id.
      change (map T (join (prod W) (A := ?A)) ○ σ ∘ pair w)
        with  (map T (join (prod W) (A := A)) ∘ (σ ∘ pair w)).
      rewrite (strength_2).
      rewrite <- (fun_map_map (F := G)).
      compose near (map T σ t) on right.
      reassociate -> on right.
      change (map G (map T ?f)) with (map (G ∘ T) f).
      rewrite (natural (ϕ := @dist T _ G _ _ _) (pair w)).
      unfold compose. compose near t on right.
      now rewrite (fun_map_map (F := T)).
    Qed.

    (** Push the applicative wire underneath a <<dec (U ∘ T)>> operation *)
    Lemma strength_shift2 : forall (A : Type) `{Applicative G},
        δ U G ∘ map U (σ ∘ map (prod W) (δ T G ∘ map T σ))
          ∘ (dec U ∘ map U (dec T (A := G A))) =
          map G (dec U ∘ map U (dec T)) ∘ δ (U ∘ T) G.
    Proof.
      intros. rewrite <- (natural (ϕ := @dec W U _)).
      reassociate <- on left; reassociate -> near (map (U ○ prod W) (dec T)).
      rewrite (fun_map_map (F := U)). do 2 reassociate -> on left.
      rewrite (fun_map_map (F := prod W)).
      rewrite (dtfun_compat A); auto.
      rewrite <- (fun_map_map (F := U)).
      change (map U (map (W ×) ?f)) with (map (U ∘ (W ×)) f).
      reassociate -> on left. rewrite (natural (ϕ := @dec W U _)).
      do 2 reassociate <- on left.
      rewrite (dtfun_compat _); auto.
      rewrite <- (fun_map_map (F := U)). reassociate <- on left.
      change (map U (map G ?f)) with (map (U ∘ G) f).
      reassociate -> near (map (U ∘ G) (dec T)).
      rewrite <- (natural (ϕ := @dist U _ G _ _ _)).
      reassociate <- on left.
      rewrite (fun_map_map (F := G)). reflexivity.
    Qed.

    Theorem dtfun_compat_compose : forall `{Applicative G} {A : Type},
        δ (U ∘ T) G ∘ map (U ∘ T) σ ∘ dec (U ∘ T) (A := G A) =
        map G (dec (U ∘ T)) ∘ dist (U ∘ T) G.
    Proof.
      intros. reassociate -> on left.
      unfold dec at 1, Decorate_compose.
      unfold dist at 1, Dist_compose.
      (* bring <<strength G >> and <<shift T>> together*)
      do 3 reassociate <- on left;
        reassociate -> near (map U (shift T));
      rewrite (fun_map_map (F := U)).
      reassociate -> near (map U (map T σ ∘ shift T)).
      rewrite (fun_map_map (F := U)).
      reassociate <- on left.
      rewrite (strength_shift); auto.
      (* move <<δ U G>> under <<shift>> *)
      do 3 reassociate -> on left;
      rewrite <- (fun_map_map (F := U));
      do 3 reassociate <- on left.
      change (map U (map G ?f)) with (map (U ∘ G) f).
      rewrite <- (natural (ϕ := @dist U _ G _ _ _) (shift T)).
      do 3 reassociate -> on left.
      reassociate <- near (δ U G).
      rewrite strength_shift2; auto.
      reassociate <- on left.
      now rewrite (fun_map_map (F := G)).
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
      dist T G ∘ map T σ ∘ dec T =
      map G (dec T) ∘ dist T G (A := A).
  Proof.
    intros. unfold_ops @Decorate_zero.
    reassociate -> on left. rewrite (fun_map_map (F := T)).
    change_right (map (G ∘ T) (pair Ƶ) ∘ δ T G (A := A)).
    rewrite (natural (ϕ := @dist T _ G _ _ _) (@pair W A Ƶ)).
    now unfold_ops @Map_compose.
  Qed.

  Instance DecoratedTraversableFunctor_zero :
    DecoratedTraversableFunctor W T :=
    {| dtfun_compat := @dtfun_compat_zero |}.

End TraversableFunctor_zero_DT.
