From Tealeaves Require Export
  Classes.Functor
  Applicative.

Import Functor.Notations.
Import Applicative.Notations.

#[local] Generalizable Variable X Y T U G ϕ A.

(** * Traversable functors *)
(******************************************************************************)
Section TraversableFunctor_operation.

  Context
    (F : Type -> Type).

  Class Dist :=
    dist : forall (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}, F ○ G ⇒ G ○ F.

End TraversableFunctor_operation.

Section TraversableFunctor.

  Context
    (F : Type -> Type)
    `{Functor F}
    `{Dist F}.

  Class TraversableFunctor :=
    { trav_functor :> Functor F;
      dist_natural :> forall `{Applicative G},
          @Natural (F ∘ G) _ (G ∘ F) _ (dist F G);
      dist_morph : forall `{ApplicativeMorphism G1 G2 ϕ} A,
          dist F G2 A ∘ fmap F (ϕ A) = ϕ (F A) ∘ dist F G1 A;
      dist_unit :
        `(dist F (fun A => A) A = id);
      dist_linear : forall `{Applicative G1} `{Applicative G2},
          `(dist F (G1 ∘ G2) A = fmap G1 (dist F G2 A) ∘ dist F G1 (G2 A));
    }.

End TraversableFunctor.

#[global] Arguments dist F%function_scope {Dist} G%function_scope {H H0 H1} {A}%type_scope.

(** ** Distribution-respecting natural transformations *)
(******************************************************************************)
Section TraversableMorphism.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  Class TraversableMorphism (ϕ : T ⇒ U) :=
    { trvmor_trv_F : TraversableFunctor T;
      trvmor_trv_G : TraversableFunctor U;
      trvmor_nat :> Natural ϕ;
      trvmor_hom : forall `{Applicative G},
          `(fmap G (ϕ A) ∘ dist T G = dist U G ∘ ϕ (G A));
    }.

End TraversableMorphism.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'δ'" := (dist) : tealeaves_scope.
End Notations.

(** * Monoid structure of traversable functors *)
(******************************************************************************)

(** ** The identity functor is traversable *)
(******************************************************************************)
#[export] Instance Dist_I : Dist (fun A => A) := fun F fmap mult pure A a => a.

#[export, program] Instance Traversable_I : TraversableFunctor (fun A => A).

Next Obligation.
  constructor; try typeclasses eauto.
  intros. ext a. unfold transparent tcs.
  reflexivity.
Qed.

Next Obligation.
  unfold transparent tcs. ext a.
  symmetry. now rewrite (fun_fmap_id G1).
Qed.

(** ** Traversable functors are closed under composition *)
(******************************************************************************)
Section TraversableFunctor_compose.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  #[export] Instance Dist_compose : Dist (T ∘ U) :=
    fun G map mult pure A =>
      dist T G ∘ fmap T (dist U G (A := A)).

  Lemma dist_unit_compose : forall A,
      dist (T ∘ U) (fun A => A) = @id (T (U A)).
  Proof.
    intros. unfold transparent tcs.
    rewrite (dist_unit T).
    rewrite (dist_unit U).
    now rewrite (fun_fmap_id T).
  Qed.

  Lemma dist_natural_compose : forall `{Applicative G} `(f : X -> Y),
      fmap (G ∘ (T ∘ U)) f ∘ dist (T ∘ U) G = dist (T ∘ U) G ∘ fmap ((T ∘ U) ∘ G) f.
  Proof.
    intros. unfold transparent tcs.
    change_left (fmap (G ∘ T) (fmap U f) ∘ dist T G ∘ fmap T (dist U G)).
    #[local] Set Keyed Unification.
    rewrite (natural (ϕ := @dist T _ G _ _ _ ) (F := T ∘ G)).
    #[local] Unset Keyed Unification.
    unfold_ops @Fmap_compose.
    reassociate -> on left.
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    rewrite (fun_fmap_fmap T).
    change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f).
    now rewrite <- (natural (ϕ := @dist U _ G _ _ _)).
  Qed.

  Instance dist_natural_compose_ : forall `{Applicative G}, Natural (@dist (T ∘ U) _ G _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    intros. apply dist_natural_compose.
  Qed.

  Lemma dist_morph_compose : forall `{ApplicativeMorphism G1 G2 ϕ} (A : Type),
      dist (T ∘ U) G2 ∘ fmap (T ∘ U) (ϕ A) = ϕ (T (U A)) ∘ dist (T ∘ U) G1.
  Proof.
    intros. unfold transparent tcs.
    reassociate -> on left.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    rewrite (dist_morph U).
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on left.
    now rewrite (dist_morph T).
  Qed.

  Lemma dist_linear_compose : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (T ∘ U) (G1 ∘ G2) = fmap G1 (dist (T ∘ U) G2) ∘ dist (T ∘ U) G1 (A := G2 A).
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap G1).
    reassociate -> on right;
      change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f);
      reassociate <- near (fmap (G1 ∘ T) (dist U G2)).
    #[local] Set Keyed Unification.
    rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
    #[local] Unset Keyed Unification.
    reassociate -> on right;
      unfold_ops @Fmap_compose;
      rewrite (fun_fmap_fmap T).
    #[local] Set Keyed Unification.
    rewrite (dist_linear U).
    rewrite (dist_linear T).
    #[local] Unset Keyed Unification.
    reflexivity.
  Qed.

  #[export] Instance Traversable_compose : TraversableFunctor (T ∘ U) :=
    {| dist_morph := @dist_morph_compose;
       dist_unit := @dist_unit_compose;
       dist_linear := @dist_linear_compose;
    |}.

End TraversableFunctor_compose.
