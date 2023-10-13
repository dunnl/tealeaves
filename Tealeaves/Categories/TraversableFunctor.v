From Tealeaves Require Import
  Classes.Categorical.TraversableFunctor.

#[local] Generalizable Variables T F U G X Y ϕ.

(** * Monoid structure of traversable functors *)
(******************************************************************************)

(** ** The identity functor is traversable *)
(******************************************************************************)
#[export] Instance Dist_I : ApplicativeDist (fun A => A) := fun F map mult pure A a => a.

#[export, program] Instance Traversable_I : TraversableFunctor (fun A => A).

Next Obligation.
  constructor; try typeclasses eauto.
  intros. ext a. unfold transparent tcs.
  reflexivity.
Qed.

Next Obligation.
  unfold transparent tcs. ext a.
  symmetry. now rewrite (fun_map_id (F := G1)).
Qed.

(** ** Traversable functors are closed under composition *)
(******************************************************************************)
Section TraversableFunctor_compose.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  #[export] Instance Dist_compose : ApplicativeDist (T ∘ U) :=
    fun G Gmap mult pure A =>
      dist T G ∘ map T (dist U G (A := A)).

  Lemma dist_unit_compose : forall A,
      dist (T ∘ U) (fun A => A) = @id (T (U A)).
  Proof.
    intros. unfold transparent tcs.
    rewrite (dist_unit (F := T)).
    rewrite (dist_unit (F := U)).
    now rewrite (fun_map_id (F := T)).
  Qed.

  Lemma dist_natural_compose : forall `{Applicative G} `(f : X -> Y),
      map (G ∘ (T ∘ U)) f ∘ dist (T ∘ U) G = dist (T ∘ U) G ∘ map ((T ∘ U) ∘ G) f.
  Proof.
    intros. unfold transparent tcs.
    change_left (map (G ∘ T) (map U f) ∘ dist T G ∘ map T (dist U G)).
    #[local] Set Keyed Unification.
    rewrite (natural (ϕ := @dist T _ G _ _ _ ) (F := T ∘ G)).
    #[local] Unset Keyed Unification.
    unfold_ops @Map_compose.
    reassociate -> on left.
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (fun_map_map (F := T)).
    rewrite (fun_map_map (F := T)).
    change (map ?F (map ?G ?f)) with (map (F ∘ G) f).
    now rewrite <- (natural (ϕ := @dist U _ G _ _ _)).
  Qed.

  Instance dist_natural_compose_ : forall `{Applicative G}, Natural (@dist (T ∘ U) _ G _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    intros. apply dist_natural_compose.
  Qed.

  Lemma dist_morph_compose : forall `{ApplicativeMorphism G1 G2 ϕ} (A : Type),
      dist (T ∘ U) G2 ∘ map (T ∘ U) (ϕ A) = ϕ (T (U A)) ∘ dist (T ∘ U) G1.
  Proof.
    intros. unfold transparent tcs.
    reassociate -> on left.
    unfold_compose_in_compose.
    rewrite (fun_map_map (F := T)).
    rewrite (dist_morph (F := U)).
    rewrite <- (fun_map_map (F := T)).
    reassociate <- on left.
    now rewrite (dist_morph (F := T)).
  Qed.

  Lemma dist_linear_compose : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (T ∘ U) (G1 ∘ G2) = map G1 (dist (T ∘ U) G2) ∘ dist (T ∘ U) G1 (A := G2 A).
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_map_map (F := G1)).
    reassociate -> on right;
      change (map ?F (map ?G ?f)) with (map (F ∘ G) f);
      reassociate <- near (map (G1 ∘ T) (dist U G2)).
    #[local] Set Keyed Unification.
    rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
    #[local] Unset Keyed Unification.
    reassociate -> on right;
      unfold_ops @Map_compose;
      rewrite (fun_map_map (F := T)).
    #[local] Set Keyed Unification.
    rewrite (dist_linear (F := U)).
    rewrite (dist_linear (F := T)).
    #[local] Unset Keyed Unification.
    reflexivity.
  Qed.

  #[export] Instance Traversable_compose : TraversableFunctor (T ∘ U) :=
    {| dist_morph := @dist_morph_compose;
       dist_unit := @dist_unit_compose;
       dist_linear := @dist_linear_compose;
    |}.

End TraversableFunctor_compose.
