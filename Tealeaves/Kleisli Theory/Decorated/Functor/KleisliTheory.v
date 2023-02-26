From Tealeaves Require Export
  Theory.Algebraic.Decorated.Functor.ToKleisli.

Import Product.Notations.

#[local] Generalizable Variables E.

(** * Derived Kleisli laws *)
(******************************************************************************)

Import ToKleisli.Operation.
Import ToKleisli.Instance.

(** *** Specification for <<fmap>>  *)
(******************************************************************************)
Section decoratedfunctor_suboperations.

  Context
    (F : Type -> Type)
    `{Algebraic.Decorated.Functor.DecoratedFunctor E F}.

  Theorem fmap_to_fmapd {A B} : forall (f : A -> B),
      fmap F f = fmapd F (f ∘ extract (prod E)).
  Proof.
    introv. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap F).
    reassociate -> on right.
    now rewrite (dfun_dec_extract E F).
  Qed.

End decoratedfunctor_suboperations.

(** *** Interaction of [dec] and [fmapd], [fmap] *)
(******************************************************************************)
Section decoratedfunctor_dec_fmapd.

  Context
    (F : Type -> Type)
    `{Algebraic.Decorated.Functor.DecoratedFunctor E F}.

  Theorem dec_fmapd {A B}: forall (f : E * A -> B),
      dec F ∘ fmapd F f = fmapd F (cobind (prod E) f).
  Proof.
    introv. unfold transparent tcs.
    reassociate <- on left.
    rewrite <- (natural (G := F ○ prod E)).
    reassociate -> on left.
    rewrite (dfun_dec_dec E F).
    reassociate <- on left.
    unfold transparent tcs. rewrite (fun_fmap_fmap F).
    reflexivity.
  Qed.

  Theorem dec_fmap {A B}: forall (f : A -> B),
      dec F ∘ fmap F f = fmap F (fmap (prod E) f) ∘ dec F.
  Proof.
    introv. now rewrite <- (natural (G := F ○ prod E)).
  Qed.

End decoratedfunctor_dec_fmapd.

(** *** Derived composition laws *)
(******************************************************************************)
Section fmapd_suboperation_composition.

  Context
    (F : Type -> Type)
    `{Algebraic.Decorated.Functor.DecoratedFunctor E F}.

  (** *** Composition between <<fmapd>> and <<fmap>> *)
  (******************** **********************************************************)
  Corollary fmap_fmapd {A B C} : forall (g : B -> C) (f : E * A -> B),
    fmap F g ∘ fmapd F f = fmapd F (g ∘ f).
  Proof.
    intros. unfold_ops @Fmapd_alg.
    reassociate <-.
    rewrite (fun_fmap_fmap F).
    reflexivity.
  Qed.

  Corollary fmapd_fmap {A B C} : forall (g : E * B -> C) (f : A -> B),
      fmapd F g ∘ fmap F f = fmapd F (g ∘ fmap (E ×) f).
  Proof.
    intros. unfold_ops @Fmapd_alg.
    rewrite <- (fun_fmap_fmap F).
    reassociate -> on right.
    rewrite <- (dec_fmap F).
    reflexivity.
  Qed.

End fmapd_suboperation_composition.
