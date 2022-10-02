From Tealeaves Require Export
  Classes.Algebraic.Decorated.Functor
  Classes.Kleisli.Decorated.Functor
  Data.Product.

Import Algebraic.Comonad.Notations.

#[local] Generalizable Variables E.

(** * Derived operation <<fmapd>>  *)
(******************************************************************************)
Module Operation.
  Section operation.

    Context
      (E : Type)
      (F : Type -> Type)
      `{Fmap F} `{Decorate E F}.

    #[export] Instance Fmapd_alg : Fmapd E F :=
      fun A B (f : E * A -> B) => fmap F f ∘ dec F.

    End operation.
End Operation.

Import Operation.

(** * Kleisli laws for <<fmapd>> *)
(******************************************************************************)
Section laws.

  Context
    (F : Type -> Type)
    `{Algebraic.Decorated.Functor.DecoratedFunctor E F}.

  Theorem fmapd_id {A} : fmapd F (extract _) = @id (F A).
  Proof.
    introv. unfold_ops @Fmapd_alg.
    apply (dfun_dec_extract E F).
  Qed.

  Theorem fmapd_fmapd (A B C : Type) (g : E * B -> C) (f : E * A -> B) :
    fmapd F g ∘ fmapd F f = fmapd F (g co⋆ f).
  Proof.
    intros. unfold transparent tcs.
    reassociate <- on left.
    reassociate -> near (fmap F f).
    rewrite <- (natural (G := F ○ prod E)).
    reassociate <- on left.
    unfold transparent tcs.
    rewrite (fun_fmap_fmap F).
    reassociate -> on left.
    rewrite (dfun_dec_dec E F).
    reassociate <- on left.
    rewrite (fun_fmap_fmap F).
    reflexivity.
  Qed.

  #[export] Instance: Kleisli.Decorated.Functor.DecoratedFunctor E F :=
    {| dfun_fmapd1 := @fmapd_id;
       dfun_fmapd2 := @fmapd_fmapd
    |}.

End laws.

(** ** Specification for <<fmap>>  *)
(******************************************************************************)
Section decoratedfunctor_suboperations.

  Context
    (F : Type -> Type)
    `{Algebraic.Decorated.Functor.DecoratedFunctor E F}.

  (** *** [fmap] as a special case of [fmapd] *)
  Theorem fmap_to_fmapd {A B} : forall (f : A -> B),
      fmap F f = fmapd F (f ∘ extract (prod E)).
  Proof.
    introv. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap F).
    reassociate -> on right.
    now rewrite (dfun_dec_extract E F).
  Qed.

End decoratedfunctor_suboperations.

(** ** Interaction of [dec] and [fmapd], [fmap] *)
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

(** ** Composition laws for <<fmapd>> and <<fmap>> *)
(******************************************************************************)
Section fmapd_suboperation_composition.

  Context
    (F : Type -> Type)
    `{Algebraic.Decorated.Functor.DecoratedFunctor E F}.

  Corollary fmap_fmapd {A B C} : forall (g : B -> C) (f : E * A -> B),
    fmap F g ∘ fmapd F f = fmapd F (g ∘ f).
  Proof.
    introv. rewrite (fmap_to_fmapd F), (fmapd_fmapd F).
    do 2 fequal. now ext [w a].
  Qed.

  Corollary fmapd_fmap {A B C} : forall (g : E * B -> C) (f : A -> B),
      fmapd F g ∘ fmap F f = fmapd F (g ∘ map_snd f).
  Proof.
    introv. rewrite (fmap_to_fmapd F), (fmapd_fmapd F).
    fequal. now ext [w a].
  Qed.

End fmapd_suboperation_composition.
