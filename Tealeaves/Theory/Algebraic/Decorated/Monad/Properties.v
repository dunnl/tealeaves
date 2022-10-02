From Tealeaves Require Export
  Classes.Algebraic.Decorated.Monad
  Classes.Monoid
  Data.Product.

Import Product.Notations.

#[local] Generalizable Variables E F ϕ A B.

(** * Pushing decorations through a monoid homomorphism *)
(** If a functor is readable by a monoid, it is readable by any target
    of a homomorphism from that monoid too. *)
(******************************************************************************)
Section DecoratedFunctor_monoid_homomorphism.

  Context
    (Wsrc Wtgt : Type)
    `{Monoid_Morphism Wsrc Wtgt ϕ}
    `{Decorate Wsrc F} `{Fmap F} `{Return F} `{Join F}
    `{! DecoratedMonad Wsrc F}.

  Instance Decorate_homomorphism :
    Decorate Wtgt F := fun A => fmap F (map_fst ϕ) ∘ dec F.

  Instance Natural_read_morphism : Natural (@dec Wtgt F Decorate_homomorphism).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Decorate_homomorphism.
      unfold_ops @Fmap_compose.
      reassociate <- on left.
      rewrite (fun_fmap_fmap F).
      rewrite (product_fmap_commute).
      rewrite <- (fun_fmap_fmap F).
      reassociate -> on left.
      change (fmap F (fmap (prod Wsrc) f)) with
          (fmap (F ∘ prod Wsrc) f).
      now rewrite (natural (ϕ := @dec Wsrc F _ )).
  Qed.

  Instance DecoratedFunctor_morphism : DecoratedFunctor Wtgt F.
  Proof.
    constructor; try typeclasses eauto.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate <-. reassociate -> near (fmap F (map_fst ϕ)).
      rewrite <- (natural (ϕ := @dec Wsrc F _) (map_fst ϕ)).
      reassociate <-. unfold_ops @Fmap_compose. rewrite (fun_fmap_fmap F).
      reassociate -> near (@dec Wsrc F _ A).
      rewrite (dfun_dec_dec Wsrc F).
      reassociate <-. rewrite (fun_fmap_fmap F).
      reassociate <-. rewrite (fun_fmap_fmap F).
      fequal. fequal. ext [w a]. reflexivity.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate <-. rewrite (fun_fmap_fmap F).
      replace (extract (Wtgt ×) ∘ map_fst ϕ)
        with (@extract (Wsrc ×) _ A) by now ext [w a].
      now rewrite (dfun_dec_extract Wsrc F).
  Qed.

  Instance DecoratedMonad_morphism : DecoratedMonad Wtgt F.
  Proof.
    inversion H3.
    constructor; try typeclasses eauto.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate ->. rewrite (dmon_ret Wsrc F).
      reassociate <-. rewrite (natural (ϕ := @ret F _)).
      ext a. unfold compose; cbn.
      now rewrite (monmor_unit).
    - intros. unfold dec, Decorate_homomorphism.
      reassociate ->. rewrite (dmon_join Wsrc F).
      repeat reassociate <-.
      rewrite (natural (ϕ := @join F _)).
      reassociate -> near (fmap F (shift F)).
      unfold_ops @Fmap_compose.
      unfold_compose_in_compose.
      rewrite (fun_fmap_fmap F _ _ _ (shift F) (fmap F (map_fst ϕ))).
      reassociate -> near (fmap F (map_fst ϕ)). rewrite (fun_fmap_fmap F).
      rewrite <- (fun_fmap_fmap F _ _ _ (dec F) (fmap F (map_fst ϕ))).
      reassociate <-. reassociate -> near (fmap F (fmap F (map_fst ϕ))).
      rewrite <- (natural (ϕ := @dec Wsrc F _)).
      reassociate <-. unfold_ops @Fmap_compose.
      reassociate -> near (fmap F (fmap (prod Wsrc) (fmap F (map_fst ϕ)))).
      rewrite (fun_fmap_fmap F).
      repeat fequal. ext [w t].
      unfold compose; cbn.
      change (id ?f) with f. unfold shift.
      unfold compose; cbn.
      do 2 (compose near t;
            repeat rewrite (fun_fmap_fmap F)).
      fequal. ext [w' a].
      unfold compose; cbn. rewrite monmor_op.
      reflexivity.
  Qed.

End DecoratedFunctor_monoid_homomorphism.
