From Tealeaves.Classes Require Export
  Decorated.Functor
  Decorated.Monad
  Kleisli.Decorated.Monad.

Import Monoid.Notations.
Import Product.Notations.
Import Functor.Notations.
Import Kleisli.Decorated.Monad.Notations.
Import Kleisli.Monad.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables A B C.

(** * Algebraic operations from Kleisli operation *)
(******************************************************************************)

Section with_kleisli.

  Context
    (W : Type)
      (T : Type -> Type)
      `{Bindd W T T}
      `{Return T}.

  #[export] Instance Fmap_Bindd: Fmap T := fun A B f => bindd T (ret T ∘ f ∘ extract (W ×)).
  #[export] Instance Join_Bindd: Join T := fun A => bindd T (B := A) (A := T A) (extract (W ×)).
  #[export] Instance Decorate_Bindd: Decorate W T := fun A => bindd T (ret T).

End with_kleisli.

Module Instances.

  Import Kleisli.Decorated.Monad.Derived.

  Section with_monad.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Kleisli.Decorated.Monad.Monad W T}.

    Lemma fmap_id : forall (A : Type),
        fmap T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Fmap_Bindd.
      change (ret T ∘ id) with (ret T (A := A)).
      now rewrite (kmond_bindd1 T).
    Qed.

    Lemma fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Bindd.
      rewrite (kmond_bindd2 T).
      fequal.
      reassociate -> near (extract (prod W) (A := A)).
      now rewrite (dm_kleisli_star5 T).
    Qed.

    #[local] Instance: Classes.Functor.Functor T :=
      {| fun_fmap_id := fmap_id;
        fun_fmap_fmap := fmap_fmap;
      |}.

    Lemma ret_natural : Natural (@ret T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Fmap_Bindd.
        rewrite (kmond_bindd0 T).
        reflexivity.
    Qed.

    Lemma join_natural : Natural (@join T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Fmap_compose.
        unfold_ops @Fmap_Bindd.
        unfold_ops @Join_Bindd.
        unfold_compose_in_compose.
        rewrite (kmond_bindd2 T). (* left *)
        rewrite (kmond_bindd2 T). (* right *)
        rewrite (dm_kleisli_star2 T).
        reassociate -> near (extract (W ×)).
        rewrite (dm_kleisli_star1 T).
        fequal.
        rewrite cokleisli_id_l.
        reflexivity.
    Qed.

    Lemma join_ret : `(join T ∘ ret T = @id (T A)).
    Proof.
      intros.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      rewrite (kmond_bindd0 T).
      reflexivity.
    Qed.

    Lemma join_fmap_ret : `(join T ∘ fmap T (ret T) = @id (T A)).
    Proof.
      intros.
      unfold_ops @Fmap_Bindd.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      rewrite (kmond_bindd2 T).
      reassociate -> near (extract (W ×)).
      rewrite (dm_kleisli_star1 T).
      rewrite cokleisli_id_l.
      rewrite (kmond_bindd1 T).
      reflexivity.
    Qed.

    Lemma join_join :
      `(join T ∘ join T (A := T A) = join T ∘ fmap T (join T)).
    Proof.
      intros.
      (* Merge LHS *)
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      rewrite (kmond_bindd2 T).
      (* Merge RHS *)
      unfold_ops @Fmap_Bindd.
      rewrite (kmond_bindd2 T).
      fequal.
      reassociate ->.
      rewrite (dm_kleisli_star1 T).
      rewrite (cokcompose_misc1).
      ext [w a]. cbn.
      now rewrite preincr_extract2.
    Qed.

    #[local] Instance: Classes.Monad.Monad T :=
      {| mon_ret_natural := ret_natural;
        mon_join_natural := join_natural;
        mon_join_ret := join_ret;
        mon_join_fmap_ret := join_fmap_ret;
        mon_join_join := join_join;
      |}.

    Lemma dec_dec : forall (A : Type),
        dec T ∘ dec T = fmap T (cojoin (W ×)) ∘ dec T (A := A).
    Proof.
      intros.
      (* Merge LHS *)
      unfold_ops @Decorate_Bindd.
      rewrite (kmond_bindd2 T).
      (* Merge RHS *)
      unfold_ops @Fmap_Bindd.
      rewrite (kmond_bindd2 T).
      fequal. rewrite (dm_kleisli_star2 T).
      rewrite (Kleisli.Monad.kleisli_id_r T).
      ext [w a]. cbn.
      compose near (w, a) on left.
      rewrite (kmond_bindd0 T).
      unfold compose; cbn.
      unfold_ops @Return_writer.
      unfold preincr, compose, incr.
      now simpl_monoid.
    Qed.

    Lemma dec_extract : forall (A : Type),
        fmap T (extract (W ×)) ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_ops @Decorate_Bindd.
      unfold_ops @Fmap_Bindd.
      rewrite (kmond_bindd2 T).
      change (ret T (A := W * A)) with (ret T ∘ @id (W * A)).
      rewrite (dm_kleisli_star5 T).
      apply (kmond_bindd1 T).
    Qed.

    Lemma dec_natural : Natural (@dec W T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Fmap_compose.
        unfold_ops @Fmap_Bindd.
        unfold_ops @Decorate_Bindd.
        rewrite (kmond_bindd2 T).
        rewrite (kmond_bindd2 T).
        fequal.
        change (ret T (A := W * A)) with (ret T ∘ @id (W * A)).
        rewrite (dm_kleisli_star5 T).
        reassociate -> near (extract (W ×)).
        rewrite (dm_kleisli_star1 T).
        now rewrite cokcompose_misc1.
    Qed.

    #[local] Instance: Decorated.Functor.DecoratedFunctor W T :=
      {| dfun_dec_natural := dec_natural;
        dfun_dec_dec := dec_dec;
        dfun_dec_extract := dec_extract;
      |}.

    Lemma dmon_ret_ : forall (A : Type),
        dec T ∘ ret T = ret T ∘ pair Ƶ (B:=A).
    Proof.
      intros.
      unfold_ops @Decorate_Bindd.
      now rewrite (kmond_bindd0 T).
    Qed.

    Lemma dmon_join_ : forall (A : Type),
        dec T ∘ join T (A:=A) = join T ∘ fmap T (shift T) ∘ dec T ∘ fmap T (dec T).
    Proof.
      intros. unfold shift, strength.
      unfold_ops @Decorate_Bindd.
      unfold_ops @Fmap_Bindd.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      repeat rewrite (kmond_bindd2 T).
      fequal. reassociate -> near (extract (W ×)).
      rewrite (dm_kleisli_star1 T).
      rewrite (dm_kleisli_star1 T).
      rewrite cokcompose_misc1.
      rewrite cokleisli_id_l.
      rewrite (dm_kleisli_star2 T).
      ext [w t].
      unfold Monad.kcompose.
      rewrite (Monad.kmon_bind0 T).
      unfold compose; cbn.
      compose near t on right.
      rewrite (Monad.kmond_bindd2 T).
      compose near t on right.
      rewrite (Monad.kmond_bindd2 T).
      fequal. ext [w' a].
      cbn. compose near (w', a) on right.
      rewrite (Monad.kmond_bindd0 T).
      unfold compose. cbn.
      compose near (w', a) on right.
      rewrite preincr_ret.
      unfold compose; cbn.
      compose near (id w, (w', a)) on right.
      rewrite (kmond_bindd0 T).
      rewrite preincr_ret.
      reflexivity.
    Qed.

    #[local] Instance: Decorated.Monad.DecoratedMonad W T :=
      {| dmon_ret := dmon_ret_;
        dmon_join := dmon_join_;
      |}.

  End with_monad.

End Instances.

#[local] Generalizable Variables T W.

Module CategoricalToKleisli.

  Context
    `{fmapT : Fmap T}
    `{decT : Decorate W T}
    `{joinT : Join T}
    `{retT : Return T}
    `{Monoid W}
    `{! Decorated.Monad.DecoratedMonad W T}.

  #[local] Instance bindd' : Bindd W T T := ToKleisli.Bindd_dec W T.

  Definition fmap' : Fmap T := Fmap_Bindd W T.
  Definition dec' : Decorate W T := Decorate_Bindd W T.
  Definition join' : Join T := Join_Bindd W T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @Fmap_Bindd.
    unfold bindd, bindd'.
    unfold_ops @ToKleisli.Bindd_dec.
    ext A B f.
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    reassociate ->.
    rewrite (dfun_dec_extract W T).
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

  Goal decT = dec'.
  Proof.
    unfold dec'. unfold_ops @Decorate_Bindd.
    unfold bindd, bindd'.
    unfold_ops @ToKleisli.Bindd_dec.
    ext A.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @Join_Bindd.
    unfold bindd, bindd'.
    unfold_ops @ToKleisli.Bindd_dec.
    ext A.
    reassociate ->.
    rewrite (dfun_dec_extract W T).
    reflexivity.
  Qed.

End CategoricalToKleisli.

Module KleisliToAlgebraic.

  Context
    `{binddT : Bindd W T T}
    `{retT : Return T}
    `{Monoid W}
    `{@Classes.Kleisli.Decorated.Monad.Monad W T retT binddT _ _}.

  #[local] Instance fmap' : Fmap T := Fmap_Bindd W T.
  #[local] Instance dec' : Decorate W T := Decorate_Bindd W T.
  #[local] Instance join' : Join T := Join_Bindd W T.

  Definition bindd' : Bindd W T T := ToKleisli.Bindd_dec W T.

  Goal binddT = bindd'.
  Proof.
    unfold bindd'. unfold_ops @ToKleisli.Bindd_dec.
    unfold fmap, fmap', dec, dec', join, join'.
    unfold_ops @Fmap_Bindd.
    unfold_ops @Join_Bindd.
    unfold_ops @Decorate_Bindd.
    ext A B f.
    unfold_compose_in_compose.
    rewrite (kmond_bindd2 T).
    rewrite (kmond_bindd2 T).
    fequal.
    reassociate -> near (extract (W ×)).
    rewrite (Derived.dm_kleisli_star1 T).
    rewrite cokleisli_id_l.
    change (@ret T _ (W * A)) with (@ret T _ (W * A) ∘ id).
    rewrite (Derived.dm_kleisli_star5 T).
    reflexivity.
  Qed.

End KleisliToAlgebraic.
