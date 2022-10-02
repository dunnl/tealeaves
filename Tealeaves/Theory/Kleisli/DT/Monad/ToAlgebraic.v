From Tealeaves.Classes Require Export
  Functor
  Algebraic.Monad
  Algebraic.Decorated.Functor
  Algebraic.Decorated.Monad
  Algebraic.Traversable.Functor
  Algebraic.Traversable.Monad
  Algebraic.DT.Functor
  Algebraic.DT.Monad
  Kleisli.DT.Monad.


From Tealeaves.Theory Require Import
  Kleisli.Traversable.Monad.DerivedInstances
  Kleisli.Decorated.Monad.DerivedInstances
  Kleisli.DT.Monad.DerivedInstances
  Kleisli.DT.Monad.ToFunctor.

Import Monoid.Notations.
Import Product.Notations.
Import Functor.Notations.
Import Kleisli.Monad.Notations.
Import Kleisli.Decorated.Monad.Notations.
Import Kleisli.Traversable.Monad.Notations.
Import Kleisli.DT.Monad.Notations.
Import Algebraic.Comonad.Notations.

#[local] Generalizable Variables A B C.

Import ToFunctor.Operation.

Module Operations.
  Section with_kleisli.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Binddt W T T}
      `{Return T}.

    #[export] Instance Join_Binddt: Join T := fun A => binddt T (fun A => A) (B := A) (A := T A) (extract (W ×)).
    #[export] Instance Decorate_Binddt: Decorate W T := fun A => binddt T (fun A => A) (ret T).
    #[export] Instance Dist_Binddt: Dist T := fun G _ _ _ A => binddt T G (fmap G (ret T) ∘ extract (W ×)).

  End with_kleisli.
End Operations.

Import Operations.

Section with_monad.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Kleisli.DT.Monad.ToFunctor.Operation.
  Import Kleisli.DT.Monad.ToFunctor.Instances.
  Import Kleisli.DT.Monad.DerivedInstances.Operations.
  Import Kleisli.DT.Monad.DerivedInstances.Instances.

  Lemma ret_natural : Natural (@ret T _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Fmap_Binddt.
      rewrite (kdtm_binddt0 W T _ _ (G := fun A => A)).
      reflexivity.
  Qed.

  Lemma join_natural : Natural (@join T _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      unfold_ops @Fmap_compose.
      unfold_ops @Fmap_Binddt.
      unfold_ops @Join_Binddt.
      do 4 change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (T := T) f).
      unfold_compose_in_compose.
      rewrite (Instances.kmond_bindd2_T W T). (* left *)
      rewrite (Instances.kmond_bindd2_T W T). (* right *)
      rewrite (Decorated.Monad.DerivedInstances.dm_kleisli_star2).
      reassociate -> near (extract (W ×)).
      rewrite (DerivedInstances.dm_kleisli_star1).
      fequal.
      rewrite cokleisli_id_l.
      reflexivity.
  Qed.

  Lemma join_ret : `(join T ∘ ret T = @id (T A)).
  Proof.
    intros.
    unfold_ops @Join_Binddt.
    unfold_compose_in_compose.
    rewrite (kdtm_binddt0 W T _ _ (G := fun A => A)).
    now rewrite bimonad_baton.
  Qed.

  Lemma join_fmap_ret : `(join T ∘ fmap T (ret T) = @id (T A)).
  Proof.
    intros.
    unfold_ops @Fmap_Binddt.
    unfold_ops @Join_Binddt.
    unfold_compose_in_compose.
    change (binddt T (fun A0 : Type => A0) (extract (prod W) (A := T A)))
      with (fmap (fun A => A) (binddt T (fun A0 : Type => A0) (extract (prod W) (A := T A)))).
    rewrite (kdtm_binddt2 W T _ _ _ (G1 := fun A => A) (G2 := fun A => A)).
    rewrite (dtm_kleisli_70 W T).
    rewrite <- (natural (ϕ := @extract (W ×) _)).
    change (fmap (fun A => A) ?f) with f.
    rewrite <- (kdtm_binddt1 W T).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma join_join :
    `(join T ∘ join T (A := T A) = join T ∘ fmap T (join T)).
  Proof.
    intros.
    unfold_ops @Join_Binddt.
    unfold_compose_in_compose.
    unfold compose at 4. (* hidden  *)
    rewrite (binddt_fmap T (fun A => A) _ _ _ (extract (W ×)) (binddt T (fun A0 : Type => A0) (extract (prod W)))).
    do 3 change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (T := T) f).
    (* Merge LHS *)
    rewrite (kmond_bindd2 T).
    fequal. ext [w a]. cbn.
    now rewrite prepromote_extract2.
  Qed.

  #[local] Instance: Algebraic.Monad.Monad T :=
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
    unfold_ops @Decorate_Binddt.
    change (fmap T (coμ (prod W) (A := A)))
      with (fmap (fun A => A) (fmap T (coμ (A := A) (prod W)))).
    rewrite (fmap_binddt T (fun A => A)); try typeclasses eauto.
    do 3 change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (T := T) f).
    (* Merge LHS *)
    rewrite (kmond_bindd2 T).
    fequal.
    change (ret T) with (ret T ∘ (@id (W * A))) at 2.
    rewrite dm_kleisli_star1.
    change (fmap (fun A => A) ?f) with f.
    rewrite (natural (ϕ := @ret T _ )).
    change (fmap (fun A => A) ?f) with f.
    ext [w a]. cbn. reflexivity.
  Qed.

  Lemma dec_extract : forall (A : Type),
      fmap T (extract (W ×)) ∘ dec T = @id (T A).
  Proof.
    intros.
    unfold_ops @Decorate_Binddt.
    unfold_ops @Fmap_Binddt.
    do 2 change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (T := T) f).
    rewrite (kmond_bindd2 T).
    rewrite dm_kleisli_star2.
    rewrite Kleisli.Monad.Properties.kcompose01.
    change (ret T (A := W * A)) with (ret T ∘ @id (W * A)).
    reassociate <-. change (?g ∘ id) with g.
    rewrite (natural (ϕ := @ret T _ )).
    apply (kmond_bindd1 T).
  Qed.

  Lemma dec_natural : Natural (@dec W T _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Fmap_compose.
      unfold_ops @Fmap_Binddt.
      unfold_ops @Decorate_Binddt.
      do 2 change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (T := T) f).
      rewrite (kmond_bindd2 T).
      rewrite (kmond_bindd2 T).
      fequal.
      change (ret T (A := W * A)) with (ret T ∘ @id (W * A)).
      rewrite dm_kleisli_star5.
      reassociate -> near (extract (W ×)).
      rewrite dm_kleisli_star1.
      now rewrite cokcompose_misc1.
  Qed.

  #[local] Instance: Algebraic.Decorated.Functor.DecoratedFunctor W T :=
    {| dfun_dec_natural := dec_natural;
       dfun_dec_dec := dec_dec;
       dfun_dec_extract := dec_extract;
    |}.

  Lemma dmon_ret_ : forall (A : Type),
      dec T ∘ ret T = ret T ∘ pair Ƶ (B:=A).
  Proof.
    intros.
    unfold_ops @Decorate_Binddt.
    change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (T := T) f).
    now rewrite (kmond_bindd0 T).
  Qed.

  Lemma dmon_join_ : forall (A : Type),
      dec T ∘ join T (A:=A) = join T ∘ fmap T (shift T) ∘ dec T ∘ fmap T (dec T).
  Proof.
    intros. unfold shift, strength.
    unfold_ops @Decorate_Binddt.
    unfold_ops @Fmap_Binddt.
    unfold_ops @Join_Binddt.
    repeat change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (T := T) f).
    unfold_compose_in_compose.
    repeat rewrite (kmond_bindd2 T).
    fequal. reassociate -> near (extract (W ×)).
    rewrite dm_kleisli_star1.
    rewrite dm_kleisli_star1.
    rewrite cokcompose_misc1.
    rewrite cokleisli_id_l.
    rewrite dm_kleisli_star2.
    ext [w t].
    unfold kcompose.
    rewrite (kmon_bind0 T).
    unfold compose; cbn.
    compose near t on right.
    rewrite (kmond_bindd2 T).
    compose near t on right.
    rewrite (kmond_bindd2 T).
    fequal. ext [w' a].
    cbn. compose near (w', a) on right.
    rewrite (kmond_bindd0 T).
    unfold compose. cbn.
    compose near (w', a) on right.
    rewrite prepromote_ret.
    unfold compose; cbn.
    compose near (id w, (w', a)) on right.
    rewrite (kmond_bindd0 T).
    rewrite prepromote_ret.
    reflexivity.
  Qed.

  #[local] Instance: Algebraic.Decorated.Monad.DecoratedMonad W T :=
    {| dmon_ret := dmon_ret_;
       dmon_join := dmon_join_;
    |}.

End with_monad.

