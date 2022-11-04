From Tealeaves.Classes Require Export
  Functor
  Algebraic.Monad
  Algebraic.Decorated.Functor
  Algebraic.Decorated.Monad
  Algebraic.Traversable.Functor
  Algebraic.Traversable.Monad
  Algebraic.DT.Functor
  Algebraic.DT.Monad
  Kleisli.DT.Monad
  Kleisli.Traversable.Functor.

From Tealeaves.Theory Require Import
  Kleisli.Traversable.Monad.DerivedInstances
  Kleisli.Decorated.Monad.DerivedInstances
  Kleisli.DT.Functor.DerivedInstances
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
  Import Kleisli.DT.Monad.ToFunctor.Instance.
  Import Kleisli.DT.Monad.DerivedInstances.Operations.
  Import Kleisli.DT.Monad.DerivedInstances.Instances.

  (** *** Monad instance *)
  (******************************************************************************)
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
      rewrite (Decorated.Monad.DerivedInstances.dm_kleisli_star2 T).
      reassociate -> near (extract (W ×)).
      rewrite (DerivedInstances.dm_kleisli_star1 T).
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

  (** *** Decorated functor instance *)
  (******************************************************************************)
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
    rewrite (dm_kleisli_star1 T).
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
    rewrite (dm_kleisli_star2 T).
    rewrite Instances.kcompose01.
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
      rewrite (dm_kleisli_star5 T).
      reassociate -> near (extract (W ×)).
      rewrite (dm_kleisli_star1 T).
      now rewrite cokcompose_misc1.
  Qed.

  #[local] Instance: Algebraic.Decorated.Functor.DecoratedFunctor W T :=
    {| dfun_dec_natural := dec_natural;
       dfun_dec_dec := dec_dec;
       dfun_dec_extract := dec_extract;
    |}.

  (** *** Decorated monad instance *)
  (******************************************************************************)
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
    rewrite (dm_kleisli_star1 T).
    rewrite (dm_kleisli_star1 T).
    rewrite cokcompose_misc1.
    rewrite cokleisli_id_l.
    rewrite (dm_kleisli_star2 T).
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

  (** *** Traversable functor instance *)
  (******************************************************************************)
  Lemma dist_natural_T : forall (G : Type -> Type) (H2 : Fmap G) (H3 : Pure G) (H4 : Mult G),
      Applicative G -> Natural (@dist T _ G H2 H3 H4).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      unfold_ops @Fmap_compose @Dist_Binddt @Fmap_Binddt.
      change_left (fmap G (fmap T f) ∘ bindt T G (fmap G (ret T))).
      rewrite (fmap_bindt T G).
      rewrite (fun_fmap_fmap G).
      (* RHS *)
      change_right (
          bindt T G (fmap G (ret T)) ∘
            bind T (ret T ∘ fmap G f)).
      rewrite (bindt_bind T G).
      reassociate <- on right.
      rewrite (ktm_bindt0 T); [|assumption].
      rewrite (fun_fmap_fmap G).
      rewrite (natural (ϕ := @ret T _)).
      reflexivity.
  Qed.

  Lemma dist_morph_T : forall (G1 G2 : Type -> Type) (H2 : Fmap G1) (H3 : Pure G1) (H4 : Mult G1) (H5 : Fmap G2)
                         (H6 : Pure G2) (H7 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist T G2 ∘ fmap T (ϕ A) = ϕ (T A) ∘ dist T G1.
  Proof.
    introv morph. inversion morph.
    intros.
    unfold_ops @Dist_Binddt @Fmap_Binddt.
    change (fmapdt T G2 (extract (prod W)) ∘ fmap T (ϕ A)
            = ϕ (T A) ∘ traverse T G1 (@id (G1 A))).
    change (@Fmap_Binddt T W H0 H)
      with (@Operation.Fmap_Fmapdt T W _).
    rewrite (fmapdt_fmap T G2).
    rewrite (trf_traverse_morphism T).
    rewrite <- (natural (ϕ := @extract (W ×) _)).
    reflexivity.
  Qed.

  Lemma dist_unit_T : forall A : Type,
      dist T (fun A0 : Type => A0) = @id (T A).
  Proof.
    intros. unfold_ops @Dist_Binddt.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Fmap G1) (H3 : Pure G1) (H4 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H6 : Fmap G2) (H7 : Pure G2) (H8 : Mult G2),
        Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = fmap G1 (dist T G2) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Binddt.
    rewrite (kdtm_binddt2 W T); try typeclasses eauto.
    fequal.
    rewrite (kcompose_dtm_33 W T).
    change (fmap G1 (ret T (A := G2 A))) with (fmap G1 (ret T) ∘ @id (G1 (G2 A))).
    rewrite (kcompose_tm31 T); try typeclasses eauto.
    reflexivity.
  Qed.

  #[export] Instance: Algebraic.Traversable.Functor.TraversableFunctor T :=
    {| dist_natural := dist_natural_T;
       dist_morph := dist_morph_T;
       dist_unit := dist_unit_T;
       dist_linear := dist_linear_T;
    |}.

  (** *** Decorated Traversable functor instance *)
  (******************************************************************************)
  Lemma dtfun_compat_T : forall (G : Type -> Type) (H2 : Fmap G) (H3 : Pure G) (H4 : Mult G),
      Applicative G -> forall A : Type,
        dist T G ∘ fmap T (strength G) ∘ dec (A := G A) T = fmap G (dec T) ∘ dist T G.
  Proof.
    intros. unfold_ops @Dist_Binddt @Fmap_Binddt @Decorate_Binddt.
    change (fmapdt T G (extract (prod W)) ∘ fmapd T (strength G ∘ extract (prod W)) ∘ fmapd T (@id (W * G A)) =
              fmap G (fmapd T id) ∘ fmapdt T G (extract (prod W))).
    rewrite (fmapdt_fmapd T G).
    rewrite (fmapdt_fmapd T G).
    rewrite (fmapd_fmapdt T G).
    rewrite (cobind_id (W ×)).
    rewrite (fun_fmap_id G).
    fequal. ext [w a].
    reflexivity.
  Qed.

  #[export] Instance: Algebraic.DT.Functor.DecoratedTraversableFunctor W T :=
    {| dtfun_compat := dtfun_compat_T;
    |}.

  (** *** Traversable monad instance *)
  (******************************************************************************)
  Lemma trvmon_ret_T : forall (G : Type -> Type) (H3 : Fmap G) (H4 : Pure G) (H5 : Mult G),
      Applicative G -> forall A : Type, dist T G ∘ ret T (A := G A) = fmap G (ret T).
  Proof.
    intros. unfold_ops @Dist_Binddt @Fmap_Binddt.
    rewrite (kdtm_binddt0 W T); [|assumption].
    ext a. reflexivity.
  Qed.


  Lemma trvmon_join_T : forall (G : Type -> Type) (H3 : Fmap G) (H4 : Pure G) (H5 : Mult G),
      Applicative G -> forall A : Type, dist T G ∘ join T = fmap G (join T) ∘ dist (T ∘ T) G (A := A).
  Proof.
    intros.
    unfold_ops @Dist_compose.
    unfold_ops @Dist_Binddt @Fmap_Binddt @Join_Binddt.
    change_left (bindt T G (fmap G (ret T)) ∘ bind T (@id (T (G A)))).
    change_right (fmap G (bind T (@id (T A)))
                    ∘ (bindt T G (fmap G (ret T))
                         ∘ bind T (ret T ∘ bindt T G (fmap G (ret T))))).
    rewrite (bindt_bind T G).
    rewrite (bindt_bind T G).
    reassociate <-. rewrite (ktm_bindt0 T); [|typeclasses eauto].
    rewrite (bind_bindt T G).
    reassociate <- on right.
    rewrite (fun_fmap_fmap G).
    rewrite (kmon_bind0 T).
    rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

  #[export] Instance: Algebraic.Traversable.Monad.TraversableMonad T :=
    {| trvmon_ret := trvmon_ret_T;
      trvmon_join := trvmon_join_T;
    |}.

  (** *** Decorated Traversable monad instance *)
  (******************************************************************************)
  #[export] Instance: Algebraic.DT.Monad.DecoratedTraversableMonad W T :=
    ltac:(constructor; typeclasses eauto).

End with_monad.

