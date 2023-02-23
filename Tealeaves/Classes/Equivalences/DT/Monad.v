From Tealeaves.Classes Require Export
  Functor
  Monad
  Decorated.Functor
  Decorated.Monad
  Traversable.Functor
  Traversable.Monad
  DT.Functor
  DT.Monad.

From Tealeaves.Classes.Kleisli Require Export  
  Monad
  Decorated.Functor
  Decorated.Monad
  Traversable.Functor
  Traversable.Monad
  DT.Functor
  DT.Monad.

Import Monoid.Notations.
Import Product.Notations.
Import Functor.Notations.
Import Kleisli.Monad.Notations.
Import Kleisli.Decorated.Monad.Notations.
Import Kleisli.Traversable.Monad.Notations.
Import Kleisli.DT.Monad.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables A B C.

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

  Import DT.Monad.Derived.

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
      rewrite (kmond_bindd2_T W T). (* left *)
      rewrite (kmond_bindd2_T W T). (* right *)
      rewrite (Decorated.Monad.Derived.dm_kleisli_star2 T).
      reassociate -> near (extract (W ×)).
      rewrite (Derived.dm_kleisli_star1 T).
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
    now rewrite Mult_compose_identity1.
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
    now rewrite preincr_extract2.
  Qed.

  #[local] Instance: Classes.Monad.Monad T :=
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
    rewrite (Derived.dm_kleisli_star1 T).
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
    rewrite (Derived.dm_kleisli_star2 T).
    rewrite Monad.ToFunctor.kcompose01.
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
      rewrite (Derived.dm_kleisli_star5 T).
      reassociate -> near (extract (W ×)).
      rewrite (Derived.dm_kleisli_star1 T).
      now rewrite cokcompose_misc1.
  Qed.

  #[local] Instance: Decorated.Functor.DecoratedFunctor W T :=
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
    rewrite (Derived.dm_kleisli_star1 T).
    rewrite (Derived.dm_kleisli_star1 T).
    rewrite cokcompose_misc1.
    rewrite cokleisli_id_l.
    rewrite (Derived.dm_kleisli_star2 T).
    ext [w t].
    unfold Monad.kcompose.
    rewrite (Monad.kmon_bind0 T).
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
      with (@Derived.Fmap_Fmapdt T W _).
    rewrite (Derived.fmapdt_fmap T G2).
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
    rewrite (Derived.kcompose_tm31 (fmap G2 (ret T))).
    reflexivity.
  Qed.

  #[export] Instance: Traversable.Functor.TraversableFunctor T :=
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

  #[export] Instance: DT.Functor.DecoratedTraversableFunctor W T :=
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

  #[export] Instance: Traversable.Monad.TraversableMonad T :=
    {| trvmon_ret := trvmon_ret_T;
      trvmon_join := trvmon_join_T;
    |}.

  (** *** Decorated Traversable monad instance *)
  (******************************************************************************)
  #[export] Instance: DT.Monad.DecoratedTraversableMonad W T :=
    ltac:(constructor; typeclasses eauto).

End with_monad.

#[local] Generalizable Variables T W.

Module AlgebraicToKleisli.

  Context
    `{Monoid W}
    `{fmapT : Fmap T}
    `{distT : Dist T}
    `{joinT : Join T}
    `{decorateT : Decorate W T}
    `{Return T}
    `{! Classes.DT.Monad.DecoratedTraversableMonad W T}.

  #[local] Instance binddt' : Binddt W T T := ToKleisli.Binddt_ddj T.

  Definition fmap' : Fmap T := Derived.Fmap_Binddt T.
  Definition join' : Join T := Operations.Join_Binddt W T.
  Definition decorate' : Decorate W T := Operations.Decorate_Binddt W T.
  Definition dist' : Dist T := Operations.Dist_Binddt W T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @Derived.Fmap_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_ddj.
    ext A B f.
    unfold_ops @Fmap_I.
    rewrite (dist_unit T).
    change (?f ∘ id) with f.
    do 2 rewrite <- (fun_fmap_fmap T).
    do 2 reassociate <- on right.
    rewrite (mon_join_fmap_ret T).
    change (id ∘ ?f) with f.
    reassociate -> on right.
    rewrite (dfun_dec_extract W T).
    reflexivity.
  Qed.

  Goal forall G `{Applicative G}, @distT G _ _ _ = @dist' G _ _ _.
  Proof.
    intros.
    unfold dist'. unfold_ops @Operations.Dist_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_ddj.
    ext A.
    rewrite <- (fun_fmap_fmap T).
    unfold_compose_in_compose.
    reassociate <- on right.
    reassociate -> near (fmap T (fmap G (ret T (A := A)))).
    change (fmap T (fmap G (ret T (A := A))))
      with ((fmap (T ○ G) (ret T (A := A)))).
    rewrite <- (natural (ϕ := @dist T _ G _ _ _)).
    unfold_ops @Fmap_compose.
    reassociate <- on right.
    rewrite (fun_fmap_fmap G).
    rewrite (mon_join_fmap_ret T).
    rewrite (fun_fmap_id G).
    reassociate -> on right.
    rewrite (dfun_dec_extract W T).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @Operations.Join_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_ddj.
    ext A.
    rewrite (dist_unit T).
    reassociate -> on right.
    rewrite (dfun_dec_extract W T).
    reflexivity.
  Qed.

  Goal decorateT = decorate'.
  Proof.
    unfold decorate'. unfold_ops @Operations.Decorate_Binddt.
    unfold binddt, binddt'.
    unfold_ops @ToKleisli.Binddt_ddj @Fmap_I.
    ext A.
    rewrite (dist_unit T).
    change (?f ∘ id) with f.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

End AlgebraicToKleisli.

Module KleisliToAlgebraic.

  Context
    `{binddtT : Binddt W T T}
    `{Monoid W}
    `{Return T}
    `{! Classes.Kleisli.DT.Monad.Monad W T}.

  #[local] Instance fmap' : Fmap T := Derived.Fmap_Binddt T.
  #[local] Instance dist' : Dist T := Operations.Dist_Binddt W T.
  #[local] Instance join' : Join T := Operations.Join_Binddt W T.
  #[local] Instance decorate' : Decorate W T := Operations.Decorate_Binddt W T.

  Definition binddt' : Binddt W T T := ToKleisli.Binddt_ddj T.

  Import Derived.

  Goal forall G `{Applicative G}, @binddtT G _ _ _ = @binddt' G _ _ _ .
  Proof.
    intros.
    unfold binddt'. unfold_ops @ToKleisli.Binddt_ddj.
    ext A B f.
    unfold fmap at 2, fmap', Fmap_Binddt.
    unfold dist, dist', Dist_Binddt.
    unfold dec, decorate', Decorate_Binddt.
    change_right (fmap G (join T) ∘ bindt T G (fmap G (ret T))
                    ∘ fmap T f ∘ bindd T (ret T)).
    reassociate -> on right.
    unfold fmap'.
    change (@Fmap_Binddt T W _ _) with (@Derived.Fmap_Bindd T _ W _).
    rewrite (Derived.fmap_bindd T).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (Derived.bindt_bindd T G).
    reassociate <- on right.
    Set Keyed Unification.
    rewrite (Kleisli.DT.Monad.Derived.bindt_fmap T G).
    Unset Keyed Unification.
    rewrite (ktm_bindt0 T); [| assumption].
    unfold join, join'; unfold_ops @Operations.Join_Binddt.
    unfold compose at 2.
    rewrite (kdtm_binddt2 W T _ _ _ (G1 := G) (G2 := fun A => A)).
    change_left (binddt T G f).
    fequal. now rewrite Mult_compose_identity1.
    change_right (id ∘ extract (prod W) ⋆dtm fmap G (ret T) ∘ f).
    rewrite (Derived.dtm_kleisli_37 W T).
    rewrite (@Traversable.Monad.Derived.kcompose_tm21 T _ _ _ G); [|assumption].
    rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

End KleisliToAlgebraic.
