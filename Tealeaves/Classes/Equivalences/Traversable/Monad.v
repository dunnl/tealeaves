From Tealeaves.Classes Require Export
  Traversable.Monad
  Kleisli.Traversable.Monad
  Kleisli.Traversable.Functor
  Kleisli.Monad.

Import Kleisli.Monad.Notations.

#[local] Generalizable Variables A B C.

About Traversable.Monad.Derived.

(** * Traversable Monads: Kleisli to Algebraic *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Module Operations.
  Section with_kleisli.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Return T}
      `{Bindt T T}.

    #[export] Instance Dist_Bindt: Dist T := fun G _ _ _ A => bindt T G (fmap G (ret T) ∘ @id (G A)).
    #[export] Instance Join_Bindt: Join T := fun A => bindt T (fun A => A) (@id (T A)).

  End with_kleisli.
End Operations.

Import Operations.

(** ** Instances *)
(******************************************************************************)
Module Instances.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  Import Kleisli.Traversable.Monad.Derived.

  (** *** Traversable functor instance *)
  (******************************************************************************)
  Lemma dist_natural_T : forall (G : Type -> Type) (H2 : Fmap G) (H3 : Pure G) (H4 : Mult G),
      Applicative G -> Natural (@dist T _ G H2 H3 H4).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Fmap_compose @Dist_Bindt @Fmap_Bindt.
      change (bindt T ?G (fmap ?G (ret T) ∘ ?rest)) with (traverse T G rest).
      change (bindt T (fun A0 : Type => A0) (ret T ∘ f)) with (fmap T f).
      change (bindt T (fun A0 : Type => A0) (ret T ∘ fmap G f)) with (fmap (T ∘ G) f).
      rewrite (Derived.fmap_traverse T); auto.
      unfold_ops @Fmap_compose.
      rewrite (Derived.traverse_fmap T); auto.
  Qed.

  Lemma dist_morph_T : forall (G1 G2 : Type -> Type) (H2 : Fmap G1) (H3 : Pure G1) (H4 : Mult G1) (H5 : Fmap G2)
                         (H6 : Pure G2) (H7 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist T G2 ∘ fmap T (ϕ A) = ϕ (T A) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Bindt @Fmap_Bindt.
    change (bindt T ?G (fmap ?G (ret T) ∘ ?rest)) with (traverse T G rest).
    change (bindt T (fun A0 : Type => A0) (ret T ∘ ϕ A)) with (fmap T (ϕ A)).
    inversion H8; rewrite (Derived.traverse_fmap T); auto.
    change (id ∘ ?g) with (g ∘ id).
    now rewrite (trf_traverse_morphism T).
  Qed.

  Lemma dist_unit_T : forall A : Type,
      dist T (fun A0 : Type => A0) = @id (T A).
  Proof.
    intros. unfold_ops @Dist_Bindt.
    change (bindt T ?id (fmap ?id ?g ∘ id)) with (bindt T (fun A => A) (ret T (A := A))).
    now rewrite (ktm_bindt1 T).
  Qed.

  Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Fmap G1) (H3 : Pure G1) (H4 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H6 : Fmap G2) (H7 : Pure G2) (H8 : Mult G2),
        Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = fmap G1 (dist T G2) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Bindt.
    change (bindt T ?G (fmap ?G (ret T) ∘ ?rest)) with (traverse T G rest).
    rewrite (trf_traverse_traverse T G1); try typeclasses eauto.
    rewrite (fun_fmap_id G1).
    reflexivity.
  Qed.

  #[export] Instance: Classes.Traversable.Functor.TraversableFunctor T :=
    {| dist_natural := dist_natural_T;
       dist_morph := dist_morph_T;
       dist_unit := dist_unit_T;
       dist_linear := dist_linear_T;
    |}.

  (** *** Monad instance *)
  (******************************************************************************)
  #[export] Instance: Natural (@ret T _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Fmap_Bindt.
      rewrite (ktm_bindt0 T _ _ (G := fun A => A)).
      reflexivity.
  Qed.

  #[export] Instance: Natural (@join T _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Fmap_compose @Join_Bindt.
      change (bindt T (fun A => A) ?g) with (bind T g).
      unfold_compose_in_compose.
      rewrite (Derived.fmap_bind T).
      rewrite (Derived.bind_fmap T).
      reflexivity.
  Qed.

  Lemma mon_join_ret_T : forall A : Type, join T ∘ ret T = @id (T A).
  Proof.
    intros. unfold_ops @Join_Bindt.
    unfold_compose_in_compose.
    change_left (bind (B := A) T id ∘ ret T).
    now rewrite (kmon_bind0 T).
  Qed.

  Lemma mon_join_fmap_ret_T : forall A : Type, join T ∘ fmap T (ret T) = @id (T A).
  Proof.
    intros.
    unfold_ops @Join_Bindt @Fmap_Bindt.
    change_left (bind T (@id (T A)) ∘ fmap T (ret T)).
    rewrite (bind_fmap T).
    change (id ∘ ?g) with g.
    now rewrite (kmon_bind1 T).
  Qed.

  Lemma mon_join_join_T : forall A : Type, join (A := A) T ∘ join T = join T ∘ fmap T (join T).
  Proof.
    intros.
    unfold_ops @Join_Bindt @Fmap_Bindt.
    change (bindt T (fun A => A) ?g) with (bind T g).
    change (bindt T (fun A => A) ?g) with (bind T g).
    unfold_compose_in_compose.
    rewrite (kmon_bind2 T).
    rewrite (kmon_bind2 T).
    rewrite (ToFunctor.kcompose10 T).
    reflexivity.
  Qed.

  #[export] Instance: Classes.Monad.Monad T :=
    {| mon_join_ret := mon_join_ret_T;
       mon_join_fmap_ret := mon_join_fmap_ret_T;
       mon_join_join := mon_join_join_T;
    |}.

  (** *** Traversable monad instance *)
  (******************************************************************************)
  Lemma trvmon_ret_T : forall (G : Type -> Type) (H3 : Fmap G) (H4 : Pure G) (H5 : Mult G),
      Applicative G -> forall A : Type, dist T G ∘ ret T (A := G A) = fmap G (ret T).
  Proof.
    intros. unfold_ops @Dist_Bindt.
    rewrite (ktm_bindt0 T); auto.
  Qed.

  Lemma trvmon_join_T : forall (G : Type -> Type) (H3 : Fmap G) (H4 : Pure G) (H5 : Mult G),
      Applicative G -> forall A : Type, dist T G ∘ join T (A := G A) = fmap G (join T) ∘ dist (T ∘ T) G.
  Proof.
    intros. unfold_ops @Dist_compose @Dist_Bindt @Join_Bindt.
    change_left (bindt (B := A) T G (fmap G (ret T) ∘ id) ∘ bind T id).
    rewrite (bindt_bind T); auto.
    rewrite (bindt_fmap T); auto.
    change (?g ∘ id) with g.
    change(bindt T (fun A => A) ?g) with (bind T g).
    unfold_compose_in_compose; unfold compose at 4.
    rewrite (bind_bindt T G).
    reassociate <-. rewrite (fun_fmap_fmap G).
    rewrite (kmon_bind0 T).
    rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

  #[export] Instance: Traversable.Monad.TraversableMonad T :=
    {| trvmon_ret := trvmon_ret_T;
       trvmon_join := trvmon_join_T;
    |}.

End Instances.

#[local] Generalizable Variables T.

Module AlgebraicToKleisli.

  Context
    `{fmapT : Fmap T}
    `{distT : Dist T}
    `{joinT : Join T}
    `{Return T}
    `{! Classes.Traversable.Monad.TraversableMonad T}.

  #[local] Instance bindt' : Bindt T T := ToKleisli.Bindt_distjoin T.

  Definition fmap' : Fmap T := Derived.Fmap_Bindt T.
  Definition dist' : Dist T := Dist_Bindt T.
  Definition join' : Join T := Join_Bindt T.

  Goal fmapT = fmap'.
  Proof.
    unfold fmap'. unfold_ops @Derived.Fmap_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_distjoin.
    ext A B f.
    unfold_ops @Fmap_I.
    rewrite (dist_unit T).
    change (?g ∘ id) with g.
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on right.
    now rewrite (mon_join_fmap_ret T).
  Qed.

  Goal forall G `{Applicative G}, @distT G _ _ _ = @dist' _ _ _ _.
  Proof.
    intros.
    unfold dist'. unfold_ops @Operations.Dist_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_distjoin.
    ext A.
    change (?g ∘ id) with g.
    change (fmap T (fmap G (ret T)))
      with (fmap (T ∘ G) (ret (A := A) T)).
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite <- (natural (Natural := dist_natural T) (ϕ := @dist T _ G _ _ _)).
    reassociate <- on right.
    unfold_ops @Fmap_compose.
    rewrite (fun_fmap_fmap G).
    rewrite (mon_join_fmap_ret T).
    rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @Operations.Join_Bindt.
    unfold bindt, bindt'.
    unfold_ops @ToKleisli.Bindt_distjoin.
    ext A. rewrite (fun_fmap_id T).
    unfold_ops @Fmap_I.
    rewrite (dist_unit T).
    reflexivity.
  Qed.

End AlgebraicToKleisli.

Module KleisliToAlgebraic.

  Context
    `{bindtT : Bindt T T}
    `{Return T}
    `{! Classes.Kleisli.Traversable.Monad.Monad T}.

  #[local] Instance fmap' : Fmap T := Derived.Fmap_Bindt T.
  #[local] Instance dist' : Dist T := Dist_Bindt T.
  #[local] Instance join' : Join T := Join_Bindt T.

  Definition bindt' : Bindt T T := ToKleisli.Bindt_distjoin T.

  Goal forall A B G `{Applicative G}, @bindtT G A B _ _ _ = @bindt' G A B _ _ _.
  Proof.
    intros. ext f.
    unfold bindt'. unfold_ops @ToKleisli.Bindt_distjoin.
    unfold join, join', dist, dist', fmap at 2, fmap'.
    unfold_ops @Operations.Join_Bindt.
    unfold_ops @Operations.Dist_Bindt.
    unfold_ops @Derived.Fmap_Bindt.
    change (?g ∘ id) with g.
    reassociate -> on right.
    change (bindt T G (fmap G (ret T (A := T B))))
      with (fmap (fun A => A) (bindt T G (fmap G (ret T (A := T B))))).
    unfold_compose_in_compose.
    rewrite (ktm_bindt2 T _ _ _ (G2 := G) (G1 := fun A => A)).
    unfold kcompose_tm.
        unfold_ops @Fmap_I.
    reassociate <- on right.
    unfold_compose_in_compose.
    rewrite (ktm_bindt0 T (G (T B)) (T B) (fmap G (ret T (A := T B))) (G := G)).
    change ((fun A0 : Type => A0) ∘ G) with G.
    rewrite (Mult_compose_identity2).
    unfold_ops @Fmap_compose @Pure_compose.
    unfold_ops @Pure_I @Mult_compose @Mult_I.
    Set Keyed Unification.
    unfold id at 3.
    change ((fun (A0 : Type) (a : A0) => @pure G H2 A0 a)) with H2.
    change (@mult G H3) with H3.
    rewrite (ktm_bindt2 T A _ _ (G1 := G) (G2 := fun A => A)).
    Unset Keyed Unification.
    unfold kcompose_tm.
    reassociate <- on right.
    rewrite (fun_fmap_fmap G).
    rewrite (ktm_bindt0 T _ _ (G := fun A => A)).
    rewrite (fun_fmap_id G).
    fequal. rewrite Mult_compose_identity1.
    reflexivity.
  Qed.

End KleisliToAlgebraic.
