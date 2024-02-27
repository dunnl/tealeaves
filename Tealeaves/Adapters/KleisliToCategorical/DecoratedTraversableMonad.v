From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Categorical.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableMonad.

Import DecoratedTraversableMonad.Notations.
Import DecoratedMonad.Notations.
Import Product.Notations.
Import Monoid.Notations.
Import Functor.Notations.
Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables T A B C.

#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments extract (W)%function_scope {Extract} (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin} {A}%type_scope _.
#[local] Arguments mapd {E}%type_scope T%function_scope {Mapd}
  {A B}%type_scope _%function_scope _.
#[local] Arguments mapdt {E}%type_scope T%function_scope {Mapdt}
  G%function_scope {H H0 H1} {A B}%type_scope _%function_scope.
#[local] Arguments bindd {W}%type_scope {T} (U)%function_scope {Bindd} {A B}%type_scope _ _.
#[local] Arguments traverse T%function_scope {Traverse} G%function_scope
  {H H0 H1} {A B}%type_scope _%function_scope _.

(** * DTMs from Kleisli DTMs *)
(******************************************************************************)

Module ToCategorical.

  (** ** Operations *)
  (******************************************************************************)
  Section operations.
    Context
      (W : Type)
      (T : Type -> Type)
      `{Binddt W T T}
      `{Return T}.

    #[export] Instance Join_Binddt: Join T :=
      fun A => binddt (G := fun A => A) (B := A) (A := T A) (extract (W ×) (T A)).
    #[export] Instance Decorate_Binddt: Decorate W T :=
      fun A => binddt (G := fun A => A) (ret T (W * A)).
    #[export] Instance Dist_Binddt: ApplicativeDist T :=
      fun G _ _ _ A => binddt (T := T) (map G (ret T A) ∘ extract (W ×) (G A)).

  End operations.

  (** ** Laws *)
  (******************************************************************************)
  Section with_monad.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}.

    Existing Instances
      Map_Binddt.

    #[local] Tactic Notation "unfold_everything" :=
      unfold_ops @Map_compose;
      unfold_ops @Decorate_Binddt;
      unfold_ops @Map_Binddt;
      unfold_ops @Dist_Binddt;
      unfold_ops @Join_Binddt.

    #[local] Tactic Notation "binddt_to_bindd" :=
      rewrite <- bindd_to_binddt.

    #[local] Tactic Notation "mapdt_to_mapd" :=
      rewrite <- mapd_to_mapdt.

    #[local] Tactic Notation "mapd_to_map" :=
      rewrite <- map_to_mapd.

    (** *** Monad instance *)
    (******************************************************************************)
    Lemma ret_natural : Natural (@ret T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        rewrite map_to_binddt.
        rewrite (kdtm_binddt0 (G := fun A => A)).
        reflexivity.
    Qed.

    Lemma join_natural : Natural (@join T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_everything.
        binddt_to_bindd.
        unfold_compose_in_compose.
        rewrite map_bindd.
        binddt_to_bindd.
        rewrite bindd_map.
        rewrite <- (natural (Natural := Natural_extract_reader W)
                           (ϕ := @extract (W ×) _) (map T f)).
        reflexivity.
    Qed.

    Lemma join_ret : `(join T ∘ ret T (T A) = @id (T A)).
    Proof.
      intros.
      unfold_ops @Join_Binddt.
      unfold_compose_in_compose.
      rewrite (kdtm_binddt0 (G := fun A => A)).
      now rewrite bimonad_baton.
    Qed.

    Lemma join_map_ret : `(join T ∘ map T (ret T A) = @id (T A)).
    Proof.
      intros.
      unfold_everything.
      unfold_compose_in_compose.
      binddt_to_bindd.
      rewrite bindd_map.
      rewrite <- (natural (Natural := Natural_extract_reader W)
                         (ϕ := @extract (W ×) _)).
      unfold_ops @Map_I.
      rewrite kmond_bindd1.
      reflexivity.
    Qed.

    Lemma join_join :
      `(join T ∘ join T (A := T A) = join T ∘ map T (join T)).
    Proof.
      intros.
      unfold_everything.
      repeat binddt_to_bindd.
      unfold_compose_in_compose.
      (* Merge LHS *)
      rewrite (kmond_bindd2 (T := T)).
      (* Merge RHS *)
      rewrite (bindd_map).
      rewrite <- (natural (Natural := Natural_extract_reader W)
                         (ϕ := @extract (W ×) _)).
      unfold_ops @Map_I.
      unfold kc5.
      fequal.
      ext [w t].
      rewrite extract_preincr.
      reflexivity.
    Qed.

    #[local] Instance: Categorical.Monad.Monad T :=
      {| Monad.mon_ret_natural := ret_natural;
        mon_join_natural := join_natural;
        mon_join_ret := join_ret;
        mon_join_map_ret := join_map_ret;
        mon_join_join := join_join;
      |}.


    (** *** Decorated functor laws *)
    (******************************************************************************)
    Lemma dec_dec : forall (A : Type),
        dec T ∘ dec T = map T (cojoin (W ×)) ∘ dec T (A := A).
    Proof.
      intros.
      unfold_everything.
      do 2 binddt_to_bindd.
      unfold_compose_in_compose.
      (* Merge LHS *)
      rewrite (kmond_bindd2 (T := T)).
      (* Merge RHS *)
      rewrite map_to_bindd.
      rewrite (kmond_bindd2 (T := T)).
      fequal.
      rewrite kc5_05.
      change (ret T (W * A)) with (ret T (W * A) ∘ id) at 1.
      rewrite kc5_54.
      unfold kc4.
      rewrite (natural (ϕ := ret T)).
      reflexivity.
    Qed.

    Lemma dec_extract : forall (A : Type),
        map T (extract (W ×) A) ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_everything.
      binddt_to_bindd.
      unfold_ops @Map_I.
      rewrite map_bindd.
      rewrite (natural (ϕ := ret T)).
      unfold_ops @Map_I.
      rewrite kmond_bindd1.
      reflexivity.
    Qed.

    Lemma dec_natural : Natural (@dec W T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_everything.
        do 2 binddt_to_bindd.
        rewrite map_bindd.
        rewrite bindd_map.
        rewrite (natural (ϕ := ret T)).
        reflexivity.
    Qed.

    #[local] Instance: Categorical.DecoratedFunctor.DecoratedFunctor W T :=
      {| dfun_dec_natural := dec_natural;
        dfun_dec_dec := dec_dec;
        dfun_dec_extract := dec_extract;
      |}.

    (** *** Decorated monad laws *)
    (******************************************************************************)
    Lemma dmon_ret_ : forall (A : Type),
        dec T ∘ ret T A = ret T (W * A) ∘ pair Ƶ (B:=A).
    Proof.
      intros.
      unfold_everything.
      binddt_to_bindd.
      now rewrite (kmond_bindd0 (T := T)).
    Qed.

    Lemma dmon_join_ : forall (A : Type),
        dec T ∘ join T (A:=A) = join T ∘ map T (shift T) ∘ dec T ∘ map T (dec T).
    Proof.
      intros.
      unfold shift. unfold strength.
      unfold_everything.
      repeat binddt_to_bindd.
      unfold_compose_in_compose.
      (* Fuse LHS *)
      rewrite (kmond_bindd2 (T := T)) at 1.
      change (extract (W ×) (T A))
        with (id ∘ extract (W ×) (T A)) at 1.
      rewrite kc5_51.
      rewrite (fun_map_id (F := (W ×))).
      change (?f ∘ id) with f.
      (* Fuse RHS *)
      rewrite map_to_bindd.
      rewrite (kmond_bindd2 (T := T)).
      reassociate -> near (extract (W ×) _).
      rewrite (kc5_54).
      rewrite (kc4_id_l).
      rewrite (kmond_bindd2 (T := T)).
      change (ret T ((W × ) (T ((W × ) A))))
        with ((ret T ((W × ) (T ((W × ) A)))) ∘ id).
      rewrite (kc5_54).
      rewrite (kc4_04).
      change (?f ∘ id) with f.
      rewrite bindd_map.
      (* Now compare inner functions *)
      fequal.
      ext [w t].
      do 2 (unfold compose; cbn).
      compose near (bindd T (ret T (W * A)) t).
      rewrite (fun_map_map (F := T)).
      compose near t on right.
      rewrite map_bindd.
      rewrite (natural (ϕ := ret T)).
      reflexivity.
    Qed.

    #[local] Instance: Categorical.DecoratedMonad.DecoratedMonad W T :=
      {| dmon_ret := dmon_ret_;
        dmon_join := dmon_join_;
      |}.

    (** *** Traversable functor instance *)
    (******************************************************************************)
    Lemma dist_natural_T :
      forall (G : Type -> Type) (H2 : Map G) (H3 : Pure G) (H4 : Mult G)
        (Happ: Applicative G),
        Natural (@dist T _ G H2 H3 H4).
    Proof.
      intros. inversion Happ. constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_everything.
        rewrite map_binddt.
        rewrite binddt_map.
        (* LHS *)
        reassociate <- on left.
        rewrite (fun_map_map (F := G)).
        (* RHS *)
        reassociate -> on right.
        rewrite <- (natural (Natural := Natural_extract_reader W)
                           (ϕ := @extract (W ×) _)).
        unfold_ops Map_I.
        reassociate <- on right.
        rewrite (fun_map_map (F := G)).
        rewrite (natural (ϕ := ret T)).
        reflexivity.
    Qed.

    Lemma dist_morph_T : forall (G1 G2 : Type -> Type) (H2 : Map G1) (H4 : Mult G1) (H3 : Pure G1) (H5 : Map G2)
                           (H7 : Mult G2) (H6 : Pure G2) (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist T G2 ∘ map T (ϕ A) = ϕ (T A) ∘ dist T G1.
    Proof.
      introv morph; inversion morph; intros.
      unfold_ops @Dist_Binddt.
      rewrite binddt_map.
      rewrite (kdtm_morph G1 G2 (ϕ := ϕ)).
      reassociate -> on left.
      rewrite <- (natural (Natural := Natural_extract_reader W)
                         (ϕ := @extract (W ×) _)).
      unfold_ops Map_I.
      reassociate <- on left.
      rewrite (natural (ϕ := ϕ)).
      reflexivity.
    Qed.

    Lemma dist_unit_T : forall A : Type,
        dist T (fun A0 : Type => A0) = @id (T A).
    Proof.
      intros. unfold_ops @Dist_Binddt.
      apply (kdtm_binddt1).
    Qed.

    #[local] Instance TraversableMonadFull_Categorical_of_Kleisli: TraversableMonadFull T.
    Proof.
      constructor; typeclasses eauto.
    Qed.

    Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Map G1) (H3 : Pure G1) (H4 : Mult G1),
        Applicative G1 ->
        forall (G2 : Type -> Type) (H6 : Map G2) (H7 : Pure G2) (H8 : Mult G2),
          Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = map G1 (dist T G2) ∘ dist T G1.
    Proof.
      intros. unfold_ops @Dist_Binddt.
      rewrite (kdtm_binddt2); try typeclasses eauto.
      fequal.
      rewrite (kc7_33).
      rewrite (kc3_id_l').
      reflexivity.
    Qed.

    #[export] Instance: Categorical.TraversableFunctor.TraversableFunctor T :=
      {| dist_natural := dist_natural_T;
        dist_morph := dist_morph_T;
        dist_unit := dist_unit_T;
        dist_linear := dist_linear_T;
      |}.

    (** *** Traversable monad instance *)
    (******************************************************************************)
    Lemma trvmon_ret_T : forall (G : Type -> Type) (H3 : Map G) (H4 : Pure G) (H5 : Mult G),
        Applicative G -> forall A : Type, dist T G ∘ ret T (G A) = map G (ret T A).
    Proof.
      intros. unfold_ops @Dist_Binddt @Map_Binddt.
      rewrite (kdtm_binddt0).
      reflexivity.
    Qed.

    Lemma trvmon_join_T :
      forall (G : Type -> Type) (H3 : Map G)
        (H4 : Pure G) (H5 : Mult G)
        (Happ: Applicative G),
      forall A : Type, dist T G ∘ join T = map G (join T) ∘ dist T G ∘ map T (dist T G (A := A)).
    Proof.
      intros.
      unfold_ops @Dist_Binddt @Join_Binddt.
      repeat rewrite <- mapdt_to_binddt.
      repeat binddt_to_bindd.
      unfold_compose_in_compose.
      rewrite mapdt_bindd.
      unfold compose at 4.
      rewrite bindd_mapdt.
      rewrite binddt_map.
      fequal.
      ext [w a].
      unfold compose. cbn.
      change (fun a0 => a0) with (@id (T A)).
      unfold compose. cbn.
      inversion Happ.
      rewrite (fun_map_id (F := G)).
      rewrite extract_preincr.
      reflexivity.
    Qed.

    #[export] Instance: Categorical.TraversableMonad.TraversableMonad T :=
      {| trvmon_ret := trvmon_ret_T;
        trvmon_join := trvmon_join_T;
      |}.

    (** *** Decorated Traversable functor instance *)
    (******************************************************************************)
    Lemma dtfun_compat_T :
      forall (G : Type -> Type) (H2 : Map G) (H3 : Pure G) (H4 : Mult G)
        (Happ: Applicative G),
      forall A : Type,
          dist T G ∘ map T (strength) ∘ dec (A := G A) T = map G (dec T) ∘ dist T G.
    Proof.
      intros. unfold_ops @Dist_Binddt @Decorate_Binddt.
      change (ret T (W * G A)) with (ret T (W * G A) ∘ id).
      rewrite <- mapd_to_binddt.
      rewrite <- bindd_to_binddt.
      reassociate -> on left.
      rewrite map_mapd.
      do 2 rewrite <- mapdt_to_binddt.
      change (extract (prod W) ?A) with (id ∘ extract (prod W) A).
      rewrite (mapdt_mapd).
      rewrite (bindd_mapdt).
      rewrite mapdt_to_binddt.
      rewrite kc4_04.
      fequal.
      ext [w a].
      unfold compose. cbn.
      compose near a on left.
      inversion Happ.
      rewrite (fun_map_map (F := G)).
      reflexivity.
    Qed.

    #[export] Instance: Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor W T :=
      {| dtfun_compat := dtfun_compat_T;
      |}.

    (** *** Decorated Traversable monad instance *)
    (******************************************************************************)
    #[export] Instance: Categorical.DecoratedTraversableMonad.DecoratedTraversableMonad W T :=
      ltac:(constructor; typeclasses eauto).

  End with_monad.
End ToCategorical.
