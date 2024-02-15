From Tealeaves Require Export
  Classes.Categorical.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableMonad.

Import DecoratedTraversableMonad.Notations.
Import DecoratedMonad.Notations.
Import Product.Notations.
Import Monoid.Notations.
Import Functor.Notations.
Import Comonad.Notations.

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
      fun A => binddt (fun A => A) (B := A) (A := T A) (extract (W ×) (T A)).
    #[export] Instance Decorate_Binddt: Decorate W T := fun A => binddt T (fun A => A) (ret T (W * A)).
    #[export] Instance Dist_Binddt: ApplicativeDist T := fun G _ _ _ A => binddt T G (map G (ret T A) ∘ extract (W ×) (G A)).

  End operations.

  (** ** Laws *)
  (******************************************************************************)
  Section with_monad.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

    Existing Instances
      Map_Binddt.

    #[local] Tactic Notation "unfold_everything" :=
      unfold_ops @Map_compose;
      unfold_ops @Decorate_Binddt;
      unfold_ops @Map_Binddt;
      unfold_ops @Dist_Binddt;
      unfold_ops @Join_Binddt.

    #[local] Tactic Notation "binddt_to_bindd" :=
      change (binddt T (fun A0 : Type => A0) ?f) with (bindd T (U := T) f).

    #[local] Tactic Notation "mapdt_to_mapd" :=
      change (mapdt T (fun A => A) (A := ?A) (B := ?B)) with (mapd T (A := A) (B := B)).

    #[local] Tactic Notation "mapd_to_map" :=
      change (mapd T (?f ∘ extract (prod W) ?A)) with (map T f).

    (** *** Monad instance *)
    (******************************************************************************)
    Lemma ret_natural : Natural (@ret T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Map_Binddt.
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
        rewrite (DerivedInstances.bindd_bindd W T). (* left *)
        rewrite (DerivedInstances.kc5_05).
        rewrite (DerivedInstances.bindd_bindd W T). (* right *)
        rewrite (DerivedInstances.kc5_50).
        (* TODO Next two steps should be lemmaized *)
        rewrite map_to_cobind.
        rewrite kcom_cobind0.
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
      rewrite (bindd_bindd W T).
      rewrite (DecoratedMonad.DerivedInstances.kc5_50).
      (* TODO lemma *)
      rewrite map_to_cobind.
      rewrite kcom_cobind0.
      rewrite (kmond_bindd1 (T := T)).
      reflexivity.
    Qed.

    Lemma join_join :
      `(join T ∘ join T (A := T A) = join T ∘ map T (join T)).
    Proof.
      intros.
      unfold_everything.
      binddt_to_bindd.
      unfold_compose_in_compose.
      (* Merge LHS *)
      rewrite (kmond_bindd2 (T := T)).
      (* Merge RHS *)
      rewrite (kmond_bindd2 (T := T)).
      rewrite (DecoratedMonad.DerivedInstances.kc5_50).
      rewrite map_to_cobind.
      rewrite kcom_cobind0.
      fequal.
      unfold kc5.
      cbn.
      ext [w t].
      setoid_rewrite extract_preincr.
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
      binddt_to_bindd.
      unfold_compose_in_compose.
      (* Merge LHS *)
      rewrite (kmond_bindd2 (T := T)).
      (* Merge RHS *)
      rewrite (kmond_bindd2 (T := T)).
      fequal.
      rewrite (DecoratedMonad.DerivedInstances.kc5_05).
      change (ret T (W * A)) with (ret T (W * A) ∘ id) at 1.
      rewrite (kc5_54).
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
      rewrite (kmond_bindd2 (T := T)).
      change (ret T (W * A)) with (ret T (W * A) ∘ @id (W * A)).
      rewrite (DecoratedMonad.DerivedInstances.kc5_05).
      change (?f ∘ id) with f.
      rewrite (natural (ϕ := ret T)).
      apply (kmond_bindd1 (T := T)).
    Qed.

    Lemma dec_natural : Natural (@dec W T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_everything.
        binddt_to_bindd.
        rewrite (kmond_bindd2 (T := T)).
        rewrite (kmond_bindd2 (T := T)).
        fequal.
        rewrite (DecoratedMonad.DerivedInstances.kc5_05).
        rewrite (DecoratedMonad.DerivedInstances.kc5_50).
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
      binddt_to_bindd.
      unfold_compose_in_compose.
      (* Fuse LHS *)
      rewrite (kmond_bindd2 (T := T)) at 1.
      change (extract (W ×) (T A))
        with (id ∘ extract (W ×) (T A)) at 1.
      rewrite (DecoratedMonad.DerivedInstances.kc5_51).
      rewrite (fun_map_id (F := (W ×))).
      change (?f ∘ id) with f.
      (* Fuse RHS *)
      rewrite (kmond_bindd2 (T := T)).
      reassociate -> near (extract (W ×) _).
      rewrite (DecoratedMonad.DerivedInstances.kc5_54).
      rewrite (DerivedInstances.kc4_id_l).
      rewrite (kmond_bindd2 (T := T)).
      change (ret T ((W × ) (T ((W × ) A))))
        with ((ret T ((W × ) (T ((W × ) A)))) ∘ id).
      rewrite (DecoratedMonad.DerivedInstances.kc5_54).
      rewrite (DerivedInstances.kc4_04).
      change (?f ∘ id) with f.
      rewrite (kmond_bindd2 (T := T)).
      rewrite (DecoratedMonad.DerivedInstances.kc5_54).
      rewrite (DerivedInstances.kc4_40).
      (* Now compare inner functions *)
      fequal.
      ext [w t].
      do 2 (unfold compose; cbn).
      compose near t on right.
      binddt_to_bindd.
      rewrite (kmond_bindd2).
      change (ret T ((W × ) A)) with (ret T ((W × ) A) ∘ id).
      rewrite (DecoratedMonad.DerivedInstances.kc5_54).
      compose near t on right.
      rewrite (kmond_bindd2).
      (* Now compare inner functions again *)
      fequal.
      ext [w' a].
      unfold preincr; unfold compose; cbn.
      unfold kc4; unfold_ops @Cobind_env.
      unfold compose; cbn.
      change (id ?x) with x.
      compose near (w, (w', a)).
      rewrite (kmond_bindd0).
      reflexivity.
    Qed.

    #[local] Instance: Categorical.DecoratedMonad.DecoratedMonad W T :=
      {| dmon_ret := dmon_ret_;
        dmon_join := dmon_join_;
      |}.

    (** *** Traversable functor instance *)
    (******************************************************************************)
    Lemma dist_natural_T : forall (G : Type -> Type) (H2 : Map G) (H3 : Pure G) (H4 : Mult G),
        Applicative G -> Natural (@dist T _ G H2 H3 H4).
    Proof.
      intros. constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_everything.
        binddt_to_bindd.
        (* LHS *)
        rewrite (bindd_binddt W T).
        (* RHS *)
        rewrite (binddt_bindd W T).
        fequal. ext [w ga]. compose near (w, ga).
        (* LHS *)
        rewrite (extract_preincr2).
        reassociate <-.
        rewrite (fun_map_map (F := G)).
        rewrite (kmond_bindd0).
        reassociate -> near (ret (W ×) A).
        rewrite (bimonad_baton (W := W)).
        (* RHS *)
        do 2 reassociate <- on right.
        rewrite (kdtm_binddt0).
        rewrite (extract_preincr2).
        reassociate -> near (ret (W ×) (G B)).
        rewrite (bimonad_baton (W := W)).
        change (?f ∘ id) with f.
        rewrite (fun_map_map (F := G)).
        reflexivity.
    Qed.

    Lemma dist_morph_T : forall (G1 G2 : Type -> Type) (H2 : Map G1) (H3 : Pure G1) (H4 : Mult G1) (H5 : Map G2)
                           (H6 : Pure G2) (H7 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist T G2 ∘ map T (ϕ A) = ϕ (T A) ∘ dist T G1.
    Proof.
      introv morph; inversion morph; intros.
      change (mapdt T G2 (extract (prod W) _) ∘ map T (ϕ A)
              = ϕ (T A) ∘ traverse T G1 (@id (G1 A))).
      rewrite (DerivedInstances.mapdt_map T G2).
      rewrite (trf_traverse_morphism (T := T)).
      change (Map_Env) with (Map_prod) in *.
      rewrite <- (natural (ϕ := @extract (W ×) _)).
      reflexivity.
    Qed.

    Lemma dist_unit_T : forall A : Type,
        dist T (fun A0 : Type => A0) = @id (T A).
    Proof.
      intros. unfold_ops @Dist_Binddt.
      apply (kdtm_binddt1 W T).
    Qed.

    #[local] Instance TODO_clean_me_up : TraversableMonadFull T.
    Proof.
      constructor; [
          typeclasses eauto |
          reflexivity |
          reflexivity |
          reflexivity
        ].
    Qed.

    Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Map G1) (H3 : Pure G1) (H4 : Mult G1),
        Applicative G1 ->
        forall (G2 : Type -> Type) (H6 : Map G2) (H7 : Pure G2) (H8 : Mult G2),
          Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = map G1 (dist T G2) ∘ dist T G1.
    Proof.
      intros. unfold_ops @Dist_Binddt.
      rewrite (kdtm_binddt2 W T); try typeclasses eauto.
      fequal.
      rewrite (kc7_33 W T).
      rewrite (kc3_id_l' T G1 G2).
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
      rewrite (kdtm_binddt0 W T); [|assumption].
      ext a. reflexivity.
    Qed.

    Lemma trvmon_join_T : forall (G : Type -> Type) (H3 : Map G) (H4 : Pure G) (H5 : Mult G),
        Applicative G -> forall A : Type, dist T G ∘ join T = map G (join T) ∘ dist T G ∘ map T (dist T G (A := A)).
    Proof.
      intros.
      unfold_ops @Dist_Binddt @Map_Binddt @Join_Binddt.
      change_left (bindt G _ _ (map G (ret T _)) ∘ bind T (@id (T (G A)))).
      change_right (map G (bind T (@id (T A)))
                      ∘ (bindt G _ _ (map G (ret T _))
                           ∘ bind T (ret T _ ∘ bindt G _ _ (map G (ret T _))))).
      rewrite (bindt_bind W T G).
      rewrite (bindt_bind W T G).
      reassociate <-. rewrite (ktm_bindt0); [|typeclasses eauto].
      rewrite (bind_bindt W T G).
      reassociate <- on right.
      rewrite (fun_map_map (F := G)).
      rewrite (kmon_bind0).
      rewrite (fun_map_id (F := G)).
      reflexivity.
    Qed.

    #[export] Instance: Categorical.TraversableMonad.TraversableMonad T :=
      {| trvmon_ret := trvmon_ret_T;
        trvmon_join := trvmon_join_T;
      |}.

    (** *** Decorated Traversable functor instance *)
    (******************************************************************************)
    Lemma dtfun_compat_T : forall (G : Type -> Type) (H2 : Map G) (H3 : Pure G) (H4 : Mult G),
        Applicative G -> forall A : Type,
          dist T G ∘ map T (strength G) ∘ dec (A := G A) T = map G (dec T) ∘ dist T G.
    Proof.
      intros. unfold_ops @Dist_Binddt @Map_Binddt @Decorate_Binddt.
      change (mapdt T G (extract (prod W) _) ∘ mapd T (strength G ∘ extract (prod W) _) ∘ mapd T (@id (W * G A)) =
                map G (mapd T id) ∘ mapdt T G (extract (prod W) _)).
      rewrite (mapdt_mapd W T G).
      rewrite (mapdt_mapd W T G).
      rewrite (mapd_mapdt W T G).
      rewrite (kcom_cobind1).
      rewrite (fun_map_id (F := G)).
      fequal. ext [w a].
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
