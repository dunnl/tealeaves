From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Categorical.DecoratedTraversableFunctor.

Import Comonad.Notations.
Import Product.Notations.

#[local] Generalizable Variables G ϕ.

#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.
#[local] Arguments join T%function_scope {Join} (A)%type_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments extract (W)%function_scope {Extract} (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin} {A}%type_scope _.
#[local] Arguments mapd {E}%type_scope T%function_scope {Mapd}
  {A B}%type_scope _%function_scope _.
#[local] Arguments mapdt {E}%type_scope T%function_scope {Mapdt}
  G%function_scope {H H0 H1} {A B}%type_scope _%function_scope.

Module ToCategorical.

  Section operations.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Mapdt E T}.

    #[export] Instance Dist_Mapdt: ApplicativeDist T := fun G _ _ _ A => mapdt T G (extract (E ×) (G A)).
    #[export] Instance Decorate_Mapdt: Decorate E T := fun A => mapdt T (fun A => A) (@id ((E ×) A)).

  End operations.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

    Import DecoratedTraversableFunctor.DerivedOperations.
    #[local] Existing Instance MakeFull_DecoratedTraversableFunctor.

    #[local] Tactic Notation "unfold_everything" :=
         unfold_ops @Map_compose;
         unfold_ops @Decorate_Mapdt;
         unfold_ops @Map_Mapdt;
         unfold_ops @Dist_Mapdt.

    #[local] Tactic Notation "mapdt_to_mapd" :=
      change (mapdt T (fun A => A) (A := ?A) (B := ?B)) with (mapd T (A := A) (B := B)).

    #[local] Tactic Notation "mapd_to_map" :=
      change (mapd T (?f ∘ extract (prod E) ?A)) with (map T f).

      Lemma dec_dec : forall (A : Type),
        dec T ∘ dec T = map T (cojoin (E ×)) ∘ dec T (A := A).
    Proof.
      intros.
      unfold_everything.
      mapdt_to_mapd.
      mapd_to_map.
      rewrite (dfun_mapd2 (E := E) (T := T)).
      rewrite map_mapd.
      reflexivity.
    Qed.

    Lemma dec_extract : forall (A : Type),
        map T (extract (E ×) A) ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_everything.
      mapdt_to_mapd.
      mapd_to_map.
      rewrite map_mapd.
      rewrite (dfun_mapd1 (E := E) (T := T)).
      reflexivity.
    Qed.

    Lemma dec_natural : Natural (@dec E T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_everything.
        mapdt_to_mapd.
        mapd_to_map.
        rewrite map_mapd.
        rewrite mapd_map.
        reflexivity.
    Qed.

    #[export] Instance: Categorical.DecoratedFunctor.DecoratedFunctor E T :=
      {| dfun_dec_natural := dec_natural;
        dfun_dec_dec := dec_dec;
        dfun_dec_extract := dec_extract;
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
      mapdt_to_mapd.
      mapd_to_map.
      rewrite map_mapdt.
      rewrite mapdt_map.
      (* TODO Fix this *)
      change Map_Env with Map_prod.
      rewrite <- (natural (ϕ := extract (E ×))).
      reflexivity.
  Qed.

  Lemma dist_morph_T : forall `{ApplicativeMorphism G1 G2 ϕ},
    forall A : Type, dist T G2 ∘ map T (ϕ A) = ϕ (T A) ∘ dist T G1.
  Proof.
    intros.
    unfold_everything.
    mapdt_to_mapd.
    mapd_to_map.
    infer_applicative_instances.
    rewrite mapdt_map.
    (* TODO Fix this *)
    change Map_Env with Map_prod.
    rewrite <- (natural (ϕ := extract (E ×))).
    rewrite <- (kdtfun_morph (E := E) (T := T)).
    reflexivity.
  Qed.

  Lemma dist_unit_T : forall A : Type,
      dist T (fun A0 : Type => A0) = @id (T A).
  Proof.
    intros.
    unfold_everything.
    now rewrite (kdtfun_mapdt1 (E := E) (T := T)).
  Qed.

  Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Map G1) (H3 : Pure G1) (H4 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H6 : Map G2) (H7 : Pure G2) (H8 : Mult G2),
        Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = map G1 (dist T G2) ∘ dist T G1.
  Proof.
    intros.
    unfold_everything.
    rewrite (kdtfun_mapdt2 (E := E) (T := T)).
    change (extract (E ×) ?f) with (id ∘ extract (E ×) f) at 2.
    rewrite kc6_26.
    rewrite (fun_map_id (F := G1)).
    reflexivity.
  Qed.

  #[export] Instance: Categorical.TraversableFunctor.TraversableFunctor T :=
    {| dist_natural := dist_natural_T;
       dist_morph := @dist_morph_T;
       dist_unit := dist_unit_T;
       dist_linear := dist_linear_T;
    |}.

  Lemma dtfun_compat_T :
    forall (G : Type -> Type) (H2 : Map G) (H3 : Pure G) (H4 : Mult G),
      Applicative G -> forall A : Type,
        dist T G ∘ map T strength ∘ dec (A := G A) T = map G (dec T) ∘ dist T G.
  Proof.
    intros.

    unfold_everything.
    mapdt_to_mapd.
    rewrite mapdt_mapd.
    rewrite mapdt_mapd.
    rewrite mapd_mapdt.
    rewrite (fun_map_id (F := G)).
    rewrite kcom_cobind1.
    change (extract (prod E) (G (E * A))) with (id ∘ (extract (prod E) (G (E * A)))).
    rewrite (DerivedInstances.kc4_04).
    fequal. now ext [e ga].
  Qed.

  #[export] Instance: Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T :=
    {| dtfun_compat := dtfun_compat_T;
    |}.

End ToCategorical.
