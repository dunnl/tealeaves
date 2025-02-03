From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Categorical.DecoratedTraversableFunctor.

Import Comonad.Notations.
Import Product.Notations.

#[local] Generalizable Variables G ϕ.

(** * Categorical DTFs from Kleisli DTFs *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.
  Section operations.

    Context
      (E: Type)
      (T: Type -> Type)
      `{Mapdt E T}.

    #[export] Instance Dist_Mapdt: ApplicativeDist T :=
      fun G _ _ _ A =>
        mapdt (T := T) (G := G) (extract (W := (E ×)) (A := G A)).

    #[export] Instance Decorate_Mapdt: Decorate E T :=
      fun A => mapdt (G := fun A => A) (@id (E * A)).

  End operations.
End DerivedOperations.

(** ** Derived Instances *)
(**********************************************************************)
Module DerivedInstances.

  (* Alectryon doesn't like this
     Import KleisliToCategorical.DecoratedTraversableFunctor.DerivedOperations.
   *)
  Import DerivedOperations.
  Import Kleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import Kleisli.DecoratedTraversableFunctor.DerivedInstances.

  Section instances.

    Context
      (E: Type)
      (T: Type -> Type)
      `{Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

    Lemma dec_dec: forall (A: Type),
        dec T ∘ dec T =
          map (F := T) (cojoin (W := (E ×))) ∘ dec T (A := A).
    Proof.
      intros.
      unfold_ops @Decorate_Mapdt.
      rewrite <- mapd_to_mapdt.
      rewrite <- mapd_to_mapdt.
      rewrite mapd_mapd.
      rewrite map_mapd.
      reflexivity.
    Qed.

    Lemma dec_extract: forall (A: Type),
        map (F := T) (extract (W := (E ×))) ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_ops @Decorate_Mapdt.
      rewrite <- mapd_to_mapdt.
      rewrite map_mapd.
      change (?f ∘ id) with f.
      rewrite mapd_id.
      reflexivity.
    Qed.

    Lemma dec_natural: Natural (@dec E T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Map_compose.
        unfold_ops @Decorate_Mapdt.
        rewrite <- mapd_to_mapdt.
        rewrite <- mapd_to_mapdt.
        rewrite map_mapd.
        rewrite mapd_map.
        reflexivity.
    Qed.

    #[export] Instance DecoratedFunctor_Categorical_Kleisli:
      Categorical.DecoratedFunctor.DecoratedFunctor E T :=
      {| dfun_dec_natural := dec_natural;
         dfun_dec_dec := dec_dec;
         dfun_dec_extract := dec_extract;
      |}.

    (** *** Traversable functor instance *)
    (******************************************************************)
    Lemma dist_natural_T:
      forall (G: Type -> Type) (H2: Map G) (H3: Pure G) (H4: Mult G),
        Applicative G -> Natural (@dist T _ G H2 H3 H4).
    Proof.
      intros. constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Map_compose.
        unfold_ops @Dist_Mapdt.
        rewrite map_mapdt.
        rewrite mapdt_map.
        rewrite <- (natural (ϕ := fun A => extract (A := A))).
        reflexivity.
    Qed.

    Lemma dist_morph_T: forall `{ApplicativeMorphism G1 G2 ϕ},
      forall (A: Type),
        dist T G2 ∘ map (F := T) (ϕ A) = ϕ (T A) ∘ dist T G1.
    Proof.
      intros.
      unfold_ops @Map_compose.
      unfold_ops @Dist_Mapdt.
      infer_applicative_instances.
      rewrite mapdt_map.
      rewrite <- (natural (ϕ := fun A => extract (W := (E ×)) (A := A))).
      rewrite (kdtf_morph (E := E) (T := T)).
      reflexivity.
    Qed.

    Lemma dist_unit_T: forall (A: Type),
        dist T (fun A0: Type => A0) = @id (T A).
    Proof.
      intros.
      unfold_ops @Dist_Mapdt.
      now rewrite (kdtf_mapdt1 (E := E) (T := T)).
    Qed.

    (* TODO Typeset this better *)
    Lemma dist_linear_T:
      forall (G1: Type -> Type)
        (H2: Map G1) (H3: Pure G1) (H4: Mult G1),
        Applicative G1 ->
        forall (G2: Type -> Type)
          (H6: Map G2) (H7: Pure G2) (H8: Mult G2),
          Applicative G2 -> forall (A: Type),
            dist T (G1 ∘ G2) (A := A) =
              map (F := G1) (dist T G2) ∘ dist T G1.
    Proof.
      intros.
      unfold_ops @Dist_Mapdt.
      rewrite (kdtf_mapdt2 (E := E) (T := T)).
      change (extract (W := prod E) (A := G2 A)) with
        (id ∘ extract (W := prod E) (A := G2 A)).
      rewrite kc3_23.
      rewrite (fun_map_id (F := G1)).
      reflexivity.
    Qed.

    #[export] Instance TraversableFunctor_Categorical_DecoratedTraversableFunctor_Kleisli
     : Categorical.TraversableFunctor.TraversableFunctor T :=
      {| dist_natural := dist_natural_T;
         dist_morph := @dist_morph_T;
         dist_unit := dist_unit_T;
         dist_linear := dist_linear_T;
      |}.

    Lemma dtfun_compat_T:
      forall (G: Type -> Type) (H2: Map G) (H3: Pure G) (H4: Mult G),
        Applicative G -> forall (A: Type),
          dist T G ∘ map (F := T) strength ∘ dec (A := G A) T =
            map (F := G) (dec T) ∘ dist T G.
    Proof.
      intros.
      unfold_ops @Dist_Mapdt.
      unfold_ops @Decorate_Mapdt.
      rewrite <- mapd_to_mapdt.
      reassociate -> on left.
      rewrite map_mapd.
      rewrite <- mapd_to_mapdt.
      rewrite mapdt_mapd.
      rewrite mapd_mapdt.
      rewrite (fun_map_id (F := G)).
      rewrite kcom_cobind1.
      change (extract (W := prod E) (A := G (E * A))) with
        (id ∘ (extract (W := prod E) (A := G (E * A)))).
      rewrite kc1_01.
      reflexivity.
    Qed.


    (** ** Typeclass Instance *)
    (******************************************************************)
    #[export] Instance
      DecoratedTraversableFunctor_Categorical_Kleisli:
      Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T :=
      {| dtfun_compat := dtfun_compat_T;
      |}.

  End instances.
End DerivedInstances.
