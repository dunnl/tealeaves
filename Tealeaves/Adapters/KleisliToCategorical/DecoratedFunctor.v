From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Categorical.DecoratedFunctor.

Import Kleisli.Comonad.Notations.
Import Product.Notations.

#[local] Generalizable Variables T E A B C.

(** * Categorical Decorated Functors to Kleisli Decorated Functors *)
(******************************************************************************)

(** ** Derived <<mapd>> Operation *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Decorate_Mapd
    (E: Type) (T: Type -> Type) `{Mapd_ET: Mapd E T}:
  Decorate E T := fun A => mapd (@id ((E ×) A)).

End DerivedOperations.

(** ** Derived Decorated Functor Laws *)
(******************************************************************************)
Module DerivedInstances.

  Section properties.

    Context
      (E: Type)
      (T: Type -> Type)
      `{Kleisli.DecoratedFunctor.DecoratedFunctor E T}.

    Import KleisliToCategorical.DecoratedFunctor.DerivedOperations.
    Import Kleisli.DecoratedFunctor.DerivedOperations.
    Import Kleisli.DecoratedFunctor.DerivedInstances.

    Lemma cojoin_spec: forall (A: Type),
        cojoin (W := (E ×)) =
          id (A := E * (E * A)) ⋆1 id (A := E * A).
    Proof.
      intros.
      unfold kc1.
      reflexivity.
    Qed.

    Lemma dec_dec: forall (A: Type),
        dec T ∘ dec T = map (cojoin (W := (E ×))) ∘ dec T (A := A).
    Proof.
      intros.
      unfold_ops @Decorate_Mapd.
      rewrite kdf_mapd2.
      rewrite <- cojoin_spec.
      rewrite map_mapd.
      reflexivity.
    Qed.

    Lemma dec_extract: forall (A: Type),
        map (F := T) extract ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_ops @Decorate_Mapd.
      rewrite map_mapd.
      change (?f ∘ id) with f.
      rewrite kdf_mapd1.
      reflexivity.
    Qed.

    Lemma dec_natural: Natural (@dec E T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Map_compose.
        unfold_ops @Decorate_Mapd.
        rewrite map_mapd.
        rewrite mapd_map.
        reflexivity.
    Qed.

    #[export] Instance CategoricalDecoratedFunctor_Kleisli:
      Categorical.DecoratedFunctor.DecoratedFunctor E T :=
      {| dfun_dec_natural := dec_natural;
         dfun_dec_dec := dec_dec;
         dfun_dec_extract := dec_extract;
      |}.

  End properties.

End DerivedInstances.
