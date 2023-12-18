From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Categorical.DecoratedFunctor.

Import Product.Notations.

#[local] Generalizable Variables T E A B C.

#[export] Instance Decorate_Mapd
  (E : Type) (T : Type -> Type) `{Mapd E T}
  : Decorate E T := fun A => mapd (@id ((E ×) A)).

Import Kleisli.DecoratedFunctor.DerivedInstances.

Section properties.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Kleisli.DecoratedFunctor.DecoratedFunctor E T}.

  Lemma dec_dec : forall (A : Type),
      dec T ∘ dec T = map (cojoin (W := (E ×))) ∘ dec T (A := A).
  Proof.
    intros.
    (* Merge LHS *)
    unfold_ops @Decorate_Mapd.
    rewrite (dfun_mapd2 (E := E) (T := T)).
    (* Merge RHS *)
    unfold_ops @Map_Mapd.
    rewrite (dfun_mapd2 (E := E) (T := T)).
    rewrite DerivedInstances.kc4_04.
    reflexivity.
  Qed.

  Lemma dec_extract : forall (A : Type),
      map (F := T) extract ∘ dec T = @id (T A).
  Proof.
    intros.
    unfold_ops @Decorate_Mapd.
    unfold_ops @Map_Mapd.
    rewrite (dfun_mapd2 (E := E) (T := T)).
    rewrite DerivedInstances.kc4_04.
    change (?f ∘ id) with f.
    apply (dfun_mapd1 (E := E) (T := T)).
  Qed.

  Lemma dec_natural : Natural (@dec E T _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Map_compose.
      unfold_ops @Map_Mapd.
      unfold_ops @Decorate_Mapd.
      rewrite (dfun_mapd2 (E := E) (T := T)).
      rewrite (dfun_mapd2 (E := E) (T := T)).
    rewrite DerivedInstances.kc4_04.
    rewrite DerivedInstances.kc4_40.
    reflexivity.
  Qed.

  #[export] Instance: Categorical.DecoratedFunctor.DecoratedFunctor E T :=
    {| dfun_dec_natural := dec_natural;
       dfun_dec_dec := dec_dec;
       dfun_dec_extract := dec_extract;
    |}.

End properties.
