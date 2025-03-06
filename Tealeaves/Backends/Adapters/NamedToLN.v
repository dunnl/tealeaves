From Tealeaves Require Import
  Backends.LN
  Backends.Named.Common
  Backends.Common.Names
  Backends.Named.FV
  Backends.Named.Alpha
  Functors.Option
  Theory.DecoratedTraversableFunctorPoly
  CategoricalToKleisli.DecoratedFunctorPoly
  CategoricalToKleisli.TraversableFunctor
  CategoricalToKleisli.DecoratedTraversableFunctorPoly
  Adapters.PolyToMono.Kleisli.DecoratedFunctor.

Import Subset.Notations.
Import Classes.Categorical.DecoratedFunctorPoly.
Import DecoratedTraversableMonad.UsefulInstances.
Import List.ListNotations.

#[local] Generalizable Variables W T U.
#[local] Open Scope list_scope.

From Tealeaves Require
  Adapters.MonoidHom.DecoratedTraversableMonad
  Adapters.PolyToMono.Kleisli.DecoratedFunctor
  Adapters.PolyToMono.Kleisli.DecoratedTraversableFunctor
  Adapters.PolyToMono.Kleisli.DecoratedTraversableMonad
  Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly.

Section DTM.

  Import CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedInstances.

  Context
    (T: Type -> Type -> Type)
    `{Categorical.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly T}.

  #[export] Instance Binddt_MONO_NAME:
    Binddt (list name) (T name) (T name).
  Proof.
    apply PolyToMono.Kleisli.DecoratedTraversableMonad.Binddt_of_Binddtp.
  Defined.

  #[export] Instance Binddt_MONO:
    Binddt nat (T unit) (T unit).
  assert (Binddt (list unit) (T unit) (T unit)).
  apply PolyToMono.Kleisli.DecoratedTraversableMonad.Binddt_of_Binddtp.
  apply (MonoidHom.DecoratedTraversableMonad.Binddt_Morphism (@length unit)).
  Defined.

  Import PolyToMono.Kleisli.DecoratedTraversableMonad.

  #[export] Instance DTM_MONO:
    DecoratedTraversableMonad nat (T unit).
  Proof.
    assert (DecoratedTraversableMonad (list unit) (T unit)).
    { apply
        PolyToMono.Kleisli.DecoratedTraversableMonad.DTM_of_DTMP.
    }
    apply MonoidHom.DecoratedTraversableMonad.DTM_of_DTM.
    { constructor; try typeclasses eauto.
      reflexivity. intros.
      unfold monoid_op, Monoid_op_list.
      induction a1.
      reflexivity.
      cbn. now  rewrite IHa1.
    }
  Qed.

End DTM.





(** * Local Translations *)
(**********************************************************************)
Section with_DTM.

  Context
    (T: Type -> Type -> Type)
    `{Categorical.DecoratedFunctorPoly.DecoratedFunctorPoly T}.

  Import Kleisli.DecoratedFunctorPoly.
  Import CategoricalToKleisli.DecoratedFunctorPoly.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.

  (** ** Named to Locally Nameless *)
  (********************************************************************)
  Definition binding_to_ln: Binding -> LN :=
    fun b =>
      match b with
      | Bound prefix var postfix =>
          Bd (length prefix)
      | Unbound context var =>
          Fr var
      end.

  Definition name_to_ln:
    list name * name -> LN.
  Proof.
    intros [ctx x].
    exact (binding_to_ln (get_binding ctx x)).
  Defined.

  (** ** Locally Nameless to Named *)
  (********************************************************************)
  Definition INDEX_EXCEEDS_CONTEXT: nat := 1337.

  Fixpoint ix_new_name_core (avoid: list name) (n: nat): name :=
    match n with
    | 0 => fresh avoid
    | S n' => fresh (avoid ++ [ix_new_name_core avoid n'])
    end.

  Definition ix_new_name (top_conflicts: list name) (ctx: list unit) (n: nat) :=
    if Nat.ltb n (length ctx)
    then ix_new_name_core top_conflicts (n - length ctx)
    else INDEX_EXCEEDS_CONTEXT.

  Definition ln_to_name (top_conflicts: list name):
    list unit * LN -> name :=
    fun '(depth, v) =>
      match v with
      | Fr x => x
      | Bd n => ix_new_name (top_conflicts) depth n
      end.

  Definition ln_to_binder (top_conflicts: list name):
    list unit * unit -> name :=
    (fun '(ctx, _) => ix_new_name top_conflicts ctx (length ctx)).

  (** ** Lifted Operations *)
  (********************************************************************)
  Definition term_ln_to_nominal (conflicts: list name):
    T unit LN -> T name name :=
    mapdp (T := T)
      (ln_to_binder conflicts)
      (ln_to_name conflicts).

  Definition term_nominal_to_ln:
    T name name -> T unit LN :=
    mapdp (T := T) (const tt) name_to_ln.

  Definition roundtrip_Named `{Traverse (T unit)}:
    T name name -> T name name :=
    fun t => let t_ln := term_nominal_to_ln t
          in term_ln_to_nominal (LN.free t_ln) t_ln.

  Lemma roundtrip_Named_spec1 `{Traverse (T unit)}:
    forall (t: T name name),
      roundtrip_Named t =
        mapdp
          (kc_dz (ln_to_binder (free (mapdp (const tt) name_to_ln t))) (const tt))
          (kc_dfunp (ln_to_name (free (mapdp (const tt) name_to_ln t))) (const tt) name_to_ln) t.
  Proof.
    intros.
    unfold roundtrip_Named.
    unfold term_ln_to_nominal.
    unfold term_nominal_to_ln.
    compose near t on left.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  Lemma roundtrip_Named_spec2 `{Traverse (T unit)}:
    forall (t: T name name),
      roundtrip_Named t =
        rename_binders
          (kc_dz
             (ln_to_binder (free (mapdp (const tt) name_to_ln t)))
             (const tt))
          (mapd (T := T name)
             (kc_dfunp
                (ln_to_name (free (mapdp (const tt) name_to_ln t)))
                (const tt)
                name_to_ln)
             t).
  Proof.
    intros.
    rewrite roundtrip_Named_spec1.
    rewrite mapd_decompose.
    reflexivity.
  Qed.

  Lemma term_nominal_to_ln_spec (conflicts: list name):
    mapdp (T := T)
      (ln_to_binder conflicts)
      (ln_to_name conflicts) =
      rename_binders (ln_to_binder conflicts) ∘ mapd (ln_to_name conflicts).
  Proof.
    rewrite mapd_decompose.
    reflexivity.
  Qed.

  Lemma locally_correct (fv: list name):
    forall (t: T name name),
      (kc_dz (B1 := name) (ln_to_binder fv) (const tt)) =
        (kc_dz (ln_to_binder fv) (const tt)).
  Proof.
    intros.
    ext [w v].
    unfold kc_dz, const.
  Abort.

End with_DTM.



(** * Relating Operations *)
(**********************************************************************)
Section with_DTM.

  Context
    (T: Type -> Type -> Type)
      `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import Categorical.DecoratedFunctorPoly.ToMono.
  Import Categorical.TraversableFunctor2.ToMono.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.

  Lemma FV_same_converson: forall (t: T name name),
      FV (T name) t =
        LN.free (term_nominal_to_ln T t).
  Proof.
    intros.
    unfold FV.
    unfold term_nominal_to_ln.
    unfold free.
    rewrite (foldMap_to_traverse1).
    unfold_ops @Traverse_Categorical.
    unfold_ops @Dist2_1.
    unfold_ops @Map2_1.
    reassociate -> on right.
    rewrite (fun2_map_map).
    unfold mapdp.
    unfold DerivedOperations.Mapdp_Categorical.
    change (?x ∘ id) with x; change (id ∘ ?x) with x.
    unfold compose.
    compose near (decp t).
    rewrite (fun2_map_map).
    unfold foldMapd.
    unfold mapdt.
    unfold Mapdt_Categorical.
    unfold TraversableFunctor.dist.
    change (?f ○ ?g) with (f ∘ g).
    unfold map.
    reassociate -> near (map2 id FV_loc).
    rewrite fun2_map_map.
    unfold_ops @Decorate_PolyVar.
    reassociate <- on left.
    reassociate -> near
                    (@map2 T H (Z atom) (Z2 atom atom) atom (Z2 atom atom)
                       (@extract Z Extract_Z atom) (@id (Z2 atom atom))).
    rewrite fun2_map_map.
    change (?x ∘ id) with x; change (id ∘ ?x) with x.
    unfold compose.
    change (?f ○ ?g) with (f ∘ g).
    unfold compose.
    assert
      (InnerEq: @map2 T H (Z atom) (Z2 atom atom) (@const Type Type (list atom) atom) (@const Type Type (list atom) False)
   (@pure (@const Type Type (list atom)) (@Pure_const (list atom) (@Monoid_unit_list atom)) atom ○ @extract Z Extract_Z atom)
   FV_loc (@decp T H0 atom atom t) =
                  @map2 T H (list atom * atom) (list atom * atom) (@const Type Type (list atom) unit) (@const Type Type (list atom) False)
                    (@pure (@const Type Type (list atom)) (@Pure_const (list atom) (@Monoid_unit_list atom)) unit
                       ○ @const (list atom * atom) unit tt) (free_loc ○ name_to_ln) (@decp T H0 atom atom t)).
    { fequal.
      { ext [l v].
        unfold compose.
        unfold name_to_ln.
        destruct (get_binding_spec l v) as [[Hbinding Hspec] | [pre [post [Hbinding [Hspec1 Hspec2]]]]].
        - cbn.
          rewrite Hbinding.
          reflexivity.
        - cbn.
          rewrite Hbinding.
          reflexivity.
      }
    }
    rewrite InnerEq.
    fequal.
  Admitted.

End with_DTM.

Section alpha_reasoning.

  Context
    (T: Type -> Type -> Type)
    `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  (*
  Lemma correctness: forall (t: T name name),
        (alpha (T name) t (roundtrip_Named T t)).
  Proof.
    intros.
    rewrite roundtrip_Named_spec.
    unfold roundtrip_Named.
    unfold alpha.
    compose near t on right.
    replace ((traversep (T := T) (G := fun A => A -> Prop)
   *)

End alpha_reasoning.
