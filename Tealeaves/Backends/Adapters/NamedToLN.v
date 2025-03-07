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
Import List.ListNotations.
Import DecoratedContainerFunctor.Notations.

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
  Proof.
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

  Import PolyToMono.Kleisli.DecoratedFunctor.ToMono1.

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


  Import DecoratedFunctorPoly.ToMono.
  Import TraversableFunctor2.ToMono.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.


  Context
    `{ToCtxset (list atom) (T atom)}
     `{Traverse (T unit)}.

  Definition cobind_binders {B1 B2}:
    forall (ρ: list B1 * B1 -> B2) (p: list B1 * B1), list B2 * B2 :=
    fun ρ p => map (F := Z) ρ (cojoin (W := Z) p).

  Definition cobind_vars {B1 B2 V}:
    forall (ρ: list B1 * B1 -> B2) (p: list B1 * V), list B2 * V :=
    fun ρ '(w, v) => (map (F := list) ρ (decorate_prefix_list w), v).

  Definition rt_local_binders (avoid: list atom) (ctx: list atom): list atom :=
    map (kc_dz (ln_to_binder avoid) (const tt)) (decorate_prefix_list ctx).

  (*
  Lemma rt_local_binders_spec (avoid: list atom) (ctx:list atom):
    rt_local_binders avoid ctx = cobind_vars (kc_dz (ln_to_binder ctx) (const tt)) ctx.
   *)

  Definition rt_local_atom (avoid: list atom) (ctx: list atom) (a: atom): atom :=
    ln_to_name avoid (map (const tt) ctx, name_to_ln (ctx, a)).

  Lemma decorate_rename_binders {B1 B2 V}:
    forall (ρ: list B1 * B1 -> B2) (t: T B1 V),
      delete_binders (dec (T B2) (rename_binders ρ t)) =
        delete_binders (map (F := T B1) (cobind_vars ρ) (dec (T B1) t)).
  Proof.
    intros.
    unfold delete_binders.
    unfold_ops @Map2_1.
    unfold_ops @Map2_2.
    unfold_ops @Decorate_PolyVar.
    unfold compose.
    compose near (decp (rename_binders ρ t)).
    rewrite fun2_map_map.
    change (id ∘ ?x) with x.
    compose near (decp t).
    rewrite (fun2_map_map).
    change (id ∘ ?x) with x.
    compose near (decp t).
    rewrite (fun2_map_map).
    change (id ∘ ?x) with x.
    change (?x ∘ id) with x.
    change ((@const B2 unit tt ∘ @extract Z Extract_Z B2)) with
      (@const (Z B2) unit tt).
    change ((@const B1 unit tt ∘ @extract Z Extract_Z B1)) with
      (@const (Z B1) unit tt).
    unfold rename_binders.
    unfold mapdz.
    unfold_ops @ToMono2.MapdZ_of_Mapdp2.
    unfold mapdp.
    unfold Mapdp_Categorical.
    unfold compose.
    compose near (decp t) on left.
    rewrite (polydecnat).
    unfold compose.
    compose near t on left.
    rewrite dfunp_dec_dec.
    unfold compose.
    compose near (decp t) on left.
    rewrite (fun2_map_map).
    compose near (decp t) on left.
    rewrite (fun2_map_map).
    fequal.
    change (id ∘ ?x) with x.
    unfold cobind_vars.
    ext [w v].
    unfold compose.
    cbn.
    reflexivity.
  Qed.

  Lemma decorate_rename_binders2 {B1 B2 V}:
    forall (ρ: list B1 * B1 -> B2) (t: T B1 V),
      delete_binders (dec (T B2) (rename_binders ρ t)) =
        map (F := T unit) (cobind_vars ρ) (delete_binders (dec (T B1) t)).
  Proof.
    intros.
    rewrite decorate_rename_binders.
    compose near (dec (T B1) t).
    unfold delete_binders.
    rewrite fun2_map22_map21_commute.
    reflexivity.
  Qed.

End with_DTM.

(** * Relating Operations *)
(**********************************************************************)
Section with_DTM.

  Context
    (T: Type -> Type -> Type)
      `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.
  Import Categorical.DecoratedFunctorPoly.ToMono.
  Import Categorical.TraversableFunctor2.ToMono.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.

  Lemma normalize_foldMap {M} `{Monoid M} `(f: list name * name -> M): forall (t: T name name),
      foldMapd f t = mapdtp (A2 := False) (G := const M) (T := T) (pure (F := const M) ∘ (const tt)) f t.
  Proof.
  Admitted.

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
    rewrite normalize_foldMap.
    unfold mapdtp.
    unfold Mapdt_Categorical.
    unfold TraversableFunctor.dist.
    change (?f ○ ?g) with (f ∘ g).
    unfold compose.
    fequal.
    fequal.
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
  Qed.

End with_DTM.


Section alpha_reasoning.

  Context
    (T: Type -> Type -> Type)
      `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Import TraversableFunctor2.ToMono.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.TraversableFunctor.DerivedInstances.
  Import Theory.LiftRel.TraversableFunctor.

  Import PolyToMono.Kleisli.DecoratedFunctor.
  Import PolyToMono.Kleisli.DecoratedFunctor.ToMono1.

  Import Categorical.DecoratedFunctorPoly.ToMono.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.

  Existing Instance Theory.TraversableFunctor.ToSubset_Traverse.

  Lemma in_del_binders {B A}: forall (t: T B A) (a: A),
      element_of a (delete_binders t) = element_of a t.
  Proof.
    intros.
    unfold delete_binders.
    unfold element_of.
    rewrite tosubset_to_foldMap.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_to_traverse1.
    rewrite foldMap_to_traverse1.
    unfold_ops @Traverse_Categorical.
    unfold compose.
    compose near t.
    rewrite <- fun2_map22_map21_commute.
    unfold compose.
    rewrite Dist2_1_natural2.
    reflexivity.
  Qed.


  Import ContainerFunctor.Notations.

  Definition rt_local (avoid: list atom): list atom * atom -> list atom * atom :=
    fun '(ctx, a) =>
    (cobind_vars (kc_dz (ln_to_binder avoid) (const tt))
       (cobind (kc_dfunp (ln_to_name avoid) (const tt) name_to_ln) (ctx, a))).

  Lemma rt_local_spec (avoid: list atom): forall (p: list atom * atom),
      rt_local avoid p = match p with
                         | (ctx, a) => (rt_local_binders avoid ctx, rt_local_atom avoid ctx a)
                         end.
  Proof.
    intros [ctx a].
    cbn.
    destruct (get_binding_spec ctx a) as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin]]]]].
    { rewrite Case1.
      reflexivity.
    }
    { rewrite Case2.
      repeat fequal.
      rewrite map_to_traverse.
      (* mapdt_ci lemma *)
      admit.
    }
  Admitted.

  Lemma rt_correct_local:
    forall (t: T name name) (avoid: list name)
      (Havoidinit: forall (a: name), (a ∈ FV (T name) t -> a ∈ avoid)),
      forall (ctx: list name) (a: name),
        (ctx, a) ∈ (dec (T atom) t) ->
        alpha_equiv_local (ctx, a)
          (rt_local_binders avoid ctx, rt_local_atom avoid ctx a).
  Proof.
    introv HavoidInit.
    introv Helt.
    destruct (get_binding_spec ctx a) as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin]]]]].
    {
      unfold alpha_equiv_local.
      rewrite Case1.
      assert (get_binding
                (rt_local_binders avoid ctx)
                (rt_local_atom avoid ctx a)
              = Unbound (rt_local_binders avoid ctx) a).
      { destruct (get_binding_spec  (rt_local_binders avoid ctx) (rt_local_atom avoid ctx a))
          as [[Case1' rest'] | [prefix' [postfix' [Case2' [ctxspec' Hnin']]]]].
        { rewrite Case1'.
          admit.
        }
        get_binding (rt_local_binders avoid ctx) (rt_local_atom avoid ctx a) = Unbound ctx a).
      {
      assert (rt_local_binders avoid ctx = Unbound ctx a).
    induction ctx.
    - cbn. destruct_eq_args a a.
    - unfold rt_local_binders.


    destruct (get_binding_spec ctx a) as [[Case1 rest] | [Case2 [rest1 rest2]]]. *)
  Admitted.

  Lemma rt_correct_local1:  forall (t: T name name),
    Forall
    (fun a : list atom * atom =>
     (precompose (cobind (kc_dfunp (ln_to_name (free (mapdp (const tt) name_to_ln t))) (const tt) name_to_ln))
      ∘ (precompose (cobind_vars (kc_dz (ln_to_binder (free (mapdp (const tt) name_to_ln t))) (const tt)))
           ∘ alpha_equiv_local)) a a) (delete_binders (dec (T atom) t)).
  Proof.
    intros t.
    rewrite TraversableFunctor.forall_iff.
    intros [ctx a].
    rewrite in_del_binders.
    unfold compose, precompose.
    intros.
    pose (rt_local_spec ((free (mapdp (const tt) name_to_ln t))) (ctx, a)).
    unfold rt_local in e.
    rewrite e.
    eapply rt_correct_local; try eassumption.
    { intro x.
      rewrite (FV_same_converson T).
      easy.
    }
  Qed.

  Theorem roundtrip_correct: forall (t: T name name),
      polymorphic_alpha T t (roundtrip_Named T t).
  Proof.
    intros.
    rewrite (roundtrip_Named_spec2 T).
    unfold polymorphic_alpha.
    unfold lift_relation_ctx_poly.
    rewrite (decorate_rename_binders2 T).
    rewrite TraversableFunctor.relation_natural2.
    rewrite (CategoricalToKleisli.DecoratedFunctor.dec_mapd2 (list atom) (F := T atom)).
    rewrite delete_binders_map.
    rewrite relation_natural2.
    apply relation_diagonal1.
    apply rt_correct_local1.
  Qed.

  Print Assumptions roundtrip_correct.

End alpha_reasoning.
