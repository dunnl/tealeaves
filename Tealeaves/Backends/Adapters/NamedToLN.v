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
Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variables W T U.
#[local] Open Scope list_scope.

From Tealeaves Require
  Adapters.MonoidHom.DecoratedTraversableMonad
  Adapters.PolyToMono.Kleisli.DecoratedFunctor
  Adapters.PolyToMono.Kleisli.DecoratedTraversableFunctor
  Adapters.PolyToMono.Kleisli.DecoratedTraversableMonad
  Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly.


(** * Single-Argument DTM Instance *)
(**********************************************************************)
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
    `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Import Kleisli.DecoratedFunctorPoly.
  Import CategoricalToKleisli.DecoratedFunctorPoly.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.
  Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.

  Import DecoratedFunctorPoly.ToMono.
  Import TraversableFunctor2.ToMono.
  Import PolyToMono.Kleisli.DecoratedFunctor.ToMono1.

  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.TraversableFunctor.DerivedInstances.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.

  Existing Instance Theory.DecoratedTraversableFunctor.ToCtxset_Mapdt.
  Existing Instance Theory.TraversableFunctor.ToSubset_Traverse.


  Fail Import Categorical.DecoratedTraversableFunctorPoly.ToMono.

  Context `{! DecoratedTraversableFunctor (list atom) (T atom)}. (* TODO Infer this *)

  (** ** Named to Locally Nameless *)
  (********************************************************************)
  Definition binding_to_ln: Binding -> LN :=
    fun b =>
      match b with
      | Bound prefix var postfix =>
          Bd (length postfix)
      | Unbound context var =>
          Fr var
      end.

  Definition name_to_ln:
    list name * name -> LN.
  Proof.
    intros [ctx x].
    exact (binding_to_ln (get_binding ctx x)).
  Defined.

  Definition term_nominal_to_ln:
    T name name -> T unit LN :=
    mapdp (T := T) (const tt) name_to_ln.

  (** ** Locally Nameless to Named *)
  (********************************************************************)
  (* crash hard, crash often *)
  Definition PANIC_INDEX_EXCEEDS_CONTEXT: nat := 1337.

  (** ** <<to_name_from_history>> *)
  (********************************************************************)
  (** Perform one local binder renaming on a locally nameless binder occurrence, given
      the history (the names assigned to binders higher in the tree) and the initial avoid set. *)
  Definition to_name_from_history (top_conflicts: list name) (p: list name * unit): name :=
    match p with
    | (history, u) => fresh (top_conflicts ++ history)
    end.


  (** *** Rewriting Principles for <<to_name_from_history>> *)
  (********************************************************************)
  Lemma to_name_from_history_nil (top_conflicts: list name) (u: unit):
    to_name_from_history top_conflicts (@nil atom, u) = fresh top_conflicts.
  Proof.
    cbn.
    rewrite List.app_nil_r.
    reflexivity.
  Qed.

  Lemma to_name_from_history_pair (top_conflicts: list name) (history: list atom) (u: unit):
    to_name_from_history top_conflicts (history, u) = fresh (top_conflicts ++ history).
  Proof.
    reflexivity.
  Qed.

  Lemma to_name_from_history_preincr (top_conflicts: list name) (ctx: list atom):
    to_name_from_history top_conflicts ⦿ ctx = to_name_from_history (top_conflicts ++ ctx).
  Proof.
    ext [w l].
    unfold preincr, incr, compose.
    rewrite to_name_from_history_pair.
    unfold to_name_from_history.
    fequal.
    rewrite <- List.app_assoc.
    reflexivity.
  Qed.

  (** *** Freshness for <<to_name_from_history>> *)
  (********************************************************************)
  Lemma to_name_from_history_fresh (top_conflicts: list name): forall p,
      ~ (to_name_from_history top_conflicts p ∈ top_conflicts).
  Proof.
    intros.
    unfold to_name_from_history.
    destruct p.
    specialize (fresh_not_in (top_conflicts ++ l)).
    intros hyp contra.
    apply hyp.
    rewrite element_of_list_app.
    now left.
  Qed.

  (** ** <<to_history_from_prefix>> *)
  (********************************************************************)

  (** Given a locally nameless binding context (a list of unit values, representing its length-many binders opened in
      scope), convert the context into same-length list of names assigned to each binder, given a top-level avoid
      set. *)
  Definition to_history_from_prefix (top_conflicts: list name): list unit -> list name :=
    fold_with_history (to_name_from_history top_conflicts).

  Lemma to_history_from_prefix_preincr (top_conflicts: list name) (ctx: list atom):
    fold_with_history (to_name_from_history top_conflicts ⦿ ctx) =
      to_history_from_prefix (top_conflicts ++ ctx).
  Proof.
    ext l.
    generalize dependent top_conflicts.
    generalize dependent ctx.
    induction l; intros.
    - cbn.
      reflexivity.
    - rewrite fold_with_history_cons.
      unfold to_history_from_prefix.
      rewrite fold_with_history_cons.
      fequal.
      { unfold preincr, incr, compose.
        change (ctx ● []) with (ctx ++ []).
        rewrite List.app_nil_r.
        cbn.
        rewrite List.app_nil_r.
        reflexivity.
      }
      { rewrite preincr_preincr.
        rewrite IHl.
        unfold to_history_from_prefix.
        rewrite IHl.
        change (?l1 ● ?l2) with (l1 ++ l2).
        unfold to_history_from_prefix.
        rewrite to_name_from_history_preincr.
        rewrite List.app_assoc.
        reflexivity.
      }
  Qed.

  (* Tailored for use when the list is a nominal binding context decomposition *)
  Corollary to_history_from_prefix_decompose (top_conflicts: list name) {l1 l2: list unit} {u: unit}:
to_history_from_prefix top_conflicts (l1 ++ [u] ++ l2) =
        to_history_from_prefix top_conflicts l1 ++
          [to_name_from_history top_conflicts
             (to_history_from_prefix top_conflicts l1, u)] ++
          fold_with_history
          (to_name_from_history top_conflicts ⦿
             (to_history_from_prefix top_conflicts l1 ++
                [to_name_from_history top_conflicts (to_history_from_prefix top_conflicts l1, u)])) l2.
  Proof.
    intros.
    unfold to_history_from_prefix.
    rewrite fold_with_history_decompose.
    reflexivity.
  Qed.


  (** *** Rewriting rules *)
  (********************************************************************)
  Lemma to_history_from_prefix_nil (top_conflicts: list name):
    to_history_from_prefix top_conflicts nil = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma to_history_from_prefix_cons (top_conflicts: list name) (u: unit) (pre: list unit):
    to_history_from_prefix top_conflicts (u :: pre) =
      fresh top_conflicts :: to_history_from_prefix (top_conflicts ++ [fresh top_conflicts]) pre.
  Proof.
    unfold to_history_from_prefix.
    rewrite fold_with_history_cons.
    fequal.
    - rewrite to_name_from_history_nil.
      reflexivity.
    - rewrite to_name_from_history_nil.
      fequal.
      ext [x y].
      unfold preincr, incr, compose.
      unfold_ops @Monoid_op_list.
      unfold to_name_from_history.
      rewrite List.app_assoc.
      reflexivity.
  Qed.

  (** *** Freshness for <<to_history_from_prefix>> *)
  (********************************************************************)
  Lemma to_history_from_prefix_fresh (top_conflicts: list name): forall (prefix: list unit),
    forall (a: name),
      a ∈ top_conflicts ->
      ~ a ∈ (to_history_from_prefix top_conflicts prefix).
  Proof.
    introv Hin.
    unfold to_name_from_history.
    enough (cut: forall (x: atom), x ∈ to_history_from_prefix top_conflicts prefix -> x <> a).
    { intro contra.
      specialize (cut a).
      apply cut; auto.
    }
    apply fold_with_history_ind.
    intros u h Hnotin.
    specialize (to_name_from_history_fresh top_conflicts (h, u)).
    intro Hfresh.
    intro contra.
    subst. contradiction.
  Qed.

  (** ** <<to_name_from_prefix>> *)
  (********************************************************************)
  Definition to_name_from_prefix (top_conflicts: list name): list unit * unit -> name :=
    run_using_prefix (to_name_from_history top_conflicts).

  (** *** Relation between <<to_history_from_prefix>> and <<to_name_from_prefix>> *)
  (********************************************************************)
  Lemma to_history_from_prefix_spec (top_conflicts: list name):
    to_history_from_prefix top_conflicts =
      mapdz (T := list) (to_name_from_prefix top_conflicts).
  Proof.
    unfold to_name_from_prefix.
    rewrite run_using_prefix_spec.
    reflexivity.
  Qed.

  (** *** Rewriting rules for <<to_name_from_prefix>> *)
  (********************************************************************)
  Lemma to_name_from_prefix_rw_nil (top_conflicts: list name): forall (u: unit),
      to_name_from_prefix (top_conflicts) (nil, u) =
        fresh top_conflicts.
  Proof.
    intros.
    cbn.
    rewrite List.app_nil_r.
    reflexivity.
  Qed.

  Lemma to_name_from_prefix_rw_cons (top_conflicts: list name): forall (u: unit) (rest: list unit) (u': unit),
      to_name_from_prefix (top_conflicts) (u :: rest, u') =
        fresh
    (top_conflicts ++
       fresh top_conflicts ::
       fold_with_history (preincr (to_name_from_history top_conflicts) [fresh top_conflicts]) rest).
  Proof.
    intros.
    unfold to_name_from_prefix.
    unfold run_using_prefix.
    rewrite fold_with_history_cons.
    unfold to_name_from_history at 1.
    unfold to_name_from_history at 1.
    rewrite List.app_nil_r.
    unfold to_name_from_history at 2.
    rewrite List.app_nil_r.
    reflexivity.
  Qed.

  (** *** Freshness for <<to_name_from_prefix>> *)
  (********************************************************************)
  Lemma to_name_from_prefix_fresh (top_conflicts: list name) (prefix: list unit) (u: unit):
    ~ to_name_from_prefix top_conflicts (prefix, u) ∈ top_conflicts.
  Proof.
    intros.
    unfold to_name_from_prefix.
    intro contra.
    unfold run_using_prefix in contra.
    specialize (to_name_from_history_fresh top_conflicts
                  (fold_with_history (to_name_from_history top_conflicts) prefix, u)).
    intro Hyp.
    apply Hyp.
    assumption.
  Qed.

  Fixpoint length_to_list_unit (length: nat): list unit :=
    match length with
    | 0 => nil
    | S n => tt :: length_to_list_unit n
    end.

  (* Give a DB index (Bd N), define its new name *)
  Definition LN_BD_to_binder_name (top_conflicts: list name) (ctx: list unit) (n: nat): atom :=
    if Nat.ltb n (length ctx)
    then to_name_from_prefix top_conflicts (length_to_list_unit (length ctx - (n + 1)), tt)
    else PANIC_INDEX_EXCEEDS_CONTEXT.

  Lemma LN_BD_to_binder_name_fresh: forall avoid a ctx n,
      length ctx > n ->
      a ∈ avoid -> LN_BD_to_binder_name avoid ctx n <> a.
  Proof.
    introv Hlt Hin.
    unfold LN_BD_to_binder_name.
    apply PeanoNat.Nat.ltb_lt in Hlt.
    rewrite Hlt.
    intro contra.
    subst.
    apply to_name_from_prefix_fresh in Hin.
    assumption.
  Qed.

  Definition ln_to_name (top_conflicts: list name):
    list unit * LN -> name :=
    fun '(depth, v) =>
      match v with
      | Fr x => x
      | Bd n => LN_BD_to_binder_name (top_conflicts) depth n
      end.

  Definition term_ln_to_nominal (conflicts: list name):
    T unit LN -> T name name :=
    mapdp (T := T)
      (to_name_from_prefix conflicts)
      (ln_to_name conflicts).


  (** ** Roundtrip Specifications *)
  (********************************************************************)
  Definition roundtrip_Named `{Traverse (T unit)}:
    T name name -> T name name :=
    fun t => let t_ln := term_nominal_to_ln t
          in term_ln_to_nominal (LN.free t_ln) t_ln.

  Lemma roundtrip_Named_spec1 `{Traverse (T unit)}:
    forall (t: T name name),
      roundtrip_Named t =
        mapdp
          (kc_dz (to_name_from_prefix (free (term_nominal_to_ln t))) (const tt))
          (kc_dfunp (ln_to_name (free (term_nominal_to_ln t))) (const tt) name_to_ln) t.
  Proof.
    intros.
    unfold roundtrip_Named.
    compose near t on left.
    unfold term_nominal_to_ln at 2.
    unfold term_ln_to_nominal at 1.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  (** *** Lemmas about mapping (const tt) *)
  (********************************************************************)
  Lemma mapd_list_prefix_const: forall (A: Type) (w: list A),
      mapdz (T := list) (const tt) w = map (F := list) (const tt) w.
  Proof.
    intros.
    rewrite mapd_list_prefix_spec.
    unfold compose.
    induction w.
    - reflexivity.
    - cbn. fequal.
      compose near (decorate_prefix_list w).
      rewrite (fun_map_map).
      rewrite <- IHw.
      reflexivity.
  Qed.

  Lemma cobind_Z_const: forall (A: Type),
      cobind (A := A) (W := Z) (const tt) = map (F := Z) (const tt).
  Proof.
    introv.
    ext [w a].
    cbn.
    rewrite mapd_list_prefix_const.
    reflexivity.
  Qed.

  Lemma cobind_Z2_const: forall (A A' B: Type) (f: Z2 B A -> A'),
      cobind_Z2 (B1 := B) (A1 := A) (const tt) f =
        fun '(w, a) => (map (F := list) (const tt) w, f (w, a)).
  Proof.
    introv.
    ext [w a].
    cbn.
    compose near w on left.
    unfold_Z.
    rewrite <- mapd_list_prefix_spec.
    rewrite mapd_list_prefix_const.
    reflexivity.
  Qed.

  (** *** Presented in terms of <<mapd>> composed with <<rename_binders>> *)
  (********************************************************************)

  (* Given a binding occurrence (pre, b) in a nominal term t,
     return the new name of b after a Nominal~>LN~>Nominal roundtrip *)
  Definition roundtrip_Binders (avoid: list atom): Z atom -> atom :=
    to_name_from_prefix avoid ∘ map (const tt).

  (* Given a variable occurrence (pre, v) in a nominal term t,
     return the new name of v after a Nominal~>LN~>Nominal roundtrip *)
  Definition roundtrip_Vars (avoid: list atom): Z2 atom atom -> atom :=
    kc_dfunp (ln_to_name avoid) (const tt) name_to_ln.

  Lemma roundtrip_Binders_spec (avoid: list atom):
    mapdz (T := list) (roundtrip_Binders avoid) =
      to_history_from_prefix avoid ∘ map (const tt).
  Proof.
    intros.
    unfold roundtrip_Binders.
    rewrite to_history_from_prefix_spec.
    Set Keyed Unification.
    rewrite (mapdz_map_list (A' := atom) (B := atom) (A := unit)).
    Unset Keyed Unification.
    reflexivity.
  Qed.

  Lemma roundtrip_Named_spec_decomposed:
    forall (t: T name name),
      roundtrip_Named t =
        let avoid := LN.free (term_nominal_to_ln t)
        in rename_binders
             (roundtrip_Binders avoid)
             (mapd (T := T name) (roundtrip_Vars avoid) t).
  Proof.
    intros.
    rewrite roundtrip_Named_spec1.
    unfold kc_dz.
    rewrite cobind_Z_const.
    rewrite mapd_decompose.
    reflexivity.
  Qed.

  (** *** Roundtrip effect on context occurrences *)
  (* if (ctx, a) ∈d t, then (roundtrip_Occ (free t) (ctx, a)) ∈d roundtrip t *)
  (********************************************************************)
  Definition roundtrip_Occ (avoid: list atom): list atom * atom -> list atom * atom :=
    fun '(ctx, a) =>
      (mapdz (roundtrip_Binders avoid) ctx, roundtrip_Vars avoid (ctx, a)).


  Lemma roundtrip_Named_var_spec {avoid: list atom}:
    (kc_dfunp
       (ln_to_name (avoid))
       (const tt)
       name_to_ln) =
      fun '(ctx, nm) =>
        match binding_to_ln (get_binding ctx nm) with
        | Fr x => x
        | Bd n => LN_BD_to_binder_name avoid (map (const tt) ctx) n
        end.
  Proof.
    ext [ctx nm].
    unfold kc_dfunp.
    unfold compose.
    unfold cobind_Z2.
    unfold compose.
    unfold map_Z2.
    cbn.
    compose near ctx.
    unfold_Z.
    rewrite <- mapd_list_prefix_spec.
    rewrite mapd_list_prefix_const.
    reflexivity.
  Qed.

  (** ** Deleting Binders *)
  (********************************************************************)
  Lemma decorate_rename_binders {B1 B2 V}:
    forall (ρ: list B1 * B1 -> B2) (t: T B1 V),
      delete_binders (dec (T B2) (rename_binders ρ t)) =
        delete_binders (map (F := T B1) (map_fst (mapdz (T := list) ρ)) (dec (T B1) t)).
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
    ext [w v].
    unfold compose.
    cbn.
    rewrite mapd_list_prefix_spec.
    reflexivity.
  Qed.

  Lemma decorate_rename_binders2 {B1 B2 V}:
    forall (ρ: list B1 * B1 -> B2) (t: T B1 V),
      delete_binders (dec (T B2) (rename_binders ρ t)) =
        map (F := T unit)
          (map_fst (mapdz (T := list) ρ))
          (delete_binders (dec (T B1) t)).
  Proof.
    intros.
    rewrite decorate_rename_binders.
    compose near (dec (T B1) t).
    unfold delete_binders.
    rewrite fun2_map22_map21_commute.
    reflexivity.
  Qed.

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

  (** ** Relating Free Variables During Translation *)
  (********************************************************************)
  Lemma normalize_foldMap {M} `{Monoid M} `(f: list name * name -> M): forall (t: T name name),
      foldMapd f t = mapdtp (A2 := False) (G := const M) (T := T) (pure (F := const M) ∘ (const tt)) f t.
  Proof.
  Admitted.

  Lemma FV_preserved: forall (t: T name name),
      FV (T name) t =
        LN.free (term_nominal_to_ln t).
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
    unfold DerivedOperations.Mapdt_Categorical.
    unfold compose.
    assert (cut: FV_loc = free_loc ∘ name_to_ln).
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
    }.
    rewrite cut.
    reflexivity.
  Qed.

  (** ** Alpha Equivalence Local Reasoning *)
  (********************************************************************)
  Lemma to_name_from_prefix_preincr: forall avoid a,
      to_name_from_prefix avoid ∘ cobind (W := Z) (const tt) ∘ incr [a] =
        to_name_from_prefix (avoid ++ [fresh avoid]) ∘ cobind (const tt).
  Proof.
    intros.
    ext [ctx x].
    unfold compose.
    unfold to_name_from_prefix.
  Abort.

  Lemma roundtrip_Occ_Unbound_spec1: forall (avoid: list atom) (ctx: list atom) (a: atom),
      get_binding ctx a = Unbound ctx a ->
      roundtrip_Occ avoid (ctx, a) = (mapdz (roundtrip_Binders avoid) ctx, a).
  Proof.
    introv Hyp.
    cbn.
    fequal.
    rewrite Hyp.
    cbn.
    reflexivity.
  Qed.

  Lemma roundtrip_Occ_Bound_spec1: forall (avoid: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      roundtrip_Occ avoid (ctx, a) =
        (mapdz (roundtrip_Binders avoid) ctx, roundtrip_Vars avoid (ctx, a)).
  Proof.
    introv Hyp.
    clear Hyp.
    unfold roundtrip_Occ.
    rewrite roundtrip_Binders_spec.
    reflexivity.
  Qed.

  Lemma roundtrip_Occ_Unbound_spec2: forall (avoid: list atom) (ctx: list atom) (a: atom),
      a ∈ avoid ->
      get_binding ctx a = Unbound ctx a ->
      match roundtrip_Occ avoid (ctx, a) with
      | (foo, x) =>
          get_binding foo x = Unbound (mapdz (roundtrip_Binders avoid) ctx) a
      end.
  Proof.
    introv Hnin Hyp.
    rewrite roundtrip_Occ_Unbound_spec1; auto.
    destruct (get_binding_spec (mapdz (roundtrip_Binders avoid) ctx) a)
      as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin']]]]].
    { rewrite Case1.
      reflexivity. }
    { assert (Hfresh: ~ a ∈ mapdz (roundtrip_Binders avoid) ctx).
      { rewrite roundtrip_Binders_spec.
        unfold compose at 1.
        apply to_history_from_prefix_fresh.
        assumption.
      }
      apply get_binding1 in Hfresh.
      assumption.
    }
  Qed.

  Lemma roundtrip_Vars_Bound_spec: forall (avoid: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      ctx = prefix ++ [a'] ++ postfix ->
      a = a' ->
      roundtrip_Vars avoid (ctx, a) =
        to_name_from_history avoid (to_history_from_prefix avoid (map (const tt) prefix), tt).
  Proof.
    introv Hbinding Hctx Haeq.
    unfold to_name_from_history.
    unfold roundtrip_Vars.
    unfold kc_dfunp.
    rewrite cobind_Z2_const.
    unfold compose at 1.
    unfold name_to_ln.
    rewrite Haeq in *; clear Haeq.
    rewrite Hbinding.
    unfold binding_to_ln.
    unfold ln_to_name.
    unfold LN_BD_to_binder_name.
    rewrite map_preserve_length.
    assert (HsafeIx: length postfix < length ctx).
    { subst.
      rewrite List.app_length.
      rewrite List.app_length.
      cbn.
      lia.
    }
    rewrite <- PeanoNat.Nat.ltb_lt in HsafeIx.
    rewrite HsafeIx.
    unfold to_name_from_prefix.
    unfold run_using_prefix.
    unfold to_name_from_history.
    fequal.
    fequal.
    unfold to_history_from_prefix.
    fequal.
    assert (Hineq: length ctx - (length postfix + 1) = length prefix).
    { subst.
      rewrite List.app_length.
      rewrite List.app_length.
      cbn.
      lia.
    }
    rewrite Hineq.
    { clear. induction prefix.
      - reflexivity.
      - cbn. now rewrite IHprefix. }
  Qed.

  Lemma roundtrip_Occ_Bound_spec2: forall (avoid: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      a = a' ->
      ctx = prefix ++ [a'] ++ postfix ->
      ~ a ∈ postfix ->
      match roundtrip_Occ avoid (ctx, a) with
      | (foo, x) =>
          get_binding foo x =
            let NewPrefix := to_history_from_prefix avoid (map (const tt) prefix)
            in let NewVar := to_name_from_history avoid (NewPrefix, tt)
               in let NewPost := to_history_from_prefix (avoid ++ NewPrefix ++ [NewVar]) (map (const tt) postfix)
                  in Bound NewPrefix NewVar NewPost
      end.
  Proof.
    introv Hyp Haeq Hctxeq Hnin.
    unfold roundtrip_Occ.
    rewrite roundtrip_Binders_spec.
    unfold compose at 1.
    remember (to_history_from_prefix avoid (map (const tt) ctx)) as NewContext.
    remember (roundtrip_Vars avoid (ctx, a)) as NewVar'.
    rewrite Hctxeq in HeqNewContext.
    rewrite map_list_app in HeqNewContext.
    rewrite map_list_app in HeqNewContext.
    rewrite map_list_one in HeqNewContext.
    change (const tt a') with tt in HeqNewContext.
    rewrite (to_history_from_prefix_decompose avoid) in HeqNewContext.

    remember (to_history_from_prefix avoid (map (const tt) prefix)) as NewPrefix.
    remember (to_name_from_history avoid (NewPrefix, tt)) as NewVar.
    rewrite (roundtrip_Vars_Bound_spec avoid ctx a prefix a' postfix Hyp Hctxeq Haeq) in HeqNewVar'.
    assert (NewVar = NewVar').
    { subst. reflexivity. }
    rewrite <- H3 in *; clear H3.
    rewrite to_name_from_history_preincr in HeqNewContext.
    remember (fold_with_history (to_name_from_history avoid ⦿ (NewPrefix ++ [NewVar]))
                (map (const tt) postfix)) as NewPostFix.
    rewrite to_name_from_history_preincr in HeqNewPostFix.
    unfold to_history_from_prefix.
    rewrite <- HeqNewPostFix.
    assert (Hnin': ~ NewVar ∈ NewPostFix).
    { rewrite HeqNewPostFix.
      admit.
    }
    rewrite HeqNewContext.
    rewrite <- HeqNewPostFix.
    admit.
  Admitted.

  Lemma rt_correct_local2:
    forall (t: T name name) (avoid: list name)
      (Havoidinit: forall (a: name), (a ∈ FV (T name) t -> a ∈ avoid)),
    forall (ctx: list name) (a: name),
      (ctx, a) ∈ (dec (T atom) t) ->
      alpha_equiv_local (ctx, a) (roundtrip_Occ avoid (ctx, a)).
  Proof.
    introv HFV.
    introv Hin.
    unfold alpha_equiv_local.
    destruct (get_binding_spec ctx a) as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin]]]]].
    { rewrite Case1.
      assert (Havoid: a ∈ avoid).
      { apply HFV.
        apply (FV_lift_local (T atom) _ ctx); auto.
      }
      specialize (roundtrip_Occ_Unbound_spec2 avoid ctx a Havoid Case1).
      intro X.
      destruct (roundtrip_Occ avoid (ctx, a)).
      rewrite X. destruct_eq_args a a.
    }
    {
      rewrite Case2.
      apply (roundtrip_Occ_Bound_spec2 avoid) in Case2; auto.
      destruct (roundtrip_Occ avoid (ctx, a)).
      rewrite Case2.
      cbn.
      cbn.
      admit.
    }
  Admitted.

  Lemma rt_correct_local1:  forall (t: T name name),
    TraversableFunctor.Forall
    (fun a: list atom * atom =>
     (precompose (cobind (kc_dfunp (ln_to_name (free (term_nominal_to_ln t))) (const tt) name_to_ln))
        ∘ (precompose (map_fst (mapd_list_prefix
                                  (kc_dz (to_name_from_prefix (free (term_nominal_to_ln t))) (const tt))))
           ∘ alpha_equiv_local)) a a) (delete_binders (dec (T atom) t)).
  Proof.
    intros t.
    rewrite TraversableFunctor.forall_iff.
    intros [ctx a].
    rewrite in_del_binders.
    unfold compose, precompose.
    intro Hin.
    apply (rt_correct_local2 t).
    { rewrite (FV_preserved T t).
      easy.
    }
    assumption.
  Qed.

  Theorem roundtrip_correct: forall (t: T name name),
      polymorphic_alpha T t (roundtrip_Named T t).
  Proof.
    intros.
    rewrite (roundtrip_Named_spec_decomposed T).
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

End with_DTM.
