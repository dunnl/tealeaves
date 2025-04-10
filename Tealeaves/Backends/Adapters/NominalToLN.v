From Tealeaves Require Import
  Backends.LN
  Backends.Nominal.Common
  Backends.Common.Names
  Backends.Nominal.FV
  Backends.Nominal.Alpha
  Functors.Option
  LiftRel.TraversableFunctor
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



(** * Properties about mapping over <<list>>/<<Z>> *)
(**********************************************************************)
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
    { Fail apply PolyToMono.Kleisli.DecoratedTraversableMonad.DTM_of_DTMP.
      admit.
    }
    apply MonoidHom.DecoratedTraversableMonad.DTM_of_DTM.
    { constructor; try typeclasses eauto.
      reflexivity. intros.
      unfold monoid_op, Monoid_op_list.
      induction a1.
      reflexivity.
      cbn. now  rewrite IHa1.
    }
    Admitted.

End DTM.

(** * Histories and Contexts *)
(********************************************************************)
Section to_name_from_history.

  (** ** <<to_name_from_history>> *)
  (** Perform one local binder renaming on a locally nameless binder occurrence, given the history (the names assigned
    to binders higher in the tree) and the initial avoid set.  *)
  (********************************************************************)
  Definition to_name_from_history
    (top_avoid: list name)
    (p: list name * unit): name :=
    match p with
    | (history, u) =>
        fresh (top_avoid ++ history)
    end.

  (** *** Rewriting Principles for <<to_name_from_history>> *)
  (********************************************************************)
  Section to_name_from_history_rw.

    Context (avoid: list name).

    Lemma to_name_from_history_nil (u: unit):
      to_name_from_history avoid (@nil atom, u) = fresh avoid.
    Proof.
      cbn -[fresh].
      rewrite List.app_nil_r.
      reflexivity.
    Qed.

    Lemma to_name_from_history_pair (history: list atom) (u: unit):
      to_name_from_history avoid (history, u) = fresh (avoid ++ history).
    Proof.
      reflexivity.
    Qed.

    Lemma to_name_from_history_preincr (history: list atom):
      to_name_from_history avoid ⦿ history =
        to_name_from_history (avoid ++ history).
    Proof.
      ext [w l].
      unfold preincr, incr, compose.
      rewrite to_name_from_history_pair.
      unfold to_name_from_history.
      unfold_ops @Monoid_op_list.
      rewrite <- List.app_assoc.
      reflexivity.
    Qed.

  End to_name_from_history_rw.

  (** *** Freshness for <<to_name_from_history>> *)
  (********************************************************************)
  Lemma to_name_from_history_fresh (avoid: list name): forall p,
      ~ (to_name_from_history avoid p ∈ avoid).
  Proof.
    intros.
    unfold to_name_from_history.
    destruct p.
    specialize (fresh_not_in (avoid ++ l)).
    intros hyp contra.
    apply hyp.
    rewrite element_of_list_app.
    now left.
  Qed.

  (** ** <<to_history_from_ctx>> *)
  (** Given a locally nameless binding context (a list of unit values, representing its length-many binders in scope),
    convert the context into same-length list of names assigned to each binder, given a top-level avoid set. *)
  (********************************************************************)
  Definition to_history_from_ctx (avoid: list name):
    list unit -> list name :=
    fold_with_history (to_name_from_history avoid).

  Ltac fold_folds :=
    repeat change (fold_with_history (to_name_from_history ?avoid)) with
      (to_history_from_ctx avoid) in *.

  (** *** Basic Properties of <<to_history_from_ctx>> *)
  (********************************************************************)
  Corollary length_to_history_from_ctx (avoid: list name) (l: list unit):
    length (to_history_from_ctx avoid l) = length l.
  Proof.
    intros.
    unfold to_history_from_ctx.
    rewrite length_fold_with_history.
    reflexivity.
  Qed.

  (** *** Rewriting Principles for <<to_history_from_ctx>> *)
  (********************************************************************)
  Section to_name_from_history_rw.

    Context (avoid: list name).

    Lemma to_history_from_ctx_nil:
      to_history_from_ctx avoid nil = nil.
    Proof.
      reflexivity.
    Qed.

    Lemma to_history_from_ctx_cons (u: unit) (pre: list unit):
      to_history_from_ctx avoid (u :: pre) =
        fresh avoid :: to_history_from_ctx (avoid ++ [fresh avoid]) pre.
    Proof.
      unfold to_history_from_ctx.
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

    Lemma to_history_from_ctx_preincr
      (history: list atom):
      fold_with_history (to_name_from_history avoid ⦿ history) =
        to_history_from_ctx (avoid ++ history).
    Proof.
      ext l.
      generalize dependent avoid.
      generalize dependent history.
      induction l; intros.
      - cbn.
        reflexivity.
      - rewrite fold_with_history_cons.
        unfold to_history_from_ctx.
        rewrite fold_with_history_cons.
        fequal.
        { unfold preincr, incr, compose.
          change (history ● []) with (history ++ []).
          rewrite List.app_nil_r.
          cbn.
          rewrite List.app_nil_r.
          reflexivity.
        }
        { rewrite preincr_preincr.
          rewrite IHl.
          unfold to_history_from_ctx.
          rewrite IHl.
          change (?l1 ● ?l2) with (l1 ++ l2).
          unfold to_history_from_ctx.
          rewrite to_name_from_history_preincr.
          rewrite List.app_assoc.
          reflexivity.
        }
    Qed.

  End to_name_from_history_rw.

  (** *** Distributing <<to_history_from_ctx>> over a context *)
  (********************************************************************)
  (* Tailored for use when the list is a nominal binding context decomposition *)
  Section to_history_from_ctx_decompose.

    Context (avoid: list name) {l1 l2: list unit} {u: unit}.

    Corollary to_history_from_ctx_decompose:
      to_history_from_ctx avoid (l1 ++ [u] ++ l2) =
        let init := to_history_from_ctx avoid l1 in
        let mid := [to_name_from_history avoid (init , u)] in
        let tail := to_history_from_ctx (avoid ++ init ++ mid) l2
        in init ++ mid ++ tail.
    Proof.
      intros.
      unfold to_name_from_history at 1.
      unfold to_history_from_ctx.
      rewrite fold_with_history_decompose.
      rewrite to_history_from_ctx_preincr.
      reflexivity.
    Qed.

  End to_history_from_ctx_decompose.

  (** *** Freshness for <<to_history_from_ctx>> *)
  (********************************************************************)
  Lemma to_history_from_ctx_fresh (avoid: list name): forall (prefix: list unit),
    forall (a: name),
      a ∈ avoid ->
      ~ a ∈ (to_history_from_ctx avoid prefix).
  Proof.
    introv Hin.
    unfold to_name_from_history.
    enough (cut: forall (x: atom), x ∈ to_history_from_ctx avoid prefix -> x <> a).
    { intro contra.
      specialize (cut a).
      apply cut; auto.
    }
    apply fold_with_history_ind.
    intros u h Hnotin.
    specialize (to_name_from_history_fresh avoid (h, u)).
    intro Hfresh.
    intro contra.
    subst. contradiction.
  Qed.

  (** ** <<to_name_from_ctx>> *)
  (* give a name to a nameless binder in a context *)
  (********************************************************************)
  Definition to_name_from_ctx (avoid: list name):
    list unit * unit -> name :=
    run_using_prefix (to_name_from_history avoid).

  (** *** Relation between <<to_history_from_ctx>> and <<to_name_from_ctx>> *)
  (********************************************************************)
  Lemma to_history_from_ctx_spec (avoid: list name):
    to_history_from_ctx avoid =
      mapdz (T := list) (to_name_from_ctx avoid).
  Proof.
    unfold to_name_from_ctx.
    rewrite run_using_prefix_spec.
    reflexivity.
  Qed.

  Lemma to_name_from_ctx_spec (avoid: list name) (ctx: list unit) (a: unit):
    to_name_from_ctx avoid (ctx, a) =
      to_name_from_history avoid (to_history_from_ctx avoid ctx, a).
  Proof.
    reflexivity.
  Qed.

  (** *** Rewriting rules for <<to_name_from_ctx>> *)
  (********************************************************************)
  Lemma to_name_from_ctx_rw_nil (avoid: list name): forall (u: unit),
      to_name_from_ctx (avoid) (nil, u) =
        fresh avoid.
  Proof.
    intros.
    cbn.
    rewrite List.app_nil_r.
    reflexivity.
  Qed.

  Lemma to_name_from_ctx_rw_cons (avoid: list name): forall (u: unit) (rest: list unit) (u': unit),
      to_name_from_ctx avoid (u :: rest, u') =
        fresh (avoid ++ fresh avoid :: to_history_from_ctx (avoid ++ [fresh avoid]) rest).
  Proof.
    intros.
    unfold to_name_from_ctx.
    unfold run_using_prefix.
    rewrite fold_with_history_cons.
    unfold to_name_from_history at 1.
    unfold to_name_from_history at 1.
    rewrite List.app_nil_r.
    rewrite to_history_from_ctx_preincr.
    rewrite to_name_from_history_nil.
    reflexivity.
  Qed.

  (** *** Freshness for <<to_name_from_ctx>> *)
  (********************************************************************)
  Lemma to_name_from_ctx_fresh (avoid: list name) (prefix: list unit) (u: unit):
    ~ to_name_from_ctx avoid (prefix, u) ∈ avoid.
  Proof.
    intros.
    unfold to_name_from_ctx.
    intro contra.
    unfold run_using_prefix in contra.
    specialize (to_name_from_history_fresh avoid
                  (fold_with_history (to_name_from_history avoid) prefix, u)).
    intro Hyp.
    apply Hyp.
    assumption.
  Qed.

End to_name_from_history.


(** * Converting a depth to (list unit) binding context *)
(**********************************************************************)
Fixpoint length_to_list_unit (length: nat): list unit :=
  match length with
  | 0 => nil
  | S n => tt :: length_to_list_unit n
  end.


(** * Local Translations *)
(**********************************************************************)
Section with_DTM.

  Context
    (T: Type -> Type -> Type)
    `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Import Kleisli.DecoratedFunctorPoly.
  Import Categorical.DecoratedFunctor.
  Import CategoricalToKleisli.DecoratedFunctorPoly.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.
  Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.
  Import PolyToMono.Categorical.DecoratedFunctor.ToMono1.
  Import PolyToMono.Categorical.TraversableFunctor.ToMono.
  Import PolyToMono.Kleisli.DecoratedFunctor.ToMono1.
  Import PolyToMono.Kleisli.DecoratedFunctor.ToMono2.
  Import CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.TraversableFunctor.DerivedInstances.
  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.

  Existing Instance Theory.DecoratedTraversableFunctor.ToCtxset_Mapdt.
  Existing Instance Theory.TraversableFunctor.ToSubset_Traverse.

  Instance Decorate_MONO:
    Decorate nat (T unit).
  Proof.
    intros A t.
    apply (dec (E := list unit)) in t; try typeclasses eauto.
    exact (map (F := T unit) (map_fst (@length unit)) t).
  Defined.

  Fail Import Categorical.DecoratedTraversableFunctorPoly.ToMono.

  Context `{! DecoratedTraversableFunctor (list atom) (T atom)}. (* TODO Infer this *)

  (** ** Nominal to Locally Nameless *)
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

  (** ** Locally Nameless to Nominal *)
  (********************************************************************)
  (* crash hard, crash often *)
  Definition PANIC_INDEX_EXCEEDS_CONTEXT: nat := 1337.

  (* Give a DB index (Bd N), define its new name *)
  Definition LN_BD_to_binder_name (avoid: list name) (ctx: list unit) (n: nat): atom :=
    if Nat.ltb n (length ctx)
    then to_name_from_ctx avoid (length_to_list_unit (length ctx - (n + 1)), tt)
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
    apply to_name_from_ctx_fresh in Hin.
    assumption.
  Qed.

  Definition ln_to_name (avoid: list name):
    list unit * LN -> name :=
    fun '(depth, v) =>
      match v with
      | Fr x => x
      | Bd n => LN_BD_to_binder_name avoid depth n
      end.

  Definition term_ln_to_nominal (conflicts: list name):
    T unit LN -> T name name :=
    mapdp (T := T)
      (to_name_from_ctx conflicts)
      (ln_to_name conflicts).


  (** ** Roundtrip Specifications *)
  (********************************************************************)
  (* The operation mapping a nominal term to a locally nameless term, then back again into a nominal term *)
  Definition roundtrip_Nominal:
    T name name -> T name name :=
    fun t => let t_ln := term_nominal_to_ln t
          in term_ln_to_nominal (LN.free t_ln) t_ln.

  Lemma roundtrip_Nominal_spec1:
    forall (t: T name name),
      roundtrip_Nominal t =
        mapdp
          (kc_dz (to_name_from_ctx (free (term_nominal_to_ln t))) (const tt))
          (kc_dfunp (ln_to_name (free (term_nominal_to_ln t))) (const tt) name_to_ln) t.
  Proof.
    intros.
    unfold roundtrip_Nominal.
    compose near t on left.
    unfold term_nominal_to_ln at 2.
    unfold term_ln_to_nominal at 1.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  (** ** Decomposed into a Variable Op and Binder Op *)
  (********************************************************************)
  (* Given a binding occurrence (pre, b) in a nominal term t,
     return the new name of b after a Nominal~>LN~>Nominal roundtrip *)
  Section avoid.

    Context (avoid: list atom).

    Definition roundtrip_Binder_loc: Z atom -> atom :=
      to_name_from_ctx avoid ∘ map (const tt).

    (* Given a variable occurrence (pre, v) in a nominal term t,
     return the new name of v after a Nominal~>LN~>Nominal roundtrip *)
    Definition roundtrip_Var_loc: Z2 atom atom -> atom :=
      kc_dfunp (ln_to_name avoid) (const tt) name_to_ln.

    Lemma roundtrip_Binder_loc_spec:
      mapdz (T := list) roundtrip_Binder_loc =
        to_history_from_ctx avoid ∘ map (const tt).
    Proof.
      intros.
      unfold roundtrip_Binder_loc.
      rewrite to_history_from_ctx_spec.
      Set Keyed Unification.
      rewrite (mapdz_map_list (A' := atom) (B := atom) (A := unit)).
      Unset Keyed Unification.
      reflexivity.
    Qed.

  End avoid.

  Lemma roundtrip_Nominal_spec_decomposed:
    forall (t: T name name),
      roundtrip_Nominal t =
        let avoid := LN.free (term_nominal_to_ln t)
        in rename_binders
             (roundtrip_Binder_loc avoid)
             (mapd (T := T name) (roundtrip_Var_loc avoid) t).
  Proof.
    intros.
    rewrite roundtrip_Nominal_spec1.
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
      (mapdz (roundtrip_Binder_loc avoid) ctx, roundtrip_Var_loc avoid (ctx, a)).

  Lemma roundtrip_Occ_spec (avoid: list atom): forall ctx a,
      roundtrip_Occ avoid (ctx, a) =
        (map_fst (mapdz (T := list) (roundtrip_Binder_loc avoid))
           (cobind (W := prod (list atom)) (roundtrip_Var_loc avoid) (ctx, a))).
  Proof.
    intros.
    unfold roundtrip_Occ.
    unfold cobind.
    reflexivity.
  Qed.

  Lemma roundtrip_Nominal_var_spec {avoid: list atom}:
    (kc_dfunp
       (ln_to_name avoid)
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


  (** ** Lemma About Mapdtp with Constant Applicatives *)
  (**********************************************************************)
  Section constant_applicatives.

    Context
      {M} `{Monoid M}.

    Import Categorical.TraversableFunctor2.

    Lemma mapdtp_const1:
      forall {A1 B1: Type} (A2 B2: Type) `(g: list B1 * B1 -> M) `(f: list B1 * A1 -> M),
        mapdtp (G := const M) (B2 := False) (A2 := False) g f =
          mapdtp (G := const M) (B2 := B2) (A2 := A2) g f.
    Proof.
      intros.
      change_left
        (map (F := const M)
           (A := T False False)
           (B := T B2 A2)
           (map2 (F := T) (B1 := False) (A1 := False) (B2 := B2) (A2 := A2) exfalso exfalso)
           ∘ mapdtp (T := T) (G := const M) g f).
      unfold mapdtp.
      unfold DerivedOperations.Mapdtp_Categorical.
      reassociate <- on left.
      reassociate <- on left.
      unfold compose.
      ext t.
      rewrite <- dist2_natural_rw.
      compose near (decp t).
      rewrite fun2_map_map.
      fequal.
    Qed.


    Lemma mapdtp_const_normalize:
      forall {A1 B1: Type} (A2 B2: Type) `(g: list B1 * B1 -> M) `(f: list B1 * A1 -> M),
        mapdtp (G := const M) (B2 := B2) (A2 := A2) g f =
          mapdtp (G := const M) (B2 := False) (A2 := False) g f.
    Proof.
      intros.
      symmetry.
      apply mapdtp_const1.
    Qed.

  End constant_applicatives.

  (** ** Relating Free Variables During Translation *)
  (********************************************************************)
  Lemma normalize_foldMap {M} `{Monoid M} `(f: list name * name -> M): forall (t: T name name),
      foldMapd f t = mapdtp (A2 := False) (G := const M) (T := T) (pure (F := const M) ∘ (const tt)) f t.
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    unfold mapdt.
    unfold Mapdt_Categorical.
    unfold_ops @Dist2_1.
    unfold_ops @Decorate_PolyVar.
    change_left ((TraversableFunctor2.dist2 (B := atom) (A := False) ∘ (map2 pure id ∘ map f ∘ map2 extract id) ∘ decp) t).
    rewrite fun2_map2_map21.
    rewrite fun2_map_map.
    change (id ∘ ?f) with f.
    change (f ∘ ?id) with f.
    change_left ((mapdtp (B2 := atom) (A2 := False) (B1 := atom) (A1 := atom) (pure (F := const M)) f) t).
    pose @mapdtp_const_normalize.
    specialize (e M _ _ H3).
    specialize (e atom atom False atom).
    rewrite e.
    clear e.
    pose @mapdtp_const_normalize.
    specialize (e M _ _ H3).
    specialize (e atom atom False unit).
    rewrite e.
    clear e.
    reflexivity.
  Qed.

  Lemma FV_preserved: forall (t: T name name),
      FV t =
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
    unfold DerivedOperations.Mapdtp_Categorical.
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
    }
    rewrite cut.
    reflexivity.
  Qed.

  (** ** Alpha Equivalence Local Reasoning *)
  (********************************************************************)
  Lemma to_name_from_ctx_preincr: forall avoid a,
      to_name_from_ctx avoid ∘ cobind (W := Z) (const tt) ∘ incr [a] =
        to_name_from_ctx (avoid ++ [fresh avoid]) ∘ cobind (const tt).
  Proof.
    intros.
    ext [ctx x].
    unfold compose.
    unfold to_name_from_ctx.
  Abort.

  (** *** Specification of <<roundtrip_Occ>> *)
  (********************************************************************)
  Lemma roundtrip_Occ_spec_pw: forall (avoid: list atom) (ctx: list atom) (a: atom),
      roundtrip_Occ avoid (ctx, a) =
        (mapdz (roundtrip_Binder_loc avoid) ctx, roundtrip_Var_loc avoid (ctx, a)).
  Proof.
    unfold roundtrip_Occ.
    reflexivity.
  Qed.

  (** *** Specification of <<roundtrip_Occ>> when a is unbound *)
  (********************************************************************)
  Lemma roundtrip_Occ_Unbound_spec: forall (avoid: list atom) (ctx: list atom) (a: atom),
      get_binding ctx a = Unbound ctx a ->
      roundtrip_Occ avoid (ctx, a) = (mapdz (roundtrip_Binder_loc avoid) ctx, a).
  Proof.
    introv Hyp.
    rewrite roundtrip_Occ_spec_pw.
    fequal.
    cbn.
    rewrite Hyp.
    reflexivity.
  Qed.

  (** *** Specification of <<roundtrip_Var_loc>> when a is bound *)
  (********************************************************************)
  Lemma roundtrip_Var_loc_Bound_spec: forall (avoid: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      ctx = prefix ++ [a'] ++ postfix ->
      a = a' ->
      roundtrip_Var_loc avoid (ctx, a) =
        to_name_from_history avoid (to_history_from_ctx avoid (map (const tt) prefix), tt).
  Proof.
    introv Hbinding Hctx Haeq.
    unfold to_name_from_history.
    unfold roundtrip_Var_loc.
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
    unfold to_name_from_ctx.
    unfold run_using_prefix.
    unfold to_name_from_history.
    fequal.
    fequal.
    unfold to_history_from_ctx.
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

  (** *** Specification of <<get_binding ∘ roundtrip_Occ>> when a is unbound *)
  (********************************************************************)
  Lemma roundtrip_Occ_get_binding_Unbound_spec:
    forall (avoid: list atom) (ctx: list atom) (a: atom),
      a ∈ avoid ->
      get_binding ctx a = Unbound ctx a ->
      match roundtrip_Occ avoid (ctx, a) with
      | (foo, x) =>
          get_binding foo x = Unbound (mapdz (roundtrip_Binder_loc avoid) ctx) a
      end.
  Proof.
    introv Hnin Hyp.
    rewrite roundtrip_Occ_Unbound_spec; auto.
    destruct (get_binding_spec (mapdz (roundtrip_Binder_loc avoid) ctx) a)
      as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin']]]]].
    { rewrite Case1.
      reflexivity. }
    { assert (Hfresh: ~ a ∈ mapdz (roundtrip_Binder_loc avoid) ctx).
      { rewrite roundtrip_Binder_loc_spec.
        unfold compose at 1.
        apply to_history_from_ctx_fresh.
        assumption.
      }
      apply get_binding1 in Hfresh.
      assumption.
    }
  Qed.

  (** *** Specification of <<get_binding ∘ roundtrip_Occ>> when a is bound *)
  (********************************************************************)
  Lemma roundtrip_Occ_get_binding_Bound_spec:
    forall (avoid: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      a = a' ->
      ctx = prefix ++ [a'] ++ postfix ->
      ~ a ∈ postfix ->
      match roundtrip_Occ avoid (ctx, a) with
      | (foo, x) =>
          let NewPrefix := to_history_from_ctx avoid (map (const tt) prefix)
          in let NewVar := to_name_from_history avoid (NewPrefix, tt)
             in let NewPost := to_history_from_ctx (avoid ++ NewPrefix ++ [NewVar]) (map (const tt) postfix)
                in get_binding foo x = Bound NewPrefix NewVar NewPost /\ length NewPrefix = length prefix
      end.
  Proof.
    introv Hyp Haeq Hctxeq Hnin.
    remember (roundtrip_Occ avoid (ctx, a)).
    destruct p.
    rewrite roundtrip_Occ_spec_pw in Heqp.
    injection Heqp; introv Hctx' HVar'.
    clear Heqp.
    intros NewPrefix NewVar NewPost.
    split.
    { assert
        (HRoundtripMapsToNewVar:
          roundtrip_Var_loc avoid (prefix ++ [a'] ++ postfix, a') = NewVar).
      { subst.
        unfold NewVar.
        unfold NewPrefix.
        eapply roundtrip_Var_loc_Bound_spec;
          eauto.
      }
      apply get_binding2.
      - subst. apply HRoundtripMapsToNewVar.
      - subst.
        rewrite roundtrip_Binder_loc_spec.
        unfold compose.
        rewrite map_list_app.
        rewrite map_list_app.
        rewrite map_list_one.
        change (const tt a') with tt.
        rewrite to_history_from_ctx_decompose.
        fold NewPrefix.
        fold NewVar.
        fold NewPost.
        rewrite HRoundtripMapsToNewVar.
        reflexivity.
      - apply to_history_from_ctx_fresh.
        rewrite element_of_list_app.
        rewrite element_of_list_app.
        right; right.
        rewrite element_of_list_one.
        subst.
        assumption.
    }
    { unfold NewPrefix.
      rewrite length_to_history_from_ctx.
      rewrite map_preserve_length.
      reflexivity.
    }
  Qed.

  Lemma rt_correct_local2:
    forall (t: T name name) (avoid: list name)
      (Havoidinit: forall (a: name), (a ∈ FV t -> a ∈ avoid)),
    forall (ctx: list name) (a: name),
      (ctx, a) ∈ (dec (T atom) t) ->
      alpha_equiv_local (ctx, a) (roundtrip_Occ avoid (ctx, a)).
  Proof.
    introv HFV.
    introv Hin.
    unfold alpha_equiv_local.
    destruct (get_binding_spec ctx a) as [[Case1 Hanin] | [prefix [postfix [Case2 [ctxspec Hnin]]]]].
    { rewrite Case1.
      assert (Havoid: a ∈ avoid).
      { apply HFV.
        apply (FV_lift_local _ ctx); auto.
      }
      specialize (roundtrip_Occ_get_binding_Unbound_spec avoid ctx a Havoid Case1).
      intro X.
      destruct (roundtrip_Occ avoid (ctx, a)).
      rewrite X. destruct_eq_args a a.
    }
    {
      rewrite Case2.
      apply (roundtrip_Occ_get_binding_Bound_spec avoid) in Case2; auto.
      destruct (roundtrip_Occ avoid (ctx, a)).
      destruct Case2 as [Case2RW Case2Len].
      rewrite Case2RW.
      rewrite Case2Len.
      destruct_eq_args (length prefix) (length prefix).
    }
  Qed.

  Lemma rt_correct_local1:  forall (t: T name name),
      TraversableFunctor.Forall
        (fun a: list atom * atom =>
           (precompose (cobind (W := prod (list atom)) (roundtrip_Var_loc (free (term_nominal_to_ln t))))
              ∘ (precompose (map_fst (mapdz (roundtrip_Binder_loc (free (term_nominal_to_ln t))))) ∘ alpha_equiv_local)) a a)
        (delete_binders (dec (T atom) t)).
  Proof.
    intros t.
    rewrite TraversableFunctor.forall_iff.
    intros [ctx a].
    rewrite in_del_binders.
    unfold compose, precompose.
    rewrite <- roundtrip_Occ_spec.
    apply rt_correct_local2.
    clear a.
    introv HinFV.
    rewrite (FV_preserved t) in HinFV.
    assumption.
  Qed.

  Theorem roundtrip_correct: forall (t: T name name),
      polymorphic_alpha T t (roundtrip_Nominal t).
  Proof.
    intros.
    rewrite (roundtrip_Nominal_spec_decomposed).
    unfold polymorphic_alpha.
    unfold lift_relation_ctx_poly.
    rewrite (decorate_rename_binders2).
    rewrite TraversableFunctor.relation_natural2.
    rewrite (CategoricalToKleisli.DecoratedFunctor.dec_mapd2 (list atom) (F := T atom)).
    rewrite delete_binders_map.
    rewrite relation_natural2.
    apply relation_diagonal1.
    apply rt_correct_local1.
  Qed.


  Theorem roundtrip_correct2: forall (t: T name name),
      polymorphic_alpha T t (term_ln_to_nominal (free (term_nominal_to_ln t)) (term_nominal_to_ln t)).
  Proof.
    intros.
    unfold roundtrip_Nominal.
    apply roundtrip_correct.
  Qed.

  Print Assumptions roundtrip_correct.

  (** ** Roundtrip in the Other Direction *)
  (********************************************************************)
  Definition roundtrip_LN:
    T unit LN -> T unit LN :=
    fun t => let t_nom := term_ln_to_nominal (LN.free t) t
          in term_nominal_to_ln t_nom.

  Lemma roundtrip_LN_spec1:
    forall (t: T unit LN),
      roundtrip_LN t =
        mapdp (kc_dz (const tt) (to_name_from_ctx (free t)))
          (kc_dfunp name_to_ln (to_name_from_ctx (free t)) (ln_to_name (free t))) t.
  Proof.
    intros.
    unfold roundtrip_LN.
    compose near t on left.
    unfold term_nominal_to_ln at 1.
    unfold term_ln_to_nominal at 1.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  Lemma roundtrip_LN_spec_decomposed:
    forall (t: T unit LN),
      roundtrip_LN t =
        let avoid := free t
        in (rename_binders (const tt)
           (mapd (T := T unit) (kc_dfunp (T := T)
                                  name_to_ln
                                  (to_name_from_ctx avoid)
                                  (ln_to_name avoid)) t)).
  Proof.
    intros.
    rewrite roundtrip_LN_spec1.
    unfold kc_dz.
    change (const tt ∘ cobind (to_name_from_ctx (free t)))
      with (const (A := list unit * unit) tt).
    rewrite mapd_decompose.
    reflexivity.
  Qed.

  Lemma roundtrip_LN_spec_decomposed2:
    forall (t: T unit LN),
      roundtrip_LN t =
        let avoid := free t
        in (mapd (T := T unit)
              (kc_dfunp (T := T)
                 name_to_ln
                 (to_name_from_ctx avoid)
                 (ln_to_name avoid)) t).
  Proof.
    intros.
    rewrite roundtrip_LN_spec_decomposed.
    assert (Hren: rename_binders (V1 := LN) (T := T) (const tt (A := list unit * unit)) = id).
    { unfold rename_binders.
      assert (Hconst: const tt (A := list unit * unit) = extract).
      { ext [? u]. cbv.
        destruct u. reflexivity. }
      rewrite Hconst.
      rewrite kdz_mapdz1.
      reflexivity.
    }
    rewrite Hren.
    reflexivity.
  Qed.

  Context
    `{! Compat_Map_Mapd (list unit) (T unit)}
      `{! DecoratedContainerFunctor (list unit) (T unit)}.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.

  Lemma length_length_to_list_unit: forall n,
      length (length_to_list_unit n) = n.
  Proof.
    intros. induction n.
    - reflexivity.
    - cbn. fequal; auto.
  Qed.

  Lemma get_binding_LN_rt2: forall (l: list atom) (ctx: list unit) (n: nat),
      n < length ctx ->
      (get_binding (to_history_from_ctx l ctx)
         (to_name_from_ctx l (length_to_list_unit (length ctx - (n + 1)), tt))) =
        Bound
          (to_history_from_ctx l (length_to_list_unit (length ctx - (n + 1))))
          (to_name_from_ctx l (length_to_list_unit (length ctx - (n + 1)), tt))
          (to_history_from_ctx l (length_to_list_unit n)).
  Proof.
    introv Hlt.
    induction ctx.
    - false.
      inversion Hlt.
    - cbn in Hlt.
      change (length (?x :: ?xs)) with (S (length xs)).

      admit.
  Admitted.

  Lemma get_binding_LN_rt1: forall (l: list atom) (ctx: list unit) (n: nat),
      n < length ctx ->
      binding_to_ln
      (get_binding (to_history_from_ctx l ctx)
         (to_name_from_ctx l (length_to_list_unit (length ctx - (n + 1)), tt))) =
        Bd n.
  Proof.
    intros.
    rewrite get_binding_LN_rt2; auto.
    unfold binding_to_ln.
    rewrite length_to_history_from_ctx.
    rewrite length_length_to_list_unit.
    reflexivity.
  Qed.

  Lemma decompose_list_by_ix: forall (A: Type) (l: list A) (n: nat),
      n < length l ->
      exists pre a post, l = pre ++ [a] ++ post /\
                      length post = n.
  Proof.
    introv Hlt.
    induction l.
    - false.
      inversion Hlt.
    - cbn in Hlt.
      compare naturals n and (length l).
      { apply IHl in ineqp.
        destruct ineqp as [pre [a' [post [Heq Hrest]]]].
        exists (a :: pre) a' post; split; auto.
        rewrite Heq.
        rewrite List.app_comm_cons.
        reflexivity.
      }
      { exists (@nil A)  a l.
        rewrite List.app_nil_l.
        auto.
      }
  Qed.

  Lemma get_binding_LN_new2: forall (l: list atom) (pre: list unit) (post: list unit),
      (get_binding
         (to_history_from_ctx l pre ++
            [to_name_from_history l (to_history_from_ctx l pre, tt)] ++
            to_history_from_ctx
            (l ++ to_history_from_ctx l pre ++ [to_name_from_history l (to_history_from_ctx l pre, tt)]) post)
         (to_name_from_history l (to_history_from_ctx l pre, tt)))
      =  Bound
           (to_history_from_ctx l pre)
           (to_name_from_history l (to_history_from_ctx l pre, tt))
           (to_history_from_ctx
              (l ++ to_history_from_ctx l pre ++ [to_name_from_history l (to_history_from_ctx l pre, tt)]) post).
  Proof.
    intros.
    apply get_binding2.
    - reflexivity.
    - reflexivity.
    - apply  to_history_from_ctx_fresh.
      rewrite element_of_list_app.
      rewrite element_of_list_app.
      rewrite element_of_list_one.
      right. right. reflexivity.
  Qed.

  Lemma get_binding_LN_new: forall (l: list atom) (ctx: list unit) (n: nat),
      n < length ctx ->
      binding_to_ln
      (get_binding (to_history_from_ctx l ctx)
         (to_name_from_ctx l (length_to_list_unit (length ctx - (n + 1)), tt))) =
        Bd n.
  Proof.
    introv Hin.
    apply decompose_list_by_ix in Hin.
    destruct Hin as [pre [a [post [Heq Hlen]]]].
    (*
    intro cut.
    rewrite Heq.
    rewrite cut.
    assert (Hlen_spec: length (pre ++ [a] ++ post) - (n + 1) = length pre).
    { subst.
      rewrite List.app_length.
      rewrite List.app_length.
      cbn.
      lia.
    }
    rewrite Hlen_spec.
    rewrite to_name_from_ctx_spec.

    assert (Hpre: length_to_list_unit (length pre) = pre).
    { admit. }
    rewrite Hpre.
    assert (Ha: a = tt).
    { now destruct a. }
    rewrite Ha.
    rewrite get_binding_LN_new2.
    unfold binding_to_ln.
    rewrite length_to_history_from_ctx.
    auto.
   *)
  Admitted.

  Lemma roundtrip_LN_id: forall (t: T unit LN),
      LC t ->
      roundtrip_LN t = t.
  Proof.
    introv HLC.
    rewrite roundtrip_LN_spec_decomposed2.
    remember (free t).
    cbn zeta.
    apply mapd_respectful_id.
    intros ctx v Hin.
    unfold kc_dfunp.
    unfold compose at 1.
    unfold cobind_Z2, cojoin_Z2, compose at 1.
    unfold map_Z2.
    compose near ctx on left.
    unfold_Z.
    rewrite <- mapd_list_prefix_spec.
    change (mapd_list_prefix (to_name_from_ctx l) ctx)
      with (mapdz (to_name_from_ctx l) ctx).
    rewrite <- to_history_from_ctx_spec.
    unfold name_to_ln.
    destruct v as [a | n].
   - unfold ln_to_name.
      destruct (get_binding_spec (to_history_from_ctx l ctx) a)
        as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin']]]]].
      + rewrite Case1.
        cbn.
        reflexivity.
      + specialize (to_history_from_ctx_fresh l) as lemma.
        false.
        assert (a_in_list: a ∈ l).
        { subst.
          admit.
        }
        specialize (lemma ctx a a_in_list).
        subst.
        rewrite ctxspec in lemma.
        apply lemma.
        rewrite element_of_list_app.
        rewrite element_of_list_app.
        right.
        left.
        rewrite element_of_list_one.
        reflexivity.
    - unfold ln_to_name.
      unfold LN_BD_to_binder_name.
      assert (H_n_lt: Nat.ltb n (length ctx) = true).
      { rewrite OrdersEx.Nat_as_OT.ltb_lt.
        unfold LC in HLC.
        unfold LCn in HLC.
        specialize (HLC (length ctx)).
        specialize (HLC (Bd n)).
        assert (cut: (length ctx, Bd n) ∈d t).
        { admit. }
        apply HLC in cut.
        unfold lc_loc in cut.
        lia.
      }
      rewrite H_n_lt.
      rewrite get_binding_LN_rt1; auto.
      rewrite <- OrdersEx.Nat_as_OT.ltb_lt.
      assumption.
  Admitted.


  Lemma roundtrip_LN_correct: forall (t: T unit LN),
      LC t ->
      term_nominal_to_ln (term_ln_to_nominal (free t) t) = t.
  Proof.
    introv HLC.
    unfold roundtrip_LN.
    apply roundtrip_LN_id.
    assumption.
  Qed.

  Theorem correctness1: forall (t u: T name name),
      term_nominal_to_ln t = term_nominal_to_ln u -> polymorphic_alpha T t u.
  Proof.
    introv Heq.
    assert (cut1: polymorphic_alpha T t (term_ln_to_nominal (FV t) (term_nominal_to_ln t))).
    { pose roundtrip_correct2.
      rewrite FV_preserved.
      admit.
    }
    assert (cut2: polymorphic_alpha T u (term_ln_to_nominal (FV u) (term_nominal_to_ln u))).
    { pose roundtrip_correct2.
      rewrite FV_preserved.
      admit.
    }
    rewrite Heq in *.
    assert (HFV: FV t = FV u).
    { rewrite  FV_preserved.
      rewrite  FV_preserved.
      rewrite Heq.
      reflexivity.
    }
    rewrite HFV in cut1.
  Admitted.

  Theorem correctness2: forall (t u: T name name),
      polymorphic_alpha T t u -> term_nominal_to_ln t = term_nominal_to_ln u.
  Proof.
    introv Halpha.
  Abort.

End with_DTM.
