From Tealeaves Require Import
  Backends.LN
  Backends.Nominal.Common.Hmap
  Backends.Nominal.Common.Freshening
  Backends.Nominal.Common.Binding
  Backends.Common.Names
  Backends.Nominal.FV
  Backends.Nominal.Alpha
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

(** ** Lemma About Mapdtp with Constant Applicatives *)
(**********************************************************************)
Section constant_applicatives.

  Context
    `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Context
    {M} `{Monoid M}.

  Import Categorical.TraversableFunctor2.
  Import Adapters.PolyToMono.Categorical.TraversableFunctor.ToMono (dist2_natural_rw).
  Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.

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

(*
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
*)

(** * Converting a depth to (list unit) binding context *)
(**********************************************************************)
Fixpoint length_to_list_unit (length: nat): list unit :=
  match length with
  | 0 => nil
  | S n => tt :: length_to_list_unit n
  end.

Lemma length_length_to_list_unit: forall n,
    length (length_to_list_unit n) = n.
Proof.
  intros. induction n.
  - reflexivity.
  - cbn. fequal; auto.
Qed.

Lemma length_cons {A} {a:A} {l: list A}:
  length (a :: l) = S (length l).
Proof.
  reflexivity.
Qed.

Lemma length_one {A} {a:A}:
  length [a] = 1.
Proof.
  reflexivity.
Qed.

Lemma length_to_list_unit_plus {n m: nat}:
  length_to_list_unit (n + m) =
    length_to_list_unit n ++
      length_to_list_unit m.
Proof.
  induction n.
  - reflexivity.
  - cbn. rewrite IHn.
    reflexivity.
Qed.

Lemma length_to_list_unit_S (n: nat):
  length_to_list_unit (S n) = tt :: length_to_list_unit n.
Proof.
  reflexivity.
Qed.

Lemma length_list_unit_iso (ctx: list unit):
  ctx = length_to_list_unit (length ctx).
Proof.
  induction ctx.
  - reflexivity.
  - cbn. destruct a.
    rewrite IHctx.
    rewrite length_length_to_list_unit.
    reflexivity.
Qed.


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
  Definition bdToName (Γ: list name) (ctx: list unit) (n: nat): atom :=
    if Nat.ltb n (length ctx)
    then assignNames_loc Γ (length_to_list_unit (length ctx - (n + 1)), tt)
    else PANIC_INDEX_EXCEEDS_CONTEXT.

  Lemma bdToName_fresh: forall Γ a ctx n,
      length ctx > n ->
      a ∈ Γ -> bdToName Γ ctx n <> a.
  Proof.
    introv Hlt Hin.
    unfold bdToName.
    apply PeanoNat.Nat.ltb_lt in Hlt.
    rewrite Hlt.
    intro contra.
    subst.
    apply assignNames_loc_fresh in Hin.
    assumption.
  Qed.

  Definition lnToName (Γ: list name):
    list unit * LN -> name :=
    fun '(depth, v) =>
      match v with
      | Fr x => x
      | Bd n => bdToName Γ depth n
      end.

  Definition term_ln_to_nominal (Γ: list name):
    T unit LN -> T name name :=
    mapdp (T := T) (assignNames_loc Γ) (lnToName Γ).

  (** ** Roundtrip from Nominal *)
  (********************************************************************)
  (* The operation mapping a nominal term to a locally nameless term, then back again into a nominal term *)
  Definition rtFromNominal: T name name -> T name name :=
    fun t =>
      let t_ln := term_nominal_to_ln t
      in term_ln_to_nominal (LN.free t_ln) t_ln.

  Lemma rtFromNominal_spec:
    forall (t: T name name),
      rtFromNominal t =
        let Γ := free (term_nominal_to_ln t)
        in mapdp
             (kc_dz (assignNames_loc Γ) (const tt))
             (kc_dfunp (lnToName Γ) (const tt) name_to_ln) t.
  Proof.
    intros.
    unfold rtFromNominal.
    compose near t on left.
    unfold term_nominal_to_ln at 2.
    unfold term_ln_to_nominal at 1.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  (** ** Decomposed into a Variable Operation and Binder Operation *)
  (********************************************************************)
  (* Given a binding occurrence (pre, b) in a nominal term t,
     return the new name of b after a Nominal~>LN~>Nominal roundtrip *)
  Section roundtrip_decompose.

    Context (Γ: list atom).

    Definition roundtrip_Binder_loc: Z atom -> atom :=
      assignNames_loc Γ ∘ map (const tt).

    (* Given a variable occurrence (pre, v) in a nominal term t,
     return the new name of v after a Nominal~>LN~>Nominal roundtrip *)
    Definition roundtrip_Var_loc: Z2 atom atom -> atom :=
      kc_dfunp (lnToName Γ) (const tt) name_to_ln.

    Lemma roundtrip_Binder_loc_spec:
      mapdz (T := list) roundtrip_Binder_loc =
        assignNames Γ ∘ map (const tt).
    Proof.
      intros.
      unfold roundtrip_Binder_loc.
      rewrite assignNames_spec.
      Set Keyed Unification.
      rewrite (mapdz_map_list (A' := atom) (B := atom) (A := unit)).
      Unset Keyed Unification.
      reflexivity.
    Qed.

  End roundtrip_decompose.

  Lemma rtFromNominal_spec_decomposed:
    forall (t: T name name),
      rtFromNominal t =
        let Γ := LN.free (term_nominal_to_ln t)
        in rename_binders (roundtrip_Binder_loc Γ)
             (mapd (T := T name) (roundtrip_Var_loc Γ) t).
  Proof.
    intros.
    rewrite rtFromNominal_spec.
    unfold kc_dz.
    rewrite cobind_Z_const.
    rewrite mapd_decompose.
    reflexivity.
  Qed.

  (** ** Roundtrip effect on context occurrences *)
  (* if (ctx, a) ∈d t, then (rtFromNominal_occ (free t) (ctx, a)) ∈d roundtrip t *)
  (********************************************************************)
  Definition rtFromNominal_occ (Γ: list atom):
    list atom * atom -> list atom * atom :=
    fun '(ctx, a) =>
      (mapdz (roundtrip_Binder_loc Γ) ctx, roundtrip_Var_loc Γ (ctx, a)).

  Lemma rtFromNominal_occ_spec (Γ: list atom): forall ctx a,
      rtFromNominal_occ Γ (ctx, a) =
        (map_fst (mapdz (T := list) (roundtrip_Binder_loc Γ))
           (cobind (W := prod (list atom)) (roundtrip_Var_loc Γ) (ctx, a))).
  Proof.
    intros.
    unfold rtFromNominal_occ.
    unfold cobind.
    reflexivity.
  Qed.

  Lemma rtFromNominal_occ_spec_pw: forall (Γ: list atom) (ctx: list atom) (a: atom),
      rtFromNominal_occ Γ (ctx, a) =
        (mapdz (roundtrip_Binder_loc Γ) ctx, roundtrip_Var_loc Γ (ctx, a)).
  Proof.
    unfold rtFromNominal_occ.
    reflexivity.
  Qed.

  Lemma rtFromNominal_var_spec {Γ: list atom}:
    (kc_dfunp
       (lnToName Γ)
       (const tt)
       name_to_ln) =
      fun '(ctx, nm) =>
        match binding_to_ln (get_binding ctx nm) with
        | Fr x => x
        | Bd n => bdToName Γ (map (const tt) ctx) n
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

  (** ** Specification for Decoration After Renaming Binders *)
  (********************************************************************)
  Lemma decorate_rename_binders {B1 B2 V}:
    forall (ρ: list B1 * B1 -> B2) (t: T B1 V),
      delete_binders (dec (T B2) (rename_binders ρ t)) =
        delete_binders (map (F := T B1) (map_fst (mapdz (T := list) ρ)) (dec (T B1) t)).
  Proof.
    intros.
    unfold delete_binders.
    unfold bmap.
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
    unfold bmap.
    rewrite fun2_map22_map21_commute.
    reflexivity.
  Qed.


  (** *** Occurence Relation After Deleting Binders *)
  (********************************************************************)
  Lemma in_del_binders {B A}: forall (t: T B A) (a: A),
      element_of a (delete_binders t) = element_of a t.
  Proof.
    intros.
    unfold delete_binders.
    unfold bmap.
    unfold element_of.
    rewrite tosubset_to_mapReduce.
    rewrite tosubset_to_mapReduce.
    rewrite mapReduce_to_traverse1.
    rewrite mapReduce_to_traverse1.
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
  Lemma normalize_mapReduce {M} `{Monoid M} `(f: list name * name -> M): forall (t: T name name),
      mapdReduce f t = mapdtp (A2 := False) (G := const M) (T := T) (pure (F := const M) ∘ (const tt)) f t.
  Proof.
    intros.
    rewrite mapdReduce_to_mapdt1.
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
    pose (cut := mapdtp_const_normalize False (A1 := atom) (B1 := atom) atom).
    rewrite cut.
    clear cut.
    pose (cut := mapdtp_const_normalize False (A1 := atom) (B1 := atom) unit).
    rewrite cut.
    clear cut.
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
    rewrite (mapReduce_to_traverse1).
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
    rewrite fun2_map_map.
    rewrite normalize_mapReduce.
    unfold mapdtp.
    unfold DerivedOperations.Mapdtp_Categorical.
    unfold compose.
    assert (cut: FV_loc = free_loc ∘ name_to_ln).
    { ext [l v].
      unfold compose.
      unfold name_to_ln.
      destruct (get_binding_spec_proof l v) as [[Hbinding Hspec] | [pre [post [Hbinding [Hspec1 Hspec2]]]]].
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
  Lemma assignNames_loc_preincr: forall Γ a,
      assignNames_loc Γ ∘ cobind (W := Z) (const tt) ∘ incr [a] =
        assignNames_loc (Γ ++ [fresh Γ]) ∘ cobind (const tt).
  Proof.
    intros.
    ext [ctx x].
    unfold compose.
    unfold assignNames_loc.
  Abort.

  (** *** Specification of <<rtFromNominal_occ>> when a is unbound *)
  (********************************************************************)
  Lemma rtFromNominal_occ_Unbound_spec: forall (Γ: list atom) (ctx: list atom) (a: atom),
      get_binding ctx a = Unbound ctx a ->
      rtFromNominal_occ Γ (ctx, a) = (mapdz (roundtrip_Binder_loc Γ) ctx, a).
  Proof.
    introv Hyp.
    rewrite rtFromNominal_occ_spec_pw.
    fequal.
    cbn.
    rewrite Hyp.
    reflexivity.
  Qed.

  (** *** Specification of <<roundtrip_Var_loc>> when a is bound *)
  (********************************************************************)
  Lemma roundtrip_Var_loc_Bound_spec: forall (Γ: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      ctx = prefix ++ [a'] ++ postfix ->
      a = a' ->
      roundtrip_Var_loc Γ (ctx, a) =
        historyToName Γ (assignNames Γ (map (const tt) prefix), tt).
  Proof.
    introv Hbinding Hctx Haeq.
    unfold historyToName.
    unfold roundtrip_Var_loc.
    unfold kc_dfunp.
    rewrite cobind_Z2_const.
    unfold compose at 1.
    unfold name_to_ln.
    rewrite Haeq in *; clear Haeq.
    rewrite Hbinding.
    unfold binding_to_ln.
    unfold lnToName.
    unfold bdToName.
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
    unfold assignNames_loc.
    unfold hadapt.
    unfold historyToName.
    fequal.
    fequal.
    unfold assignNames.
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

  (** *** Specification of <<get_binding ∘ rtFromNominal_occ>> when a is unbound *)
  (********************************************************************)
  Lemma rtFromNominal_occ_get_binding_Unbound_spec:
    forall (Γ: list atom) (ctx: list atom) (a: atom),
      a ∈ Γ ->
      get_binding ctx a = Unbound ctx a ->
      match rtFromNominal_occ Γ (ctx, a) with
      | (foo, x) =>
          get_binding foo x = Unbound (mapdz (roundtrip_Binder_loc Γ) ctx) a
      end.
  Proof.
    introv Hnin Hyp.
    rewrite rtFromNominal_occ_Unbound_spec; auto.
    destruct (get_binding_spec_proof (mapdz (roundtrip_Binder_loc Γ) ctx) a)
      as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin']]]]].
    { rewrite Case1.
      reflexivity. }
    { assert (Hfresh: ~ a ∈ mapdz (roundtrip_Binder_loc Γ) ctx).
      { rewrite roundtrip_Binder_loc_spec.
        unfold compose at 1.
        apply assignNames_fresh.
        assumption.
      }
      apply get_binding1 in Hfresh.
      assumption.
    }
  Qed.

  (** *** Specification of <<get_binding ∘ rtFromNominal_occ>> when a is bound *)
  (********************************************************************)
  Lemma rtFromNominal_occ_get_binding_Bound_spec:
    forall (Γ: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      a = a' ->
      ctx = prefix ++ [a'] ++ postfix ->
      ~ a ∈ postfix ->
      match rtFromNominal_occ Γ (ctx, a) with
      | (foo, x) =>
          let NewPrefix := assignNames Γ (map (const tt) prefix)
          in let NewVar := historyToName Γ (NewPrefix, tt)
             in let NewPost := assignNames (Γ ++ NewPrefix ++ [NewVar]) (map (const tt) postfix)
                in get_binding foo x = Bound NewPrefix NewVar NewPost /\ length NewPrefix = length prefix
      end.
  Proof.
    introv Hyp Haeq Hctxeq Hnin.
    remember (rtFromNominal_occ Γ (ctx, a)).
    destruct p.
    rewrite rtFromNominal_occ_spec_pw in Heqp.
    injection Heqp; introv Hctx' HVar'.
    clear Heqp.
    intros NewPrefix NewVar NewPost.
    split.
    { assert
        (HRoundtripMapsToNewVar:
          roundtrip_Var_loc Γ (prefix ++ [a'] ++ postfix, a') = NewVar).
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
        rewrite assignNames_decompose.
        fold NewPrefix.
        fold NewVar.
        fold NewPost.
        rewrite HRoundtripMapsToNewVar.
        reflexivity.
      - apply assignNames_fresh.
        rewrite element_of_list_app.
        rewrite element_of_list_app.
        right; right.
        rewrite element_of_list_one.
        subst.
        assumption.
    }
    { unfold NewPrefix.
      rewrite length_assignNames.
      rewrite map_preserve_length.
      reflexivity.
    }
  Qed.

  Lemma rt_correct_local2:
    forall (t: T name name) (Γ: list name)
      (HΓinit: forall (a: name), (a ∈ FV t -> a ∈ Γ)),
    forall (ctx: list name) (a: name),
      (ctx, a) ∈ (dec (T atom) t) ->
      alpha_equiv_local (ctx, a) (rtFromNominal_occ Γ (ctx, a)).
  Proof.
    introv HFV.
    introv Hin.
    unfold alpha_equiv_local.
    destruct (get_binding_spec_proof ctx a) as [[Case1 Hanin] | [prefix [postfix [Case2 [ctxspec Hnin]]]]].
    { rewrite Case1.
      assert (HΓ: a ∈ Γ).
      { apply HFV.
        apply (FV_lift_local _ ctx); auto.
      }
      specialize (rtFromNominal_occ_get_binding_Unbound_spec Γ ctx a HΓ Case1).
      intro X.
      destruct (rtFromNominal_occ Γ (ctx, a)).
      rewrite X. destruct_eq_args a a.
    }
    {
      rewrite Case2.
      apply (rtFromNominal_occ_get_binding_Bound_spec Γ) in Case2; auto.
      destruct (rtFromNominal_occ Γ (ctx, a)).
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
    rewrite <- rtFromNominal_occ_spec.
    apply rt_correct_local2.
    clear a.
    introv HinFV.
    rewrite (FV_preserved t) in HinFV.
    assumption.
  Qed.

  (** ** Correctness of <<rtFromNominal>> *)
  (********************************************************************)
  Theorem rtFromNominal_correct: forall (t: T name name),
      polymorphic_alpha T t (rtFromNominal t).
  Proof.
    intros.
    rewrite (rtFromNominal_spec_decomposed).
    unfold polymorphic_alpha.
    unfold lift_relation_ctx2.
    rewrite (decorate_rename_binders2).
    rewrite TraversableFunctor.relation_natural2.
    rewrite (CategoricalToKleisli.DecoratedFunctor.dec_mapd2 (list atom) (F := T atom)).
    change (map (F := ?F) (A := ?A) (B := ?B)) with (vmap (B := atom) (V1 := A) (V2 := A)).
    rewrite delete_binders_vmap.
    unfold vmap.
    rewrite relation_natural2.
    apply relation_diagonal1.
    apply rt_correct_local1.
  Qed.

  Theorem rtFromNominal_correct2: forall (t: T name name),
      polymorphic_alpha T t (term_ln_to_nominal (free (term_nominal_to_ln t)) (term_nominal_to_ln t)).
  Proof.
    intros.
    unfold rtFromNominal.
    apply rtFromNominal_correct.
  Qed.

  (** ** Roundtrip in the Other Direction *)
  (********************************************************************)
  Definition rtFromLN:
    T unit LN -> T unit LN :=
    fun t =>
      let t_nom := term_ln_to_nominal (LN.free t) t
      in term_nominal_to_ln t_nom.

  Lemma rtFromLN_spec1:
    forall (t: T unit LN),
      rtFromLN t =
        mapdp (kc_dz (const tt) (assignNames_loc (free t)))
          (kc_dfunp name_to_ln (assignNames_loc (free t)) (lnToName (free t))) t.
  Proof.
    intros.
    unfold rtFromLN.
    compose near t on left.
    unfold term_nominal_to_ln at 1.
    unfold term_ln_to_nominal at 1.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  Lemma rtFromLN_spec_decomposed:
    forall (t: T unit LN),
      rtFromLN t =
        let Γ := free t
        in (rename_binders (const tt)
           (mapd (T := T unit) (kc_dfunp (T := T)
                                  name_to_ln
                                  (assignNames_loc Γ)
                                  (lnToName Γ)) t)).
  Proof.
    intros.
    rewrite rtFromLN_spec1.
    unfold kc_dz.
    change (const tt ∘ cobind (assignNames_loc (free t)))
      with (const (A := list unit * unit) tt).
    rewrite mapd_decompose.
    reflexivity.
  Qed.

  Lemma rtFromLN_spec_decomposed2:
    forall (t: T unit LN),
      rtFromLN t =
        let Γ := free t
        in (mapd (T := T unit)
              (kc_dfunp (T := T)
                 name_to_ln
                 (assignNames_loc Γ)
                 (lnToName Γ)) t).
  Proof.
    intros.
    rewrite rtFromLN_spec_decomposed.
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


  Section support.
    Context (Γ: list atom).

    Lemma get_binding_LN_rt2_lemma1: forall (ctx: list unit) (n: nat),
        n < length ctx ->
        ctx = (length_to_list_unit (length ctx - (n + 1)) ++ [ tt ]  ++ length_to_list_unit n).
    Proof.
      introv Hlt. induction ctx.
      - false. cbn in Hlt. lia.
      - compare naturals n and (length ctx).
        + specialize (IHctx ineqp).
          rewrite IHctx.
          rewrite length_cons.
          rewrite List.app_length.
          rewrite length_length_to_list_unit.
          rewrite List.app_length.
          rewrite length_length_to_list_unit.
          rewrite (length_one (a := tt)).
          assert (HlenEq: (S (length ctx - (n + 1) + (1 + n)) - (n + 1)) = S (length ctx - (n + 1))).
          { lia. }
          rewrite HlenEq.
          rewrite length_to_list_unit_S.
          destruct a.
          reflexivity.
        + clear IHctx.
          assert (HlenEq: (length (a :: ctx) - (length ctx + 1)) = 0).
          { rewrite length_cons.
            lia.
          }
          rewrite HlenEq.
          destruct a.
          rewrite <- length_list_unit_iso.
          reflexivity.
        + false. cbn in Hlt.
          lia.
    Qed.

    #[local] Open Scope nat_scope.

    Lemma nat_decompose: forall (ctx: nat) (part: nat),
        part < ctx ->
        ctx = part + 1 + (ctx - part - 1).
    Proof.
      introv Hlen.
      lia.
    Qed.

    Lemma list_unit_decompose: forall (ctx: list unit) (part: list unit),
        length part < length ctx ->
        ctx = part ++ [tt] ++ (length_to_list_unit (length ctx - length part - 1)).
    Proof.
      introv Hlen.
      pose (Helper:= nat_decompose (length ctx) (length part) Hlen).
      rewrite (length_list_unit_iso ctx) at 1.
      rewrite (length_list_unit_iso part) at 1.
      rewrite Helper.
      clear Helper.
      rewrite length_to_list_unit_plus.
      rewrite List.app_assoc.
      rewrite length_to_list_unit_plus.
      fequal.
      fequal. lia.
    Qed.

    Lemma get_binding_LN_rt2_generalized: forall (ctx: list unit) (part: list unit),
        length part < length ctx ->
        (get_binding (assignNames Γ ctx) (assignNames_loc Γ (part, tt))) =
          Bound
            (assignNames Γ part)
            (assignNames_loc Γ (part, tt))
            (assignNames (Γ ++ assignNames Γ part ++ [assignNames_loc Γ (part, tt)])
               (length_to_list_unit (length ctx - length part - 1))).
    Proof.
      introv Hlt.
      apply get_binding2.
      - reflexivity.
      - rewrite (list_unit_decompose ctx part); [| assumption].
        rewrite assignNames_decompose.
        cbn zeta.
        rewrite assignNames_loc_spec.
        fequal.
        fequal.
        fequal.
        fequal.
        do 2 rewrite List.app_length.
        rewrite (length_one (a := tt)).
        rewrite length_length_to_list_unit.
        lia.
      - apply assignNames_fresh.
        simpl_list.
        tauto.
    Qed.

    Lemma get_binding_LN_rt2: forall (ctx: list unit) (n: nat),
        n < length ctx ->
        (get_binding (assignNames Γ ctx)
           (assignNames_loc Γ (length_to_list_unit (length ctx - (n + 1)), tt))) =
          Bound
            (assignNames Γ (length_to_list_unit (length ctx - (n + 1))))
            (assignNames_loc Γ (length_to_list_unit (length ctx - (n + 1)), tt))
            (assignNames (Γ ++ assignNames Γ (length_to_list_unit (length ctx - (n + 1))) ++
                            [assignNames_loc Γ ((length_to_list_unit (length ctx - (n + 1))), tt)])
               (length_to_list_unit n)).
    Proof.
      introv Hlt.
      rewrite get_binding_LN_rt2_generalized.
      - fequal.
        fequal.
        fequal.
        rewrite length_length_to_list_unit.
        lia.
      - rewrite length_length_to_list_unit.
        lia.
    Qed.

    Lemma get_binding_LN_rt1: forall (ctx: list unit) (n: nat),
        n < length ctx ->
        binding_to_ln
          (get_binding (assignNames Γ ctx)
             (assignNames_loc Γ (length_to_list_unit (length ctx - (n + 1)), tt))) =
          Bd n.
    Proof.
      intros.
      rewrite get_binding_LN_rt2; auto.
      unfold binding_to_ln.
      rewrite length_assignNames.
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
           (assignNames l pre ++
              [historyToName l (assignNames l pre, tt)] ++
              assignNames
              (l ++ assignNames l pre ++ [historyToName l (assignNames l pre, tt)]) post)
           (historyToName l (assignNames l pre, tt)))
        =  Bound
             (assignNames l pre)
             (historyToName l (assignNames l pre, tt))
             (assignNames
                (l ++ assignNames l pre ++ [historyToName l (assignNames l pre, tt)]) post).
    Proof.
      intros.
      apply get_binding2.
      - reflexivity.
      - reflexivity.
      - apply  assignNames_fresh.
        rewrite element_of_list_app.
        rewrite element_of_list_app.
        rewrite element_of_list_one.
        right. right. reflexivity.
    Qed.

  End support.

  Lemma rtFromLN_id_local:
    forall (t : T unit LN) (HLC: LC t)
      (FVt: list atom) (HeqFVt: FVt = free t)
      (ctx: list unit) (v: LN) (Hin: (ctx, v) ∈d t),
      binding_to_ln (get_binding (assignNames FVt ctx) (lnToName FVt (ctx, v))) = v.
  Proof.
    intros.
    destruct v as [a | n].
    - unfold lnToName.
      assert (H_a_not_assigned: ~ a ∈ assignNames FVt ctx).
      { apply assignNames_fresh.
        subst.
        admit. }
      assert (H_get_binding_Unbound:
               get_binding (assignNames FVt ctx) a = Unbound (assignNames FVt ctx) a).
      { destruct (get_binding_spec_proof (assignNames FVt ctx) a)
          as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin']]]]].
        - assumption.
        - false. apply H_a_not_assigned.
          subst. rewrite ctxspec.
          simpl_list. tauto. }
      rewrite H_get_binding_Unbound.
      reflexivity.
    - unfold lnToName.
      unfold bdToName.
      assert (H_n_lt: Nat.ltb n (length ctx) = true).
      { rewrite OrdersEx.Nat_as_OT.ltb_lt.
        (*
        Fail rewrite (LC_spec (T := T unit)) in HLC.

        specialize (HLC (length ctx)).
        specialize (HLC (Bd n)).
        assert (cut: (length ctx, Bd n) ∈d t).
        Unset Printing Notations.
        Set Printing Implicit.
        { admit. }
        apply HLC in cut.
        unfold lc_loc in cut.
        lia.
      }
      rewrite H_n_lt.
      rewrite get_binding_LN_rt1.
      + reflexivity.
      + rewrite <- OrdersEx.Nat_as_OT.ltb_lt.
        assumption.
         *)
  Admitted.

  Lemma rtFromLN_id: forall (t: T unit LN),
      LC t ->
      rtFromLN t = t.
  Proof.
    introv HLC.
    rewrite rtFromLN_spec_decomposed2.
    remember (free t) as FVt.
    cbn.
    apply mapd_respectful_id.
    intros ctx v Hin.
    unfold kc_dfunp.
    unfold compose at 1.
    unfold cobind_Z2, cojoin_Z2, compose at 1.
    unfold map_Z2.
    compose near ctx on left.
    unfold_Z.
    rewrite <- mapd_list_prefix_spec.
    change (mapd_list_prefix (assignNames_loc FVt) ctx)
      with (mapdz (assignNames_loc FVt) ctx).
    rewrite <- assignNames_spec.
    unfold name_to_ln.
    eapply rtFromLN_id_local; eauto.
  Qed.

  Lemma rtFromLN_correct: forall (t: T unit LN),
      LC t ->
      term_nominal_to_ln (term_ln_to_nominal (free t) t) = t.
  Proof.
    introv HLC.
    unfold rtFromLN.
    apply rtFromLN_id.
    assumption.
  Qed.

End with_DTM.
