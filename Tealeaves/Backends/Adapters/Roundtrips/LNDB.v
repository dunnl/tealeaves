(*|
############################################################
Translating between locally nameless and de Bruijn indices
############################################################

We reason about a translation between syntax with de Bruijn indices
and locally nameless variables. This consists of a function which,
given a locally closed term t, outputs a term of the same shape whose
leaves are de Bruijn indices and a "key": some arbitrary permutation
of the names of free variables in t. Another function accepts a key
and a de Bruijn term and computes a locally nameless term of the same
shape. The two functions are shown to be inverses.

.. contents:: Table of Contents :depth: 2

============================
Imports and setup
============================

Since we are using the Kleisli typeclass hierarchy, we import modules
under the namespaces ``Classes.Kleisli`` and ``Theory.Kleisli.``
|*)
From Tealeaves Require Export
  Backends.LN
  Backends.DB.DB
  Backends.Adapters.Key
  Backends.Adapters.LNtoDB
  Backends.Adapters.DBtoLN
  Functors.Option
  Misc.PartialBijection.

From Coq Require Import PeanoNat.

Import LN.Notations.

Import DecoratedTraversableMonad.UsefulInstances.

#[local] Generalizable Variables W T U.
#[local] Open Scope nat_scope.


Section translate.

  Context
    `{Return_T: Return T}
    `{Binddt_TT: Binddt nat T T}
    `{Binddt_TU: Binddt nat T U}
    `{Monad_inst: ! DecoratedTraversableMonad nat T}
    `{Module_inst: ! DecoratedTraversableRightPreModule nat T U
    (unit := Monoid_unit_zero)
    (op := Monoid_op_plus)}.

  (** ** Basic supporting lemmas *)
  (********************************************************************)
  Lemma lc_bound: forall t e n,
      LC (U := U) t ->
      (e, Bd n) ∈d t ->
      bound n e.
  Proof.
    introv HLC Hin. cbn.
    rewrite LC_spec in HLC.
    specialize (HLC e (Bd n) Hin).
    unfold lc_loc in HLC.
    replace (e + 0) with e in * by lia.
    destruct e.
    lia. unfold bound, bound_within.
    lia.
  Qed.

  Lemma lc_bound_b: forall t e n,
      LC (U := U) t ->
      (e, Bd n) ∈d t ->
      bound_b n e = true.
  Proof.
    intros. specialize (lc_bound t _ _ H H0).
    rewrite bound_spec.
    unfold bound, bound_within.
    lia.
  Qed.

  Lemma bound_in_plus: forall n depth,
      ~ bound (n + depth) depth.
  Proof.
    intros. unfold bound, bound_within. lia.
  Qed.

  Lemma bound_in_plus_b: forall n depth,
      bound_b (n + depth) depth = false.
  Proof.
    intros.
    rewrite bound_spec_not.
    lia.
  Qed.

  Lemma toDB_Fr: forall (n: nat) (a: atom) (k: key),
      a ∈ k ->
      exists ix, toDB_loc k (n, Fr a) = Some ix.
  Proof.
    intros.
    unfold toDB_loc.
    lookup atom a in key k.
    rewrite H_key_lookup.
    eexists. reflexivity.
  Qed.

  (** ** Totality *)
  (********************************************************************)
  (** Given a locally closed locally nameless term and a key with enough atoms,
      <<toDB>> is guaranteed to return something. *)
  Lemma to_DB_from_key_total:
    forall (t: U LN) (k: key),
      LC t ->
      scoped_key k t ->
      exists (t': U nat), toDB k t = Some t'.
  Proof.
    introv HLC Hin.
    unfold toDB.
    rewrite DecoratedTraversableFunctor.mapdt_through_runBatch.
    unfold compose at 1.
    unfold scoped_key in Hin.
    unfold element_of in Hin.
    unfold LC, LCn in HLC.
    rewrite (tosubset_through_runBatch2 _ nat) in Hin.
    (* the proof breaks here because can't rewrite under the binders. *)
    try setoid_rewrite (element_ctx_of_toctxset (E := nat) (T := U)) in HLC.
    (*
    try rewrite (toctxset_through_runBatch2) in HLC.
    rewrite toBatch_to_toBatch3 in Hin.
    unfold compose in Hin.
    induction (toBatch3 t).
    - cbv. eauto.
    - rewrite runBatch_rw2.
      assert (H: (forall x: atom,
                     @runBatch LN nat (@const Type Type (LN -> Prop))
                       (@Map_const (LN -> Prop))
                       (@Mult_const (LN -> Prop) (@Monoid_op_subset LN))
                       (@Pure_const (LN -> Prop) (@Monoid_unit_subset LN))
                       (@ret subset Return_subset LN) (nat -> C)
                       (@mapfst_Batch nat (nat -> C) (nat * LN) LN
                          (@extract (prod nat) (Extract_reader nat) LN) b)
                       (Fr x) -> x ∈ k)).
      { intros x.
        specialize (Hin x).
        intros hyp.
        apply Hin.
        left.
        assumption. }
      specialize (IHb H).
      destruct IHb as [f Hfeq].
      rewrite Hfeq.
      destruct a as [depth l].
      destruct l.
      + pose toDB_Fr.
        specialize (e depth n k).
        enough (H_a_in_k: n ∈ k).
        { specialize (e H_a_in_k).
          destruct e as [ix Hixeq].
          rewrite Hixeq.
          cbn.
          eauto. }
        apply Hin.
        cbn. right.
        reflexivity.
      + (* Proof missing due to technical difficulties above *)
     *)
  Abort.

  Lemma mapdt_None:
    forall (A B: Type) (t: T A) (f: nat * A -> option B),
      (exists (n: nat) (a: A), (n, a) ∈d t /\ f (n, a) = None) ->
      mapdt f t = None.
  Proof.
    intros.
    rewrite mapdt_through_runBatch.
  Abort.

  Lemma to_DB_from_key_None:
    forall (t: U LN) (k: key),
      (exists (x: atom), Fr x ∈ t /\ ~ x ∈ k) ->
      toDB k t = None.
  Proof.
    intros. unfold scoped_key in H.
  Abort.


  (** ** Roundtrip from LN *)
  (********************************************************************)

  (** A helper lemma used below *)
  Lemma LN_DB_roundtrip_loc_helper1: forall k depth x,
      x ∈ k ->
      map (F := option)
        (toLN_loc k ∘ pair depth ∘ (fun ix: nat => ix + depth))
        (key_lookup_atom k x) = Some (Some (Fr x)).
  Proof.
    intros.
    lookup atom x in key k.
    rewrite H_key_lookup.
    change (map ?f (Some ?n)) with (Some (f n)).
    unfold compose, toLN_loc.
    rewrite bound_in_plus_b.
    replace (n + depth - depth) with n by lia.
    rewrite (key_bijection1 x k n H_key_lookup).
    reflexivity.
  Qed.

  (** Starting with a locally closed term and a big enough key,
      the roundtrip is locally the identity function *)
  Lemma LN_DB_roundtrip_loc: forall (t: U LN) k depth l,
      LC t ->
      scoped_key k t ->
      (depth, l) ∈d t ->
      (toLN_loc k ⋆3 toDB_loc k) (depth, l) = pure (F := option ∘ option) l.
  Proof.
    introv Hlc Hwhole Hin.
    rewrite kc3_spec.
    unfold scoped_key in Hwhole.
    destruct l as [x|n].
    - rewrite toDB_loc_rw2.
      compose near (key_lookup_atom k x).
      rewrite (fun_map_map (F := option)).
      apply ind_implies_in in Hin.
      rewrite <- in_free_iff in Hin.
      specialize (Hwhole x Hin); clear Hin.
      now apply LN_DB_roundtrip_loc_helper1.
    - rewrite toDB_loc_rw1.
      change (map ?f (Some ?n)) with (Some (f n)).
      unfold compose.
      unfold toLN_loc.
      now rewrite (lc_bound_b t depth n Hlc Hin).
      rewrite LC_spec in Hlc.
      specialize (Hlc depth (Bd n) Hin).
      unfold lc_loc in Hlc.
      lia.
  Qed.

  (** Starting with a locally closed term and a big enough key,
      the roundtrip is locally the identity function *)
  Theorem LN_DB_roundtrip:
    forall (t: U LN) (k: key),
      scoped_key k t ->
      LC t ->
      map (F := option) (toLN k) (toDB k t) =
        Some (Some t).
  Proof.
    intros.
    unfold toLN.
    unfold toDB.
    compose near t on left.
    rewrite mapdt_mapdt.
    change (Some (Some t)) with (pure (F := option ∘ option) t).
    apply (mapdt_respectful_pure _ (G := option ∘ option)).
    intros.
    rewrite (LN_DB_roundtrip_loc t); auto.
  Qed.

  (** ** Roundtrip from DB *)
  (********************************************************************)

  (** A helper lemma used below *)
  Lemma DB_LN_roundtrip_loc_helper1:
    forall (t:U nat) k gap (GapNotZero: gap <> 0) depth (n:nat),
      unique k ->
       n < depth + gap ->
       resolves_gap gap k ->
      bound_b n depth = false ->
      (depth, n) ∈d t ->
      map (toDB_loc k ∘ pair depth) (map Fr (key_lookup_index k (n - depth))) = Some (Some n).
  Proof.
    introv Hnz Huniq Hclosed Hcont Hbound Helt.
    unfold toLN_loc.
    rewrite resolves_gap_spec in Hcont.
    assert (n >= depth).
    { unfold bound, bound_within in Hbound.
      apply PeanoNat.Nat.ltb_ge in Hbound.
      lia.
    }
    destruct Hcont as [Okay | GapZero].
    { remember (key_lookup_index k (n - depth)).
      symmetry in Heqo.
      destruct o.
      { cbn.
        rewrite key_bijection in Heqo; auto.
        rewrite Heqo.
        cbn.
        fequal. fequal. lia.
      }
      { cbn. false.
        apply key_lookup_ix_None1 in Heqo.
        unfold contains_ix_upto in *. lia.
      }
    }
    { subst. false. }
  Qed.

  (** A helper lemma used below *)
  Lemma DB_LN_roundtrip_loc: forall (t:U nat) k gap depth (n:nat),
      unique k ->
      cl_at gap t ->
      resolves_gap gap k ->
      (depth, n) ∈d t ->
      (toDB_loc k ⋆3 toLN_loc k) (depth, n) =
        pure (F := option ∘ option) n.
  Proof.
    introv Huniq Hclosed Hcont Helt.
    unfold_ops @Pure_compose @Pure_option.
    rewrite kc3_spec.
    unfold toLN_loc.
    bound_induction.
    { cbn.
      rewrite cl_at_spec in Hclosed.
      specialize (Hclosed depth n Helt).
      unfold cl_at_loc, bound_within in Hclosed.
      assert (gap <> 0) by lia. (* nothing is less than zero. *)
      apply (DB_LN_roundtrip_loc_helper1 t k gap); eauto.
    }
    { cbn.
      destruct depth.
      - false.
      - assert (Hle: n <= depth) by lia.
        rewrite <- Nat.leb_le in Hle.
        rewrite Hle.
        reflexivity.
    }
  Qed.

  (** Starting with a term with no more than <<gap>>-level free variables, if the key has at least <<gap>> many unique
      names, the roundtrip of a de Bruijn index is locally the identity function. *)
  Theorem DB_LN_roundtrip: forall k gap (t: U nat),
      unique k ->
      cl_at gap t ->
      resolves_gap gap k ->
      map (F := option) (toDB k) (toLN k t) =
        Some (Some t).
  Proof.
    intros.
    unfold toLN.
    unfold toDB.
    compose near t on left.
    rewrite mapdt_mapdt.
    all: try typeclasses eauto.
    change (Some (Some t)) with (pure (F := option ∘ option) t).
    apply (mapdt_respectful_pure _ (G := option ∘ option)).
    intros.
    now rewrite (DB_LN_roundtrip_loc t k gap).
  Qed.

  Theorem DB_LN_partial_bijection_iff: forall k,
      unique k ->
      (forall (t: U LN) (u: U nat),
          toDB k t = Some u <-> toLN k u = Some t).
  Proof.
    intros.
    apply partial_bijection_spec.
    clear t u. split; intros t.
    - rewrite toLN_None_iff.
      destruct (cl_at_decidable (length k) t) as [Hclosedat | Not_Hclosedat].
      right.
      eapply (DB_LN_roundtrip k (length k)).
      + assumption.
      + assumption.
      + unfold resolves_gap. lia.
      + now left.
    - rewrite toDB_None_iff2.
      destruct (scoped_key_decidable k t).
      { destruct (LC_decidable t).
        { right. apply LN_DB_roundtrip; assumption. }
        { left. now right. }
      }
      { left. now left. }
  Qed.

  Lemma not_scoped_LC_iff: forall (k: key) (t: U LN),
      ~ (scoped_key k t /\ LC t) <-> ~ scoped_key k t \/ ~ LC t.
  Proof.
    intros.
    split.
    - intros.
      apply Decidable.not_and.
      apply scoped_key_decidable.
      assumption.
    - tauto.
  Qed.

  Theorem DB_LN_partial_bijection:
    forall (k: key),
      unique k ->
      PartialBijectionSpec
        (U LN) (U nat)
        (fun t => (forall (x: atom), x ∈ free t -> x ∈ k) /\ LC t)
        (fun t => level t <= length k)
        (toDB k) (toLN k).
  Proof.
    intros.
    constructor.
    - intros.
      apply DB_LN_partial_bijection_iff.
      assumption.
    - intros t.
      rewrite toDB_None_iff2.
      rewrite <- (not_scoped_LC_iff k t).
      unfold scoped_key.
      reflexivity.
    - intros t.
      rewrite toLN_None_iff.
      rewrite level_iff.
      reflexivity.
  Qed.

End translate.

