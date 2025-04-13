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
From Tealeaves Require Import
  Backends.LN
  Backends.DB.DB
  Backends.Adapters.Key
  Backends.Adapters.LNtoDB
  Backends.Adapters.DBtoLN
  Functors.Option.

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
      bound n e = true.
  Proof.
    introv HLC Hin. cbn.
    unfold LC, LCn in HLC.
    specialize (HLC e (Bd n) Hin).
    unfold lc_loc in HLC.
    replace (e + 0) with e in * by lia.
    destruct e.
    lia.
    rewrite PeanoNat.Nat.leb_le. lia.
  Qed.

  Lemma bound_in_plus: forall n depth,
      bound (n + depth) depth = false.
  Proof.
    intros. destruct depth.
    - reflexivity.
    - cbn.
      rewrite Compare_dec.leb_iff_conv.
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

  Definition scoped_key (t: U LN) (k: key) :=
    forall x: atom, Fr x ∈ t -> x ∈ k.

  (** ** Totality *)
  (********************************************************************)
  (** Given a locally closed locally nameless term and a key with enough atoms,
      <<toDB>> is guaranteed to return something. *)
  Lemma to_DB_from_key_total:
    forall (t: U LN) (k: key),
      LC t ->
      scoped_key t k ->
      exists (t': U nat), toDB_from_key k t = Some t'.
  Proof.
    introv HLC Hin.
    unfold toDB_from_key.
    rewrite DecoratedTraversableFunctor.mapdt_through_runBatch.
    unfold compose at 1.
    unfold scoped_key in Hin.
    unfold element_of in Hin.
    unfold LC, LCn in HLC.
    rewrite (tosubset_through_runBatch2 _ nat) in Hin.
    (* the proof breaks here because can't rewrite under the binders. *)
    try setoid_rewrite (element_ctx_of_toctxset (E := nat) (T := U)) in HLC.
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
      toDB_from_key k t = None.
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
    rewrite bound_in_plus.
    replace (n + depth - depth) with n by lia.
    rewrite (key_bijection1 x k n H_key_lookup).
    reflexivity.
  Qed.

  (** Starting with a locally closed term and a big enough key,
      the roundtrip is locally the identity function *)
  Lemma LN_DB_roundtrip_loc: forall t k depth l,
      LC t ->
      scoped_key t k ->
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
      specialize (Hwhole x Hin); clear Hin.
      now apply LN_DB_roundtrip_loc_helper1.
    - rewrite toDB_loc_rw1.
      change (map ?f (Some ?n)) with (Some (f n)).
      unfold compose.
      unfold toLN_loc.
      now rewrite (lc_bound t depth n Hlc Hin).
      specialize (Hlc depth (Bd n) Hin).
      unfold lc_loc in Hlc.
      lia.
  Qed.

  (** Starting with a locally closed term and a big enough key,
      the roundtrip is locally the identity function *)
  Theorem LN_DB_roundtrip:
    forall (t: U LN) (k: key),
      (forall x: atom, Fr x ∈ t -> x ∈ k) ->
      LC t ->
      map (F := option) (toLN_from_key k) (toDB_from_key k t) =
        Some (Some t).
  Proof.
    intros.
    unfold toLN_from_key.
    unfold toDB_from_key.
    compose near t on left.
    rewrite mapdt_mapdt.
    all: try typeclasses eauto.
    change (Some (Some t)) with (pure (F := option ∘ option) t).
    apply (mapdt_respectful_pure _ (G := option ∘ option)).
    intros.
    now rewrite (LN_DB_roundtrip_loc t).
  Qed.

  (** ** Roundtrip from DB *)
  (********************************************************************)

  (** A helper lemma used below *)
  Lemma DB_LN_roundtrip_loc_helper1:
    forall (t:U nat) k gap (GapNotZero: gap <> 0) depth (n:nat),
      unique k ->
       n < depth + gap ->
       resolves_gap gap k ->
      bound n depth = false ->
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
    { specialize (Hclosed depth n Helt).
      unfold cl_at_loc, bound_within in Hclosed.
      rewrite PeanoNat.Nat.ltb_lt in Hclosed.
      cbn.
      assert (gap <> 0).
      { lia. }
      apply (DB_LN_roundtrip_loc_helper1 t k gap); eauto.
    }
    { cbn.
      destruct depth.
      - false.
      - assert (Hle: n <= depth) by lia.
        rewrite <- PeanoNat.Nat.leb_le in Hle.
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
      map (F := option) (toDB_from_key k) (toLN_from_key k t) =
        Some (Some t).
  Proof.
    intros.
    unfold toLN_from_key.
    unfold toDB_from_key.
    compose near t on left.
    rewrite mapdt_mapdt.
    all: try typeclasses eauto.
    change (Some (Some t)) with (pure (F := option ∘ option) t).
    apply (mapdt_respectful_pure _ (G := option ∘ option)).
    intros.
    now rewrite (DB_LN_roundtrip_loc t k gap).
  Qed.

  (** ** Roundtrip from DB *)
  (********************************************************************)


  (*
  (** A helper lemma used below *)
  Lemma DB_LN_roundtrip_loc_helper1:
    forall (t:U nat) k gap (GapNotZero: gap <> 0) depth (n:nat),
      unique k ->
      cl_at gap t ->
      contains_ix_upto (gap - 1) k ->
      bound n depth = false ->
      (depth, n) ∈d t ->
      map (toDB_loc k ∘ pair depth) (map Fr (key_lookup_index k (n - depth))) = Some (Some n).
  Proof.
    introv Hnz Huniq Hclosed Hcont Hbound Helt.
    unfold toLN_loc.
    assert (Hcont_minus: contains_ix_upto (n - depth) k).
    { clear Hbound.
      unfold contains_ix_upto in *.
      (* assert (n - depth <= gap).*)
      unfold cl_at in Hclosed;
        specialize (Hclosed depth n Helt);
        clear Helt;
        unfold cl_at_loc in Hclosed;
        unfold bound_within in Hclosed;
        rewrite PeanoNat.Nat.ltb_lt in Hclosed.
      destruct Hcont; lia.
    }
    {
      destruct (key_lookup_ix_Some2 k (n-depth) Hcont_minus) as [a Halookup].
      rewrite Halookup.
      change (map ?f (Some ?n)) with (Some (f n)).
      change (map ?f (Some ?n)) with (Some (f n)).
      cbn.
      apply (key_bijection2) in Halookup; auto.
      rewrite Halookup; clear Halookup.
      change (map ?f (Some ?n)) with (Some (f n)).
      cbn.
      replace (n - depth + depth) with n.
      reflexivity.
      unfold bound, bound_within in Hbound.
      rewrite PeanoNat.Nat.ltb_nlt in Hbound.
      lia.
    }
  Qed.

  (** A helper lemma used below *)
  Lemma DB_LN_roundtrip_loc: forall (t:U nat) k gap depth (n:nat),
      unique k ->
      cl_at gap t ->
      contains_ix_upto (gap - 1) k ->
      (depth, n) ∈d t ->
      (toDB_loc k ⋆3 toLN_loc k) (depth, n) =
        pure (F := option ∘ option) n.
  Proof.
    introv Huniq Hclosed Hcont Helt.
    unfold_ops @Pure_compose @Pure_option.
    rewrite kc3_spec.
    unfold toLN_loc.
    bound_induction.
    cbn.
    assert (gap <> 0). admit.
    apply (DB_LN_roundtrip_loc_helper1 t k gap ltac:(assumption) depth n
             Huniq Hclosed Hcont Hbound Helt).
  Admitted.

  (** Starting with a term with no more than <<gap>>-level free variables, if the key has at least <<gap>> many unique
      names, the roundtrip of a de Bruijn index is locally the identity function. *)
  Theorem DB_LN_roundtrip: forall k gap (t: U nat),
      unique k ->
      cl_at gap t ->
      contains_ix_upto (gap - 1) k ->
      map (F := option) (toDB_from_key k) (toLN_from_key k t) =
        Some (Some t).
  Proof.
    intros.
    unfold toLN_from_key.
    unfold toDB_from_key.
    compose near t on left.
    rewrite mapdt_mapdt.
    all: try typeclasses eauto.
    change (Some (Some t)) with (pure (F := option ∘ option) t).
    apply (mapdt_respectful_pure _ (G := option ∘ option)).
    intros.
    now rewrite (DB_LN_roundtrip_loc t k gap).
  Qed.
  *)

  (** ** Partial Bijections *)
  (********************************************************************)
  Theorem partial_bijection_spec1:
    forall (A B: Type) (f: A -> option B) (g: B -> option A),
      (forall (a: A), f a = None \/ map g (f a) = Some (Some a)) ->
      (forall (b: B), g b = None \/ map f (g b) = Some (Some b)) ->
      (forall (a: A) (b: B), f a = Some b <-> g b = Some a).
  Proof.
    introv HA HB.
    intros a b.
    split.
    - intros Hf.
      specialize (HA a).
      rewrite Hf in HA.
      cbn in HA.
      inversion HA.
      + inversion H.
      + inversion H.
        reflexivity.
    - intros Hg.
      specialize (HB b).
      rewrite Hg in HB.
      cbn in HB.
      inversion HB.
      + inversion H.
      + inversion H.
        reflexivity.
  Qed.

  Theorem partial_bijection_spec2:
    forall (A B: Type) (f: A -> option B) (g: B -> option A),
      (forall (a: A) (b: B), f a = Some b <-> g b = Some a) ->
      (forall (a: A), f a = None \/ map g (f a) = Some (Some a)).
  Proof.
    introv H. intro a.
    specialize (H a).
    destruct (f a) as [b|].
    - right.
      destruct (H b) as [H1 _].
      specialize (H1 ltac:(reflexivity)).
      cbn. fequal.
      assumption.
    - now left.
  Qed.

  Theorem partial_bijection_spec3:
    forall (A B: Type) (f: A -> option B) (g: B -> option A),
      (forall (a: A) (b: B), f a = Some b <-> g b = Some a) ->
      (forall (b: B), g b = None \/ map f (g b) = Some (Some b)).
  Proof.
    introv H. intro b.
    remember (g b) as gb.
    destruct gb as [a|].
    - right.
      cbn.
      fequal.
      apply H.
      symmetry.
      assumption.
    - now left.
  Qed.

  Theorem partial_bijection_spec:
    forall (A B: Type) (f: A -> option B) (g: B -> option A),
      (forall (a: A) (b: B), f a = Some b <-> g b = Some a) <->
      (forall (b: B), g b = None \/ map f (g b) = Some (Some b)) /\
        (forall (a: A), f a = None \/ map g (f a) = Some (Some a)).
  Proof.
    intros. split.
    - intros. split.
      now apply partial_bijection_spec2.
      now apply partial_bijection_spec3.
    - intros [H1 H2].
      apply partial_bijection_spec1.
      assumption.
      assumption.
  Qed.

  Theorem DB_LN_partial_bijection1: forall k,
      unique k ->
      (forall (t: U LN) (u: U nat),
          toDB_from_key k t = Some u <-> toLN_from_key k u = Some t).
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
    - rewrite toDB_from_key_None_iff.
  Abort.

End translate.

