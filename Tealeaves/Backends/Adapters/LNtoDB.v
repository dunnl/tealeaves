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
  Functors.Option.

Import LN.Notations.

Import DecoratedTraversableMonad.UsefulInstances.

#[local] Generalizable Variables W T U.
#[local] Open Scope nat_scope.

(*|
============================
Translation operations
============================
|*)
Definition toDB_loc (k: key) '(depth, l) : option nat :=
  match l with
  | Bd n => Some n
  | Fr x => map (fun ix => ix + depth) (key_lookup_atom k x)
  end.

Definition toLN_loc (k: key) '(depth, ix) : option LN :=
  if bound ix depth == true
  then
    Some (Bd ix)
  else
    map (F := option) Fr (key_lookup_index k (ix - depth)).

Fixpoint toLNkey_list (l: list LN): key :=
  match l with
  | [] => nil
  | (Bd n :: rest) => toLNkey_list rest
  | (Fr x :: rest) => key_insert_atom (toLNkey_list rest) x
  end.

(*|
============================
Simplification support
============================
|*)
Lemma toDB_loc_rw1 (k: key) (depth: nat) (n: nat):
  toDB_loc k (depth, Bd n) = Some n.
Proof.
  reflexivity.
Qed.

Lemma toDB_loc_rw2 (k: key) (depth: nat) (x: atom):
  toDB_loc k (depth, Fr x) =
    map (fun ix => ix + depth) (key_lookup_atom k x).
Proof.
  reflexivity.
Qed.

(*|
============================
Properties of toLNkey
============================
|*)
Lemma toLNkey_unique: forall l,
    unique (toLNkey_list l).
Proof.
  intros l. induction l as [|[x|n] rest].
  - exact I.
  - now apply key_insert_unique.
  - cbn. assumption.
Qed.

Lemma toLNkey_bijection: forall l ix a,
    key_lookup_index (toLNkey_list l) ix = Some a <->
      key_lookup_atom (toLNkey_list l) a = Some ix.
Proof.
  intros.
  apply key_bijection.
  apply toLNkey_unique.
Qed.
(*|
============================
Global operations
============================
|*)
Definition toDB_from_key
  `{Mapdt_inst: Mapdt nat T} (k: key): T LN -> option (T nat) :=
  mapdt (G := option) (toDB_loc k).

Definition toLN_from_key
  `{Mapdt_inst: Mapdt nat T} (k: key): T nat -> option (T LN) :=
  mapdt (G := option) (toLN_loc k).

Definition toLNkey
  `{Traverse_inst: Traverse T} (t: T LN): key :=
  toLNkey_list (tolist t).

Definition toDB
  `{Traverse_inst: Traverse T}
  `{Mapdt_inst: Mapdt nat T} (t: T LN): option (T nat) :=
  toDB_from_key (toLNkey t) t.

Section translate.

  Context
    `{Return_T: Return T}
    `{Binddt_TT: Binddt nat T T}
    `{Binddt_TU: Binddt nat T U}
    `{Monad_inst: ! DecoratedTraversableMonad nat T}
    `{Module_inst: ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.

  (** ** Boring admitted lemmas *)
  (******************************************************************************)
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

  (** ** Supporting lemmas *)
  (******************************************************************************)
  Definition whole_key (t: U LN) (k: key) :=
    forall x : atom, Fr x ∈ t -> x ∈ k.

  (** ** LN to DB to LN *)
  (******************************************************************************)
  Lemma to_DB_from_key_total:
    forall (t: U LN) (k : key),
      whole_key t k ->
      exists (t': U nat), toDB_from_key k t = Some t'.
  Proof.
    introv Hin.
    unfold toDB_from_key.
    rewrite DecoratedTraversableFunctor.mapdt_through_runBatch.
    unfold compose at 1.
    unfold whole_key in Hin.
    unfold element_of in Hin.
    rewrite (tosubset_through_runBatch2 _ nat) in Hin.
    rewrite toBatch_to_toBatch3 in Hin.
    unfold compose in Hin.
    induction (toBatch3 t).
    - cbv. eauto.
    - rewrite runBatch_rw2.
      assert (H: (forall x : atom,
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
        specialize (e depth a k).
        enough (H_a_in_k: a ∈ k).
        { specialize (e H_a_in_k).
          destruct e as [ix Hixeq].
          rewrite Hixeq.
          cbn.
          eauto. }
        apply Hin.
        cbn. right.
        reflexivity.
      + cbn. eauto.
  Qed.

  Lemma LN_DB_roundtrip_loc1: forall k depth x,
      x ∈ k ->
      map (F := option)
        (toLN_loc k ∘ pair depth ∘ (fun ix : nat => ix + depth))
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

  Lemma LN_DB_roundtrip_loc: forall t k depth l,
      LC t ->
      whole_key t k ->
      (depth, l) ∈d t ->
      (toLN_loc k ⋆3 toDB_loc k) (depth, l) = pure (F := option ∘ option) l.
  Proof.
    introv Hlc Hwhole Hin.
    rewrite kc3_spec.
    unfold whole_key in Hwhole.
    destruct l as [x|n].
    - rewrite toDB_loc_rw2.
      compose near (key_lookup_atom k x).
      rewrite (fun_map_map (F := option)).
      apply ind_implies_in in Hin.
      specialize (Hwhole x Hin); clear Hin.
      now apply LN_DB_roundtrip_loc1.
    - rewrite toDB_loc_rw1.
      change (map ?f (Some ?n)) with (Some (f n)).
      unfold compose.
      unfold toLN_loc.
      now rewrite (lc_bound t depth n Hlc Hin).
  Qed.

  Theorem LN_DB_roundtrip:
    forall (t : U LN) (k: key),
      (forall x : atom, Fr x ∈ t -> x ∈ k) ->
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

  (** ** DB to LN to DB *)
  (******************************************************************************)
  Lemma DB_LN_roundtrip_loc1:
    forall (t:U nat) k gap depth (n:nat),
      unique k ->
      cl_at gap t ->
      contains_ix_upto gap k ->
      bound n depth = false ->
      (depth, n) ∈d t ->
      map (toDB_loc k ∘ pair depth) (map Fr (key_lookup_index k (n - depth))) = Some (Some n).
  Proof.
    introv Huniq Hclosed Hcont Hbound Helt.
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
      lia.
    }
    {
      unfold bound, bound_within in Hbound;
        rewrite PeanoNat.Nat.ltb_ge in Hbound;
        replace (depth + 0) with depth in Hbound by lia.
      destruct (key_lookup_ix_Some2 k (n-depth) Hcont_minus) as [a Halookup].
      rewrite Halookup.
      change (map ?f (Some ?n)) with (Some (f n)).
      change (map ?f (Some ?n)) with (Some (f n)).
      cbn.
      apply (key_bijection2) in Halookup; auto.
      rewrite Halookup; clear Halookup.
      change (map ?f (Some ?n)) with (Some (f n)).
      cbn.
      replace (n - depth + depth) with n by lia.
      reflexivity.
    }
  Qed.

  Lemma DB_LN_roundtrip_loc: forall (t:U nat) k gap depth (n:nat),
      unique k ->
      cl_at gap t ->
      contains_ix_upto gap k ->
      (depth, n) ∈d t ->
      (toDB_loc k ⋆3 toLN_loc k) (depth, n) =
        pure (F := option ∘ option) n.
  Proof.
    introv Huniq Hclosed Hcont Helt.
    unfold_ops @Pure_compose @Pure_option.
    rewrite kc3_spec.
    unfold toLN_loc.
    bound_induction.
    apply (DB_LN_roundtrip_loc1 t k gap depth n
             Huniq Hclosed Hcont Hbound Helt).
  Qed.

  Theorem DB_LN_roundtrip: forall k gap (t: U nat),
      unique k ->
      cl_at gap t ->
      contains_ix_upto gap k ->
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

End translate.
