From Tealeaves.Misc Require Import
  NaturalNumbers.
From Tealeaves.Theory Require Import
  TraversableFunctor
  DecoratedTraversableFunctor
  DecoratedTraversableMonad.

From Tealeaves Require Import
  Backends.LN.
From Tealeaves.Adapters Require Import
  MonadToApplicative
  KleisliToCategorical.Monad.

Import PeanoNat.Nat.
Import Coq.Init.Nat. (* Nat notations *)

Import
  Product.Notations
  Monoid.Notations
  Batch.Notations
  List.ListNotations
  Subset.Notations
  Kleisli.Monad.Notations
  Kleisli.Comonad.Notations
  ContainerFunctor.Notations
  DecoratedMonad.Notations
  DecoratedContainerFunctor.Notations
  DecoratedTraversableMonad.Notations.

#[local] Generalizable Variables W T U.

Open Scope nat_scope.

(* Iterate an endofunction <<n>> times *)
Fixpoint iterate (n : nat) {A : Type} (f : A -> A) :=
  match n with
  | 0 => @id A
  | S n' => iterate n' f ∘ f
  end.

Lemma iterate_rw0 : forall {A : Type} (f : A -> A),
    iterate 0 f = id.
Proof.
  reflexivity.
Qed.

Lemma iterate_rw1 : forall (n : nat) {A : Type} (f : A -> A),
    iterate (S n) f = (iterate n f) ∘ f.
Proof.
  intros.
  cbn.
  reflexivity.
Qed.

(** ** De Bruijn operations as defined by Tealeaves *)
(******************************************************************************)
Section ops.

  Context
    `{ret_inst : Return T}
      `{Mapd_T_inst : Mapd nat T}
      `{Mapd_U_inst : Mapd nat U}
      `{Bindd_U_inst : Bindd nat T U}
      `{ToCtxset_U_inst : ToCtxset nat U}.

  Definition bound_in_gap (gap: nat) : nat -> nat -> bool :=
    fun ix depth => ix <? depth + gap.

  Definition bound_in: nat -> nat -> bool :=
    bound_in_gap 0.

  (* Local function for incrementing free variables
     by <<n>> *)
  (* n: A value by which to increment free indices *)
  Definition lift (n : nat) (p : nat * nat) : nat :=
    match p with
    | (depth, ix) =>
        if bound_in ix depth
        then ix
        else ix + n
    end.

  (* Given a depth and local substitution σ,
       adjust σ to account for the depth
       - σ should be a top-level map, e.g.
         σ 0 is the first element being substituted
         For subst_by, σ 0 = u and σ (S n) = (S n)
       (<<ix - depth>> is the index into σ,
       adjusted to account for bound variables in scope
   *)
  (* TODO: Decrement free variables if necessary *)
  Definition scoot : nat -> (nat -> T nat) -> (nat -> T nat) :=
    fun depth σ ix =>
      if bound_in ix depth
      then ret ix
      else mapd (lift depth) (σ (ix - depth)).

  Definition scoot_ren : nat -> (nat -> nat) -> (nat -> nat) :=
    fun depth ρ ix =>
      if bound_in ix depth
      then ix
      else
        lift depth (0, ρ (ix - depth))
             (* = ρ (ix - depth) + depth *).

  Definition rename_loc (ρ : nat -> nat) (p: nat * nat): nat :=
    match p with
    | (depth, ix) => scoot_ren depth ρ ix
    end.

  Definition subst_loc (σ : nat -> T nat) (p: nat * nat): T nat :=
    match p with
    | (depth, ix) => scoot depth σ ix
    end.

  Definition rename (ρ : nat -> nat) : U nat -> U nat :=
    mapd (T := U) (rename_loc ρ).

  Definition subst (σ : nat -> T nat) : U nat -> U nat :=
    bindd (subst_loc σ).

  Definition one (u: T nat): nat -> T nat :=
    fun n => if n =? 0 then u else ret n.

  Definition subst_by (u : T nat) : U nat -> U nat :=
    subst (one u).

  Definition closed_gap_loc (gap: nat) (p: nat * nat): bool :=
    match p with
    | (depth, ix) => bound_in_gap gap ix depth
    end.

  Definition closed_loc (p: nat * nat): bool :=
    closed_gap_loc 0 p.

  Definition closed_gap (gap: nat) (t: U nat): Prop :=
    forall (depth ix: nat),
      (depth, ix) ∈d t ->
      closed_gap_loc gap (depth, ix) = true.

  Definition closed (t: U nat): Prop :=
    closed_gap 0 t.

End ops.

Implicit Types (ρ: nat -> nat).

Section theory.

  Lemma bound_in_zero: forall ix,
      bound_in ix 0 = false.
  Proof.
    reflexivity.
  Qed.

  Lemma bound_in_lt: forall ix n,
      ix < n ->
      bound_in ix n = true.
  Proof.
    introv Hlt.
    rewrite <- ltb_lt in Hlt.
    unfold bound_in, bound_in_gap.
    replace (n + 0) with n by lia.
    destruct n; auto.
  Qed.

  Lemma bound_in_lt_iff: forall ix n,
      ix < n <->
      bound_in ix n = true.
  Proof.
    intros. split.
    - apply bound_in_lt.
    - cbn. destruct n.
      + inversion 1.
      + cbn.
        rewrite OrdersEx.Nat_as_OT.leb_le.
        lia.
  Qed.

  Lemma bound_in_ge: forall ix n,
      ix >= n ->
      bound_in ix n = false.
  Proof.
    introv Hlt.
    unfold bound_in, bound_in_gap.
    replace (n + 0) with n by lia.
    destruct n; cbn; auto.
    now rewrite leb_gt.
  Qed.

  Lemma bound_in_ge_iff: forall ix n,
      ix >= n <->
      bound_in ix n = false.
  Proof.
    intros. split.
    - apply bound_in_ge.
    - cbn. replace (n + 0) with n by lia.
      destruct n.
      + lia.
      + intros.
        rewrite leb_gt in H.
        lia.
  Qed.

  Lemma bound_in_ind: forall ix n (P:Prop),
      (ix >= n -> bound_in ix n = false -> P) ->
      (ix < n -> bound_in ix n = true -> P) ->
      P.
  Proof.
    introv.
    rewrite <- bound_in_ge_iff.
    rewrite <- bound_in_lt_iff.
    introv Hge Hlt.
    compare naturals ix and n; auto.
    apply Hge; lia.
  Qed.

  Lemma bound_in_mono: forall ix n m,
      m > n ->
      bound_in ix n = true ->
      bound_in ix m = true.
  Proof.
    introv Hlt Hbound.
    rewrite <- bound_in_lt_iff in Hbound.
    rewrite <- bound_in_lt_iff.
    lia.
  Qed.

  Lemma bound_rev_mono: forall ix n m,
      m < n ->
      bound_in ix n = false ->
      bound_in ix m = false.
  Proof.
    introv Hlt Hbound.
    rewrite <- bound_in_ge_iff in Hbound.
    rewrite <- bound_in_ge_iff.
    lia.
  Qed.

  Lemma lift_lt: forall n depth ix,
      ix < depth ->
      lift n (depth, ix) = ix.
  Proof.
    intros. unfold lift.
    rewrite bound_in_lt_iff in H.
    now rewrite H.
  Qed.

  Lemma lift_ge: forall n depth ix,
      ix >= depth ->
      lift n (depth, ix) = ix + n.
  Proof.
    intros. unfold lift.
    rewrite bound_in_ge_iff in H.
    now rewrite H.
  Qed.

  Lemma lift_zero:
    lift 0 = extract.
  Proof.
    ext [depth ix].
    cbn. replace (depth + 0) with depth by lia.
    destruct depth.
    - lia.
    - destruct (ix <=? depth); lia.
  Qed.

  Lemma lift_depth_zero: forall n ix,
      lift n (0, ix) = ix + n.
  Proof.
    reflexivity.
  Qed.

End theory.

Ltac bound_induction :=
  match goal with
  | |- context[bound_in ?ix ?n] =>
      apply (bound_in_ind ix n);
      let Hord := fresh "Hord" in
      let Hbound := fresh "Hbound" in
      introv Hord Hbound;
      try rewrite Hbound in *;
      try solve [lia | easy]
  end.

Section theory.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Mapd_T_inst : Mapd nat T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Mapdt_T_inst : Mapdt nat T}
      `{Bindd_T_inst : Bindd nat T T}
      `{Bindt_T_inst : Bindt T T}
      `{Binddt_T_inst : Binddt nat T T}
      `{! Compat_Map_Binddt nat T T}
      `{! Compat_Mapd_Binddt nat T T}
      `{! Compat_Traverse_Binddt nat T T}
      `{! Compat_Bind_Binddt nat T T}
      `{! Compat_Mapdt_Binddt nat T T}
      `{! Compat_Bindd_Binddt nat T T}
      `{! Compat_Bindt_Binddt nat T T}
      `{Monad_inst : ! DecoratedTraversableMonad nat T}
      `{Map_U_inst : Map U}
      `{Mapd_U_inst : Mapd nat U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Mapdt_U_inst : Mapdt nat U}
      `{Bindd_U_inst : Bindd nat T U}
      `{Bindt_U_inst : Bindt T U}
      `{Binddt_U_inst : Binddt nat T U}
      `{! Compat_Map_Binddt nat T U}
      `{! Compat_Mapd_Binddt nat T U}
      `{! Compat_Traverse_Binddt nat T U}
      `{! Compat_Bind_Binddt nat T U}
      `{! Compat_Mapdt_Binddt nat T U}
      `{! Compat_Bindd_Binddt nat T U}
      `{! Compat_Bindt_Binddt nat T U}
      `{Module_inst : ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.

  Lemma lift_lift1: forall n m depth ix,
      lift m (depth, lift n (depth, ix)) = lift (m + n) (depth, ix).
  Proof.
    intros. unfold lift.
    - bound_induction.
      + bound_induction.
      + bound_induction.
  Qed.

  Lemma lift_lift2: forall (n m: nat),
      lift m ⋆4 lift n = lift (m + n).
  Proof.
    intros. ext [depth ix].
    unfold kc4, compose.
    unfold_ops @Cobind_reader.
    rewrite lift_lift1.
    reflexivity.
  Qed.

  Lemma scoot_zero:
    scoot 0 = id.
  Proof.
    unfold scoot. ext σ ix. cbn.
    rewrite lift_zero.
    rewrite mapd_id.
    replace (ix - 0) with ix by lia.
    reflexivity.
  Qed.

  Lemma scoot_ren_zero:
    scoot_ren 0 = id.
  Proof.
    unfold scoot. ext σ ix. cbn.
    replace (ix - 0) with ix by lia.
    replace (σ ix + 0) with (σ ix) by lia.
    reflexivity.
  Qed.

  Lemma scoot_scoot : forall (n m: nat),
      scoot m ∘ scoot n = scoot (m + n).
  Proof.
    intros. ext σ ix.
    unfold compose, scoot.
    bound_induction.
    - bound_induction.
      + bound_induction.
        { compose near (σ (ix - m - n)) on left.
          rewrite mapd_mapd.
          rewrite lift_lift2.
          do 2 fequal. lia. }
      + bound_induction.
        { compose near (ix - m).
          rewrite mapd_ret.
          unfold compose; cbn.
          fequal. lia. }
    - bound_induction.
  Qed.

  Lemma scoot_ren_scoot_ren : forall (n m: nat),
      scoot_ren m ∘ scoot_ren n = scoot_ren (m + n).
  Proof.
    intros. ext σ ix.
    unfold compose, scoot_ren.
    bound_induction.
    - bound_induction.
      + bound_induction.
        rewrite lift_lift1.
        do 2 rewrite lift_depth_zero.
        do 2 fequal.
        lia.
      + bound_induction.
        rewrite lift_depth_zero.
        lia.
    - bound_induction.
  Qed.

  Corollary scoot_S: forall (n: nat),
      scoot (S n) = scoot n ∘ scoot 1.
  Proof.
    intros.
    replace (S n) with (n + 1) by lia.
    now rewrite scoot_scoot.
  Qed.

  Corollary scoot_ren_S: forall (n: nat),
      scoot_ren (S n) = scoot_ren n ∘ scoot_ren 1.
  Proof.
    intros.
    replace (S n) with (n + 1) by lia.
    now rewrite scoot_ren_scoot_ren.
  Qed.

  Lemma iterate_scoot: forall n,
      scoot n = iterate n (scoot 1).
  Proof.
    intros. induction n.
    - rewrite scoot_zero. reflexivity.
    - rewrite scoot_S.
      rewrite IHn.
      rewrite iterate_rw1.
      reflexivity.
  Qed.

  Lemma scoot_ren_spec: forall ρ n,
      ret ∘ (scoot_ren n ρ) = scoot n (ret ∘ ρ).
  Proof.
    intros.
    ext m.
    unfold compose; cbn.
    unfold scoot, scoot_ren.
    bound_induction.
    compose near (ρ (m - n)).
    rewrite (mapd_ret).
    unfold compose.
    reflexivity.
  Qed.

  Lemma iterate_scoot_ren: forall n,
      scoot_ren n = iterate n (scoot_ren 1).
  Proof.
    intros.
    induction n.
    - rewrite scoot_ren_zero.
      reflexivity.
    - rewrite scoot_ren_S.
      rewrite IHn.
      rewrite iterate_rw1.
      reflexivity.
  Qed.

  Lemma rename_loc_preincr (ρ : nat -> nat) (n: nat):
    rename_loc ρ ⦿ n =
      rename_loc (scoot_ren n ρ).
  Proof.
    unfold rename_loc.
    ext (depth, ix); cbn.
    compose near ρ on right.
    rewrite (scoot_ren_scoot_ren).
    change (?n ● ?m) with (n + m).
    fequal. lia.
  Qed.

  Lemma subst_loc_preincr (σ : nat -> T nat) (n: nat):
      subst_loc σ ⦿ n =
        subst_loc (scoot n σ).
  Proof.
    unfold subst_loc.
    ext (depth, ix); cbn.
    compose near σ on right.
    rewrite (scoot_scoot).
    change (?n ● ?m) with (n + m).
    fequal. lia.
  Qed.

End theory.
