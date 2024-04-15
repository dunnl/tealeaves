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

Lemma iterate_rw0' : forall {A : Type} (f : A -> A) a,
    iterate 0 f a = a.
Proof.
  reflexivity.
Qed.

Lemma iterate_rw1' : forall (n : nat) {A : Type} (f : A -> A) a,
    iterate (S n) f a = (iterate n f) (f a).
Proof.
  reflexivity.
Qed.

(** ** Operations with policy *)
(******************************************************************************)
Definition map_with_policy `{Mapd nat T}
  (policy : (nat -> nat) -> (nat -> nat)) (ρ : nat -> nat): T nat -> T nat :=
  mapd (fun '(depth, ix) => iterate depth policy ρ ix).

Definition bind_with_policy `{Bindd nat T U}
  (policy : (nat -> T nat) -> (nat -> T nat)) (σ : nat -> T nat): U nat -> U nat :=
  bindd (fun '(depth, ix) => iterate depth policy σ ix).

  (* Given a depth and local substitution σ,
       adjust σ to account for the depth
       - σ should be a top-level map, e.g.
         σ 0 is the replacement for the first free variable
         σ 1 is the replacement for the second free variable
         ...
   *)

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

  (*
  (* Local function for incrementing free variables
     by <<n>> *)
  (* n: A value by which to increment free indices *)
  Definition raiseFreeBy_loc (n : nat) (p : nat * nat) : nat :=
    match p with
    | (depth, ix) =>
        if bound_in ix depth
        then ix
        else ix + n
    end.

  (* Increment all free indices by <<n>> *)
  Definition raiseFreeBy (n: nat): T nat -> T nat :=
    mapd (raiseFreeBy_loc n).
  *)

  (* Given a depth and renaming ρ, adjust ρ to account for the
     depth *)
  Definition liftRenamingBy: nat -> (nat -> nat) -> (nat -> nat) :=
    fun depth ρ ix =>
      if bound_in ix depth
      then ix
      else let normalized_ix := ix - depth
           in ρ normalized_ix + depth.

  Definition lift__ren (ρ : nat -> nat) (p: nat * nat): nat :=
    match p with
    | (depth, ix) => liftRenamingBy depth ρ ix
    end.

  Definition rename (ρ : nat -> nat): T nat -> T nat :=
    mapd (T := T) (lift__ren ρ).

  (* Given a depth and substitution σ, adjust σ to account for the
       depth *)
  Definition liftSubstitutionBy: nat -> (nat -> T nat) -> (nat -> T nat) :=
    fun depth σ ix =>
      if bound_in ix depth
      then ret ix
      else let normalized_ix := ix - depth
           in rename (fun n => n + depth) (σ normalized_ix).

  Definition lift__sub (σ : nat -> T nat) (p: nat * nat): T nat :=
    match p with
    | (depth, ix) => liftSubstitutionBy depth σ ix
    end.

  Definition subst (σ : nat -> T nat) : U nat -> U nat :=
    bindd (lift__sub σ).

  (*
  Definition one (u: T nat): nat -> T nat :=
    fun n => if n =? 0 then u else ret n.

  Definition subst_one (u : T nat) : U nat -> U nat :=
    subst (one u).
  *)

End ops.

Section alt_presentation.

  Context
    `{ret_inst : Return T}
      `{Mapd_T_inst : Mapd nat T}
      `{Mapd_U_inst : Mapd nat U}
      `{Bindd_U_inst : Bindd nat T U}
      `{ToCtxset_U_inst : ToCtxset nat U}.

  Definition cons {X : Type} : X -> (nat -> X) -> (nat -> X)  :=
    fun new sub n => match n with
                  | O => new
                  | S n' => sub n'
                  end.

  Definition uparrow: nat -> nat := S.

  (* adjust a renaming to go under one binder *)
  Definition up__ren (ρ: nat -> nat): nat -> nat :=
    cons 0 (S ∘ ρ).

  Definition rename_alt: forall (ρ : nat -> nat), T nat -> T nat :=
    map_with_policy up__ren.

  (* adjust a substitution to go under one binder *)
  Definition up (σ: nat -> T nat): nat -> T nat :=
    cons (ret 0) (rename_alt S ∘ σ).

  Definition subst_alt (σ : nat -> T nat): U nat -> U nat :=
    bind_with_policy (T := T) (U := U) up σ.

  (*
  Definition incrementFree: T nat -> T nat :=
    map_with_policy up__ren uparrow.

  Goal incrementFree = rename_alt S.
    reflexivity.
  Qed.
  *)

End alt_presentation.

#[local] Notation "↑" := uparrow.
#[local] Notation "'⇑'" := up.
#[local] Notation "'⇑__ren'" := up.
#[local] Notation "f '✪' g" := (kc1 g f) (at level 30).
#[local] Infix "⋅" := (cons) (at level 10).

Lemma cons_rw0 {A}: forall `(x: A) σ, (x ⋅ σ) 0 = x.
Proof.
  reflexivity.
Qed.

Lemma cons_rw1 {A}: forall `(x: A) (n: nat) σ, (x ⋅ σ) (S n) = σ n.
Proof.
  reflexivity.
Qed.

Lemma cons_sub_id {X}: forall (σ: nat -> X),
    (σ 0) ⋅ (σ ∘ S) = σ.
Proof.
  intros.
  ext ix.
  destruct ix.
  - rewrite cons_rw0.
    reflexivity.
  - rewrite cons_rw1.
    reflexivity.
Qed.

(*
Lemma cons_sub_id {X}: forall (σ: nat -> T nat),
    (x ⋅ σ) ∘ rename S = σ.
Proof.
  intros.
  ext ix.
  destruct ix.
  - rewrite cons_rw0.
    reflexivity.
  - rewrite cons_rw1.
    reflexivity.
Qed.
*)

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

  Lemma bound_in_1: forall ix,
      bound_in ix 1 = true <-> ix = 0.
  Proof.
    destruct ix; intuition.
  Qed.

  (*
  Lemma raiseFreeBy_loc_lt: forall n depth ix,
      ix < depth ->
      raiseFreeBy_loc n (depth, ix) = ix.
  Proof.
    intros. unfold raiseFreeBy_loc.
    rewrite bound_in_lt_iff in H.
    now rewrite H.
  Qed.

  Lemma raiseFreeBy_loc_ge: forall n depth ix,
      ix >= depth ->
      raiseFreeBy_loc n (depth, ix) = ix + n.
  Proof.
    intros. unfold raiseFreeBy_loc.
    rewrite bound_in_ge_iff in H.
    now rewrite H.
  Qed.

  Lemma raiseFreeBy_loc_zero:
    raiseFreeBy_loc 0 = extract.
  Proof.
    ext [depth ix].
    cbn. replace (depth + 0) with depth by lia.
    destruct depth.
    - lia.
    - destruct (ix <=? depth); lia.
  Qed.

  Lemma raiseFreeBy_loc_depth_zero: forall n ix,
      raiseFreeBy_loc n (0, ix) = ix + n.
  Proof.
    reflexivity.
  Qed.
  *)

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

  (*
  Lemma raiseFreeBy_loc_raiseFreeBy_loc1: forall n m depth ix,
      raiseFreeBy_loc m (depth, raiseFreeBy_loc n (depth, ix)) =
        raiseFreeBy_loc (m + n) (depth, ix).
  Proof.
    intros. unfold raiseFreeBy_loc.
    - bound_induction.
      + bound_induction.
      + bound_induction.
  Qed.

  Lemma raiseFreeBy_loc_raiseFreeBy_loc2: forall (n m: nat),
      raiseFreeBy_loc m ⋆4 raiseFreeBy_loc n = raiseFreeBy_loc (m + n).
  Proof.
    intros. ext [depth ix].
    unfold kc4, compose.
    unfold_ops @Cobind_reader.
    rewrite raiseFreeBy_loc_raiseFreeBy_loc1.
    reflexivity.
  Qed.
  *)

  Lemma lift__ren_id:
    lift__ren id = extract.
  Proof.
    ext [depth ix].
    cbn.
    unfold liftRenamingBy, id.
    bound_induction.
  Qed.

  Lemma lift__ren_zero: forall ρ ix,
    lift__ren ρ (0, ix) = ρ ix.
  Proof.
    intros. cbn.
    rewrite add_0_r.
    fequal. lia.
  Qed.

  Corollary rename_ret: forall ρ ix,
      rename ρ (ret ix) = ret (ρ ix).
  Proof.
    intros.
    unfold rename.
    compose near ix.
    rewrite mapd_ret.
    unfold transparent tcs.
    unfold compose. cbn.
    fequal. rewrite add_0_r.
    fequal. lia.
  Qed.

  Lemma liftRenamingBy_zero:
    liftRenamingBy 0 = id.
  Proof.
    unfold liftSubstitutionBy. ext σ ix. cbn.
    replace (ix - 0) with ix by lia.
    replace (σ ix + 0) with (σ ix) by lia.
    reflexivity.
  Qed.

  Lemma liftRenamingBy_compose : forall (n m: nat),
      liftRenamingBy m ∘ liftRenamingBy n = liftRenamingBy (m + n).
  Proof.
    intros. ext σ ix.
    unfold compose, liftRenamingBy.
    bound_induction.
    - bound_induction.
      + bound_induction.
        rewrite (add_comm m n).
        rewrite add_assoc.
        fequal. fequal. fequal. lia.
      + bound_induction.
    - bound_induction.
  Qed.

  Corollary liftRenamingBy_S: forall (n: nat) ρ,
      liftRenamingBy (S n) ρ = liftRenamingBy n (liftRenamingBy 1 ρ).
  Proof.
    intros.
    replace (S n) with (n + 1) by lia.
    compose near ρ on right.
    now rewrite liftRenamingBy_compose.
  Qed.

  Lemma iterate_liftRenamingBy: forall n,
      liftRenamingBy n = iterate n (liftRenamingBy 1).
  Proof.
    intros.
    induction n.
    - rewrite liftRenamingBy_zero.
      reflexivity.
    - ext ρ.
      rewrite liftRenamingBy_S.
      rewrite IHn.
      rewrite iterate_rw1.
      reflexivity.
  Qed.

  Lemma rename_rename_loc: forall ρ2 ρ1,
      lift__ren ρ2 ⋆4 lift__ren ρ1 = lift__ren (ρ2 ∘ ρ1).
  Proof.
    intros.
    ext [depth ix].
    cbn.
    compose near ix on left.
    unfold liftRenamingBy.
    unfold compose.
    bound_induction.
    bound_induction.
    fequal. fequal. lia.
    bound_induction.
  Qed.

  Lemma rename_rename : forall ρ2 ρ1,
      rename ρ2 ∘ rename ρ1 = rename (T := T) (ρ2 ∘ ρ1).
  Proof.
    intros.
    unfold rename.
    rewrite mapd_mapd.
    rewrite rename_rename_loc.
    reflexivity.
  Qed.

  Lemma liftSubstitutionBy_zero:
    liftSubstitutionBy 0 = id.
  Proof.
    ext σ ix. unfold id.
    unfold liftSubstitutionBy.
    cbn.
    replace (ix - 0) with ix by lia.
    replace (fun n => n + 0) with (@id nat).
    2:{ ext n. unfold id. lia. }
    unfold rename.
    rewrite lift__ren_id.
    rewrite mapd_id.
    reflexivity.
  Qed.

  Lemma liftSubstitutionBy_compose : forall (n m: nat),
      liftSubstitutionBy m ∘ liftSubstitutionBy n =
        liftSubstitutionBy (m + n).
  Proof.
    intros. ext σ ix.
    unfold compose, liftSubstitutionBy.
    bound_induction.
    - bound_induction.
      + bound_induction.
        compose near (σ (ix - m - n)) on left.
        rewrite rename_rename.
        unfold compose at 1.
        fequal.
        * ext x. lia.
        * fequal. lia.
      + bound_induction.
        compose near (ix - m).
        unfold rename.
        rewrite mapd_ret.
        unfold compose; cbn.
        fequal.
        unfold_ops @Monoid_unit_zero.
        lia.
    - bound_induction.
  Qed.

  Corollary liftSubstitutionBy_S: forall (n: nat) σ,
      liftSubstitutionBy (S n) σ =
        liftSubstitutionBy n (liftSubstitutionBy 1 σ).
  Proof.
    intros.
    replace (S n) with (n + 1) by lia.
    compose near σ on right.
    now rewrite liftSubstitutionBy_compose.
  Qed.

  Lemma iterate_liftSubstitutionBy: forall n,
      liftSubstitutionBy n = iterate n (liftSubstitutionBy 1).
  Proof.
    intros. induction n.
    - rewrite liftSubstitutionBy_zero.
      reflexivity.
    - ext σ.
      rewrite liftSubstitutionBy_S.
      rewrite iterate_rw1'.
      rewrite IHn.
      reflexivity.
  Qed.

  Lemma liftRenamingBy_spec: forall ρ n,
      ret ∘ liftRenamingBy n ρ = liftSubstitutionBy n (ret ∘ ρ).
  Proof.
    intros.
    ext m.
    unfold compose; cbn.
    unfold liftSubstitutionBy, liftRenamingBy.
    bound_induction.
    rewrite rename_ret.
    reflexivity.
  Qed.

  Lemma lift__ren_preincr (ρ : nat -> nat) (n: nat):
    lift__ren ρ ⦿ n =
      lift__ren (liftRenamingBy n ρ).
  Proof.
    ext (depth, ix); cbn.
    change (?n ● ?m) with (n + m).
    compose near ρ.
    rewrite (liftRenamingBy_compose).
    fequal; lia.
  Qed.

  Lemma lift__sub_preincr (σ : nat -> T nat) (n: nat):
    lift__sub σ ⦿ n =
      lift__sub (liftSubstitutionBy n σ).
  Proof.
    unfold lift__sub.
    ext (depth, ix); cbn.
    compose near σ on right.
    rewrite (liftSubstitutionBy_compose).
    change (?n ● ?m) with (n + m).
    fequal. lia.
  Qed.

  Lemma liftRenamingBy_1:
      liftRenamingBy 1 = up__ren.
  Proof.
    intros. ext ρ ix.
    unfold liftRenamingBy.
    unfold up__ren.
    bound_induction.
    - cbn. destruct ix.
      + false.
      + cbn. unfold compose.
        rewrite add_1_r.
        do 2 fequal. lia.
    - apply bound_in_1 in Hbound.
      subst. reflexivity.
  Qed.

  Lemma liftRenaming_policy_repr: forall depth,
    liftRenamingBy depth = iterate depth up__ren.
  Proof.
    intros. induction depth.
    - ext ρ ix. cbn.
      rewrite add_0_r.
      fequal; lia.
    - ext ρ ix.
      rewrite iterate_rw1'.
      rewrite liftRenamingBy_S.
      rewrite IHdepth.
      rewrite liftRenamingBy_1.
      reflexivity.
  Qed.

  Corollary lift__ren_policy_repr: forall ρ depth ix,
      lift__ren ρ (depth, ix) = iterate depth up__ren ρ ix.
  Proof.
    intros. cbn.
    rewrite liftRenaming_policy_repr.
    reflexivity.
  Qed.

  Lemma rename_policy_repr (ρ : nat -> nat):
    rename (T := T) ρ = rename_alt ρ.
  Proof.
    unfold rename, rename_alt.
    unfold map_with_policy.
    fequal. ext [depth ix].
    apply lift__ren_policy_repr.
  Qed.

  (*
  Lemma liftRenaming_S: forall depth ix,
      liftRenamingBy depth S ix = raiseFreeBy_loc 1 (depth, ix).
  Proof.
    intros.
    induction depth.
    - cbn. rewrite add_0_r. lia.
    - cbn. unfold liftRenamingBy.
      rewrite add_0_r.
      bound_induction.
      + cbn.
        assert (ix <=? depth = false).
        rewrite leb_gt. lia.
        rewrite H.
        rewrite add_1_r. lia.
      + assert (ix <=? depth = true).
        rewrite leb_le. lia. rewrite H. reflexivity.
  Qed.
   *)

  (*
  Corollary lift__ren_S:
    lift__ren S = raiseFreeBy_loc 1.
  Proof.
    ext [depth ix]. cbn.
    apply liftRenaming_S.
  Qed.
   *)


  (*
  Lemma incrementFree_spec:
    rename (U := U) S = incrementFree.
  Proof.
    unfold incrementFree.
    rewrite rename_policy_repr.
    reflexivity.
  Qed.
  *)

  (*
  Lemma raiseFreeBy_spec: forall depth,
    rename (T := T) (fun n => n + depth) = raiseFreeBy depth.
  Proof.
    intros.
    unfold raiseFreeBy.
    unfold rename.
    fequal.
    unfold lift__ren.
    unfold raiseFreeBy_loc.
    unfold liftRenamingBy.
    ext [depth' ix].
    bound_induction.
  Qed.
   *)

  Lemma up_spec:
    liftSubstitutionBy 1 = up.
  Proof.
    ext σ ix.
    unfold up.
    unfold liftSubstitutionBy.
    bound_induction.
    - apply bound_in_ge_iff in Hbound.
      assert (Hgt1: exists ix', ix = S ix').
      { destruct ix. false; lia. eauto. }
      destruct Hgt1 as [ix' Heq]; subst.
      rewrite cons_rw1; unfold compose at 1.
      replace (S ix' - 1) with ix' by lia.
      rewrite <- rename_policy_repr.
      fequal. ext n. lia.
    - apply bound_in_1 in Hbound.
      now subst.
  Qed.

  (*
  Goal forall (n: nat) σ,
      (0 ⋅ (1 ⋅ σ)) n =
        if bound_in n 2 then n else σ (n - 2).
  Proof.
    intros. bound_induction.
    - unfold cons.
      destruct n. lia.
      destruct n. lia. cbn.
      fequal. lia.
    - unfold cons.
      destruct n. lia.
      destruct n. lia.
      lia.
  Qed.
  *)

  Lemma lift__sub_policy_repr: forall depth ix σ,
      lift__sub σ (depth, ix) = iterate depth up σ ix.
  Proof.
    intros.
    unfold lift__sub.
    rewrite iterate_liftSubstitutionBy.
    fequal.
    apply up_spec.
  Qed.

  Lemma subst_policy_repr (σ : nat -> T nat):
    subst σ = subst_alt σ.
  Proof.
    unfold subst, subst_alt.
    unfold bind_with_policy.
    fequal.
    ext [depth ix].
    rewrite lift__sub_policy_repr.
    reflexivity.
  Qed.

End theory.
