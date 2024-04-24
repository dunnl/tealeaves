From Tealeaves.Misc Require Export
  NaturalNumbers.
From Tealeaves.Theory Require Export
  DecoratedTraversableMonad.

Import PeanoNat.Nat.
Import Coq.Init.Nat. (* Nat notations *)
Open Scope nat_scope.

Implicit Types (ρ: nat -> nat).

Module Notations.
  Export Categorical.Applicative.Notations.
  Export Kleisli.Comonad.Notations.
  Export Kleisli.DecoratedMonad.Notations.
  Export Kleisli.TraversableFunctor.Notations.
  Export Kleisli.TraversableMonad.Notations.
  Export Kleisli.DecoratedTraversableFunctor.Notations.
  Export Kleisli.DecoratedTraversableMonad.Notations.
  Export Kleisli.DecoratedContainerFunctor.Notations.
  Export Categorical.ContainerFunctor.Notations.
  Export Misc.Product.Notations.
  Export Monoid.Notations.
  Export Misc.Subset.Notations.
  Export List.ListNotations.
End Notations.

Import Notations.

#[local] Generalizable Variables W T U.

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

(** * Closure *)
(******************************************************************************)
Section section.

  Context
    `{ret_inst : Return T}
      `{Mapd_T_inst : Mapd nat T}
      `{Mapd_U_inst : Mapd nat U}
      `{Bindd_U_inst : Bindd nat T U}
      `{ToCtxset_U_inst : ToCtxset nat U}.

  Definition bound_within (gap: nat) : nat -> nat -> bool :=
    fun ix depth => ix <? depth + gap.

  Definition bound: nat -> nat -> bool :=
    bound_within 0.

  Definition cl_at_loc (gap: nat) (p: nat * nat): bool :=
    match p with
    | (depth, ix) => bound_within gap ix depth
    end.

  Definition cl_at (gap: nat) (t: U nat): Prop :=
    forall (depth ix: nat),
      (depth, ix) ∈d t ->
      cl_at_loc gap (depth, ix) = true.

  Definition closed (t: U nat): Prop :=
    cl_at 0 t.

End section.

Infix "`bound in`" := (bound) (at level 10).

(** ** Boundedness and closure *)
(******************************************************************************)
Lemma bound_within_spec: forall ix d k,
    bound_within k ix d =
      ix `bound in` (d + k).
Proof.
  intros. cbn. replace (d + k + 0) with (d + k) by lia.
  reflexivity.
Qed.

Lemma bound_zero: forall ix,
    ix `bound in` 0 = false.
Proof.
  reflexivity.
Qed.

Lemma bound_lt: forall ix n,
    ix < n -> ix `bound in` n = true.
Proof.
  introv Hlt.
  rewrite <- ltb_lt in Hlt.
  unfold bound, bound_within.
  replace (n + 0) with n by lia.
  destruct n; auto.
Qed.

Lemma bound_lt_iff: forall ix n,
    ix < n <-> ix `bound in` n = true.
Proof.
  intros. split.
  - apply bound_lt.
  - cbn. destruct n.
    + inversion 1.
    + cbn. rewrite leb_le. lia.
Qed.

Lemma bound_ge: forall ix n,
    ix >= n -> ix `bound in` n = false.
Proof.
  introv Hlt.
  unfold bound, bound_within.
  replace (n + 0) with n by lia.
  destruct n; cbn; auto.
  now rewrite leb_gt.
Qed.

Lemma bound_ge_iff: forall ix n,
    ix >= n <-> ix `bound in` n = false.
Proof.
  intros. split.
  - apply bound_ge.
  - cbn. replace (n + 0) with n by lia.
    destruct n.
    + lia.
    + intros.
      rewrite leb_gt in H.
      lia.
Qed.

Lemma bound_ind: forall ix n (P:Prop),
    (ix >= n -> ix `bound in` n = false -> P) ->
    (ix < n -> ix `bound in` n = true -> P) ->
    P.
Proof.
  introv.
  rewrite <- bound_ge_iff.
  rewrite <- bound_lt_iff.
  introv Hge Hlt.
  compare naturals ix and n; auto.
  apply Hge; lia.
Qed.

Lemma bound_mono: forall ix n m,
    m > n ->
    (ix `bound in` n = true) ->
    ix `bound in` m = true.
Proof.
  introv Hlt Hbound.
  rewrite <- bound_lt_iff in Hbound.
  rewrite <- bound_lt_iff.
  lia.
Qed.

Lemma bound_rev_mono: forall ix n m,
    m < n ->
    bound ix n = false ->
    bound ix m = false.
Proof.
  introv Hlt Hbound.
  rewrite <- bound_ge_iff in Hbound.
  rewrite <- bound_ge_iff.
  lia.
Qed.

Lemma bound_1: forall ix,
    bound ix 1 = true <-> ix = 0.
Proof.
  destruct ix; intuition.
Qed.

Ltac bound_induction :=
  match goal with
  | |- context[bound ?ix ?n] =>
      apply (bound_ind ix n);
      let Hord := fresh "Hord" in
      let Hbound := fresh "Hbound" in
      introv Hord Hbound;
      try rewrite Hbound in *;
      try solve [lia | easy]
  end.

(* Autosubst lift *)
(* plus with different simplification behaviour *)

Definition lift (x y : nat) : nat := plus x y.
Notation "( + x )" := (lift x) (format "( + x )").
#[global] Arguments lift x y/.


Lemma lift0 : (+0) = id. reflexivity. Qed.

Lemma lift_comp :forall m n, (+m) ∘ (+n) = (+ (m + n)).
Proof.
  intros. unfold compose, lift. ext y.
  lia.
Qed.

(*
Ltac normalize_lift :=
  rewrite ?lift_comp.

Lemma lift_scons x f n : (+S n) >>> (x .: f) = (+n) >>> f.
Proof. reflexivity. Qed.

Lemma lift_comp n m : (+n) >>> (+m) = (+m+n).
Proof. f_ext; intros x; simpl. now rewrite plusA. Qed.

Lemma lift_compR n m f : (+n) >>> ((+m) >>> f) = (+m+n) >>> f.
Proof. now rewrite <- lift_comp. Qed.

End LemmasForFun.

Lemma lift_eta n : n .: (+S n) = (+ n).
Proof. apply (scons_eta id). Qed.
*)

(** * De Bruijn operations *)
(******************************************************************************)
Section ops.

  Context
    `{ret_inst : Return T}
      `{Mapd_T_inst : Mapd nat T}
      `{Mapd_U_inst : Mapd nat U}
      `{Bindd_U_inst : Bindd nat T U}
      `{ToCtxset_U_inst : ToCtxset nat U}.

  (* Given a depth and renaming ρ, adjust ρ to account for the
     depth *)
  Definition lift__ren: nat -> (nat -> nat) -> (nat -> nat) :=
    fun depth ρ ix =>
      if bound ix depth
      then ix
      else let free_ix := ix - depth
           in ρ free_ix + depth.

  Definition local__ren (ρ : nat -> nat) (p: nat * nat): nat :=
    match p with
    | (depth, ix) => lift__ren depth ρ ix
    end.

  Definition rename (ρ : nat -> nat): T nat -> T nat :=
    mapd (T := T) (local__ren ρ).

  (* Given a depth and substitution σ, adjust σ to account for the
       depth *)
  Definition lift__sub: nat -> (nat -> T nat) -> (nat -> T nat) :=
    fun depth σ ix =>
      if ix `bound in` depth
      then ret ix
      else let free_ix := ix - depth
           in rename (+ depth) (σ free_ix).

  Definition local__sub (σ : nat -> T nat) (p: nat * nat): T nat :=
    match p with
    | (depth, ix) => lift__sub depth σ ix
    end.

  Definition subst (σ : nat -> T nat) : U nat -> U nat :=
    bindd (local__sub σ).

  Definition one (u: T nat): nat -> T nat :=
    fun n => if n =? 0 then u else ret n.

  Definition subst_one (u : T nat) : U nat -> U nat :=
    subst (one u).

End ops.

(** ** Properties of renaming *)
(******************************************************************************)
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
      `{Monad_inst : ! DecoratedTraversableMonad nat T}.

  Context
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

  (** ** Renaming and <<ret>> *)
  (******************************************************************************)
  Lemma lift__ren_zero:
    lift__ren 0 = id.
  Proof.
    unfold lift__sub.
    ext ρ ix. cbn; unfold id.
    replace (ix - 0) with ix by lia.
    replace (ρ ix + 0) with (ρ ix) by lia.
    reflexivity.
  Qed.

  Corollary local__ren_zero: forall ρ ix,
    local__ren ρ (0, ix) = ρ ix.
  Proof.
    intros.
    unfold local__ren.
    rewrite lift__ren_zero.
    reflexivity.
  Qed.

  Corollary rename_ret: forall ρ ix,
      rename ρ (ret ix) = ret (ρ ix).
  Proof.
    intros.
    unfold rename.
    compose near ix.
    rewrite mapd_ret.
    unfold compose.
    match goal with
    | [|- context[@ret _ _ ?x]] =>
        try let s := constr:(ret x) in progress change (ret x) with s
    end.
    unfold_ops @Return_Writer.
    unfold_ops @Monoid_unit_zero.
    rewrite local__ren_zero.
    reflexivity.
  Qed.

  (** ** Renaming identity *)
  (******************************************************************************)
  Lemma lift__ren_id: forall depth,
      lift__ren depth id = id.
  Proof.
    unfold lift__ren.
    intro depth. ext ix.
    unfold id.
    bound_induction.
  Qed.

  Corollary local__ren_id:
    local__ren id = extract.
  Proof.
    ext [depth ix].
    unfold local__ren.
    rewrite lift__ren_id.
    reflexivity.
  Qed.

  Lemma remame_id:
    rename id = (@id (T nat)).
  Proof.
    unfold rename.
    rewrite local__ren_id.
    apply mapd_id.
  Qed.

  (** ** Composition of renaming *)
  (******************************************************************************)
  Lemma lift__ren_loc_compose1: forall depth ix ρ1 ρ2,
      ix >= depth ->
      lift__ren depth ρ2 (ρ1 (ix - depth) + depth) =
        ρ2 (ρ1 (ix - depth)) + depth.
  Proof.
    intros. unfold lift__ren.
    bound_induction.
    cbn. fequal. fequal. lia.
  Qed.

  Lemma lift__ren_loc_compose2: forall ρ depth ix,
      ix < depth ->
      lift__ren depth ρ ix = ix.
  Proof.
    intros. unfold lift__ren.
    bound_induction.
  Qed.

  Lemma lift__ren_loc_compose: forall depth ρ1 ρ2,
      lift__ren depth ρ2 ∘ lift__ren depth ρ1 =
        lift__ren depth (ρ2 ∘ ρ1).
  Proof.
    intros. ext ix.
    unfold compose.
    unfold lift__ren at 2 3.
    bound_induction;
      auto using lift__ren_loc_compose1, lift__ren_loc_compose2.
  Qed.

  Lemma rename_rename_loc: forall ρ2 ρ1,
      local__ren ρ2 ⋆4 local__ren ρ1 = local__ren (ρ2 ∘ ρ1).
  Proof.
    intros.
    ext [depth ix]. cbn.
    compose near ix on left.
    rewrite lift__ren_loc_compose.
    reflexivity.
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

  (** ** Iterating lifting *)
  (******************************************************************************)
  Lemma lift__ren_compose: forall (n m: nat),
      lift__ren m ∘ lift__ren n = lift__ren (m + n).
  Proof.
    intros. ext σ ix.
    unfold compose, lift__ren.
    bound_induction.
    - bound_induction.
      + bound_induction.
        rewrite (add_comm m n).
        rewrite add_assoc.
        fequal. fequal. fequal. lia.
      + bound_induction.
    - bound_induction.
  Qed.

  Corollary lift__ren_S: forall (n: nat) ρ,
      lift__ren (S n) ρ = lift__ren n (lift__ren 1 ρ).
  Proof.
    intros.
    replace (S n) with (n + 1) by lia.
    compose near ρ on right.
    now rewrite lift__ren_compose.
  Qed.

  Lemma lift__ren_iter: forall n,
      lift__ren n = iterate n (lift__ren 1).
  Proof.
    intros.
    induction n.
    - rewrite lift__ren_zero.
      reflexivity.
    - ext ρ.
      rewrite lift__ren_S.
      rewrite IHn.
      rewrite iterate_rw1.
      reflexivity.
  Qed.

  Lemma local__ren_preincr (ρ : nat -> nat) (n: nat):
    (local__ren ρ) ⦿ n =
      local__ren (lift__ren n ρ).
  Proof.
    ext (depth, ix); cbn.
    change (?n ● ?m) with (n + m).
    compose near ρ.
    rewrite (lift__ren_compose).
    fequal; lia.
  Qed.

  (** * Properties of substitution *)
  (******************************************************************************)

  (** ** Substitution and ret *)
  (******************************************************************************)
  Lemma lift__sub_zero:
    lift__sub 0 = id.
  Proof.
    ext σ ix. unfold id.
    unfold lift__sub.
    cbn.
    replace (ix - 0) with ix by lia.
    replace (+ 0) with (@id nat).
    2:{ ext n. unfold lift, id. lia. }
    unfold rename.
    rewrite local__ren_id.
    rewrite mapd_id.
    reflexivity.
  Qed.

  Lemma subst_compose_ret: forall σ x,
      (local__sub σ ∘ ret) x = σ x.
  Proof.
    intros.
    unfold_ops @Return_Writer @Monoid_unit_zero.
    unfold compose.
    unfold local__sub.
    rewrite lift__sub_zero.
    reflexivity.
  Qed.

  Lemma subst_ret: forall σ x,
      subst σ (ret x) = σ x.
  Proof.
    intros.
    unfold subst.
    compose near x on left.
    rewrite bindd_ret.
    apply subst_compose_ret.
  Qed.

  (** ** Substitution and identity *)
  (******************************************************************************)
  Lemma lift__sub_id: forall depth ix,
      lift__sub depth ret ix = (ret ∘ extract) (depth, ix).
  Proof.
    intros.
    unfold lift__sub.
    bound_induction.
    rewrite rename_ret.
    unfold compose. cbn.
    fequal. lia.
  Qed.

  Corollary local__subst_id:
    local__sub (T := T) (@ret T _ nat) = ret ∘ extract.
  Proof.
    unfold local__sub. ext [depth ix].
    apply lift__sub_id.
  Qed.

  Lemma subst_id:
      subst (@ret T _ nat) = id.
  Proof.
    unfold subst.
    rewrite local__subst_id.
    apply bindd_id.
  Qed.

  (** ** Iterated lifting *)
  (******************************************************************************)
  Lemma lift__sub_compose : forall (n m: nat),
      lift__sub m ∘ lift__sub n =
        lift__sub (m + n).
  Proof.
    intros. ext σ ix.
    unfold compose, lift__sub.
    bound_induction.
    - bound_induction.
      + bound_induction.
        compose near (σ (ix - m - n)) on left.
        rewrite rename_rename.
        rewrite lift_comp.
        fequal. fequal.
        lia.
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

  Corollary lift__sub_S: forall (n: nat) σ,
      lift__sub (S n) σ =
        lift__sub n (lift__sub 1 σ).
  Proof.
    intros.
    replace (S n) with (n + 1) by lia.
    compose near σ on right.
    now rewrite lift__sub_compose.
  Qed.

  Lemma lift__sub_iter: forall n,
      lift__sub n = iterate n (lift__sub 1).
  Proof.
    intros. induction n.
    - rewrite lift__sub_zero.
      reflexivity.
    - ext σ.
      rewrite lift__sub_S.
      rewrite iterate_rw1'.
      rewrite IHn.
      reflexivity.
  Qed.

  Lemma local__sub_preincr (σ : nat -> T nat) (n: nat):
    (local__sub σ) ⦿ n =
      local__sub (lift__sub n σ).
  Proof.
    unfold local__sub.
    ext (depth, ix); cbn.
    compose near σ on right.
    rewrite (lift__sub_compose).
    change (?n ● ?m) with (n + m).
    fequal. lia.
  Qed.

  (** ** Substitution and composition *)
  (******************************************************************************)
  Lemma subst_subst_loc: forall (σ2 σ1: nat -> T nat),
      local__sub (T := T) σ2 ⋆5 local__sub (T := T) σ1 =
        local__sub (T := T) (subst σ2 ∘ σ1).
  Proof.
    intros.
    unfold kc5.
    ext [depth ix].
    unfold local__sub at 2 3.
    unfold lift__sub.
    bound_induction.
    2:{ compose near ix on left.
        rewrite bindd_ret.
        unfold compose.
        unfold_ops @Return_Writer.
        unfold local__sub. cbn.
        rewrite monoid_id_l.
        unfold lift__sub.
        rewrite Hbound. reflexivity. }
    { unfold compose at 1.
      unfold rename.
      rewrite local__sub_preincr.
      compose near (σ1 (ix - depth)) on left.
      compose near (σ1 (ix - depth)) on right.
      rewrite bindd_mapd.
      unfold subst.
      rewrite mapd_bindd.
      fequal.
      ext [depth' ix'].
      { rewrite local__ren_preincr.
        cbn. unfold lift__ren at 1.
        unfold lift__sub at 3.
        bound_induction.
        -  unfold lift at 1.
           replace (depth + (ix' - depth') + depth') with (ix' + depth) by lia.
           unfold rename.
           compose near (σ2 (ix' - depth')).
           rewrite mapd_mapd.
           rewrite rename_rename_loc.
           unfold lift__sub.
           bound_induction.
           bound_induction.
           replace (ix' + depth - depth' - depth) with (ix' - depth') by lia.
           compose near (σ2 (ix' - depth')) on left.
           rewrite rename_rename.
           unfold rename. fequal.
           unfold compose.
           fequal.
           ext m. unfold lift__ren.
           unfold lift.
           bound_induction.
        - compose near ix' on right.
          rewrite mapd_ret.
          compose near σ2 on left.
          rewrite lift__sub_compose.
          unfold compose. unfold transparent tcs.
          cbn.
          unfold lift__sub.
          bound_induction.
          fequal.
          unfold lift__ren.
          replace (ix' - 0) with ix' by lia. bound_induction.
      }
    }
  Qed.

  Lemma subst_subst : forall (σ2 σ1: nat -> T nat),
      subst σ2 ∘ subst σ1 = subst (T := T) (subst σ2 ∘ σ1).
  Proof.
    intros.
    unfold subst.
    rewrite bindd_bindd.
    rewrite subst_subst_loc.
    reflexivity.
  Qed.

  Lemma lift__ren_to_sub: forall n ρ,
      ret ∘ lift__ren n ρ = lift__sub n (ret ∘ ρ).
  Proof.
    intros. ext m.
    unfold compose; cbn.
    unfold lift__sub, lift__ren.
    unfold lift.
    bound_induction.
    rewrite rename_ret.
    fequal. lia.
  Qed.

  Lemma rename_to_subst_loc: forall ρ,
      ret ∘ local__ren ρ = local__sub (T := T) (ret ∘ ρ).
  Proof.
    intros. ext [depth ix].
    unfold compose. cbn.
    compose near ix on left.
    rewrite lift__ren_to_sub.
    reflexivity.
  Qed.

  Lemma rename_to_subst : forall ρ,
      rename ρ = subst (U := T) (ret ∘ ρ).
  Proof.
    intros.
    unfold rename, subst.
    rewrite mapd_to_bindd.
    fequal.
    (* Fails with a universe error for some reason
    rewrite (rename_to_subst_loc ρ).
     *)
    intros. ext [depth ix]. unfold compose.
    cbn. unfold lift__ren, lift__sub.
    unfold lift.
    bound_induction.
    rewrite rename_ret.
    fequal; lia.
  Qed.

  (** * Closure and substitution *)
  (******************************************************************************)
  Lemma ind_open_iff : forall l n (t:U nat) σ,
      (n, l) ∈d subst σ t <-> exists n1 n2 l1,
        (n1, l1) ∈d t /\ (n2, l) ∈d local__sub σ (n1, l1) /\ n = n1 + n2.
  Proof.
    intros. unfold subst in *.
    now rewrite ind_bindd_iff'.
  Qed.

  Lemma hm: forall (σ: nat -> T nat) (k d1 i1: nat),
    (forall (n: nat), cl_at k (σ n)) ->
    cl_at (k + d1) (lift__sub d1 σ i1).
    Proof.
    intros.
    unfold cl_at, cl_at_loc in *.
    unfold lift__sub.
    remember (i1 `bound in` d1) as b.
    intros depth ix Hin.
    rewrite bound_within_spec.
    setoid_rewrite bound_within_spec in H.
    setoid_rewrite <- bound_lt_iff in H.
    symmetry in Heqb.
    destruct b.
    - rewrite <- bound_lt_iff in Heqb.
       rewrite ind_ret_iff in Hin.
      destruct Hin as [Hdepth Hix];
        subst; unfold_ops @Monoid_unit_zero.
      rewrite <- bound_lt_iff. lia.
    - rewrite <- bound_lt_iff.
      rewrite <- bound_ge_iff in Heqb.
      specialize (H (i1 - d1) depth ix).
      admit.
    Admitted.

  Lemma hmm:
    forall (t: U nat) (σ: nat -> T nat) (k: nat),
    (forall (n: nat), cl_at k (σ n)) ->
    cl_at k (subst σ t).
  Proof.
    introv Hprem.
    unfold cl_at in *.
    unfold cl_at_loc in *.
    introv Hin.
    rewrite ind_open_iff in Hin.
    destruct Hin as [d1 [d2 [i1 [H1 [H2 H3]]]]].
    cbn.
  Admitted.


End theory.
