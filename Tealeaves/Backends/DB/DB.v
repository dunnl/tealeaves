From Tealeaves.Misc Require Export
  NaturalNumbers
  Iterate.
From Tealeaves.Theory Require Export
  DecoratedTraversableMonad.

Import DecoratedContainerMonad.
Import Kleisli.DecoratedTraversableMonad.
Import DecoratedTraversableMonad.UsefulInstances.

Import PeanoNat.Nat.
Import Coq.Init.Nat. (* Nat notations *)
Open Scope nat_scope.

Import DecoratedContainerFunctor.Notations.
Import DecoratedMonad.Notations.
Import Kleisli.Comonad.Notations.
Import Monoid.Notations.

Implicit Types (ρ: nat -> nat).

#[local] Generalizable Variables W T U.

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

#[local] Infix "`bound in`" := (bound) (at level 10): tealeaves_scope.

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

Ltac bound_induction_in H :=
  match type of H with
  | context[bound ?ix ?n] =>
      apply (bound_ind ix n);
      let Hord := fresh "Hord" in
      let Hbound := fresh "Hbound" in
      introv Hord Hbound;
      try rewrite Hbound in *;
      try solve [lia | easy]
  end.

(** * Incrementing/lifting indices *)
(******************************************************************************)
Definition lift (x y : nat) : nat := plus x y.
#[local] Notation "( + x )" := (lift x) (format "( + x )").
#[global] Arguments lift x y/.

Lemma lift0: (+0) = id. reflexivity. Qed.

Lemma lift_comp :forall m n, (+m) ∘ (+n) = (+ (m + n)).
Proof.
  intros. unfold compose, lift. ext y.
  lia.
Qed.

Lemma lift_compR n m {X}(f: nat -> X) : (f ∘ (+m)) ∘ (+n) = f ∘ (+ (m + n)).
Proof.
  now rewrite <- lift_comp.
Qed.

Lemma plusSn n m : S n + m = S (n + m). reflexivity. Qed.
Lemma plusnS n m : n + S m = S (n + m). symmetry. apply plus_n_Sm. Qed.
Lemma plusOn n : O + n = n. reflexivity. Qed.
Lemma plusnO n : n + O = n. symmetry. apply plus_n_O. Qed.

Ltac simplify_lift :=
  progress repeat match goal with
    | [|- context[(+0)]] => change (+0) with (@id nat)
    | [|- context[?s S]] => change (s S) with (s (+1))
    | [|- context[S ?n + ?m]] => rewrite (plusSn n m)
    | [|- context[?n + S ?m]] => rewrite (plusnS n m)
    | [|- context[?n + 0]] => rewrite (plusnO n)
    | [|- context[0 + ?n]] => rewrite (plusOn n)
    | [|- context[(+ ?m) ∘ (+ ?n)]] => rewrite (lift_comp m n)
    | [|- context[(?f ∘ (+ ?m)) ∘ (+ ?n)]] => rewrite (lift_compR m n f)
    end.

(** * Cons operation *)
(******************************************************************************)
Definition scons {X : Type} : X -> (nat -> X) -> (nat -> X)  :=
  fun new sub n => match n with
                | O => new
                | S n' => sub n'
                end.

#[local] Infix "⋅" := (scons) (at level 10).

(** ** Properties of scons *)
(******************************************************************************)
Lemma scons_rw0 {A}: forall `(x: A) (σ: nat -> A),
    (x ⋅ σ) 0 = x.
Proof.
  reflexivity.
Qed.

Lemma scons_rw1 {A}: forall `(x: A) (n: nat) (σ: nat -> A),
    (x ⋅ σ) (S n) = σ n.
Proof.
  reflexivity.
Qed.

Lemma scons_sub_id {X}: forall (σ: nat -> X),
    (σ 0) ⋅ (σ ∘ S) = σ.
Proof.
  intros.
  ext ix.
  destruct ix.
  - rewrite scons_rw0.
    reflexivity.
  - rewrite scons_rw1.
    reflexivity.
Qed.

Lemma cons_compose {X Y}: forall (σ: nat -> X) (f: X -> Y) (x: X),
    f ∘ (x ⋅ σ) = (f x) ⋅ (f ∘ σ).
Proof.
  intros; now ext [|n].
Qed.

(** ** Cons and lifting *)
(******************************************************************************)
Lemma cons_eta {X}: forall (σ: nat -> X) (n: nat),
    (σ n) ⋅ (σ ∘ (+ (S n))) = σ ∘ (+ n).
Proof.
  intros.
  unfold compose, lift.
  ext [|m].
  - cbn. simplify_lift. reflexivity.
  - cbn. simplify_lift. reflexivity.
Qed.

Lemma lift_eta n : n ⋅ (+ (S n)) = (+ n).
Proof.
  apply (cons_eta id).
Qed.

(** * Renaming *)
(******************************************************************************)
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

Definition rename `{Mapd_T_inst : Mapd nat T} (ρ : nat -> nat): T nat -> T nat :=
  mapd (T := T) (local__ren ρ).

(* adjust a renaming to go under one binder *)
Definition up__ren (ρ: nat -> nat): nat -> nat :=
  0 ⋅ (S ∘ ρ).

(** ** Properties of renaming *)
(******************************************************************************)
Section renaming_theory.

  Context
    `{Mapd_T_inst : Mapd nat T}
      `{Functor_inst : ! DecoratedFunctor nat T}.

  (** ** Renaming and <<ret>> *)
  (******************************************************************************)
  Lemma lift__ren_zero:
    lift__ren 0 = id.
  Proof.
    unfold lift__ren.
    ext ρ ix.
    bound_induction.
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

  Corollary rename_ret
    `{Return T}
    `{Bindd nat T T}
    `{! Compat_Mapd_Bindd nat T T}
    `{! DecoratedMonad nat T}: forall ρ ix,
      rename ρ (ret ix) = ret (ρ ix).
  Proof.
    intros.
    unfold rename.
    compose near ix.
    rewrite mapd_ret.
    unfold compose.
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
    apply kdf_mapd1.
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
      local__ren ρ2 ⋆1 local__ren ρ1 = local__ren (ρ2 ∘ ρ1).
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
    rewrite kdf_mapd2.
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

  (** ** Relating <<lift__ren>> to <<up__ren>> *)
  (******************************************************************************)
  Lemma lift__ren_1:
    lift__ren 1 = up__ren.
  Proof.
    ext ρ ix.
    unfold lift__ren, up__ren.
    bound_induction.
    - cbn. destruct ix.
      + false.
      + cbn. unfold compose.
        rewrite add_1_r.
        do 2 fequal. lia.
    - apply bound_1 in Hbound.
      subst. reflexivity.
  Qed.

  Lemma lift__ren_repr: forall depth,
      lift__ren depth = iterate depth up__ren.
  Proof.
    intros.
    induction depth.
    - rewrite lift__ren_zero.
      rewrite iterate_rw0.
      reflexivity.
    - ext ρ.
      rewrite lift__ren_S.
      rewrite iterate_rw1.
      rewrite IHdepth.
      rewrite lift__ren_1.
      reflexivity.
  Qed.

  Corollary local__ren_repr: forall ρ depth ix,
      local__ren ρ (depth, ix) = iterate depth up__ren ρ ix.
  Proof.
    intros. cbn.
    rewrite lift__ren_repr.
    reflexivity.
  Qed.

  (** ** Operations with policy *)
  (******************************************************************************)
  Definition map_with_policy `{Mapd nat T}
    (policy : (nat -> nat) -> (nat -> nat)) (ρ : nat -> nat): T nat -> T nat :=
    mapd (fun '(depth, ix) => iterate depth policy ρ ix).

  Lemma rename_policy_repr (ρ : nat -> nat):
    rename (T := T) ρ = map_with_policy up__ren ρ.
  Proof.
    unfold rename, map_with_policy.
    fequal. ext [depth ix].
    apply local__ren_repr.
  Qed.

  Lemma local__ren_preincr_1 (ρ : nat -> nat):
    (local__ren ρ) ⦿ 1 =
      local__ren (up__ren ρ).
  Proof.
    rewrite local__ren_preincr.
    rewrite lift__ren_1.
    reflexivity.
  Qed.

  (** ** Characterizing occurrence *)
  (******************************************************************************)

  Context
    `{Mapdt_inst: Mapdt nat T}
      `{! Compat_Mapd_Mapdt nat T}
      `{DTF_inst : ! DecoratedTraversableFunctor nat T}.

  Lemma ind_rename_iff : forall l n (t:T nat) ρ,
      (n, l) ∈d rename ρ t <-> exists l1,
        (n, l1) ∈d t /\
          l = (if l1 `bound in` n then l1
               else n + ρ (l1 - n)).
  Proof.
    intros.
    unfold rename in *.
    rewrite ind_mapd_iff.
    unfold local__ren, lift__ren.
    setoid_rewrite add_comm at 1.
    intuition; preprocess; eauto.
  Qed.

End renaming_theory.

(** * De Bruijn operations *)
(******************************************************************************)
Section ops.

  Context
    `{ret_inst : Return T}
      `{Mapd_T_inst : Mapd nat T}
      `{Bindd_U_inst : Bindd nat T U}.

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

  (* adjust a substitution to go under one binder *)
  Definition up__sub (σ: nat -> T nat): nat -> T nat :=
    (ret 0) ⋅ (rename (+1) ∘ σ).

End ops.

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

  Lemma local__sub_zero: forall σ n,
    local__sub σ (0, n) = σ n.
  Proof.
    intros. unfold local__sub.
    rewrite lift__sub_zero.
    reflexivity.
  Qed.

  Lemma local__sub_compose_ret: forall σ x,
      (local__sub σ ∘ ret) x = σ x.
  Proof.
    intros.
    unfold_ops @Return_Writer @Monoid_unit_zero.
    unfold compose.
    rewrite local__sub_zero.
    reflexivity.
  Qed.

  Lemma subst_ret: forall σ x,
      subst σ (ret x) = σ x.
  Proof.
    intros.
    unfold subst.
    compose near x on left.
    rewrite bindd_ret.
    apply local__sub_compose_ret.
  Qed.

  Lemma subst_compose_ret: forall σ,
      subst σ ∘ ret = σ.
  Proof.
    intros. ext x.
    unfold compose. apply subst_ret.
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
      rewrite iterate_rw1A.
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
           rewrite kdf_mapd2.
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

  (** ** Substitution and renaming *)
  (******************************************************************************)
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
    now rewrite (rename_to_subst_loc ρ).
     *)
    intros. ext [depth ix]. unfold compose.
    cbn. unfold lift__ren, lift__sub.
    unfold lift.
    bound_induction.
    rewrite rename_ret.
    fequal; lia.
  Qed.

  (** ** up__sub and lift__spec *)
  (******************************************************************************)
  Lemma up__sub_unfold (σ: nat -> T nat):
    up__sub σ = ret 0 ⋅ (subst (ret ∘ (+1)) ∘ σ).
  Proof.
    unfold up__sub.
    rewrite rename_to_subst.
    reflexivity.
  Qed.

  Lemma up_spec:
    lift__sub 1 = up__sub.
  Proof.
    ext σ ix.
    unfold up__sub, lift__sub.
    bound_induction.
    - destruct ix.
      + false.
      + replace (S ix - 1) with ix by lia.
        reflexivity.
    - apply bound_1 in Hbound.
      now subst.
  Qed.

  Lemma local__sub_policy_repr: forall depth ix σ,
      local__sub σ (depth, ix) = iterate depth up__sub σ ix.
  Proof.
    intros.
    unfold local__sub.
    rewrite lift__sub_iter.
    fequal.
    apply up_spec.
  Qed.

  Lemma local__sub_preincr_1 (σ : nat -> T nat):
    (local__sub σ) ⦿ 1 =
      local__sub (up__sub σ).
  Proof.
    rewrite local__sub_preincr.
    rewrite up_spec.
    reflexivity.
  Qed.

  Definition bind_with_policy `{Bindd nat T U}
    (policy : (nat -> T nat) -> (nat -> T nat)) (σ : nat -> T nat): U nat -> U nat :=
    bindd (fun '(depth, ix) => iterate depth policy σ ix).

  Lemma subst_policy_repr (σ : nat -> T nat):
    subst σ = bind_with_policy up__sub σ.
  Proof.
    unfold subst, bind_with_policy.
    fequal.
    ext [depth ix].
    rewrite local__sub_policy_repr.
    reflexivity.
  Qed.

  Lemma iterate_up__sub_unfold (σ: nat -> T nat) (n: nat):
    iterate (S n) up__sub σ = ret 0 ⋅ (subst (ret ∘ (+1)) ∘ iterate n up__sub σ).
  Proof.
    rewrite iterate_rw2A.
    rewrite up__sub_unfold.
    reflexivity.
  Qed.

  (** ** Characterizing occurrence *)
  (******************************************************************************)
  Lemma ind_local_sub1: forall (σ: nat -> T nat) n1 ix1,
      ix1 `bound in` n1 = true ->
                   (0, ix1) ∈d local__sub σ (n1, ix1).
  Proof.
    introv H.
    unfold local__sub, lift__sub.
    bound_induction_in H.
    rewrite ind_ret_iff.
    auto.
  Qed.
  Lemma ind_local_sub2: forall (σ: nat -> T nat) n1 ix1,
      ix1 `bound in` n1 = false ->
                   (0, ix1) ∈d local__sub σ (n1, ix1).
  Proof.
    introv H.
    unfold local__sub, lift__sub.
    bound_induction_in H.
    rewrite ind_rename_iff.
    setoid_rewrite bound_zero.
    unfold lift.
    change (0 + ?n) with n.
    setoid_rewrite sub_0_r.
  Abort.

  Lemma ind_local_sub_iff: forall (σ: nat -> T nat) n2 ix2 n1 ix1,
      (n2, ix2) ∈d local__sub σ (n1, ix1) ->
      (ix1 >= n1 /\
         exists l1 : nat,
           (n2, l1) ∈d σ (ix1 - n1) /\
             ix2 = (if l1 `bound in` n2 then l1 else n2 + (+n1) (l1 - n2)))
      \/ (ix1 < n1 /\ n2 = 0 /\ ix2 = ix1).
  Proof.
    intros.
    unfold local__sub, lift__sub in H.
    bound_induction_in H.
    { rewrite ind_rename_iff in H.
      tauto. }
    { right. rewrite ind_ret_iff in H.
      inversion H; subst. intuition.
    }
  Qed.

  Lemma ind_subst_iff : forall l n (t:U nat) σ,
      (n, l) ∈d subst σ t <-> exists n1 n2 l1,
        (n1, l1) ∈d t /\ (n2, l) ∈d local__sub σ (n1, l1) /\ n = n1 + n2.
  Proof.
    intros. unfold subst in *.
    now rewrite ind_bindd_iff'.
  Qed.

  Lemma ind_subst_iff2 : forall l n (t:U nat) σ,
      (n, l) ∈d subst σ t <->
        ((n, l) ∈d t /\ (l `bound in` n = true))
        \/ exists n1 n2 l1,
          (n1, l1) ∈d t /\
            (n2, l) ∈d local__sub σ (n1, l1) /\ n = n1 + n2.
  Proof.
    intros. unfold subst in *.
    rewrite ind_bindd_iff'.
    split.
    - intros.
      destruct H as [n1 [n2 [a [H1 [H2 H3]]]]].
      assert (H2copy: (n2, l) ∈d local__sub σ (n1, a)) by apply H2.
      unfold local__sub, lift__sub in H2.
      bound_induction_in H2.
      + right.
        exists n1 n2 a. auto.
      + rewrite ind_ret_iff in H2.
        inversion H2; subst.
        simpl_monoid. now left.
    - intros. destruct H.
      + exists n 0 l. splits.
        { tauto. }
        { unfold local__sub, lift__sub.
          bound_induction. now rewrite ind_ret_iff. }
        { easy. }
      + assumption.
  Qed.

End theory.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "↑" := S.
  Notation "'⇑'" := up__sub.
  Notation "'⇑__ren'" := up__ren.
  Notation "f ';' g" := (kc1 g f) (at level 30).
  Infix "⋅" := (scons) (at level 10).
  Notation "( + x )" := (lift x) (format "( + x )").
End Notations.

Import Notations.

(** * Other lemmas *)
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

  Lemma closed_at_sub1: forall (σ: nat -> T nat) (k d1 i1: nat),
      (forall (n: nat), cl_at k (σ n)) ->
      cl_at (k + d1) (lift__sub d1 σ i1).
  Proof.
    introv Hpremise.
    unfold cl_at, cl_at_loc in *.
    unfold lift__sub.
    remember (i1 `bound in` d1) as b.
    intros depth ix Hin.
    rewrite bound_within_spec.
    setoid_rewrite bound_within_spec in Hpremise.
    setoid_rewrite <- bound_lt_iff in Hpremise.
    symmetry in Heqb.
    destruct b.
    - rewrite <- bound_lt_iff in Heqb.
      rewrite ind_ret_iff in Hin.
      destruct Hin as [Hdepth Hix];
        subst; unfold_ops @Monoid_unit_zero.
      rewrite <- bound_lt_iff. lia.
    - rewrite <- bound_lt_iff.
      rewrite <- bound_ge_iff in Heqb.
      rewrite ind_rename_iff in Hin.
      destruct Hin as [l1 [Hin Heq]].
      bound_induction_in Heq.
      unfold lift in Heq.
      specialize (Hpremise (i1 - d1) depth l1 Hin).
      lia.
  Qed.

  Lemma closed_at_sub2:
    forall (t: T nat) (σ: nat -> T nat) (k: nat),
      (forall (n: nat), cl_at k (σ n)) ->
      cl_at k (subst σ t).
  Proof.
    introv Hprem.
    unfold cl_at in *.
    unfold cl_at_loc in *.
    unfold bound_within in *.
    setoid_rewrite ltb_lt.
    setoid_rewrite ltb_lt in Hprem.
    introv Hin.
    rewrite ind_subst_iff in Hin.
    destruct Hin as [d1 [d2 [i1 [H1 [H2 H3]]]]].
    unfold local__sub, lift__sub in *.
    bound_induction_in H2.
    + rewrite ind_rename_iff in H2.
      preprocess.
      unfold lift.
      specialize (Hprem _ _ _ H).
      bound_induction.
    + rewrite ind_ret_iff in H2.
      inversion H2. subst.
      unfold transparent tcs. lia.
  Qed.

  Lemma not_closed_at_ret:
    forall n, ~ (cl_at n (@ret T _ nat n)).
  Proof.
    intros.
    introv H.
    specialize (H 0 n).
    rewrite ind_ret_iff in H.
    specialize (H ltac:(auto)).
    unfold cl_at_loc in H.
    rewrite bound_within_spec in H.
    bound_induction_in H.
  Qed.

  Lemma closed_at_ret:
    forall n, cl_at (S n) (@ret T _ nat n).
  Proof.
    intros.
    unfold cl_at.
    intros.
    rewrite ind_ret_iff in H.
    inversion H. subst. cbn.
    apply leb_refl.
  Qed.

  Lemma closed_at_sub3:
    forall (t: T nat) (σ: nat -> T nat) (k: nat),
      (forall (n: nat), cl_at (k + n + 1) (σ n)) ->
      cl_at k (subst σ t).
  Proof.
    introv Hprem.
    unfold cl_at in *.
    unfold cl_at_loc in *.
    unfold bound_within in *.
    setoid_rewrite ltb_lt.
    setoid_rewrite ltb_lt in Hprem.
    introv Hin.
    rewrite ind_subst_iff in Hin.
    destruct Hin as [n1 [n2 [i1 [H_in_t [H_in_sig H3]]]]].
    apply ind_local_sub_iff in H_in_sig.
    destruct H_in_sig as [Hsig | Hsig].
    + preprocess. bound_induction.
      unfold lift in *.
      specialize (Hprem _ _ _ H0).
  Abort.

  Lemma subst_pw_example (k: nat) (σ1 σ2 : nat -> T nat) (t: T nat):
    cl_at k t ->
    (forall i, i < k -> σ1 i = σ2 i) ->
    subst σ1 t = subst σ2 t.
  Proof.
    unfold subst, cl_at.
    intros Hclosed Hpw.
    apply bindd_respectful.
    intros w a Hin.
    specialize (Hclosed w a Hin).
    unfold cl_at_loc, bound_within in Hclosed.
    apply leb_le in Hclosed.
    unfold local__sub, lift__sub.
    bound_induction. fequal.
    apply Hpw. lia.
  Qed.

End theory.
