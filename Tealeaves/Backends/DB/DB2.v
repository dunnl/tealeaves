
(** ** De Bruijn operations as defined by Tealeaves *)
(******************************************************************************)
Module DB1.
  Section ops.

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


    (* or uparrow *)
    (*
      fun n => ret (n + 1).
      *)

    Notation "↑" := uparrow.
    Notation "f '✪' g" := (kc1 g f) (at level 30).
    Infix "⋅" := (cons) (at level 10).

    (*
    Definition subst (σ : nat -> T nat) : T nat -> T nat :=
      bind σ.

    Lemma test: forall (a : T nat) (σ : nat -> T nat),
        ↑ ✪ (a ⋅ σ) = σ.
    Proof.
      intros.
      unfold kc1.
      unfold uparrow.
      ext n.
      unfold compose.
      compose near (n + 1) on left.
      rewrite (kmon_bind0).
      unfold cons.
      remember (n + 1) as m.
      destruct m.
      + lia.
      + assert (n = m). lia.
        now subst.
    Qed.

    Lemma test2: forall (a : T nat) (σ ρ : nat -> T nat),
        (a ⋅ σ) ✪ ρ = (subst ρ a) ⋅ (σ ✪ ρ).
    Proof.
      intros.
      unfold kc1.
      ext n.
      unfold compose, cons.
      destruct n.
      - reflexivity.
      - reflexivity.
    Qed.
    *)



    (* raise all free variables by 1 *)
    Definition lift: T nat -> T nat :=
      map_with_policy (cons 0) uparrow.

    (* adjust a substitution to go under one binder *)
    Definition go_under_one_binder (σ: nat -> T nat): nat -> T nat :=
      cons (ret 0) (lift ∘ σ).

    Definition open (σ : nat -> T nat) : T nat -> T nat :=
      bind_with_policy go_under_one_binder σ.

    Definition open_by (u : T nat) : T nat -> T nat :=
      open (u ⋅ ret).

  End ops.
End DB1.



Section equivalence.

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

  Lemma bound_in_1: forall n, DB2.bound_in n 1 = true <-> n = 0.
  Proof.
    intros. unfold DB2.bound_in.
    rewrite ltb_lt.
    lia.
  Qed.

  Lemma bound_in_1': forall n, DB2.bound_in n 1 = (n =? 0).
  Proof.
    intros. destruct n; reflexivity.
  Qed.

  (*
  Lemma tmp:
    bind DB1.uparrow = mapd (DB2.lift 1).
  Proof.
    rewrite bind_to_bindd.
    rewrite mapd_to_bindd.
    fequal.
    ext [depth ix].
    unfold compose; cbn.
    unfold DB1.uparrow.
    destruct depth.
      + reflexivity.
      + destruct (ix <=? depth).
  Abort.
   *)

  Lemma lift_to_lift': forall depth ix,
      iterate depth (DB1.cons 0) S ix =
        DB2.lift 1 (depth, ix).
  Proof.
    intros.
    induction depth.
    - rewrite iterate_rw0.
      unfold id.
      cbn.
      lia.
    - rewrite iterate_rw1.
      unfold compose.
      cbn.
      destruct ix.
      + cbn.
        Check iterate depth (DB1.cons 0).
        Check DB1.cons 0 S.
      Check (DB1.cons (ret 0) S).
      Check (DB1.cons (ret 0) S).
      About DB1.cons.
      Check iterate depth (DB1.cons (ret 0)).
      Check

  Qed.

  Abort.
  Lemma lift_to_lift:
    DB1.lift = mapd (DB2.lift 1).
  Proof.
    unfold DB1.lift, DB1.map_with_policy, DB1.uparrow.
    fequal; ext [depth ix].
    generalize dependent ix.
    induction depth; intro ix.
    - cbn. unfold id. lia.
    - rewrite iterate_rw1.

      unfold compose.
      destruct ix.
      + cbn.
        cbn.
      cbn.
      unfold DB1.cons.
    cbn.

  Lemma tmp:
    DB1.bind_with_policy (DB1.cons (ret 0)) DB1.uparrow =
      mapd (DB2.lift 1).
  Proof.
    intros.
    unfold DB1.bind_with_policy.
    rewrite mapd_to_bindd.
    fequal.
    ext [depth ix].
    unfold compose.
    unfold DB1.uparrow.
    induction depth.
    - cbn. reflexivity.
    - cbn.

  Admitted.

  Lemma under_to_scoot:
    DB1.go_under_one_binder = DB2.scoot 1.
  Proof.
    ext σ ix.
    unfold DB1.go_under_one_binder.
    unfold DB2.scoot.
    rewrite bound_in_1'.
    destruct ix.
    - cbn.
      reflexivity.
    - cbn.
      replace (ix - 0) with ix by lia.
      unfold compose at 1.
      rewrite tmp.
      reflexivity.
  Qed.


  Lemma lemma: forall (depth : nat),
      iterate depth DB1.go_under_one_binder = DB2.scoot depth.
  Proof.
    intros.
    induction depth.
    - intros. cbn.
      rewrite DB2.scoot_zero.
      reflexivity.
    - rewrite iterate_rw1.
      rewrite DB2.scoot_S.
      rewrite IHdepth.
      fequal.
      rewrite under_to_scoot.
      reflexivity.
  Qed.

  Lemma DB1_matches_DB2 :
      DB1.open = DB2.open.
  Proof.
    intros.
    ext σ.
    unfold DB1.open, DB1.bind_with_policy.
    unfold DB2.open.
    fequal.
    ext [depth ix].
    generalize dependent σ.
    induction depth; intro.
    - rewrite DB2.scoot_zero.
      cbn.
      reflexivity.
    - rewrite iterate_rw1.
      rewrite DB2.scoot_S.
      unfold compose.
      rewrite IHdepth.
      rewrite under_to_scoot.
      reflexivity.
  Qed.

End equivalence.

  (*
Lemma key_lemma :
  forall (σ : nat -> term nat) (depth : nat) (ix : nat),
    iterate depth DB1.up σ ix =
      DB2.scoot depth σ ix.
Proof.
  intros. unfold DB1.up, DB2.scoot.
  induction depth.
  - remember (Nat.ltb ix 0).
    symmetry in Heqb.
    destruct b.
    + exfalso. rewrite PeanoNat.Nat.ltb_lt in Heqb. lia.
    + cbn. rewrite DB2.uparrow_zero.
      rewrite (dfun_fmapd1 nat term).
      unfold id. fequal. lia.
  - unfold iterate. unfold compose.
    cbn. admit.
Abort.
*)
