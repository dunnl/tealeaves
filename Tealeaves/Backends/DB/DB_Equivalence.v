


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



