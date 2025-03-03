From Tealeaves Require Export
  Examples.LambdaNominal.Syntax
  Examples.LambdaNominal.Categorical
  Examples.LambdaNominal.Kleisli
  Examples.LambdaNominal.Raw
  Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly
  Classes.Categorical.DecoratedTraversableMonadPoly
  Functors.Subset
  Functors.Constant
  Backends.LN.AtomSet
  Backends.Named.NamedTraditional
  Simplification.Binddt.

Import DecoratedTraversableMonadPoly.DerivedOperations.
Import Kleisli.DecoratedTraversableMonadPoly.DerivedOperations.
Import Kleisli.DecoratedTraversableMonadPoly.
Import ContainerFunctor.Notations.

#[local] Generalizable Variables G.

Instance: Kleisli.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly term.
Admitted.

Section rw.

  Context
    {B1 V1 B2 V2: Type}
    `{Applicative G}
    {g: list B1 * B1 -> G B2}
    {f: list B1 * V1 -> G (term B2 V2)}.
    Lemma sub_term_spec: forall v,
    substitute (Substitute := Binddt_Categorical term) g f (tvar v) =
    substitute (Substitute := Substitute_lambda_term) g f (tvar v).
    Proof.
    intros.
    unfold substitute.
    unfold Binddt_Categorical.
    unfold compose.
    cbn.
    compose near (f ([], v)).
    rewrite (fun_map_map).
    change (join ∘ tvar) with (join ∘ ret (T := term B2) (A := term B2 V2)).
    rewrite mon_join_ret.
    rewrite fun_map_id.
    reflexivity.
    Qed.

End rw.

Lemma FV_loc_preincr: forall (bs: list name) (t: term name name),
    substitute (B2 := False) (A2 := False)
      (G := const (list name)) (T := term) (const [])
      (FV_loc ⦿ bs)
      t =
      remove_all bs (fvL t).
Proof.
  intros.
  generalize dependent bs.
  induction t; intros.
  - rewrite sub_term_rw1.
    rewrite fvL_rw1.
    cbn.
    change (bs ● []) with (bs ● Ƶ).
    simpl_monoid.
    remember (get_binding bs v) as R.
    destruct R.
    + destruct bs.
      * inversion HeqR.
      * cbn in *.
        destruct_eq_args v n0.
        { admit. }
        { admit. }
    + admit.
  - rewrite sub_term_rw2.
    rewrite preincr_preincr.
    rewrite IHt.
    repeat simplify_applicative_const.
    simpl_monoid.
    unfold const.
    change (@nil name) with (Ƶ: list name).
    simpl_monoid.
    rewrite fvL_rw2.
    admit.
  - rewrite sub_term_rw3.
    rewrite IHt1.
    rewrite IHt2.
    repeat simplify_applicative_const.
    simpl_monoid.
    rewrite fvL_rw3.
    admit.
Admitted.

Lemma FV_fvL: forall (t: term name name),
    FV term t = fvL t.
Proof.
  intros t.
  unfold FV.
  unfold mapdtp.
  unfold MapdtPoly_Substitute.
  replace ((map (F := const (list name)) ret ∘ FV_loc))
    with ((map (F := const (list name)) ret (A := False) ∘ FV_loc) ⦿ Ƶ).
  2:{ now rewrite preincr_zero. }
  rewrite FV_loc_preincr.
  admit.
Admitted.

Section rw.

  Context
    (conflicts: list name)
    (fv_u: list name)
    (x: name) (u: term name name).

  Lemma subst_top_rw1: forall (v: name),
      subst_top x u conflicts fv_u (tvar v) =
        if (v == x) then u else (tvar v).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_top_rw2: forall (b: name) (t: term name name),
      subst_top x u  conflicts (fv_u) (lam b t) =
        lam (rename_binder_from_ctx x conflicts fv_u ([], b))
          (substitute (G := fun A => A)
             (rename_binder_from_ctx x conflicts fv_u ⦿ [b])
             (subst_from_ctx x u conflicts fv_u ⦿ [b]) t).
  Proof.
    intros.
    unfold subst_top.
    rewrite sub_term_rw2.
    repeat simplify_applicative_I.
    reflexivity.
  Qed.

  Lemma subst_top_rw3: forall (top: list name) (t1 t2: term name name),
      subst_top x u conflicts fv_u (tap t1 t2) =
        tap (subst_top x u conflicts fv_u t1) (subst_top x u conflicts fv_u t2).
  Proof.
    reflexivity.
  Qed.

End rw.

Lemma lemma1: forall
    (conflicts: list name) (fv_u: list name) (x:name),
    (rename_binder_from_ctx x conflicts fv_u) ⦿ [x] =
      extract.
Proof.
  intros.
  ext (ctx, b).
  unfold preincr, incr, compose.
  change ([x] ● ctx) with (x::ctx).
  unfold rename_binder_from_ctx.
  rewrite rename_binder_from_ctx_rec_rw_cons_eq; auto.
Qed.

Lemma lemma2: forall
    (conflicts: list name) (fv_u: list name) (x:name) (u: term name name),
    (subst_from_ctx x u conflicts fv_u) ⦿ [x] =
      ret ∘ extract.
Proof.
  intros.
  ext (ctx, v).
  unfold preincr, incr, compose.
  change ([x] ● ctx) with (x::ctx).
  unfold subst_from_ctx.
  destruct (get_binding_spec (x :: ctx) v) as [[Heq Hnin]| H2].
  - rewrite Heq.
    assert (v <> x).
    rewrite element_of_list_cons in Hnin. tauto.
    destruct_eq_args v x.
  - destruct H2 as [pre [post [rest1 [rest2 rest3]]]].
    rewrite rest1.
    cbn.
    destruct pre.
    + cbn. fequal.
      assert (x = v).
      { now inversion rest2. }
      subst.
      unfold rename_binder_one.
      destruct_eq_args v v.
    +
      assert (x = n).
      { now inversion rest2. }
      subst.
      change_left (ret ((rename_binder_from_ctx n conflicts fv_u ⦿ [n]) (pre, v))).
      rewrite lemma1.
      reflexivity.
Qed.


Section interpret.

  Context
    (conflicts: list name)
  (fv_u: list name) (x: name) (u: term name name).

  Definition interpret_context_to_renamings  (context: list name):
    term name name -> term name name :=
    match context with
    | nil => id
    | cons b rest =>
        if b == x
        then id
        else if SmartAtom.name_inb x fv_u
             then let z := (fresh ([x] ++ l ++ [b]): name) in
                  interpret_context_to_renamings rest ∘ rename b z
                  else substF conflicts x u
                  end.

Definition interpret_context (conflicts: list name) (fv_u: list name) (x: name) (u: term name name) (context: list name):
  term name name -> term name name :=
  match context with
  | nil => substF conflicts x u
  | cons b rest =>
      if b == x
      then substF conflicts x u
      else if SmartAtom.name_inb x fv_u
           then substF (conflicts ++ context_to_renamed context) x u
           else substF conflicts x u
  end.

Lemma equiv_key:
  forall (conflicts: list name) (x: name) (u: term name name) (context: list name) (t: term name name),
     substitute (T := term) (G := fun A => A)
       (rename_binder_from_ctx x conflicts (FV term u) ⦿ context)
       (subst_from_ctx x u conflicts (FV term u) ⦿ context) t =
       interpret_context conflicts (FV term u) x u context t.
Proof.
  intros.
  induction t.
  - rewrite sub_term_rw1.
    unfold preincr, incr, compose.
    change (@nil name) with (Ƶ:list name).
    rewrite monoid_id_l.
    induction context.


Theorem woah:
  forall (conflicts: list name) (x: name) (u: term name name) (b: name) (t: term name name),
    (~ b ∈ fvL u ->
     b <> x ->
     substitute (T := term) (G := fun A => A)
       (rename_binder_from_ctx x conflicts (FV term u) ⦿ [b])
       (subst_from_ctx x u conflicts (FV term u) ⦿ [b]) t =
       substF (conflicts ++ [b]) x u t) /\
      (b ∈ fvL u ->
       b <> x ->
       substitute (T := term) (G := fun A => A)
         (rename_binder_from_ctx x conflicts (FV term u) ⦿ [b])
         (subst_from_ctx x u conflicts (FV term u) ⦿ [b]) t =
         substF (conflicts ++ [fresh ([x] ++ conflicts ++ [b])]) x u (rename b (fresh ([x] ++ conflicts ++ [b])) t)).
Proof.
  intros.
  generalize dependent conflicts.
  generalize dependent b.
  induction t.
  - admit.
  - (* λ b t *)
    intros c conflicts.
    rewrite sub_term_rw2.
    simplify_applicative_I.
    unfold ap, mult, Mult_I; unfold_ops @Map_I.
    split.
    { introv Hnin Hneq.
      rewrite substF_rw2.
      assert (b <> x). admit.
      destruct_eq_args b x.
      { rewrite preincr_preincr.
Abort.


Theorem subst_preincr_inFV_spec:
  forall (conflicts: list name) (x: name) (u: term name name) (b: name) (t: term name name),
      b ∈ fvL u ->
      b <> x ->
      substitute (T := term) (G := fun A => A)
        (rename_binder_from_ctx x conflicts (FV term u) ⦿ [b])
        (subst_from_ctx x u conflicts (FV term u) ⦿ [b]) t =
  substF (conflicts ++ [fresh ([x] ++ conflicts ++ [b])]) x u (rename b (fresh ([x] ++ conflicts ++ [b])) t).
Proof.
  introv Hin Hneq.
  generalize dependent conflicts.
  generalize dependent b.
  induction t; intros.
  - rewrite sub_term_rw1.
    rewrite rename_rw1.
    destruct_eq_args v b.
    + rewrite substF_rw1.
      unfold preincr, incr, compose.
      change ([b] ● []) with ([b]).
      unfold subst_from_ctx.
      assert (get_binding [b] b = Bound [] b []).
      { cbn. destruct_eq_args b b. }
      rewrite H.
      assert (fresh ([x] ++ conflicts ++ [b]) <> x).
      { intro contra.
        assert (~ x ∈ ([x] ++ conflicts ++ [b])).
        symmetry in contra.
        rewrite contra at 1.
        apply SmartAtom.fresh_not_in.
        rewrite element_of_list_app in H0.
        rewrite element_of_list_one in H0.
        tauto.
      }
      destruct_eq_args (fresh ([x] ++ conflicts ++ [b])) x.
      { intuition. }
      { fequal.
        unfold rename_binder_from_ctx.
        unfold rename_binder_from_ctx_rec.
        unfold rename_binder_one.
        destruct_eq_args b x.
        rewrite FV_fvL.
        step_set_test.
        rewrite List.app_nil_l.
        reflexivity.
      }
    +
      unfold preincr, incr, compose.
      change ([b] ● []) with ([b]).
      unfold subst_from_ctx.
      assert (get_binding [b] v = Unbound [b]).
      { cbn. destruct_eq_args b v. }
      rewrite H.
      destruct_eq_args v x.
      { rewrite substF_rw1.
        destruct_eq_args x x.
      }
      { rewrite substF_rw1.
        destruct_eq_args v x.
      }
  - rewrite sub_term_rw2.
    simplify_applicative_I.
    unfold ap, mult, Mult_I; unfold_ops @Map_I.
    rewrite rename_rw2_neq.

    rewrite substF_rw2.
    admit.
    admit.
  - rewrite rename_rw3.
    rewrite substF_rw3.
    rewrite <- IHt1; auto.
    rewrite <- IHt2; auto.
Admitted.

Lemma tvar_helper:
  forall (conflicts: list name) (x: name) (u: term name name) (b: name) (t: term name name) v,
    ~ b ∈ fvL u ->
     b <> x ->
     subst_from_ctx x u conflicts (FV term u) ([b], v) = (if v == x then u else tvar v).
Proof.
  intros.
  cbn.
  destruct_eq_args v b.
  destruct_eq_args b x.
  cbn.
  unfold rename_binder_one.
  destruct_eq_args b x.
  rewrite FV_fvL.
  step_set_test.
  destruct (destruct_in b []).
  inversion H2.
  now step_set_test.
Qed.


Theorem subst_preincr_ninFV_spec:
  forall (conflicts: list name) (x: name) (u: term name name) (b: name) (t: term name name),
      ~ b ∈ fvL u ->
      b <> x ->
    substitute (T := term) (G := fun A => A)
      (rename_binder_from_ctx x conflicts (FV term u) ⦿ [b])
      (subst_from_ctx x u conflicts (FV term u) ⦿ [b]) t =
      substF (conflicts ++ [b]) x u t.
Proof.
  introv Hnin Nneq.
  generalize dependent conflicts.
  generalize dependent b.
  induction t; intros.
  - rewrite sub_term_rw1.
    rewrite substF_rw1.
    unfold preincr, incr, compose.
    change ([b] ● []) with ([b]).
    rewrite tvar_helper; auto.
  - rewrite sub_term_rw2.
    simplify_applicative_I.
    unfold ap, mult, Mult_I; unfold_ops @Map_I.
    rewrite substF_rw2.

    destruct_eq_args b x.
    { fequal.
      { unfold rename_binder_from_ctx.
        unfold preincr, incr, compose.
        change ([b0] ● []) with ([b0]).
        cbn.
        destruct_eq_args b0 x.
        admit.
      }
      {
        specialize (IHt b0 Hnin Nneq).
        admit.
      }
    }
    { destruct (SmartAtom.name_inb b (fvL u)).
      admit.
      admit.
    }
  - cbn.
    rewrite substF_rw3.
    rewrite <- IHt1.
    rewrite <- IHt2.
    reflexivity.
Admitted.

Theorem equivalence:
  forall (conflicts: list name) (x: name) (u: term name name),
    subst_top x u conflicts (FV term u) =
      substF conflicts x u.
Proof.
  intros. ext t.
  induction t.
  - rewrite subst_top_rw1.
    rewrite substF_rw1.
    reflexivity.
  - rewrite subst_top_rw2.
    rewrite substF_rw2.
    destruct_eq_args b x.
    {
      fequal.
      { cbn.
        unfold rename_binder_one.
        destruct_eq_args x x.
      }
      {
        rewrite lemma1.
        unfold rename_binder_one.
        rewrite lemma2.
        rewrite kdtmp_substitute1.
        reflexivity.
      }
    }
    { destruct (destruct_in b (fvL u)).
      { step_set_test.
        fequal.
        { unfold rename_binder_from_ctx.
          rewrite rename_binder_from_ctx_rec_rw_nil.
          unfold rename_binder_one.
          destruct_eq_args b x.
          rewrite FV_fvL.
          step_set_test.
          rewrite List.app_nil_l.
          reflexivity.
        }
        {
          apply subst_preincr_inFV_spec; auto.
        }
      }
      { step_set_test.
        fequal.
        { cbn.
          unfold rename_binder_one.
          destruct_eq_args b x.
          rewrite FV_fvL.
          step_set_test.
          destruct (destruct_in b []).
          inversion H2.
          now step_set_test.
        }
        {
          rewrite subst_preincr_ninFV_spec; auto.
        }
      }
    }
  - cbn.
    rewrite substF_rw3.
    rewrite <- IHt1.
    rewrite <- IHt2.
    reflexivity.
Qed.


Lemma rename_binder_local_history_preincr_spec:
  forall (conflicts: list name) (x:name) (fv_u: list name) (b:name),
    b <> x ->
    ~ (b ∈ fv_u) ->
  (rename_binder_local_history conflicts x fv_u ⦿ [b]) =
    (rename_binder_local_history (conflicts ++ [b]) x fv_u).
Proof.
  introv BneqX BnotinFVu.
  ext (ctx, v).
  unfold preincr, compose, incr.
  change (?a ● ?g) with (a ++ g).
  unfold rename_binder_local_history.
  destruct_eq_args x v.
  destruct (SmartAtom.name_inb v fv_u).
  - repeat rewrite List.app_assoc.
    reflexivity.
  - repeat rewrite List.app_assoc.
    reflexivity.
Qed.

