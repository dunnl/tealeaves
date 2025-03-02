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

Lemma FV_fvL : forall (t: term name name),
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

(*
Section rw.

  Context (x: name) (u: term name name).

  Lemma subst_term_rw1: forall (v: name),
      Named.subst term x u (tvar v) =
        if (v == x) then u else (tvar v).
  Proof.
    reflexivity.
  Qed.
  Lemma subst_conflicts_rw1: forall top (v: name),
      subst_conflicts term top x u (tvar v) =
        if (v == x) then u else (tvar v).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_conflicts_rw2: forall (top: list name) (b: name) (t: term name name),
      subst_conflicts term top x u (lam b t) =
        lam (rename_binder_local top ([], b))
          (DecoratedTraversableMonadPoly.substitute (G := fun A => A)
             (rename_binder_local top ⦿ [b])
             (subst_local top x u ⦿ [b]) t).
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma subst_conflicts_rw3: forall (top: list name) (t1 t2: term name name),
      subst_conflicts term top x u (tap t1 t2) =
        tap (subst_conflicts term top x u t1) (subst_conflicts term top x u t2).
  Proof.
    reflexivity.
  Qed.
End rw.
*)


Section rw.

  Context
    (top: list name)
    (x: name) (fv_u: list name) (u: term name name).

  Lemma subst_top_rw1: forall (v: name),
      subst_top top x fv_u u (tvar v) =
        if (v == x) then u else (tvar v).
  Proof.
    reflexivity.
  Qed.


  Lemma subst_top_rw2: forall (b: name) (t: term name name),
      subst_top top x (fv_u) u (lam b t) =
        lam (rename_binder_local top x fv_u ([], b))
          (substitute (G := fun A => A)
             (rename_binder_local top x fv_u ⦿ [b])
             (subst_local top x fv_u u ⦿ [b]) t).
  Proof.
    intros.
    unfold subst_top.
    rewrite sub_term_rw2.
    repeat simplify_applicative_I.
    reflexivity.
  Qed.

  Lemma subst_top_rw3: forall (top: list name) (t1 t2: term name name),
      subst_top top x fv_u u (tap t1 t2) =
        tap (subst_top top x fv_u u t1) (subst_top top x fv_u u t2).
  Proof.
    reflexivity.
  Qed.

End rw.




Import ContainerFunctor.Notations.

(*
Lemma rename_binder_kill2: forall top x fv_u,
    rename_binder_local top x fv_u ([], x) = x.
Proof.
  intros.
  cbn.
  destruct_eq_args x x.
Qed.


Lemma subst_local_kill: forall top x fv_u u l ctx v,
    x ∈ l ->
    (subst_local top x fv_u u ⦿ l) (ctx, v) = tvar v.
Proof.
  intros.
  change (subst_local top x fv_u u (l ++ ctx, v) = tvar v).
  unfold subst_local.
  remember (SmartAtom.name_inb x (l ++ ctx)).
  destruct b.
  + reflexivity.
  + false.
    symmetry in Heqb.
    rewrite SmartAtom.name_inb_iff_false in Heqb.
    rewrite element_of_list_app in Heqb.
    intuition.
Qed.


Lemma kill:
  forall (top fv_u: list name) (any: list name) (x: name) (t u: term name name),
    x ∈ any ->
    substitute (T := term) (G := fun A => A)
      (rename_binder_local top x fv_u ⦿ any)
      (subst_local top x fv_u u ⦿ any) t = t.
Proof.
  intros.
  change t with (id t) at 2.
  rewrite <- (kdtmp_substitute1 (T := term) (B := name) (A := name)).
  fequal.
  - ext (ctx, v).
    now apply rename_binder_kill.
  - ext (ctx, v).
    now apply subst_local_kill.
Qed.

Lemma inb_iff: forall (l: list name) (x: name),
    SmartAtom.name_inb x l = false <-> (~ x ∈ l).
Proof.
  induction l.
  - cbv. intuition.
  - intros. cbn.
    destruct_eq_args x a.
    + cbn. firstorder. inversion H.
    + cbn. rewrite IHl. firstorder.
Qed.

Lemma inb_iff2: forall (l: list name) (x: name),
    SmartAtom.name_inb x l = true <-> (x ∈ l).
Proof.
  induction l.
  - cbv. intuition.
  - intros. cbn.
    destruct_eq_args x a.
    + cbn. firstorder.
    + cbn. rewrite IHl. firstorder.
Qed.

Lemma x1: forall top x l ctx b,
    ~ (b ∈ l) ->
    (rename_binder_local top x l (ctx, b)) = b.
Proof.
  intros. cbn.
  destruct (SmartAtom.name_inb x ctx).
  - reflexivity.
  - destruct_eq_args b x.
    rewrite <- inb_iff in H.
    rewrite H.
    reflexivity.
Qed.

Lemma rename_binder_preincr1: forall top x l b,
    b = x ->
    ~ (b ∈ l) ->
    rename_binder_local top x l ⦿ [b] =
      extract.
Proof.
  intros.
  ext (ctx, v).
  unfold preincr, compose, incr.
  unfold_ops @Monoid_op_list.
  unfold rename_binder_local.
  subst.
  assert (SmartAtom.name_inb x ([x] ++ ctx) = true).
  { rewrite SmartAtom.name_inb_iff.
    firstorder. }
  rewrite H.
  reflexivity.
Qed.
 *)




(*
Lemma needed_easier:forall (top:list name) (x:name) (l:list name) (b:name) (ctx:list name) v,
    b <> x ->
    ~ (b ∈ l) ->
    v ∈ l ->
  (rename_binder_local_history top x l ⦿ [b]) (ctx, v) =
    (rename_binder_local_history (top ++ [b]) x l) (ctx, v).
Proof.
  intros.
  unfold preincr, compose, incr.
  change (?a ● ?g) with (a ++ g).
  destruct ctx.
  - rewrite List.app_nil_r.
    unfold rename_binder_local_history.
    destruct_eq_args x v.
    rewrite <- SmartAtom.name_inb_iff in H1.
    rewrite H1.
    rewrite List.app_nil_l.
    rewrite List.app_assoc.
    reflexivity.
  - unfold rename_binder_local_history.
    destruct_eq_args x v.
    rewrite <- SmartAtom.name_inb_iff in H1.
    rewrite H1.
    change (?x :: ctx) with ([x] ++ ctx).
    repeat rewrite List.app_assoc.
    reflexivity.
Qed.

Lemma needed_harded:forall (top:list name) (x:name) (l:list name) (b:name) (ctx:list name) v,
    b <> x ->
    ~ (b ∈ l) ->
    ~ v ∈ l ->
  (rename_binder_local_history top x l ⦿ [b]) (ctx, v) =
    (rename_binder_local_history (top ++ [b]) x l) (ctx, v).
Proof.
  intros.
  unfold preincr, compose, incr.
  change (?a ● ?g) with (a ++ g).
  destruct ctx.
  - rewrite List.app_nil_r.
    unfold rename_binder_local_history.
    destruct_eq_args x v.
    rewrite <- SmartAtom.name_inb_iff_false in H1.
    rewrite H1.
    reflexivity.
  - unfold rename_binder_local_history.
    destruct_eq_args x v.
    destruct (SmartAtom.name_inb v l); auto.
    repeat rewrite List.app_assoc.
    reflexivity.
Qed.

Lemma needed_yay:forall (top:list name) (x:name) (l:list name) (b:name) (ctx:list name) v,
    b <> x ->
    ~ (b ∈ l) ->
  (rename_binder_local_history top x l ⦿ [b]) (ctx, v) =
    (rename_binder_local_history (top ++ [b]) x l) (ctx, v).
Proof.
  intros.
  destruct (destruct_in v l).
  - apply needed_easier; auto.
  -  apply needed_harded; auto.
Qed.

Lemma needed_yayy:forall (top:list name) (x:name) (l:list name) (b:name),
    b <> x ->
    ~ (b ∈ l) ->
  (rename_binder_local_history top x l ⦿ [b]) =
    (rename_binder_local_history (top ++ [b]) x l).
Proof.
  intros.
  ext (ctx, v).
  now apply needed_yay.
Qed.

Lemma needed_intermediate: forall  top x l b ctx,

    b <> x ->
    ~ b ∈ l ->
    fold_with_history (rename_binder_local_history top x l ⦿ [b]) ctx =
      fold_with_history (rename_binder_local_history (top ++ [b]) x l) ctx.
Proof.
  intros.
    induction ctx.
  - reflexivity.
  - rewrite fold_with_history_cons.
    rewrite fold_with_history_cons.
    fequal.
    { unfold preincr, compose, incr.
      change ([b] ● []) with [b].
      unfold rename_binder_local_history.
      destruct_eq_args x a.
      destruct (destruct_in a l).
      { rewrite <- SmartAtom.name_inb_iff in H1.
        rewrite H1.
        rewrite List.app_nil_l.
        rewrite List.app_assoc.
        reflexivity.
      }
      {rewrite <- SmartAtom.name_inb_iff_false in H1.
       rewrite H1.
       reflexivity.
      }
    }
    { fequal.
      rewrite needed_yayy; auto.
    }
Qed.
*)





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

Lemma fold_rename_binder_local_history_preincr_spec: forall
  (conflicts: list name) (x:name) (fv_u: list name) (b:name) (ctx:list name),

    b <> x ->
    ~ b ∈ fv_u ->
    fold_with_history (rename_binder_local_history conflicts x fv_u ⦿ [b]) ctx =
      fold_with_history (rename_binder_local_history (conflicts ++ [b]) x fv_u) ctx.
Proof.
  intros.
  rewrite rename_binder_local_history_preincr_spec; auto.
Qed.

(*
Lemma needed:
  forall (conflicts: list name) (x:name) (fv_u: list name) (b:name) (ctx: list name) (v: name),
    ~ x ∈ ([b] ++ ctx) ->
    ~ (x ∈ ctx) ->
    b <> x ->
    ~ (b ∈ fv_u) ->
    v ∈ fv_u ->
    v <> x ->
    rename_binder_local conflicts x fv_u ([b] ++ ctx, v) =
      rename_binder_local (conflicts ++ [b]) x fv_u (ctx, v).
Proof.
  intros.
  unfold rename_binder_local.
  rewrite ctx_to_history_cons_rw2.
  rewrite rename_binder_local_history_preincr_spec; auto.
  rewrite rename_binder_local_history_rw2; auto.
  rewrite rename_binder_local_history_rw2; auto.
  change (?x :: ?y) with ([x] ++ y).
  repeat rewrite <- List.app_assoc.
  rewrite List.app_nil_r.
  rewrite List.app_nil_l.
  reflexivity.
Qed.
*)

(*
Lemma rename_binder_local_preincr: forall
  (conflicts: list name) (x:name) (fv_u: list name) (b:name),
    b <> x ->
    ~ (b ∈ fv_u) ->
    rename_binder_local conflicts x fv_u ⦿ [b] =
      rename_binder_local (conflicts ++ [b]) x fv_u.
Proof.
  introv BneqX BninFVu.
  ext (ctx, v).
  unfold preincr, compose, incr.
  unfold_ops @Monoid_op_list.
  destruct (destruct_in x ([b] ++ ctx)) as [Hxin|Hxnin].
  { (* X is in context *)
    rewrite rename_binder_local_rw1; auto.
    rewrite element_of_list_app in Hxin.
    rewrite element_of_list_one in Hxin.
    destruct Hxin.
    + subst. contradiction.
    + rewrite rename_binder_local_rw1; auto.
  }
  { assert (x <> b /\ ~ x ∈ ctx) as Hyp.
    { rewrite element_of_list_app in Hxnin.
      rewrite element_of_list_one in Hxnin.
      firstorder. }
    destruct Hyp as [Xneqb Xninctx].
    destruct_eq_args v x.
    { rewrite rename_binder_local_rw2; auto.
      rewrite rename_binder_local_rw2; auto.
    }
    { destruct (destruct_in v fv_u).
      { apply needed; auto.
      }
      { rewrite rename_binder_local_rw4; auto.
        rewrite rename_binder_local_rw4; auto.
      }
    }
  }
Qed.
*)


(*
Lemma subst_local_kill: forall top x fv_u u l ctx v,
    x ∈ l ->
    (subst_local top x fv_u u ⦿ l) (ctx, v) = tvar v.
Proof.
  intros.
  change (subst_local top x fv_u u (l ++ ctx, v) = tvar v).
  unfold subst_local.
  remember (SmartAtom.name_inb x (l ++ ctx)).
  destruct b.
  + reflexivity.
  + false.
    symmetry in Heqb.
    rewrite SmartAtom.name_inb_iff_false in Heqb.
    rewrite element_of_list_app in Heqb.
    intuition.
Qed.
*)


Lemma rename_binder_kill: forall top x fv_u l ctx v,
    x ∈ l ->
    (rename_binder_local top x fv_u ⦿ l) (ctx, v) = v.
Proof.
  intros.
  change (rename_binder_local top x fv_u (l ++ ctx, v) = v).
  unfold rename_binder_local.
  rewrite ctx_to_history_app.
Abort.

Section proof_lemmas.

  Context
    (conflicts: list name)
      (fv_u : list name)
      (x: name) (u: term name name).

  Implicit Types (ctx: list name) (v: name).

  Lemma test:
    ctx_to_history conflicts x fv_u [x] = [x].
  Proof.
    intros. cbn. destruct_eq_args x x.
  Qed.

  Lemma rename_binder_kill_corrected: forall ctx v,
    (rename_binder_local conflicts x fv_u ⦿ [x]) (ctx, v) = v.
  Proof.
    intros.
    change (rename_binder_local conflicts x fv_u ([x] ++ ctx, v) = v).
    unfold rename_binder_local.
    rewrite ctx_to_history_app.
    generalize (fold_with_history
                  (rename_binder_local_history conflicts x fv_u ⦿ fold_with_history
                     (rename_binder_local_history conflicts x fv_u) [x])
                  ctx).
    intro l.
    rewrite test.
    unfo
    Search rename_binder_local_history.
    unfold rename_binder_local.
    rewrite ctx_to_history_app.
  Abort.


Lemma kill:
  forall (top fv_u: list name) (any: list name) (x: name) (t u: term name name),
    x ∈ any ->
    substitute (T := term) (G := fun A => A)
      (rename_binder_local top x fv_u ⦿ any)
      (subst_local top x fv_u u ⦿ any) t = t.
Proof.
  intros.
  change t with (id t) at 2.
  rewrite <- (kdtmp_substitute1 (T := term) (B := name) (A := name)).
  fequal.
  - ext (ctx, v).
    try now apply rename_binder_kill.
    admit.
  - ext (ctx, v).
Abort.


Lemma substSmart_equiv:
  forall (top: list name) (x: name) (u: term name name),
    subst_top top x (FV term u) u =
      substF top x u.
Proof.
  intros.
  (* unfold subst_top. ext t. *)
  intros. ext t. generalize dependent top. induction t; intros top.
  - rewrite subst_top_rw1.
    rewrite substF_rw1.
    reflexivity.
  - rewrite subst_top_rw2.
    rewrite substF_rw2.
    (* Is the binder the variable being substituted? *)
    destruct_eq_args b x.
    + (* Yes, it is. The RHS cuts off immediately. *)
      (* We must show the LHS localized fns. are effectively the identity *)
      fequal.
      { unfold rename_binder_local.
        rewrite ctx_to_history_nil.
        rewrite rename_binder_local_history_rw1; auto.
      }
      { apply kill.
        now simpl_list. }
    + (* No, it's not *)
      rewrite FV_fvL.
      (* Is b of of the variables in fvL u and therefore needs to be renamed? *)
      remember ((SmartAtom.name_inb b (fvL u))) as rem.
      destruct rem.
      * (* Yes, it is. Rename it. *)
        fequal.
        { unfold rename_binder_local.
          assert (~ x ∈ nil) by easy.
          rewrite <- inb_iff in H.
          rewrite H.
          destruct_eq_args x b.
          rewrite <- Heqrem.
          rewrite ctx_to_history_nil.
          unfold rename_binder_local_history.
          destruct_eq_args x b.
          rewrite <- Heqrem.
          rewrite List.app_nil_l.
          reflexivity. }
        {
          admit.
        }
      * (* No, it's not. Don't rename it. *)
        rewrite x1.
        2:{ rewrite <- inb_iff. easy. }
        rewrite <- IHt.
        unfold subst_top.
        fequal.
        fequal.
        { rewrite FV_fvL.
          rewrite rename_binder_local_preincr; auto.
          rewrite <- SmartAtom.name_inb_iff_false. easy.
        }
        {
          rewrite subst_binder_preincr; auto.
        }
  - rewrite subst_top_rw3.
    rewrite substF_rw3.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Admitted.



Corollary substSmart_equiv_truly:
  forall (x: name) (u: term name name) t,
    substSmart x u t =
      Raw.subst x u t.
Proof.
  intros.
  unfold substSmart.
  unfold Raw.subst.
  rewrite FV_fvL.
  rewrite FV_fvL.
  apply substSmart_equiv.
Qed.



























  (*
  Lemma subst_conflicts_rw2: forall (top: list name) (b: name) (t: term name name),
      subst_conflicts term top x u (lam b t) =
        lam (rename_binder_local top ([], b))
          (DecoratedTraversableMonadPoly.substitute (G := fun A => A)
             (rename_binder_local top ⦿ [b])
             (subst_local top x u ⦿ [b]) t).
  Proof.
    intros.
    unfold subst.
    unfold subst_conflicts.
    unfold DecoratedTraversableMonadPoly.substitute.
    unfold Binddt_Categorical.
    unfold compose at 1 2 3 4.
    rewrite dec_term_rw2.
    rewrite map2_term_rw2.
    rewrite dist2_unit.
    unfold id.
    unfold_ops @Map_I.
    rewrite join_term_rw2.
    fequal.
    change (fun x : term name (term name name) => x) with
      (@id (term name (term name name))).
    change (?f ∘ id) with f.
    compose near ([b], decp t) on left.
    compose near (decp t) on left.
    rewrite (map2_shift2_preincr
               (g := (rename_binder_local top))
               (f := (subst_local top x u))
               (w := [b])).

    reflexivity.
  Qed.
  *)
