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


Lemma test: forall (bs: list name) (t: term name name),
    substitute (B2 := False) (A2 := False)
      (G := const (list name)) (T := term) (const [])
      ((map ret ∘ (fun '(ctx, x) => if get_binding ctx x then [] else [x])) ⦿ bs)
      t =
      remove_all bs (fvL t).
Proof.
  intros.
  generalize dependent bs.
  induction t; intros.
  - cbn. change (bs ● []) with (bs ● Ƶ).
    simpl_monoid.
    remember (get_binding bs v) as R.
    destruct R.
    + induction l.
Admitted.

Lemma FV_fvL : forall (t: term name name),
    FV term t = fvL t.
Proof.
  intros t.
  induction t.
  - reflexivity.
  - unfold FV.
    unfold mapdtp.
    unfold MapdtPoly_Substitute.
    rewrite sub_term_rw2.
    assert (@const (list name * name) (list name) [] ⦿ [b] =
              (const (A := list name * name) (@nil name))).
    { ext x. reflexivity.}
    setoid_rewrite H.
    rewrite test.
    repeat simplify_applicative_const.
    simplify_monoid_units.
    cbn.
    reflexivity.
  - cbn. rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

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

Lemma rename_binder_kill2: forall top x fv_u,
    rename_binder_local top x fv_u ([], x) = x.
Proof.
  intros.
  cbn.
  destruct_eq_args x x.
Qed.

Lemma rename_binder_kill: forall top x fv_u l ctx v,
    x ∈ l ->
    (rename_binder_local top x fv_u ⦿ l) (ctx, v) = v.
Proof.
  intros.
  change (rename_binder_local top x fv_u (l ++ ctx, v) = v).
  unfold rename_binder_local.
  remember (SmartAtom.name_inb x (l ++ ctx)).
  destruct b.
  + reflexivity.
  + false.
    symmetry in Heqb.
    rewrite SmartAtom.name_inb_iff_false in Heqb.
    rewrite element_of_list_app in Heqb.
    intuition.
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

Lemma substSmart_equiv:
  forall (top: list name) (x: name) (u: term name name),
    subst_top top x (FV term u) u =
      substF top x u.
Proof.
  intros. ext t. induction t.
  - rewrite subst_top_rw1.
    rewrite substF_rw1.
    reflexivity.
  - rewrite subst_top_rw2.
    rewrite substF_rw2.
    destruct_eq_args b x.
    + fequal.
      apply rename_binder_kill2.
      apply kill.
      now simpl_list.
    +
      rewrite FV_fvL.
      remember ((SmartAtom.name_inb b (fvL u))) as rem.
      destruct rem.
      * fequal.
        { cbn.
          destruct_eq_args x b.
          rewrite <- Heqrem.
          reflexivity.
        }




      unfold rename_binder_local.
      assert (SmartAtom.name_inb x [] = false).
      { reflexivity. }
      rewrite H. destruct_eq_args x b.
      rewrite FV_fvL.
      remember ((SmartAtom.name_inb b (fvL u))) as rem.
      destruct rem.
      * fequal.
        {
        }
        {
          admit.
        }
      * cbn.
        admit.
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
