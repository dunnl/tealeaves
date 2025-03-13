From Tealeaves Require Export
  Examples.LambdaNominal.Syntax
  Examples.LambdaNominal.Categorical
  Examples.LambdaNominal.Kleisli
  Examples.LambdaNominal.Raw
  Functors.Subset
  Functors.Constant
  Backends.Common.AtomSet
  Backends.Named.Barendregt
  Backends.Named.FV.

From Tealeaves Require Import Simplification.Support.

Import Classes.Kleisli.DecoratedTraversableMonadPoly.
Import CategoricalPDTMUsefulInstances.

Import ContainerFunctor.Notations.

#[local] Generalizable Variables G.

(** * Equivalence of Direct and Categorical Definitions of <<substitute>> *)
(**********************************************************************)
Section rw.

  Context
    {B1 V1 B2 V2: Type}
    `{Applicative G}
    {g: list B1 * B1 -> G B2}
    {f: list B1 * V1 -> G (term B2 V2)}.

  Lemma sub_term_spec: forall v,
      substitute (Substitute := Substitute_Categorical term) g f (tvar v) =
        substitute (Substitute := Substitute_lambda_term) g f (tvar v).
  Proof.
    intros.
    unfold substitute.
    unfold Substitute_Categorical.
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

(** * Required Lemmas *)
(**********************************************************************)

(** ** Pre-incrementing <<FV_loc>> *)
(** This can and should be generalized to any PDTM *)
(**********************************************************************)
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
    FV t = fvL t.
Proof.
  intros t.
  unfold FV.
  unfold foldMapd.
  unfold mapdt.
  unfold Mapdt_Categorical.
  unfold dist.
  unfold Dist2_1.
  reassociate -> near (map FV_loc).
  rewrite fun2_map2_map21.
  change (id ∘ ?f) with f.
  unfold dec.
  unfold Decorate_PolyVar.
  reassociate <- on left.
  reassociate -> near (@map2 term Map2_term (Z atom) (Z2 atom atom) atom (Z2 atom atom) (@extract Z Extract_Z atom) (@id (Z2 atom atom))).
  rewrite fun2_map_map.
  change (?f ∘ id) with f.
Admitted.

Section rw.

  Context
    (conflicts: list name)
    (x: name) (u: term name name).

  Lemma subst_top_rw1: forall (v: name),
      subst_top x u conflicts (tvar v) =
        if (v == x) then u else (tvar v).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_top_rw2: forall (b: name) (t: term name name),
      subst_top x u conflicts (lam b t) =
        lam (rename_binder_from_context conflicts (@nil atom, b))
          (substitute (G := fun A => A)
             (rename_binder_from_context conflicts ⦿ [b])
             (subst_from_ctx x u conflicts ⦿ [b]) t).
  Proof.
    intros.
    unfold subst_top.
    rewrite sub_term_rw2.
    repeat simplify_applicative_I.
    reflexivity.
  Qed.

  Lemma subst_top_rw3: forall (top: list name) (t1 t2: term name name),
      subst_top x u conflicts (tap t1 t2) =
        tap (subst_top x u conflicts t1) (subst_top x u conflicts t2).
  Proof.
    reflexivity.
  Qed.

End rw.

Lemma lemma1: forall
    (conflicts: list name) (fv_u: list name) (x:name),
    (rename_binder_from_context conflicts) ⦿ [x] =
      extract.
Proof.
  intros.
  ext (ctx, b).
  unfold preincr, incr, compose.
  change ([x] ● ctx) with (x::ctx).
  unfold rename_binder_from_context.
  unfold rename_binder_from_history.
Abort.

About subst.
About subst_top.

Theorem subst_equiv: forall (x: name) (u: term name name) (t: term name name),
    Barendregt.subst x u t = Raw.subst x u t.
Proof.
  intros.
  unfold Barendregt.subst.
  unfold subst_top.
  unfold Raw.subst.
  assert (Hctx_eq: [x] ++ fvL t ++ fvL u = [x] ++ FV t ++ FV u).
  { do 2 rewrite FV_fvL.
    reflexivity.
  }
  rewrite Hctx_eq.
  remember ([x] ++ FV t ++ FV u) as CtxInit.
  generalize CtxInit.
  clear Hctx_eq HeqCtxInit CtxInit.
  induction t; intros.
  - unfold Raw.subst.
    cbn.
    rewrite substF_rw1.
    reflexivity.
  - rewrite sub_term_rw2.
    rewrite substF_rw2.
    unfold_ops @Pure_I.
    unfold id.
    destruct_eq_args b x.
    { fequal.
      - admit.
      - unfold preincr.
        (* Need to know preincr is same as adding to initial set *)
        admit.
    }
    { fequal.
      admit.
      admit.
    }
  - unfold Raw.subst.
    rewrite substF_rw3.
    rewrite sub_term_rw3.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Abort.
