From Tealeaves Require Export
  Examples.SystemF.Syntax
  Simplification.Tests.Support
  Simplification.MBinddt
  Simplification.Tests.SystemF_Binddt.

#[local] Generalizable Variables G.
#[local] Arguments mbinddt {ix} {W}%type_scope {T} U%function_scope
  {MBind} {F}%function_scope {H H0 H1 A B} _ _.

#[local] Generalizable Variables A B C F W T U K M.

Section local_lemmas_needed.

  Context
    (U : Type -> Type)
      `{MultiDecoratedTraversablePreModule W T U}
      `{! MultiDecoratedTraversableMonad W T}.

  Lemma kbindd_to_mbindd: forall A (k: K) (f: W * A -> T k A),
      kbindd U k f =  mbindd U (btgd k f).
  Proof.
    reflexivity.
  Qed.

  Lemma kbind_to_mbind: forall A (k: K) (f: A -> T k A),
      kbind U k f =  mbind U (btg k f).
  Proof.
    reflexivity.
  Qed.

  Lemma btgd_compose_incr: forall A (k: K) (f: W * A -> SystemF k A) w,
      btgd k f ◻ allK (incr w) =
        btgd k (f ⦿ w).
  Proof.
    intros.
    ext j.
    unfold allK, const.
    unfold vec_compose.
    compare values k and j.
    { autorewrite with tea_tgt_eq.
      reflexivity. }
    { autorewrite with tea_tgt_neq.
      reassociate -> on left.
      rewrite extract_incr.
      reflexivity. }
  Qed.

  Lemma tgtdt_compose_incr `{Applicative G}:
    forall A (k: K) (f: W * A -> G A) w,
      tgtdt k f ◻ allK (incr w) =
        tgtdt k (f ⦿ w).
  Proof.
    intros.
    ext j.
    unfold allK, const.
    unfold vec_compose, compose.
    unfold tgtdt.
    ext [w' a].
    compare values k and j.
  Qed.

End local_lemmas_needed.

Ltac simplify_kbindd_pre_refold_hook :=
  rewrite ?(btgd_compose_incr).

Ltac simplify_kbindd_post_refold_hook :=
  idtac.

Ltac simplify_kbindd :=
  rewrite ?kbindd_to_mbindd;
  simplify_mbindd;
   simplify_kbindd_pre_refold_hook;
  rewrite <- ?kbindd_to_mbindd;
  simplify_kbindd_post_refold_hook.

(** ** <<kbindd>> *)
(******************************************************************************)
Section rw_kbindd.

  Context
    (A : Type)
      (k : K2)
      (f : list K2 * A -> SystemF k A).

  Ltac tactic_being_tested ::= simplify_kbindd.

  Lemma kbindd_type_rw1 : forall c,
      kbindd typ k f (ty_c c) = ty_c c.
  Proof.
    test_simplification.
  Qed.

  Lemma kbindd_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      kbindd typ k f (ty_v a) = ty_v a.
  Proof.
    intros.
    simplify_kbindd.
    rewrite btgd_neq; auto.
  Qed.

  (*
    Lemma kbindd_type_neq_rw2_eq : forall (a : A) (Heq: k = ktyp),
        kbindd typ k f (ty_v a) = rew Heq in (f ([], a)).
    Proof.
      intros.
      simplify_kbindd.
      subst.
      rewrite btgd_eq. auto.
    Qed.
   *)

  Lemma kbindd_type_rw3 : forall (t1 t2 : typ A),
      kbindd typ k f (ty_ar t1 t2) =
        ty_ar (kbindd typ k f t1) (kbindd typ k f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma kbindd_type_rw4 : forall (body : typ A),
      kbindd typ k f (ty_univ body) =
        ty_univ (kbindd typ k (f ⦿ [ktyp]) body).
  Proof.
    test_simplification.
  Qed.

  Lemma kbindd_term_rw1_neq : forall (a : A),
      k <> ktrm ->
      kbindd term k f (tm_var a) = tm_var a.
  Proof.
    intros.
    simplify_kbindd.
    rewrite btgd_neq; auto.
  Qed.

  Lemma kbindd_term_rw2 : forall (τ : typ A) (t : term A),
      kbindd term k f (tm_abs τ t) =
        tm_abs (kbindd typ k f τ) (kbindd term k (f ⦿ [ktrm]) t).
  Proof.
    test_simplification.
  Qed.

  Lemma kbindd_term_rw3 : forall (t1 t2 : term A),
      kbindd term k f (tm_app t1 t2) =
        tm_app (kbindd term k f t1) (kbindd term k f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma kbindd_term_rw4 : forall (t : term A),
      kbindd term k f (tm_tab t) =
        tm_tab (kbindd term k (f ⦿ [ktyp]) t).
  Proof.
    test_simplification.
  Qed.

  Lemma kbindd_term_rw5 : forall (t: term A) (τ : typ A),
      kbindd term k f (tm_tap t τ) =
        tm_tap (kbindd term k f t) (kbindd typ k f τ).
  Proof.
    test_simplification.
  Qed.

End rw_kbindd.

Ltac simplify_kbind_pre_refold_hook :=
  rewrite ?(btgd_compose_incr).

Ltac simplify_kbind_post_refold_hook :=
  idtac.

Ltac simplify_kbind :=
  rewrite ?kbind_to_mbind;
  simplify_mbind;
  simplify_kbind_pre_refold_hook;
  rewrite <- ?kbind_to_mbind;
  simplify_kbind_post_refold_hook.

(** ** <<kbind>> *)
(******************************************************************************)
Section rw_kbind.

  Context
    (A : Type)
      (k : K2)
      (f : A -> SystemF k A).
  Ltac tactic_being_tested ::= simplify_kbind.

  Lemma kbind_type_rw1 : forall c,
      kbind typ k f (ty_c c) = ty_c c.
  Proof.
    test_simplification.
  Qed.

  Lemma kbind_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      kbind typ k f (ty_v a) = ty_v a.
  Proof.
    intros.
    rewrite ?kbind_to_mbind;
  simplify_mbind;
  simplify_kbind_pre_refold_hook;
  rewrite <- ?kbind_to_mbind;
  simplify_kbind_post_refold_hook.
    try rewrite btg_neq; auto.
  Abort.

  Lemma kbind_type_rw3 : forall (t1 t2 : typ A),
      kbind typ k f (ty_ar t1 t2) =
        ty_ar (kbind typ k f t1) (kbind typ k f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma kbind_type_rw4 : forall (body : typ A),
      kbind typ k f (ty_univ body) =
        ty_univ (kbind typ k f body).
  Proof.
    test_simplification.
  Qed.

  Lemma kbind_term_rw1_neq : forall (a : A),
      k <> ktrm ->
      kbind term k f (tm_var a) = tm_var a.
  Proof.
    intros.
    simplify_kbind.
    try rewrite btg_neq; auto.
  Abort.

  Lemma kbind_term_rw2 : forall (τ : typ A) (t : term A),
      kbind term k f (tm_abs τ t) =
        tm_abs (kbind typ k f τ) (kbind term k f t).
  Proof.
    test_simplification.
  Qed.

  Lemma kbind_term_rw3 : forall (t1 t2 : term A),
      kbind term k f (tm_app t1 t2) =
        tm_app (kbind term k f t1) (kbind term k f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma kbind_term_rw4 : forall (t : term A),
      kbind term k f (tm_tab t) =
        tm_tab (kbind term k f t).
  Proof.
    test_simplification.
  Qed.

  Lemma kbind_term_rw5 : forall (t: term A) (τ : typ A),
      kbind term k f (tm_tap t τ) =
        tm_tap (kbind term k f t) (kbind typ k f τ).
  Proof.
    test_simplification.
  Qed.

End rw_kbind.

Ltac simplify_kmapdt_pre_refold_hook ix :=
  rewrite ?(tgtdt_compose_incr (ix := ix)).

Ltac simplify_kmapdt_post_refold_hook :=
  idtac.

Ltac simplify_kmapdt :=
  match goal with
  | |- context[kmapdt (W := ?W) (T := ?T) (ix := ?ix)
                ?U ?k ?f ?t] =>
      rewrite ?kmapdt_to_mmapdt;
      simplify_mmapdt;
      simplify_kmapdt_pre_refold_hook ix;
      rewrite <- ?kmapdt_to_mmapdt;
      simplify_kmapdt_post_refold_hook
  end.

(** ** <<kmapdt>> *)
(******************************************************************************)
Section rw_kmapdt.

  Context
    (A : Type)
      `{Applicative G}
      (k : K2)
      (f : list K2 * A -> G A).

  Ltac tactic_being_tested ::= simplify_kmapdt.

  Lemma kmapdt_type_rw1 : forall c,
      kmapdt (G := G) typ k f (ty_c c) = pure (F := G) (ty_c c).
  Proof.
    test_simplification.
  Qed.

  Lemma kmapdt_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      kmapdt typ k f (ty_v a) = pure (ty_v a).
  Proof.
    intros.
    simplify_kmapdt.
  Abort.

  (*
    Lemma kmapdt_type_neq_rw2_eq : forall (a : A) (Heq: k = ktyp),
        kmapdt typ k f (ty_v a) = rew Heq in (f ([], a)).
    Proof.
      intros.
      simplify_kmapdt.
      subst.
      rewrite btgd_eq. auto.
    Qed.
   *)

  Lemma kmapdt_type_rw3 : forall (t1 t2 : typ A),
      kmapdt typ k f (ty_ar t1 t2) =
        pure ty_ar <⋆> (kmapdt typ k f t1) <⋆> (kmapdt typ k f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma kmapdt_type_rw4 : forall (body : typ A),
      kmapdt typ k f (ty_univ body) =
        pure ty_univ <⋆> (kmapdt typ k (f ⦿ [ktyp]) body).
  Proof.
    test_simplification.
  Qed.

  (*
  Lemma kmapdt_term_rw1_neq : forall (a : A),
      k <> ktrm ->
      kmapdt term k f (tm_var a) = tm_var a.
  Proof.
    intros.
    simplify_kmapdt.
    rewrite btgd_neq; auto.
  Qed.
  *)

  Lemma kmapdt_term_rw2 : forall (τ : typ A) (t : term A),
      kmapdt term k f (tm_abs τ t) =
        pure tm_abs <⋆> (kmapdt typ k f τ)
          <⋆> (kmapdt term k (f ⦿ [ktrm]) t).
  Proof.
    test_simplification.
  Qed.

  Lemma kmapdt_term_rw3 : forall (t1 t2 : term A),
      kmapdt term k f (tm_app t1 t2) =
        pure tm_app <⋆> (kmapdt term k f t1)
          <⋆> (kmapdt term k f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma kmapdt_term_rw4 : forall (t : term A),
      kmapdt term k f (tm_tab t) =
        pure tm_tab <⋆> (kmapdt term k (f ⦿ [ktyp]) t).
  Proof.
    test_simplification.
  Qed.

  Lemma kmapdt_term_rw5 : forall (t: term A) (τ : typ A),
      kmapdt term k f (tm_tap t τ) =
        pure tm_tap <⋆> (kmapdt term k f t) <⋆> (kmapdt typ k f τ).
  Proof.
    test_simplification.
  Qed.

End rw_kmapdt.

Ltac simplify_foldMapkd_pre_refold_hook ix :=
  idtac.

Ltac simplify_foldMapkd_post_refold_hook M :=
  repeat simplify_applicative_const;
  repeat simplify_monoid_units;
  change (@const Type Type M ?anything) with M.

Ltac simplify_foldMapkd :=
  match goal with
  | |- context[foldMapkd (W := ?W) (T := ?T) (ix := ?ix)
                        (M := ?M)
                ?U ?k ?f ?t] =>
  rewrite ?(foldMapkd_to_kmapdt U (M := M));
  simplify_kmapdt;
  simplify_foldMapkd_pre_refold_hook ix;
  rewrite <- ?(foldMapkd_to_kmapdt U (M := M));
  rewrite <- ?(foldMapkd_to_kmapdt _ (M := M));
  (* ^ This is used because "_" might not match the U *)
  simplify_foldMapkd_post_refold_hook M
  end.

(** ** <<foldMapkd>> *)
(******************************************************************************)
Section rw_foldMapkd.

  Context
    (A : Type)
      `{Monoid M}
      (k : K2)
      (f : list K2 * A -> M).

  Ltac tactic_being_tested ::= simplify_foldMapkd.

  Lemma foldMapkd_type_rw1 : forall c,
      foldMapkd typ k f (ty_c c) = Ƶ.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapkd_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      foldMapkd typ k f (ty_v a) = pure (ty_v a).
  Proof.
    intros.
    simplify_foldMapkd.
  Abort.

  (*
    Lemma foldMapkd_type_neq_rw2_eq : forall (a : A) (Heq: k = ktyp),
        foldMapkd typ k f (ty_v a) = rew Heq in (f ([], a)).
    Proof.
      intros.
      simplify_foldMapkd.
      subst.
      rewrite btgd_eq. auto.
    Qed.
   *)

  Lemma foldMapkd_type_rw3 : forall (t1 t2 : typ A),
      foldMapkd typ k f (ty_ar t1 t2) =
        foldMapkd typ k f t1 ● foldMapkd typ k f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapkd_type_rw4 : forall (body : typ A),
      foldMapkd typ k f (ty_univ body) =
        foldMapkd typ k (f ⦿ [ktyp]) body.
  Proof.
    test_simplification.
  Qed.

  (*
  Lemma foldMapkd_term_rw1_neq : forall (a : A),
      k <> ktrm ->
      foldMapkd term k f (tm_var a) = tm_var a.
  Proof.
    intros.
    simplify_foldMapkd.
    rewrite btgd_neq; auto.
  Qed.
  *)

  Lemma foldMapkd_term_rw2 : forall (τ : typ A) (t : term A),
      foldMapkd term k f (tm_abs τ t) =
        foldMapkd typ k f τ ● foldMapkd term k (f ⦿ [ktrm]) t.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapkd_term_rw3 : forall (t1 t2 : term A),
      foldMapkd term k f (tm_app t1 t2) =
        foldMapkd term k f t1 ● foldMapkd term k f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapkd_term_rw4 : forall (t : term A),
      foldMapkd term k f (tm_tab t) =
        foldMapkd term k (f ⦿ [ktyp]) t.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapkd_term_rw5 : forall (t: term A) (τ : typ A),
      foldMapkd term k f (tm_tap t τ) =
        foldMapkd term k f t ● foldMapkd typ k f τ.
  Proof.
    test_simplification.
  Qed.

End rw_foldMapkd.

Ltac simplify_Forallkd_pre_refold_hook :=
  idtac.

Ltac simplify_Forallkd_post_refold_hook :=
  unfold_ops @Monoid_op_and;
  unfold_ops @Monoid_unit_true.

Ltac simplify_Forallkd :=
  match goal with
  | |- context[Forallkd (W := ?W) (T := ?T) (ix := ?ix)
                ?U ?k ?f ?t] =>
  rewrite ?Forallkd_to_foldMapkd;
  simplify_foldMapkd;
  simplify_Forallkd_pre_refold_hook;
  rewrite <- ?Forallkd_to_foldMapkd;
  simplify_Forallkd_post_refold_hook
  end.

(** ** <<Forallkd>> *)
(******************************************************************************)
Section rw_Forallkd.

  Context
    (A : Type)
      `{Monoid M}
      (k : K2)
      (f : list K2 * A -> Prop).

  Ltac tactic_being_tested ::= simplify_Forallkd.

  Lemma Forallkd_type_rw1 : forall c,
      Forallkd typ k f (ty_c c) = Ƶ.
  Proof.
    test_simplification.
  Qed.

  Lemma Forallkd_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      Forallkd typ k f (ty_v a) = True.
  Proof.
    intros.
    simplify_Forallkd.
  Abort.

  (*
    Lemma Forallkd_type_neq_rw2_eq : forall (a : A) (Heq: k = ktyp),
        Forallkd typ k f (ty_v a) = rew Heq in (f ([], a)).
    Proof.
      intros.
      simplify_Forallkd.
      subst.
      rewrite btgd_eq. auto.
    Qed.
   *)

  Lemma Forallkd_type_rw3 : forall (t1 t2 : typ A),
      Forallkd typ k f (ty_ar t1 t2) =
        (Forallkd typ k f t1 /\ Forallkd typ k f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma Forallkd_type_rw4 : forall (body : typ A),
      Forallkd typ k f (ty_univ body) =
        Forallkd typ k (f ⦿ [ktyp]) body.
  Proof.
    test_simplification.
  Qed.

  (*
  Lemma Forallkd_term_rw1_neq : forall (a : A),
      k <> ktrm ->
      Forallkd term k f (tm_var a) = tm_var a.
  Proof.
    intros.
    simplify_Forallkd.
    rewrite btgd_neq; auto.
  Qed.
  *)

  Lemma Forallkd_term_rw2 : forall (τ : typ A) (t : term A),
      Forallkd term k f (tm_abs τ t) =
        (Forallkd typ k f τ /\ Forallkd term k (f ⦿ [ktrm]) t).
  Proof.
    test_simplification.
  Qed.

  Lemma Forallkd_term_rw3 : forall (t1 t2 : term A),
      Forallkd term k f (tm_app t1 t2) =
        (Forallkd term k f t1 /\ Forallkd term k f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma Forallkd_term_rw4 : forall (t : term A),
      Forallkd term k f (tm_tab t) =
        Forallkd term k (f ⦿ [ktyp]) t.
  Proof.
    test_simplification.
  Qed.

  Lemma Forallkd_term_rw5 : forall (t: term A) (τ : typ A),
      Forallkd term k f (tm_tap t τ) =
        (Forallkd term k f t /\ Forallkd typ k f τ).
  Proof.
    test_simplification.
  Qed.

End rw_Forallkd.


Ltac simplify_foldMapk_pre_refold_hook ix :=
  repeat push_preincr_into_fn.

Ltac simplify_foldMapk_post_refold_hook M :=
  idtac.

Ltac simplify_foldMapk :=
  match goal with
  | |- context[foldMapk (W := ?W) (T := ?T) (ix := ?ix)
                        (M := ?M)
                ?U ?k ?f ?t] =>
  rewrite ?(foldMapk_to_foldMapkd (ix := ix) U (M := M));
  simplify_foldMapkd;
  simplify_foldMapk_pre_refold_hook ix;
  rewrite <- ?(foldMapk_to_foldMapkd _ (M := M));
  simplify_foldMapk_post_refold_hook M
  end.

(** ** <<foldMapk>> *)
(******************************************************************************)
Section rw_foldMapk.

  Context
    (A : Type)
      `{Monoid M}
      (k : K2)
      (f : A -> M).

  Ltac tactic_being_tested ::= simplify_foldMapk.

  Lemma foldMapk_type_rw1 : forall c,
      foldMapk typ k f (ty_c c) = Ƶ.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapk_type_rw2_neq : forall (a : A),
      k <> ktyp ->
      foldMapk typ k f (ty_v a) = Ƶ.
  Proof.
    intros.
    simplify_foldMapk.
  Abort.

  Lemma foldMapk_type_rw3 : forall (t1 t2 : typ A),
      foldMapk typ k f (ty_ar t1 t2) =
        foldMapk typ k f t1 ● foldMapk typ k f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapk_type_rw4 : forall (body : typ A),
      foldMapk typ k f (ty_univ body) =
        foldMapk typ k f body.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapk_term_rw2 : forall (τ : typ A) (t : term A),
      foldMapk term k f (tm_abs τ t) =
        foldMapk typ k f τ ● foldMapk term k f t.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapk_term_rw3 : forall (t1 t2 : term A),
      foldMapk term k f (tm_app t1 t2) =
        foldMapk term k f t1 ● foldMapk term k f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapk_term_rw4 : forall (t : term A),
      foldMapk term k f (tm_tab t) =
        foldMapk term k f t.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapk_term_rw5 : forall (t: term A) (τ : typ A),
      foldMapk term k f (tm_tap t τ) =
        foldMapk term k f t ● foldMapk typ k f τ.
  Proof.
    test_simplification.
  Qed.

End rw_foldMapk.
