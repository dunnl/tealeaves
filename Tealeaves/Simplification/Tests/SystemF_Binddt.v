From Tealeaves Require Export
  Examples.SystemF.Syntax
  Simplification.Tests.Support
  Classes.Multisorted.Theory.Foldmap.

#[local] Generalizable Variables G M.
#[local] Arguments mbinddt {ix} {W}%type_scope {T} U%function_scope
  {MBind} {F}%function_scope {H H0 H1 A B} _ _.

Ltac tactic_being_tested := idtac.

Ltac test_simplification :=
  intros;
  tactic_being_tested;
  try normalize_K;
  conclude.


(** ** <<mbinddt>> *)
(******************************************************************************)
Section rw_mbinddt.

  Context
    (A B : Type)
    `{Applicative G}
    (f : forall k, list K * A -> G (SystemF k B)).
  Ltac tactic_being_tested ::= cbn_mbinddt.

  Lemma mbinddt_type_rw1 : forall c,
      mbinddt typ f (ty_c c) = pure (ty_c c).
  Proof.
    test_simplification.
  Qed.

  Lemma mbinddt_type_rw2 : forall (a : A),
      mbinddt typ f (ty_v a) = f ktyp (nil, a).
  Proof.
    test_simplification.
  Qed.

  Lemma mbinddt_type_rw3 : forall (t1 t2 : typ A),
      mbinddt typ f (ty_ar t1 t2) =
        pure ty_ar <⋆> mbinddt typ f t1 <⋆> mbinddt typ f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma mbinddt_type_rw4 : forall (body : typ A),
      mbinddt typ f (ty_univ body) =
        pure ty_univ <⋆> mbinddt typ (f ◻ allK (incr [ktyp])) body.
  Proof.
    test_simplification.
  Qed.

  Lemma mbinddt_term_rw1 : forall (a : A),
      mbinddt term f (tm_var a) = f ktrm (nil, a).
  Proof.
    test_simplification.
  Qed.

  Lemma mbinddt_term_rw2 : forall (τ : typ A) (t : term A),
      mbinddt term f (tm_abs τ t) =
        pure tm_abs <⋆> mbinddt typ f τ <⋆>
          mbinddt term (f ◻ allK (incr [ktrm])) t.
  Proof.
    test_simplification.
  Qed.

  Lemma mbinddt_term_rw3 : forall (t1 t2 : term A),
      mbinddt term f (tm_app t1 t2) =
        pure tm_app <⋆> (mbinddt term f t1) <⋆> (mbinddt term f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma mbinddt_term_rw4 : forall (t : term A),
      mbinddt term f (tm_tab t) =
        pure tm_tab <⋆> mbinddt term (f ◻ allK (incr [ktyp])) t.
  Proof.
    test_simplification.
  Qed.

  Lemma mbinddt_term_rw5 : forall (t: term A) (τ : typ A),
      mbinddt term f (tm_tap t τ) =
        pure tm_tap <⋆> mbinddt term f t <⋆> mbinddt typ f τ.
  Proof.
    test_simplification.
  Qed.

End rw_mbinddt.

(** ** <<mbindd>> *)
(******************************************************************************)
Section rw_mbindd.

  Context
    (A B : Type)
    (f : forall k, list K * A -> SystemF k B).

  Ltac tactic_being_tested ::= simplify_mbindd.

  Lemma mbindd_type_rw1 : forall c,
      mbindd typ f (ty_c c) = ty_c c.
  Proof.
    test_simplification.
  Qed.

  Lemma mbindd_type_rw2 : forall (a : A),
      mbindd typ f (ty_v a) = f ktyp (nil, a).
  Proof.
    test_simplification.
  Qed.

  Lemma mbindd_type_rw3 : forall (t1 t2 : typ A),
      mbindd typ f (ty_ar t1 t2) =
        ty_ar (mbindd typ f t1) (mbindd typ f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma mbindd_type_rw4 : forall (body : typ A),
      mbindd typ f (ty_univ body) =
        ty_univ (mbindd typ (f ◻ allK (incr [ktyp])) body).
  Proof.
    test_simplification.
  Qed.

  Lemma mbindd_term_rw1 : forall (a : A),
      mbindd term f (tm_var a) = f ktrm (nil, a).
  Proof.
    test_simplification.
  Qed.

  Lemma mbindd_term_rw2 : forall (τ : typ A) (t : term A),
      mbindd term f (tm_abs τ t) =
        tm_abs (mbindd typ f τ)
          (mbindd term (f ◻ allK (incr [ktrm])) t).
  Proof.
    test_simplification.
  Qed.

  Lemma mbindd_term_rw3 : forall (t1 t2 : term A),
      mbindd term f (tm_app t1 t2) =
        tm_app (mbindd term f t1) (mbindd term f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma mbindd_term_rw4 : forall (t : term A),
      mbindd term f (tm_tab t) =
        tm_tab (mbindd term (f ◻ allK (incr [ktyp])) t).
  Proof.
    test_simplification.
  Qed.

  Lemma mbindd_term_rw5 : forall (t: term A) (τ : typ A),
      mbindd term f (tm_tap t τ) =
        tm_tap (mbindd term f t) (mbindd typ f τ).
  Proof.
    test_simplification.
  Qed.

End rw_mbindd.

(** ** <<mbind>> *)
(******************************************************************************)
Section rw_mbind.

  Context
    (A B : Type)
    (f : forall k, A -> SystemF k B).

  Ltac tactic_being_tested ::= simplify_mbind.

  Lemma mbind_type_rw1 : forall c,
      mbind typ f (ty_c c) = ty_c c.
  Proof.
    test_simplification.
  Qed.

  Lemma mbind_type_rw2 : forall (a : A),
      mbind typ f (ty_v a) = f ktyp a.
  Proof.
    test_simplification.
  Qed.

  Lemma mbind_type_rw3 : forall (t1 t2 : typ A),
      mbind typ f (ty_ar t1 t2) =
        ty_ar (mbind typ f t1) (mbind typ f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma mbind_type_rw4 : forall (body : typ A),
      mbind typ f (ty_univ body) =
        ty_univ (mbind typ f body).
  Proof.
    test_simplification.
  Qed.

  Lemma mbind_term_rw1 : forall (a : A),
      mbind term f (tm_var a) = f ktrm a.
  Proof.
    test_simplification.
  Qed.

  Lemma mbind_term_rw2 : forall (τ : typ A) (t : term A),
      mbind term f (tm_abs τ t) =
        tm_abs (mbind typ f τ) (mbind term f t).
  Proof.
    test_simplification.
  Qed.

  Lemma mbind_term_rw3 : forall (t1 t2 : term A),
      mbind term f (tm_app t1 t2) =
        tm_app (mbind term f t1) (mbind term f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma mbind_term_rw4 : forall (t : term A),
      mbind term f (tm_tab t) =
        tm_tab (mbind term f t).
  Proof.
    test_simplification.
  Qed.

  Lemma mbind_term_rw5 : forall (t: term A) (τ : typ A),
      mbind term f (tm_tap t τ) =
        tm_tap (mbind term f t) (mbind typ f τ).
  Proof.
    test_simplification.
  Qed.

End rw_mbind.

(** ** <<mmapdt>> *)
(******************************************************************************)
Section rw_mmapdt.

  Context
    (A B : Type)
    `{Applicative G}
    (f : forall (k: K), list K * A -> G B).

  Ltac tactic_being_tested ::= simplify_mmapdt.

  Lemma mmapdt_type_rw1 : forall c,
      mmapdt typ G f (ty_c c) = pure (ty_c c).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapdt_type_rw2 : forall (a : A),
      mmapdt typ G f (ty_v a) = pure ty_v <⋆> f ktyp (nil, a).
  Proof.
    intros.
    simplify_mmapdt.
    reflexivity.
  Qed.

  Lemma mmapdt_type_rw3 : forall (t1 t2 : typ A),
      mmapdt typ G f (ty_ar t1 t2) =
        pure ty_ar <⋆> mmapdt typ G f t1 <⋆> mmapdt typ G f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma mmapdt_type_rw4 : forall (body : typ A),
      mmapdt typ G f (ty_univ body) =
        pure ty_univ <⋆> mmapdt typ G (f ◻ allK (incr [ktyp])) body.
  Proof.
    test_simplification.
  Qed.

  Lemma mmapdt_term_rw1 : forall (a : A),
      mmapdt term G f (tm_var a) = pure tm_var <⋆> f ktrm (nil, a).
  Proof.
    intros.
    simplify_mmapdt.
    reflexivity.
  Qed.

  Lemma mmapdt_term_rw2 : forall (τ : typ A) (t : term A),
      mmapdt term G f (tm_abs τ t) =
        pure tm_abs <⋆> mmapdt typ G f τ <⋆>
          mmapdt term G (f ◻ allK (incr [ktrm])) t.
  Proof.
    test_simplification.
  Qed.

  Lemma mmapdt_term_rw3 : forall (t1 t2 : term A),
      mmapdt term G f (tm_app t1 t2) =
        pure tm_app <⋆> mmapdt term G f t1 <⋆> mmapdt term G f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma mmapdt_term_rw4 : forall (t : term A),
      mmapdt term G f (tm_tab t) =
        pure tm_tab <⋆> mmapdt term G (f ◻ allK (incr [ktyp])) t.
  Proof.
    test_simplification.
  Qed.

  Lemma mmapdt_term_rw5 : forall (t: term A) (τ : typ A),
      mmapdt term G f (tm_tap t τ) =
        pure tm_tap <⋆> mmapdt term G f t <⋆> mmapdt typ G f τ.
  Proof.
    test_simplification.
  Qed.

End rw_mmapdt.

(** ** <<mmapd>> *)
(******************************************************************************)
Section rw_mmapd.

  Context
    (A B : Type)
    (f : forall (k: K), list K * A -> B).

  Ltac tactic_being_tested ::= simplify_mmapd.

  Lemma mmapd_type_rw1 : forall c,
      mmapd typ f (ty_c c) = pure (ty_c c).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapd_type_rw2 : forall (a : A),
      mmapd typ f (ty_v a) = ty_v (f ktyp (nil, a)).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapd_type_rw3 : forall (t1 t2 : typ A),
      mmapd typ f (ty_ar t1 t2) =
        ty_ar (mmapd typ f t1) (mmapd typ f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapd_type_rw4 : forall (body : typ A),
      mmapd typ f (ty_univ body) =
        ty_univ (mmapd typ (f ◻ allK (incr [ktyp])) body).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapd_term_rw1 : forall (a : A),
      mmapd term f (tm_var a) = tm_var (f ktrm (nil, a)).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapd_term_rw2 : forall (τ : typ A) (t : term A),
      mmapd term f (tm_abs τ t) =
        tm_abs (mmapd typ f τ)
          (mmapd term (f ◻ allK (incr [ktrm])) t).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapd_term_rw3 : forall (t1 t2 : term A),
      mmapd term f (tm_app t1 t2) =
        tm_app (mmapd term f t1) (mmapd term f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapd_term_rw4 : forall (t : term A),
      mmapd term f (tm_tab t) =
        tm_tab (mmapd term (f ◻ allK (incr [ktyp])) t).
  Proof.
    test_simplification.
  Qed.

  Lemma mmapd_term_rw5 : forall (t: term A) (τ : typ A),
      mmapd term f (tm_tap t τ) =
        tm_tap (mmapd term f t) (mmapd typ f τ).
  Proof.
    test_simplification.
  Qed.

End rw_mmapd.

Ltac simplify_foldMapmd_pre_refold_hook ix := idtac.
Ltac simplify_foldMapmd_post_refold_hook M :=
  repeat simplify_applicative_const;
  (* ^ above step creates some ((Ƶ ● m) ● n) *)
  repeat simplify_monoid_units;
  change (@const Type Type M ?anything) with M.

Ltac simplify_foldMapmd :=
  match goal with
  | |- context[foldMapmd (W := ?W) (T := ?T) (ix := ?ix) (M := ?M)
                ?U ?f ?t] =>
      rewrite ?foldMapmd_to_mmapdt;
      simplify_mmapdt;
      simplify_foldMapmd_pre_refold_hook ix;
      rewrite <- ?foldMapmd_to_mmapdt;
      simplify_foldMapmd_post_refold_hook M
  end.

(** ** <<foldMapmd>> *)
(******************************************************************************)
Section rw_foldMapmd.

  Context
    (A : Type)
      `{Monoid M}
      (f : forall (k: K), list K * A -> M).

  Ltac tactic_being_tested ::= simplify_foldMapmd.

  Lemma foldMapmd_type_rw1 : forall c,
      foldMapmd typ f (ty_c c) = Ƶ.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapmd_type_rw2 : forall (a : A),
      foldMapmd typ f (ty_v a) = f ktyp (nil, a).
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapmd_type_rw3 : forall (t1 t2 : typ A),
      foldMapmd typ f (ty_ar t1 t2) =
        foldMapmd typ f t1 ● foldMapmd typ f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapmd_type_rw4 : forall (body : typ A),
      foldMapmd typ f (ty_univ body) =
        foldMapmd typ (f ◻ allK (incr [ktyp])) body.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapmd_term_rw1 : forall (a : A),
      foldMapmd term f (tm_var a) = f ktrm (nil, a).
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapmd_term_rw2 : forall (τ : typ A) (t : term A),
      foldMapmd term f (tm_abs τ t) =
        foldMapmd typ f τ ●
          foldMapmd term (f ◻ allK (incr [ktrm])) t.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapmd_term_rw3 : forall (t1 t2 : term A),
      foldMapmd term f (tm_app t1 t2) =
        foldMapmd term f t1 ● foldMapmd term f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapmd_term_rw4 : forall (t : term A),
      foldMapmd term f (tm_tab t) =
        foldMapmd term (f ◻ allK (incr [ktyp])) t.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapmd_term_rw5 : forall (t: term A) (τ : typ A),
      foldMapmd term f (tm_tap t τ) =
        foldMapmd term f t ● foldMapmd typ f τ.
  Proof.
    test_simplification.
  Qed.

End rw_foldMapmd.

(* after unfolding,
   foldMapmd U (f ◻ allK extract) (C x1 x2)
   is simplified to
   foldMapmd typ ((f ◻ allK extract) ◻ allK (incr [ktyp])) x1) ...
 *)
Ltac simplify_foldMapm_pre_refold_hook ix :=
  repeat ( rewrite ?vec_compose_assoc;
           rewrite (vec_compose_allK (H := ix));
           rewrite extract_incr).


Ltac simplify_foldMapm_post_refold_hook ix := idtac.


(* At a k-annotated leaf,
   foldMapm f (Ret x)
   becomes
   (f ◻ allK (extract (W := ?W))) k (Ƶ, x)] =>
 *)
Ltac simplify_foldMapm_at_leaf_hook :=
  simplify_mbind_at_leaf_hook.

Ltac simplify_foldMapm :=
  match goal with
  | |- context[foldMapm (W := ?W) (T := ?T) (ix := ?ix) (M := ?M)
                ?U ?f ?t] =>
      rewrite ?foldMapm_to_foldMapmd;
      simplify_foldMapmd;
      simplify_foldMapm_pre_refold_hook ix;
      rewrite <- ?foldMapm_to_foldMapmd;
      simplify_foldMapm_post_refold_hook M;
      simplify_foldMapm_at_leaf_hook
  end.

(** ** <<foldMapm>> *)
(******************************************************************************)
Section rw_foldMapm.

  Context
    (A : Type)
      `{Monoid M}
      (f : K -> A -> M).

  Ltac tactic_being_tested ::= simplify_foldMapm.

  Lemma foldMapm_type_rw1 : forall c,
      foldMapm typ f (ty_c c) = Ƶ.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapm_type_rw2 : forall (a : A),
      foldMapm typ f (ty_v a) = f ktyp a.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapm_type_rw3 : forall (t1 t2 : typ A),
      foldMapm typ f (ty_ar t1 t2) =
        foldMapm typ f t1 ● foldMapm typ f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapm_type_rw4 : forall (body : typ A),
      foldMapm typ f (ty_univ body) =
        foldMapm typ f body.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapm_term_rw1 : forall (a : A),
      foldMapm term f (tm_var a) = f ktrm a.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapm_term_rw2 : forall (τ : typ A) (t : term A),
      foldMapm term f (tm_abs τ t) =
        foldMapm typ f τ ●
          foldMapm term f t.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapm_term_rw3 : forall (t1 t2 : term A),
      foldMapm term f (tm_app t1 t2) =
        foldMapm term f t1 ● foldMapm term f t2.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapm_term_rw4 : forall (t : term A),
      foldMapm term f (tm_tab t) =
        foldMapm term f t.
  Proof.
    test_simplification.
  Qed.

  Lemma foldMapm_term_rw5 : forall (t: term A) (τ : typ A),
      foldMapm term f (tm_tap t τ) =
        foldMapm term f t ● foldMapm typ f τ.
  Proof.
    test_simplification.
  Qed.

End rw_foldMapm.

Ltac simplify_Forallmd_pre_refold_hook := idtac.
Ltac simplify_Forallmd_post_refold_hook :=
  unfold_ops @Monoid_op_and;
  unfold_ops @Monoid_unit_true.

Ltac simplify_Forallmd :=
  match goal with
  | |- context[Forallmd (W := ?W) (T := ?T) (ix := ?ix)
                ?U ?f ?t] =>
      rewrite ?Forallmd_to_foldMapmd;
      simplify_foldMapmd;
      simplify_Forallmd_pre_refold_hook;
      rewrite <- ?Forallmd_to_foldMapmd;
      simplify_Forallmd_post_refold_hook
  end.

(** ** <<Forallmd>> *)
(******************************************************************************)
Section rw_Forallmd.

  Context
    (A : Type)
      `{Monoid M}
      (f : forall (k: K), list K * A -> Prop).

  Ltac tactic_being_tested ::= simplify_Forallmd.

  Lemma Forallmd_type_rw1 : forall c,
      Forallmd typ f (ty_c c) = True.
  Proof.
    test_simplification.
  Qed.

  Lemma Forallmd_type_rw2 : forall (a : A),
      Forallmd typ f (ty_v a) = f ktyp (nil, a).
  Proof.
    test_simplification.
  Qed.

  Lemma Forallmd_type_rw3 : forall (t1 t2 : typ A),
      Forallmd typ f (ty_ar t1 t2) =
        (Forallmd typ f t1 /\ Forallmd typ f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma Forallmd_type_rw4 : forall (body : typ A),
      Forallmd typ f (ty_univ body) =
        Forallmd typ (f ◻ allK (incr [ktyp])) body.
  Proof.
    test_simplification.
  Qed.

  Lemma Forallmd_term_rw1 : forall (a : A),
      Forallmd term f (tm_var a) = f ktrm (nil, a).
  Proof.
    test_simplification.
  Qed.

  Lemma Forallmd_term_rw2 : forall (τ : typ A) (t : term A),
      Forallmd term f (tm_abs τ t) =
        (Forallmd typ f τ /\
          Forallmd term (f ◻ allK (incr [ktrm])) t).
  Proof.
    test_simplification.
  Qed.

  Lemma Forallmd_term_rw3 : forall (t1 t2 : term A),
      Forallmd term f (tm_app t1 t2) =
        (Forallmd term f t1 /\ Forallmd term f t2).
  Proof.
    test_simplification.
  Qed.

  Lemma Forallmd_term_rw4 : forall (t : term A),
      Forallmd term f (tm_tab t) =
        Forallmd term (f ◻ allK (incr [ktyp])) t.
  Proof.
    test_simplification.
  Qed.

  Lemma Forallmd_term_rw5 : forall (t: term A) (τ : typ A),
      Forallmd term f (tm_tap t τ) =
        (Forallmd term f t /\ Forallmd typ f τ).
  Proof.
    test_simplification.
  Qed.

End rw_Forallmd.
