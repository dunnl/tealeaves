From Tealeaves Require Export
  Examples.SystemF.Syntax
  Simplification.Tests.Support
  Simplification.MBinddt.

Ltac cbn_mbinddt_post_hook ::=
  try match goal with
  | |- context[bind_type ?G ?f ?τ] =>
      change (bind_type G f τ) with (mbinddt typ G f τ)
  | |- context[bind_term ?G ?f ?t] =>
      change (bind_term G f t) with (mbinddt term G f t)
  end.

#[local] Generalizable Variables G.
#[local] Arguments mbinddt {ix} {W}%type_scope {T} U%function_scope
  {MBind} {F}%function_scope {H H0 H1 A B} _ _.

(** ** <<mbinddt>> *)
(******************************************************************************)
Section rw_mbinddt.

  Context
    (A B : Type)
    `{Applicative G}
    (f : forall k, list K * A -> G (SystemF k B)).

  Ltac test_mbinddt :=
    intros;
    cbn_mbinddt;
    try normalize_K;
    conclude.

  Lemma mbinddt_type_rw1 : forall c,
      mbinddt typ f (ty_c c) = pure (ty_c c).
  Proof.
    test_mbinddt.
  Qed.

  Lemma mbinddt_type_rw2 : forall (a : A),
      mbinddt typ f (ty_v a) = f ktyp (nil, a).
  Proof.
    test_mbinddt.
  Qed.

  Lemma mbinddt_type_rw3 : forall (t1 t2 : typ A),
      mbinddt typ f (ty_ar t1 t2) =
        pure ty_ar <⋆> mbinddt typ f t1 <⋆> mbinddt typ f t2.
  Proof.
    test_mbinddt.
  Qed.

  Lemma mbinddt_type_rw4 : forall (body : typ A),
      mbinddt typ f (ty_univ body) =
        pure ty_univ <⋆> mbinddt typ (f ◻ allK (incr [ktyp])) body.
  Proof.
    test_mbinddt.
  Qed.

  Lemma mbinddt_term_rw1 : forall (a : A),
      mbinddt term f (tm_var a) = f ktrm (nil, a).
  Proof.
    test_mbinddt.
  Qed.

  Lemma mbinddt_term_rw2 : forall (τ : typ A) (t : term A),
      mbinddt term f (tm_abs τ t) =
        pure tm_abs <⋆> mbinddt typ f τ <⋆>
          mbinddt term (f ◻ allK (incr [ktrm])) t.
  Proof.
    test_mbinddt.
  Qed.

  Lemma mbinddt_term_rw3 : forall (t1 t2 : term A),
      mbinddt term f (tm_app t1 t2) =
        pure tm_app <⋆> (mbinddt term f t1) <⋆> (mbinddt term f t2).
  Proof.
    test_mbinddt.
  Qed.

  Lemma mbinddt_term_rw4 : forall (t : term A),
      mbinddt term f (tm_tab t) =
        pure tm_tab <⋆> mbinddt term (f ◻ allK (incr [ktyp])) t.
  Proof.
    test_mbinddt.
  Qed.

  Lemma mbinddt_term_rw5 : forall (t: term A) (τ : typ A),
      mbinddt term f (tm_tap t τ) =
        pure tm_tap <⋆> mbinddt term f t <⋆> mbinddt typ f τ.
  Proof.
    test_mbinddt.
  Qed.

End rw_mbinddt.

(** ** <<mbindd>> *)
(******************************************************************************)
Section rw_mbindd.

  Context
    (A B : Type)
    (f : forall k, list K * A -> SystemF k B).

  Ltac test_mbindd :=
    intros;
    simplify_mbindd;
    try normalize_K;
    conclude.

  Lemma mbindd_type_rw1 : forall c,
      mbindd typ f (ty_c c) = ty_c c.
  Proof.
    test_mbindd.
  Qed.

  Lemma mbindd_type_rw2 : forall (a : A),
      mbindd typ f (ty_v a) = f ktyp (nil, a).
  Proof.
    test_mbindd.
  Qed.

  Lemma mbindd_type_rw3 : forall (t1 t2 : typ A),
      mbindd typ f (ty_ar t1 t2) =
        ty_ar (mbindd typ f t1) (mbindd typ f t2).
  Proof.
    test_mbindd.
  Qed.

  Lemma mbindd_type_rw4 : forall (body : typ A),
      mbindd typ f (ty_univ body) =
        ty_univ (mbindd typ (f ◻ allK (incr [ktyp])) body).
  Proof.
    test_mbindd.
  Qed.

  Lemma mbindd_term_rw1 : forall (a : A),
      mbindd term f (tm_var a) = f ktrm (nil, a).
  Proof.
    test_mbindd.
  Qed.

  Lemma mbindd_term_rw2 : forall (τ : typ A) (t : term A),
      mbindd term f (tm_abs τ t) =
        tm_abs (mbindd typ f τ)
          (mbindd term (f ◻ allK (incr [ktrm])) t).
  Proof.
    test_mbindd.
  Qed.

  Lemma mbindd_term_rw3 : forall (t1 t2 : term A),
      mbindd term f (tm_app t1 t2) =
        tm_app  (mbindd term f t1) (mbindd term f t2).
  Proof.
    test_mbindd.
  Qed.

  Lemma mbindd_term_rw4 : forall (t : term A),
      mbindd term f (tm_tab t) =
        tm_tab (mbindd term (f ◻ allK (incr [ktyp])) t).
  Proof.
    test_mbindd.
  Qed.

  Lemma mbindd_term_rw5 : forall (t: term A) (τ : typ A),
      mbindd term f (tm_tap t τ) =
        tm_tap (mbindd term f t) (mbindd typ f τ).
  Proof.
    test_mbindd.
  Qed.

End rw_mbindd.

(** ** <<kbindd>> *)
(******************************************************************************)
Section rw_kbindd.

  Lemma kbindd_to_mbindd `{Ix:Index}: forall A (k: K) (f: list K * A -> SystemF k A),
    kbindd typ k f = mbindd typ (btgd k f).
  Proof.
    reflexivity.
  Qed.

  Context
    (A : Type)
    (k : K2)
    (f : list K2 * A -> SystemF k A).

  Lemma btgd_compose_incr:
    btgd k f ◻ allK (incr [ktyp]) =
      btgd k (f ⦿ [ktyp]).
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

  Ltac simplify_kbindd :=
    rewrite ?kbindd_to_mbindd;
    simplify_mbindd;
    rewrite <- ?kbindd_to_mbindd;
    autorewrite* with tea_tgt;
    try normalize_K.

  Ltac test_kbindd :=
    intros;
    simplify_kbindd.

  Lemma kbindd_type_rw1 : forall c,
      kbindd typ k f (ty_c c) = ty_c c.
  Proof.
    test_kbindd.
    conclude.
  Qed.

  Lemma kbindd_type_rw2 : forall (a : A),
      kbindd typ k f (ty_v a) =
        btgd k f ktyp ([], a).
  Proof.
    test_kbindd.
    conclude.
  Qed.

  Lemma kbindd_type_rw3 : forall (t1 t2 : typ A),
      kbindd typ k f (ty_ar t1 t2) =
        ty_ar (kbindd typ k f t1) (kbindd typ k f t2).
  Proof.
    test_kbindd.
    conclude.
  Qed.

  Lemma kbindd_type_rw4 : forall (body : typ A),
      kbindd typ k f (ty_univ body) =
        ty_univ (kbindd typ k (f ⦿ [ktyp]) body).
  Proof.
    intros.
    simplify_kbindd.
    setoid_rewrite btgd_compose_incr.
    rewrite <- kbindd_to_mbindd.
    normalize_K.
    conclude.
  Qed.

  (*
  Lemma kbindd_term_rw1 : forall (a : A),
      kbindd term ktrm f (tm_var a) = f ktrm (nil, a).
  Proof.
    test_kbindd.
  Qed.

  Lemma kbindd_term_rw2 : forall (τ : typ A) (t : term A),
      kbindd term k f (tm_abs τ t) =
        tm_abs (kbindd typ k f τ)
          (kbindd term k (f ◻ allK (incr [ktrm])) t).
  Proof.
    test_kbindd.
  Qed.

  Lemma kbindd_term_rw3 : forall (t1 t2 : term A),
      kbindd term f (tm_app t1 t2) =
        tm_app  (kbindd term f t1)  (kbindd term f t2).
  Proof.
    test_kbindd.
  Qed.

  Lemma kbindd_term_rw4 : forall (t : term A),
      kbindd term f (tm_tab t) =
        tm_tab (kbindd term (f ◻ allK (incr [ktyp])) t).
  Proof.
    test_kbindd.
  Qed.

  Lemma kbindd_term_rw5 : forall (t: term A) (τ : typ A),
      kbindd term f (tm_tap t τ) =
        tm_tap (kbindd term f t) (kbindd typ f τ).
  Proof.
    test_kbindd.
  Qed.
  *)

End rw_kbindd.

(*
(** * Rewriting operations on <<typ>> *)
(******************************************************************************)

(** ** Fundamental operations *)
(******************************************************************************)

(** *** <<mmapdt>> *)
(******************************************************************************)
Section rw_mmapdt_type.

  Context
    (A B : Type)
    `{Applicative F}
    (f : K -> list K * A -> F B).

  Lemma rw_mmapdt_type1:
    forall c, mmapdt typ F f (ty_c c) = pure (ty_c c).
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    simplify.
    reflexivity.
  Qed.

  (* Why is this expressed with ? *)
  Lemma rw_mmapdt_type2: forall (a: A), mmapdt typ F f (ty_v a) = pure ty_v  f ktyp (nil, a).
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    simplify.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma rw_mmapdt_type3: forall (t1 t2: typ A),
      mmapdt typ F f (ty_ar t1 t2) =
        pure (ty_ar)  mmapdt typ F f t1  mmapdt typ F f t2.
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    simplify.
    reflexivity.
  Qed.

  Lemma rw_mmapdt_type4: forall (body: typ A),
      mmapdt typ F f (ty_univ body) =
        pure (ty_univ)  mmapdt typ F (fun k => f k ∘ incr [ktyp]) body.
  Proof.
    reflexivity.
  Qed.

End rw_mmapdt_type.

(*
#[export] Hint Rewrite @rw_mmapdt_type1 @rw_mmapdt_type2 @rw_mmapdt_type3 @rw_mmapdt_type4: sysf_rw.
*)

(** *** <<mbindd>> *)
(******************************************************************************)
Section rw_mbindd_type.

  Context
    (A B: Type)
    (f: forall k, list K * A -> SystemF k B).

  Lemma rw_mbindd_type1: forall c, mbindd typ f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type2: forall (a: A), mbindd typ f (ty_v a) = f ktyp (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type3: forall (t1 t2: typ A), mbindd typ f (ty_ar t1 t2) = ty_ar (mbindd typ f t1) (mbindd typ f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type4: forall (body: typ A), mbindd typ f (ty_univ body) = ty_univ (mbindd typ (fun k => f k ∘ incr [ktyp]) body).
  Proof. reflexivity. Qed.

End rw_mbindd_type.

#[export] Hint Rewrite @rw_mbindd_type1 @rw_mbindd_type2 @rw_mbindd_type3 @rw_mbindd_type4: sysf_rw.

(** *** <<mbind>> *)
(******************************************************************************)
Section rw_mbind_type.

  Context
    (A B: Type)
    (f: forall k, A -> SystemF k B).

  Lemma rw_mbind_type1: forall c, mbind typ f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type2: forall (a: A), mbind typ f (ty_v a) = f ktyp a.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type3: forall (t1 t2: typ A), mbind typ f (ty_ar t1 t2) = ty_ar (mbind typ f t1) (mbind typ f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type4: forall (body: typ A), mbind typ f (ty_univ body) = ty_univ (mbind typ f body).
  Proof.
    intros. unfold mbind. rewrite rw_mbindd_type4. repeat fequal. now ext k [w a].
  Qed.

End rw_mbind_type.

#[export] Hint Rewrite @rw_mbind_type1 @rw_mbind_type2 @rw_mbind_type3 @rw_mbind_type4: sysf_rw.

(** *** <<kbindd>> with <<ktyp>> *)
(******************************************************************************)
Section rw_kbindd_type.

  Context
    (A: Type)
    (f: list K * A -> typ A).

  Lemma rw_kbindd_ktyp_type1: forall c, kbindd typ ktyp f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktyp_type2: forall a, kbindd typ ktyp f (ty_v a) = f (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktyp_type3: forall (t1 t2: typ A), kbindd typ ktyp f (ty_ar t1 t2) = ty_ar (kbindd typ ktyp f t1) (kbindd typ ktyp f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktyp_type4: forall (body: typ A), kbindd typ ktyp f (ty_univ body) = ty_univ (kbindd typ ktyp (f ∘ incr [ktyp]) body).
  Proof.
    intros. unfold kbindd. simpl_F.
    do 2 fequal. now ext j [w a].
  Qed.

End rw_kbindd_type.

#[export] Hint Rewrite @rw_kbindd_ktyp_type1 @rw_kbindd_ktyp_type2 @rw_kbindd_ktyp_type3 @rw_kbindd_ktyp_type4: sysf_rw.

(** *** <<kbindd>> with <<ktrm>> *)
(******************************************************************************)
Section rw_kbindd_type.

  Context
    (A: Type)
    (f: list K * A -> term A).

  Lemma rw_kbindd_ktrm_type1: forall c, kbindd typ ktrm f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktrm_type2: forall a, kbindd typ ktrm f (ty_v a) = ty_v a.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktrm_type3: forall (t1 t2: typ A), kbindd typ ktrm f (ty_ar t1 t2) = ty_ar (kbindd typ ktrm f t1) (kbindd typ ktrm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktrm_type4: forall (body: typ A), kbindd typ ktrm f (ty_univ body) = ty_univ (kbindd typ ktrm (f ∘ incr [ktyp]) body).
  Proof.
    intros. unfold kbindd. simpl_F.
    do 2 fequal. now ext j [w a].
  Qed.

End rw_kbindd_type.

#[export] Hint Rewrite @rw_kbindd_ktrm_type1 @rw_kbindd_ktrm_type2 @rw_kbindd_ktrm_type3 @rw_kbindd_ktrm_type4: sysf_rw.

(** *** <<kbind>> with <<ktyp>> *)
(******************************************************************************)
Section rw_kbind_type.

  Context
    (A: Type)
    (f: A -> typ A).

  Lemma rw_kbind_ktyp_type1: forall c, kbind typ ktyp f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktyp_type2: forall a, kbind typ ktyp f (ty_v a) = f a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktyp_type3: forall (t1 t2: typ A), kbind typ ktyp f (ty_ar t1 t2) = ty_ar (kbind typ ktyp f t1) (kbind typ ktyp f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktyp_type4: forall (body: typ A), kbind typ ktyp f (ty_univ body) = ty_univ (kbind typ ktyp f body).
  Proof.
    intros. unfold kbind. now simpl_F.
  Qed.

End rw_kbind_type.

#[export] Hint Rewrite @rw_kbind_ktyp_type1 @rw_kbind_ktyp_type2 @rw_kbind_ktyp_type3 @rw_kbind_ktyp_type4: sysf_rw.

(** *** <<kbind>> with <<ktrm>> *)
(******************************************************************************)
Section rw_kbind_type.

  Context
    (A: Type)
    (f: A -> term A).

  Lemma rw_kbind_ktrm_type1: forall c, kbind typ ktrm f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktrm_type2: forall a, kbind typ ktrm f (ty_v a) = ty_v a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktrm_type3: forall (t1 t2: typ A), kbind typ ktrm f (ty_ar t1 t2) = ty_ar (kbind typ ktrm f t1) (kbind typ ktrm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktrm_type4: forall (body: typ A), kbind typ ktrm f (ty_univ body) = ty_univ (kbind typ ktrm f body).
  Proof.
    intros. unfold kbind. now simpl_F.
  Qed.

End rw_kbind_type.

#[export] Hint Rewrite @rw_kbind_ktrm_type1 @rw_kbind_ktrm_type2 @rw_kbind_ktrm_type3 @rw_kbind_ktrm_type4: sysf_rw.

*)
