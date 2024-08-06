From Tealeaves Require Export
  Examples.SystemF.Syntax
  Simplification.Tests.Support.

Import Subset.Notations.
Import Monoid.Notations.
#[local] Generalizable Variables F G A B C ϕ.

Section sec.

  Context
    `{H : Index}
      `{A : K -> Type}
      `{B : K -> Type}
      `{C : K -> Type}
      `{W: Type}
      `{Monoid W}
      (g: forall k : K, B k -> C k)
      (f: forall k : K, W * A k -> B k).
  Ltac push_preincr_into_fn :=
    match goal with
    | |- context[(?g ∘ ?f) ⦿ ?w] =>
        ltac_trace "push_preincr_into_fn|assoc";
        rewrite (preincr_assoc g f w)
    | |- context[extract ⦿ ?w] =>
        ltac_trace "push_preincr_into_fn|extract";
        rewrite (extract_preincr w)
    end.

End sec.

(** * Rewriting core operations *)
(******************************************************************************)

(** ** Rewriting <<mbinddt>> *)
(******************************************************************************)
Section rw_mbinddt.

  Context
    (A B : Type)
    `{Applicative F}
    (f : forall k, list K * A -> F (SystemF k B)).

  Lemma mbinddt_type_rw1 : forall c,
      mbinddt typ f (ty_c c) = pure (ty_c c).
  Proof.
    intros.
    cbn_mbinddt.
    conclude.
  Qed.

  Lemma mbinddt_type_rw2 : forall (a : A),
      mbinddt typ f (ty_v a) = f ktyp (nil, a).
  Proof.
    intros.
    cbn_mbinddt.
    progress K_down.
    conclude.
  Qed.

  Lemma mbinddt_type_rw3 : forall (t1 t2 : typ A),
      mbinddt typ f (ty_ar t1 t2) =
        pure ty_ar <⋆> mbinddt typ f t1 <⋆> mbinddt typ f t2.
  Proof.
    intros.
    cbn_mbinddt.
    progress K_down.
    conclude.
  Qed.

  Lemma mbinddt_type_rw4 : forall (body : typ A),
      mbinddt typ f (ty_univ body) =
        pure ty_univ <⋆> mbinddt typ (f ◻ allK (incr [ktyp])) body.
  Proof.
    intros.
    cbn_mbinddt.
    progress K_down.
    conclude.
  Qed.

  Lemma mbinddt_term_rw1 : forall (a : A),
      mbinddt term f (tm_var a) = f ktrm (nil, a).
  Proof.
    intros.
    cbn_mbinddt.
    progress K_down.
    conclude.
  Qed.

  Lemma mbinddt_term_rw2 : forall (τ : typ A) (t : term A),
      mbinddt term f (tm_abs τ t) =
        pure tm_abs <⋆> mbinddt typ f τ <⋆>
          mbinddt term (f ◻ allK (incr [ktrm])) t.
  Proof.
    intros.
    cbn_mbinddt.
    use_operational_tcs.
    progress K_down.
    conclude.
  Qed.

  Lemma mbinddt_term_rw3 : forall (t1 t2 : term A),
      mbinddt term f (tm_app t1 t2) =
        pure tm_app <⋆> mbinddt term f t1 <⋆> mbinddt term f t2.
  Proof.
    intros.
    cbn_mbinddt.
    progress K_down.
    conclude.
  Qed.

  Lemma mbinddt_term_rw4 : forall (t : term A),
      mbinddt term f (tm_tab t) =
        pure tm_tab <⋆> mbinddt term (f ◻ allK (incr [ktyp])) t.
  Proof.
    intros.
    cbn_mbinddt.
    progress K_down.
    conclude.
  Qed.

  Lemma mbinddt_term_rw5 : forall (t: term A) (τ : typ A),
      mbinddt term f (tm_tap t τ) =
        pure tm_tap <⋆> mbinddt term f t <⋆> mbinddt typ f τ.
  Proof.
    intros.
    cbn_mbinddt.
    use_operational_tcs.
    progress K_down.
    conclude.
  Qed.

End rw_mbinddt.

(** ** Rewriting <<mbindd>> *)
(******************************************************************************)
Section mbindd_rw.

  Context
    (A B: Type)
    (f: forall k, list K * A -> SystemF k B).

  Lemma mbindd_type_rw1 : forall c,
      mbindd typ f (ty_c c) = ty_c c.
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

  Lemma mbindd_type_rw2 : forall (a : A),
      mbindd typ f (ty_v a) = f ktyp (nil, a).
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

  Lemma mbindd_type_rw3 : forall (t1 t2 : typ A),
      mbindd typ f (ty_ar t1 t2) =
        ty_ar (mbindd typ f t1) (mbindd typ f t2).
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

  Lemma mbindd_type_rw4 : forall (body : typ A),
      mbindd typ f (ty_univ body) =
        ty_univ (mbindd typ (f ◻ allK (incr [ktyp])) body).
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

  Lemma mbindd_term_rw1: forall (a: A),
      mbindd term f (tm_var a) = f ktrm (nil, a).
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

  Lemma mbindd_term_rw2: forall (τ: typ A) (t: term A),
      mbindd term f (tm_abs τ t) =
        tm_abs (mbindd typ f τ) (mbindd term (f ◻ allK (incr [ktrm])) t).
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

  Lemma mbindd_term_rw3: forall (t1 t2: term A),
      mbindd term f (tm_app t1 t2) =
        tm_app (mbindd term f t1) (mbindd term f t2).
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

  Lemma mbindd_term_rw4: forall (t: term A),
      mbindd term f (tm_tab t) =
        tm_tab (mbindd term (f ◻ allK (incr [ktyp])) t).
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

  Lemma mbindd_term_rw5: forall (t: term A) (τ: typ A),
      mbindd term f (tm_tap t τ) =
        tm_tap (mbindd term f t) (mbindd typ f τ).
  Proof.
    intros.
    simplify_mbindd.
    conclude.
  Qed.

End mbindd_rw.

(** ** Rewriting <<mbind>> *)
(******************************************************************************)

Ltac fixup_extract_incr :=
  rewrite vec_compose_assoc;
  K_up;
  rewrite vec_compose_allK;
  rewrite extract_incr.

Section mbind_rw.

  Context
    (A B: Type)
    (f: forall k, A -> SystemF k B).

  Lemma mbind_type_rw1 : forall c,
      mbind typ f (ty_c c) = ty_c c.
  Proof.
    intros.
    simplify_mbind.
    conclude.
  Qed.

  Lemma mbind_type_rw2 : forall (a : A),
      mbind typ f (ty_v a) = f ktyp a.
  Proof.
    intros.
    simplify_mbind.
    reflexivity.
  Qed.

  Lemma mbind_type_rw3 : forall (t1 t2 : typ A),
      mbind typ f (ty_ar t1 t2) =
        ty_ar (mbind typ f t1) (mbind typ f t2).
  Proof.
    intros.
    simplify_mbind.
    conclude.
  Qed.

  Lemma mbind_type_rw4 : forall (body : typ A),
      mbind typ f (ty_univ body) =
        ty_univ (mbind typ f body).
  Proof.
    intros.
    simplify_mbind.
    fixup_extract_incr.
    rewrite <- mbind_to_mbindd.
    conclude.
  Qed.

  Lemma mbind_term_rw1: forall (a: A),
      mbind term f (tm_var a) = f ktrm a.
  Proof.
    intros.
    simplify_mbind.
    reflexivity.
  Qed.

  Lemma mbind_term_rw2: forall (τ: typ A) (t: term A),
      mbind term f (tm_abs τ t) =
        tm_abs (mbind typ f τ) (mbind term f t).
  Proof.
    intros.
    simplify_mbind.
    fixup_extract_incr.
    rewrite <- mbind_to_mbindd.
    conclude.
  Qed.

  Lemma mbind_term_rw3: forall (t1 t2: term A),
      mbind term f (tm_app t1 t2) =
        tm_app (mbind term f t1) (mbind term f t2).
  Proof.
    intros.
    simplify_mbind.
    conclude.
  Qed.

  Lemma mbind_term_rw4: forall (t: term A),
      mbind term f (tm_tab t) =
        tm_tab (mbind term f t).
  Proof.
    intros.
    simplify_mbind.
    fixup_extract_incr.
    rewrite <- mbind_to_mbindd.
    conclude.
  Qed.

  Lemma mbind_term_rw5: forall (t: term A) (τ: typ A),
      mbind term f (tm_tap t τ) =
        tm_tap (mbind term f t) (mbind typ f τ).
  Proof.
    intros.
    simplify_mbind.
    conclude.
  Qed.

End mbind_rw.

(** ** Rewriting <<mmapdt>> *)
(******************************************************************************)
Section rw_mmapdt.

  Context
    (A B : Type)
    `{Applicative F}
    (f : forall (k: K2), list K * A -> F B).

  Lemma mapMret_simpl: forall (k: K) (x: F B),
      mapMret k x = pure (mret SystemF k) <⋆> x.
  Proof.
    intros.
    unfold mapMret, vec_apply.
    rewrite map_to_ap.
    reflexivity.
  Qed.

  Lemma mmapdt_type_rw1 : forall c,
      mmapdt typ F f (ty_c c) = pure (ty_c c).
  Proof.
    intros.
    simplify_mmapdt.
    conclude.
  Qed.

  Lemma mmapdt_type_rw2 : forall (a : A),
      mmapdt typ F f (ty_v a) = pure ty_v <⋆> f ktyp (nil, a).
  Proof.
    intros.
    simplify_mmapdt.
    unfold vec_compose, compose.
    rewrite mapMret_simpl.
    cbn_subterm (mret (A := B) SystemF ktyp).
    progress grammatical_categories_down.
    progress K_down.
    conclude.
  Qed.

    Check (@mret _ SystemF MReturn_SystemF A):
      forall (k : @K I2), A -> SystemF k A.

    Check (fun k => map (A := A) (B := SystemF k A)):
      forall (k : @K I2), (A -> SystemF k A) -> F A -> F (SystemF k A).

    Check vec_compose
      (A := fun k => SystemF k A).

    Check vec_compose
      (fun k => map (A := A) (B := SystemF k A)).
(*
    Check
      (fun k => map (A := A) (B := SystemF k A))
        ◻
      (@mret _ SystemF MReturn_SystemF A).
    change (retAll) with ((fun k => map) ◻ @mret _ SystemF MReturn_SystemF A).
    Print retAll.
    About mret.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma mmapdt_type_rw3 : forall (t1 t2 : typ A),
      mmapdt typ F f (ty_ar t1 t2) =
        pure ty_ar <⋆> mmapdt typ F f t1 <⋆> mmapdt typ F f t2.
  Proof.
    intros.
    cbn_mmapdt.
    conclude.
  Qed.

  Lemma mmapdt_type_rw4 : forall (body : typ A),
      mmapdt typ F f (ty_univ body) =
        pure ty_univ <⋆> mmapdt typ F (f ◻ allK (incr [ktyp])) body.
  Proof.
    intros.
    simplify_mmapdt.
    rewrite vec_compose_assoc.
    rewrite <- mmapdt_to_mbinddt.
    progress K_down.
    conclude.
  Qed.

  Lemma mmapdt_term_rw1 : forall (a : A),
      mmapdt term F f (tm_var a) = pure tm_var <⋆> (f ktrm (nil, a)).
  Proof.
    intros.
    cbn_mmapdt.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma mmapdt_term_rw2 : forall (τ : typ A) (t : term A),
      mmapdt term F f (tm_abs τ t) =
        pure tm_abs <⋆> mmapdt typ F f τ <⋆>
          mmapdt term F (f ◻ allK (incr [ktrm])) t.
  Proof.
    intros.
    simplify_mmapdt.
    use_operational_tcs.
    rewrite vec_compose_assoc.
    rewrite <- ?mmapdt_to_mbinddt.
    progress progress K_down.
    conclude.
  Qed.

  Lemma mmapdt_term_rw3 : forall (t1 t2 : term A),
      mmapdt term F f (tm_app t1 t2) =
        pure tm_app <⋆> mmapdt term F f t1 <⋆> mmapdt term F f t2.
  Proof.
    intros.
    simplify_mmapdt.
    conclude.
  Qed.

  Lemma mmapdt_term_rw4 : forall (t : term A),
      mmapdt term F f (tm_tab t) =
        pure tm_tab <⋆> mmapdt term F (f ◻ allK (incr [ktyp])) t.
  Proof.
    intros.
    simplify_mmapdt.
    rewrite vec_compose_assoc.
    rewrite <- ?mmapdt_to_mbinddt.
    progress K_down.
    conclude.
  Qed.

  Lemma mmapdt_term_rw5 : forall (t: term A) (τ : typ A),
      mmapdt term F f (tm_tap t τ) =
        pure tm_tap <⋆> mmapdt term F f t <⋆> mmapdt typ F f τ.
  Proof.
    intros.
    simplify_mmapdt.
    use_operational_tcs.
    rewrite <- ?mmapdt_to_mbinddt.
    conclude.
  Qed.

End rw_mmapdt.

(*
(** ** Rewriting <<mmap>> *)
(******************************************************************************)
Section rw_mmap_term.

  Context
    (A B: Type)
    (f: forall (k: K2), A -> B).

  Lemma mmap_type_rw1 : forall c,
      mmap typ f (ty_c c) = ty_c c.
  Proof.
    intros.
    simplify_mmap.
    conclude.
  Qed.

  Lemma mmap_type_rw2 : forall (a : A),
      mmap typ f (ty_v a) = f ktyp a.
  Proof.
    intros.
    simplify_mmap.
    reflexivity.
  Qed.

  Lemma mmap_type_rw3 : forall (t1 t2 : typ A),
      mmap typ f (ty_ar t1 t2) =
        ty_ar (mmap typ f t1) (mmap typ f t2).
  Proof.
    intros.
    simplify_mmap.
    conclude.
  Qed.

  Lemma mmap_type_rw4 : forall (body : typ A),
      mmap typ f (ty_univ body) =
        ty_univ (mmap typ f body).
  Proof.
    intros.
    simplify_mmap.
    fixup_extract_incr.
    rewrite <- mmap_to_mmapd.
    conclude.
  Qed.

  Lemma rw_mmap_term1: forall (a: A),
      mmap term f (tm_var a) = f ktrm a.
  Proof.
    intros.
    simplify_mmap.
    reflexivity.
  Qed.

  Lemma rw_mmap_term2: forall (τ: typ A) (t: term A),
      mmap term f (tm_abs τ t) =
        tm_abs (mmap typ f τ) (mmap term f t).
  Proof.
    intros.
    simplify_mmap.
    fixup_extract_incr.
    rewrite <- mmap_to_mmapd.
    conclude.
  Qed.

  Lemma rw_mmap_term3: forall (t1 t2: term A),
      mmap term f (tm_app t1 t2) =
        tm_app (mmap term f t1) (mmap term f t2).
  Proof.
    intros.
    simplify_mmap.
    conclude.
  Qed.

  Lemma rw_mmap_term4: forall (t: term A),
      mmap term f (tm_tab t) =
        tm_tab (mmap term f t).
  Proof.
    intros.
    simplify_mmap.
    fixup_extract_incr.
    rewrite <- mmap_to_mmapd.
    conclude.
  Qed.

  Lemma rw_mmap_term5: forall (t: term A) (τ: typ A),
      mmap term f (tm_tap t τ) =
        tm_tap (mmap term f t) (mmap typ f τ).
  Proof.
    intros.
    simplify_mmap.
    conclude.
  Qed.

End rw_mmap_term.
*)

(** * Rewriting operations on <<term>> *)
(******************************************************************************)

(** ** Fundamental operations *)
(******************************************************************************)

(** *** <<mbinddt>> *)
(******************************************************************************)

(** *** <<mmapdt>> *)
(******************************************************************************)
Section rw_mmapdt_term.

  Context
    (A B: Type)
    `{Applicative F}
    (f: K -> list K * A -> F B).

  Lemma rw_mmapdt_term1: forall (a: A), mmapdt term F f (tm_var a) = pure tm_var <⋆> f ktrm (nil, a).
  Proof. intros. unfold mmapdt. autorewrite with sysf_rw. now rewrite <- map_to_ap. Qed.

  Lemma rw_mmapdt_term2: forall (τ: typ A) (t: term A), mmapdt term F f (tm_abs τ t) = pure tm_abs <⋆> (mmapdt typ F f τ) <⋆> (mmapdt term F (fun k => f k ∘ incr [ktrm]) t).
  Proof. reflexivity. Qed.

  Lemma rw_mmapdt_term3: forall (t1 t2: term A), mmapdt term F f (tm_app t1 t2) = pure tm_app <⋆> (mmapdt term F f t1) <⋆> (mmapdt term F f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mmapdt_term4: forall (t: term A), mmapdt term F f (tm_tab t) = pure tm_tab <⋆> (mmapdt term F (fun k => f k ∘ incr [ktyp]) t).
  Proof. reflexivity. Qed.

  Lemma rw_mmapdt_term5: forall (t: term A) (τ: typ A), mmapdt term F f (tm_tap t τ) = pure tm_tap <⋆> (mmapdt term F f t) <⋆> (mmapdt typ F f τ).
  Proof. reflexivity. Qed.

End rw_mmapdt_term.

#[export] Hint Rewrite @rw_mmapdt_term1 @rw_mmapdt_term2 @rw_mmapdt_term3 @rw_mmapdt_term4 @rw_mmapdt_term5: sysf_rw.


#[export] Hint Rewrite @mbindd_term_rw1 @mbindd_term_rw2 @mbindd_term_rw3 @mbindd_term_rw4 @mbindd_term_rw5: sysf_rw.

(** *** <<mbind>> *)
(******************************************************************************)
Section mbind_term_rw.

  Context
    (A B: Type)
    (f: forall k, A -> SystemF k B).

  Lemma mbind_term_rw1: forall (a: A), mbind term f (tm_var a) = f ktrm a.
  Proof. reflexivity. Qed.

  Lemma mbind_term_rw2: forall (τ: typ A) (t: term A), mbind term f (tm_abs τ t) = tm_abs (mbind typ f τ) (mbind term f t).
  Proof. intros. unfold mbind. autorewrite with sysf_rw. repeat fequal. now ext k [w a]. Qed.

  Lemma mbind_term_rw3: forall (t1 t2: term A), mbind term f (tm_app t1 t2) = tm_app (mbind term f t1) (mbind term f t2).
  Proof. reflexivity. Qed.

  Lemma mbind_term_rw4: forall (t: term A), mbind term f (tm_tab t) = tm_tab (mbind term f t).
  Proof. intros. unfold mbind. autorewrite with sysf_rw. repeat fequal. now ext k [w a]. Qed.

  Lemma mbind_term_rw5: forall (t: term A) (τ: typ A), mbind term f (tm_tap t τ) = tm_tap (mbind term f t) (mbind typ f τ).
  Proof. reflexivity. Qed.

End mbind_term_rw.

#[export] Hint Rewrite @mbind_term_rw1 @mbind_term_rw2 @mbind_term_rw3 @mbind_term_rw4 @mbind_term_rw5: sysf_rw.

(** *** <<kbindd>> with <<ktyp>> *)
(******************************************************************************)
Section rw_kbindd_ktyp_term.

  Context
    (A: Type)
    (f: list K * A -> typ A).

  Lemma rw_kbindd_ktyp_term1: forall (a: A), kbindd term ktyp f (tm_var a) = tm_var a.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktyp_term2: forall (τ: typ A) (t: term A), kbindd term ktyp f (tm_abs τ t) = tm_abs (kbindd typ ktyp f τ) (kbindd term ktyp (f ∘ incr [ktrm]) t).
  Proof. intros. unfold kbindd. autorewrite with sysf_rw. do 2 fequal. now ext k [w a]. Qed.

  Lemma rw_kbindd_ktyp_term3: forall (t1 t2: term A), kbindd term ktyp f (tm_app t1 t2) = tm_app (kbindd term ktyp f t1) (kbindd term ktyp f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktyp_term4: forall (t: term A), kbindd term ktyp f (tm_tab t) = tm_tab (kbindd term ktyp (f ∘ incr [ktyp]) t).
  Proof. intros. unfold kbindd. autorewrite with sysf_rw. do 2 fequal. now ext k [w a]. Qed.

  Lemma rw_kbindd_ktyp_term5: forall (t: term A) (τ: typ A), kbindd term ktyp f (tm_tap t τ) = tm_tap (kbindd term ktyp f t) (kbindd typ ktyp f τ).
  Proof. reflexivity. Qed.

End rw_kbindd_ktyp_term.

#[export] Hint Rewrite @rw_kbindd_ktyp_term1 @rw_kbindd_ktyp_term2 @rw_kbindd_ktyp_term3 @rw_kbindd_ktyp_term4 @rw_kbindd_ktyp_term5: sysf_rw.

(** *** <<kbindd>> with <<ktrm>> *)
(******************************************************************************)
Section rw_kbindd_ktrm_term.

  Context
    (A: Type)
    (f: list K * A -> term A).

  Lemma rw_kbindd_ktrm_term1: forall (a: A), kbindd term ktrm f (tm_var a) = f (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktrm_term2: forall (τ: typ A) (t: term A), kbindd term ktrm f (tm_abs τ t) = tm_abs (kbindd typ ktrm f τ) (kbindd term ktrm (f ∘ incr [ktrm]) t).
  Proof. intros. unfold kbindd. autorewrite with sysf_rw. do 2 fequal. now ext k [w a]. Qed.

  Lemma rw_kbindd_ktrm_term3: forall (t1 t2: term A), kbindd term ktrm f (tm_app t1 t2) = tm_app (kbindd term ktrm f t1) (kbindd term ktrm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_ktrm_term4: forall (t: term A), kbindd term ktrm f (tm_tab t) = tm_tab (kbindd term ktrm (f ∘ incr [ktyp]) t).
  Proof. intros. unfold kbindd. autorewrite with sysf_rw. do 2 fequal. now ext k [w a]. Qed.

  Lemma rw_kbindd_ktrm_term5: forall (t: term A) (τ: typ A), kbindd term ktrm f (tm_tap t τ) = tm_tap (kbindd term ktrm f t) (kbindd typ ktrm f τ).
  Proof. reflexivity. Qed.

End rw_kbindd_ktrm_term.

#[export] Hint Rewrite @rw_kbindd_ktrm_term1 @rw_kbindd_ktrm_term2 @rw_kbindd_ktrm_term3 @rw_kbindd_ktrm_term4 @rw_kbindd_ktrm_term5: sysf_rw.

(** *** <<kbind>> with <<ktyp>> *)
(******************************************************************************)
Section rw_kbind_ktyp_term.

  Context
    (A: Type)
    (f: A -> typ A).

  Lemma rw_kbind_ktyp_term1: forall (a: A), kbind term ktyp f (tm_var a) = tm_var a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktyp_term2: forall (τ: typ A) (t: term A), kbind term ktyp f (tm_abs τ t) = tm_abs (kbind typ ktyp f τ) (kbind term ktyp f t).
  Proof. intros. unfold kbind. now autorewrite with sysf_rw. Qed.

  Lemma rw_kbind_ktyp_term3: forall (t1 t2: term A), kbind term ktyp f (tm_app t1 t2) = tm_app (kbind term ktyp f t1) (kbind term ktyp f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktyp_term4: forall (t: term A), kbind term ktyp f (tm_tab t) = tm_tab (kbind term ktyp f t).
  Proof. intros. unfold kbind. now autorewrite with sysf_rw. Qed.

  Lemma rw_kbind_ktyp_term5: forall (t: term A) (τ: typ A), kbind term ktyp f (tm_tap t τ) = tm_tap (kbind term ktyp f t) (kbind typ ktyp f τ).
  Proof. reflexivity. Qed.

End rw_kbind_ktyp_term.

#[export] Hint Rewrite @rw_kbind_ktyp_term1 @rw_kbind_ktyp_term2 @rw_kbind_ktyp_term3 @rw_kbind_ktyp_term4 @rw_kbind_ktyp_term5: sysf_rw.

(** *** <<kbind>> with <<ktrm>> *)
(******************************************************************************)
Section rw_kbind_ktrm_term.

  Context
    (A: Type)
    (f: A -> term A).

  Lemma rw_kbind_ktrm_term1: forall (a: A), kbind term ktrm f (tm_var a) = f a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktrm_term2: forall (τ: typ A) (t: term A), kbind term ktrm f (tm_abs τ t) = tm_abs (kbind typ ktrm f τ) (kbind term ktrm f t).
  Proof. intros. unfold kbind. now autorewrite with sysf_rw. Qed.

  Lemma rw_kbind_ktrm_term3: forall (t1 t2: term A), kbind term ktrm f (tm_app t1 t2) = tm_app (kbind term ktrm f t1) (kbind term ktrm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_ktrm_term4: forall (t: term A), kbind term ktrm f (tm_tab t) = tm_tab (kbind term ktrm f t).
  Proof. intros. unfold kbind. now autorewrite with sysf_rw. Qed.

  Lemma rw_kbind_ktrm_term5: forall (t: term A) (τ: typ A), kbind term ktrm f (tm_tap t τ) = tm_tap (kbind term ktrm f t) (kbind typ ktrm f τ).
  Proof. reflexivity. Qed.

End rw_kbind_ktrm_term.

#[export] Hint Rewrite @rw_kbind_ktrm_term1 @rw_kbind_ktrm_term2 @rw_kbind_ktrm_term3 @rw_kbind_ktrm_term4 @rw_kbind_ktrm_term5: sysf_rw.
 *)

End rw_mmapdt.
