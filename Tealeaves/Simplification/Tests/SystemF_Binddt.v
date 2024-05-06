From Tealeaves Require Export
  Examples.SystemF.Syntax
  Simplification.Tests.Support.

#[local] Generalizable Variables G.
#[local] Arguments mbinddt {ix} {W}%type_scope {T} U%function_scope
  {MBind} {F}%function_scope {H H0 H1 A B} _ _.

Section rw_mbinddt.

  Context
    (A B : Type)
    `{Applicative G}
    (f : forall k, list K * A -> G (SystemF k B)).

  Lemma mbinddt_type_rw1 : forall c,
      mbinddt typ f (ty_c c) = pure (ty_c c).
  Proof.
    intros.
    simplify_binddt.
    reflexivity. Qed.

  Lemma mbinddt_type_rw2 : forall (a : A),
      mbinddt typ f (ty_v a) = f KType (nil, a).
  Proof. reflexivity. Qed.

  Lemma mbinddt_type_rw3 : forall (t1 t2 : typ A),
      mbinddt typ f (ty_ar t1 t2) =
        pure ty_ar <⋆> mbinddt typ f t1 <⋆> mbinddt typ f t2.
  Proof. reflexivity. Qed.

  Lemma mbinddt_type_rw4 : forall (body : typ A),
      mbinddt typ f (ty_univ body) =
        pure ty_univ <⋆> mbinddt typ (f ◻ const (incr [KType])) body.
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw1 : forall (a : A),
      mbinddt term f (tm_var a) = f KTerm (nil, a).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw2 : forall (τ : typ A) (t : term A),
      mbinddt term f (tm_abs τ t) =
        pure tm_abs <⋆> (mbinddt typ f τ) <⋆>
          (mbinddt term (f ◻ const (incr [KTerm])) t).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw3 : forall (t1 t2 : term A),
      mbinddt term f (tm_app t1 t2) =
        pure tm_app <⋆> (mbinddt term f t1) <⋆> (mbinddt term f t2).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw4 : forall (t : term A),
      mbinddt term f (tm_tab t) =
        pure tm_tab <⋆> (mbinddt term (fun k => f k ∘ incr [KType]) t).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw5 : forall (t: term A) (τ : typ A),
      mbinddt term f (tm_tap t τ) =
        pure tm_tap <⋆> (mbinddt term f t) <⋆> (mbinddt typ f τ).
  Proof. reflexivity. Qed.

End rw_mbinddt.

#[export] Hint Rewrite @mbinddt_term_rw1 @mbinddt_term_rw2 @mbinddt_term_rw3 @mbinddt_term_rw4 @mbinddt_term_rw5 : sysf_rw.
#[export] Hint Rewrite @mbinddt_type_rw1 @mbinddt_type_rw2 @mbinddt_type_rw3 @mbinddt_type_rw4 : sysf_rw.


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

  (* Why is this expressed with <⋆>? *)
  Lemma rw_mmapdt_type2: forall (a: A), mmapdt typ F f (ty_v a) = pure ty_v <⋆> f KType (nil, a).
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    simplify.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma rw_mmapdt_type3: forall (t1 t2: typ A),
      mmapdt typ F f (ty_ar t1 t2) =
        pure (ty_ar) <⋆> mmapdt typ F f t1 <⋆> mmapdt typ F f t2.
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    simplify.
    reflexivity.
  Qed.

  Lemma rw_mmapdt_type4: forall (body: typ A),
      mmapdt typ F f (ty_univ body) =
        pure (ty_univ) <⋆> mmapdt typ F (fun k => f k ∘ incr [KType]) body.
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

  Lemma rw_mbindd_type2: forall (a: A), mbindd typ f (ty_v a) = f KType (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type3: forall (t1 t2: typ A), mbindd typ f (ty_ar t1 t2) = ty_ar (mbindd typ f t1) (mbindd typ f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type4: forall (body: typ A), mbindd typ f (ty_univ body) = ty_univ (mbindd typ (fun k => f k ∘ incr [KType]) body).
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

  Lemma rw_mbind_type2: forall (a: A), mbind typ f (ty_v a) = f KType a.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type3: forall (t1 t2: typ A), mbind typ f (ty_ar t1 t2) = ty_ar (mbind typ f t1) (mbind typ f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type4: forall (body: typ A), mbind typ f (ty_univ body) = ty_univ (mbind typ f body).
  Proof.
    intros. unfold mbind. rewrite rw_mbindd_type4. repeat fequal. now ext k [w a].
  Qed.

End rw_mbind_type.

#[export] Hint Rewrite @rw_mbind_type1 @rw_mbind_type2 @rw_mbind_type3 @rw_mbind_type4: sysf_rw.

(** *** <<kbindd>> with <<KType>> *)
(******************************************************************************)
Section rw_kbindd_type.

  Context
    (A: Type)
    (f: list K * A -> typ A).

  Lemma rw_kbindd_KType_type1: forall c, kbindd typ KType f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type2: forall a, kbindd typ KType f (ty_v a) = f (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type3: forall (t1 t2: typ A), kbindd typ KType f (ty_ar t1 t2) = ty_ar (kbindd typ KType f t1) (kbindd typ KType f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type4: forall (body: typ A), kbindd typ KType f (ty_univ body) = ty_univ (kbindd typ KType (f ∘ incr [KType]) body).
  Proof.
    intros. unfold kbindd. simpl_F.
    do 2 fequal. now ext j [w a].
  Qed.

End rw_kbindd_type.

#[export] Hint Rewrite @rw_kbindd_KType_type1 @rw_kbindd_KType_type2 @rw_kbindd_KType_type3 @rw_kbindd_KType_type4: sysf_rw.

(** *** <<kbindd>> with <<KTerm>> *)
(******************************************************************************)
Section rw_kbindd_type.

  Context
    (A: Type)
    (f: list K * A -> term A).

  Lemma rw_kbindd_KTerm_type1: forall c, kbindd typ KTerm f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type2: forall a, kbindd typ KTerm f (ty_v a) = ty_v a.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type3: forall (t1 t2: typ A), kbindd typ KTerm f (ty_ar t1 t2) = ty_ar (kbindd typ KTerm f t1) (kbindd typ KTerm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type4: forall (body: typ A), kbindd typ KTerm f (ty_univ body) = ty_univ (kbindd typ KTerm (f ∘ incr [KType]) body).
  Proof.
    intros. unfold kbindd. simpl_F.
    do 2 fequal. now ext j [w a].
  Qed.

End rw_kbindd_type.

#[export] Hint Rewrite @rw_kbindd_KTerm_type1 @rw_kbindd_KTerm_type2 @rw_kbindd_KTerm_type3 @rw_kbindd_KTerm_type4: sysf_rw.

(** *** <<kbind>> with <<KType>> *)
(******************************************************************************)
Section rw_kbind_type.

  Context
    (A: Type)
    (f: A -> typ A).

  Lemma rw_kbind_KType_type1: forall c, kbind typ KType f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type2: forall a, kbind typ KType f (ty_v a) = f a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type3: forall (t1 t2: typ A), kbind typ KType f (ty_ar t1 t2) = ty_ar (kbind typ KType f t1) (kbind typ KType f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type4: forall (body: typ A), kbind typ KType f (ty_univ body) = ty_univ (kbind typ KType f body).
  Proof.
    intros. unfold kbind. now simpl_F.
  Qed.

End rw_kbind_type.

#[export] Hint Rewrite @rw_kbind_KType_type1 @rw_kbind_KType_type2 @rw_kbind_KType_type3 @rw_kbind_KType_type4: sysf_rw.

(** *** <<kbind>> with <<KTerm>> *)
(******************************************************************************)
Section rw_kbind_type.

  Context
    (A: Type)
    (f: A -> term A).

  Lemma rw_kbind_KTerm_type1: forall c, kbind typ KTerm f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type2: forall a, kbind typ KTerm f (ty_v a) = ty_v a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type3: forall (t1 t2: typ A), kbind typ KTerm f (ty_ar t1 t2) = ty_ar (kbind typ KTerm f t1) (kbind typ KTerm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type4: forall (body: typ A), kbind typ KTerm f (ty_univ body) = ty_univ (kbind typ KTerm f body).
  Proof.
    intros. unfold kbind. now simpl_F.
  Qed.

End rw_kbind_type.

#[export] Hint Rewrite @rw_kbind_KTerm_type1 @rw_kbind_KTerm_type2 @rw_kbind_KTerm_type3 @rw_kbind_KTerm_type4: sysf_rw.

*)
