From Tealeaves Require Export
  Examples.SystemF.Syntax
  Simplification.Tests.Support
  Simplification.MBinddt.

Import Subset.Notations.
Import Monoid.Notations.
#[local] Generalizable Variables F G A B C ϕ.

#[local] Arguments mbinddt {ix} {W}%type_scope {T} U%function_scope
  {MBind} {F}%function_scope {H H0 H1 A B} _ _.

Ltac normalize := change (@K I2) with K2 in *.

(** * Miscellaneous lemmas *)
(******************************************************************************)
Lemma filterk_incr : forall (A : Type) (k : K) (l : list (list K2 * (K * A))) (inc : list K2),
    filterk k (map (F := list) (incr inc) l) = map (F := list) (incr inc) (filterk k l).
Proof.
  intros. induction l.
  - easy.
  - destruct a as  [ctx [j a]].
    rewrite map_list_cons.
    change (incr inc (ctx, (j, a))) with (inc ++ ctx, (j, a)).
    compare values k and j.
    + do 2 rewrite filterk_cons_eq.
      autorewrite with tea_list.
      now rewrite IHl.
    + rewrite filterk_cons_neq; auto.
      rewrite filterk_cons_neq; auto.
Qed.

(** * Simplification support *)
(******************************************************************************)
Lemma mextract_preincr2 :
  forall `{ix: Index} {W : Type} {op : Monoid_op W}
    {A: Type} {B : K -> Type} (f: forall k, A -> B k) (w : W),
    (f ◻ const (extract (W := prod W) (A := A))) ◻ const (incr w) =
      (f ◻ const (extract (W := prod W))).
Proof.
  intros.
  ext k. ext [w' a].
  reflexivity.
Qed.

Create HintDb sysf_rw.
Tactic Notation "simpl_F" := autorewrite with sysf_rw.

(*
#[export] Hint Rewrite @mbinddt_term_rw1 @mbinddt_term_rw2 @mbinddt_term_rw3 @mbinddt_term_rw4 @mbinddt_term_rw5 : sysf_rw.
#[export] Hint Rewrite @mbinddt_type_rw1 @mbinddt_type_rw2 @mbinddt_type_rw3 @mbinddt_type_rw4 : sysf_rw.
 *)

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
    normalize.
    conclude.
  Qed.

  Lemma mbinddt_type_rw3 : forall (t1 t2 : typ A),
      mbinddt typ f (ty_ar t1 t2) =
        pure ty_ar <⋆> mbinddt typ f t1 <⋆> mbinddt typ f t2.
  Proof.
    intros.
    cbn_mbinddt.
    normalize.
    conclude.
  Qed.

  Lemma mbinddt_type_rw4 : forall (body : typ A),
      mbinddt typ f (ty_univ body) =
        pure ty_univ <⋆> mbinddt typ (f ◻ allK (incr [ktyp])) body.
  Proof.
    intros.
    cbn_mbinddt.
    normalize.
    conclude.
    reflexivity. Qed.

  Lemma mbinddt_term_rw1 : forall (a : A),
      mbinddt term f (tm_var a) = f ktrm (nil, a).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw2 : forall (τ : typ A) (t : term A),
      mbinddt term f (tm_abs τ t) =
        pure tm_abs <⋆> (mbinddt typ f τ) <⋆>
          (mbinddt term (f ◻ const (incr [ktrm])) t).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw3 : forall (t1 t2 : term A),
      mbinddt term f (tm_app t1 t2) =
        pure tm_app <⋆> (mbinddt term f t1) <⋆> (mbinddt term f t2).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw4 : forall (t : term A),
      mbinddt term f (tm_tab t) =
        pure tm_tab <⋆> (mbinddt term (fun k => f k ∘ incr [ktyp]) t).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw5 : forall (t: term A) (τ : typ A),
      mbinddt term f (tm_tap t τ) =
        pure tm_tap <⋆> (mbinddt term f t) <⋆> (mbinddt typ f τ).
  Proof. reflexivity. Qed.

End rw_mbinddt.


Ltac simplify :=
  match goal with
  | |- context[mbinddt typ ?f ?t] =>
      first [ rewrite mbinddt_type_rw1
            | rewrite mbinddt_type_rw2
            | rewrite mbinddt_type_rw3
            | rewrite mbinddt_type_rw4 ]
  | |- context[mbinddt term ?f ?t] =>
      first [ rewrite mbinddt_term_rw1
            | rewrite mbinddt_term_rw2
            | rewrite mbinddt_term_rw3
            | rewrite mbinddt_term_rw4
            | rewrite mbinddt_term_rw5 ]
  (* new stuff *)
  | |- context[(?f ◻ const extract) ◻ const (incr ?w)] =>
      rewrite mextract_preincr2
  end.


(** ** List and occurrence operations *)
(******************************************************************************)

(** *** <<tolistmd>> *)
(******************************************************************************)
Section rw_tolistmd_type.

  Context
    (A: Type).

  Lemma rw_tolistmd_type1: forall c,
      tolistmd (A:= A) typ (ty_c c) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_tolistmd_type2: forall (a: A),
      tolistmd typ (ty_v a) = [ (nil, (ktyp, a)) ].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_tolistmd_type3: forall (t1 t2: typ A),
      tolistmd typ (ty_ar t1 t2) = tolistmd typ t1 ++ tolistmd typ t2.
  Proof.
    reflexivity.
  Qed.

  (* TODO automate and generalize this proof *)
  Lemma rw_tolistmd_type4: forall (body: typ A),
      tolistmd typ (ty_univ body) = map (F:= list) (incr [ktyp]) (tolistmd typ body).
  Proof.
    intros.
    unfold tolistmd, tolistmd_gen.
    rewrite mmapdt_to_mbinddt.
    simplify.
    simplify.
    simplify.
    simplify.
    compose near body on right.
    rewrite vec_compose_assoc.
    rewrite (dtp_mbinddt_morphism
               (list (@K I2))
               SystemF
               typ
               (const (list _))
               (const (list _))
               (ϕ := (fun k => map
                              (A := list K2 * (@K I2 * A))
                              (F := list)
                              (Map := Map_list)
                              (incr [ktyp])))).
    fequal. now ext k [w a].
  Qed.

End rw_tolistmd_type.

#[export] Hint Rewrite @rw_tolistmd_type1 @rw_tolistmd_type2 @rw_tolistmd_type3 @rw_tolistmd_type4: sysf_rw.

(** *** <<toklistd>> with <<ktyp>> *)
(******************************************************************************)
Section rw_toklistd_ktyp_type.

  Context
    (A: Type).

  Lemma rw_toklistd_ktyp_type1: forall c,
      toklistd (A:= A) typ ktyp (ty_c c) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_toklistd_ktyp_type2: forall (a: A),
      toklistd typ ktyp (ty_v a) = [ (nil, a) ].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_toklistd_ktyp_type3: forall (t1 t2: typ A),
      toklistd typ ktyp (ty_ar t1 t2) =
        toklistd typ ktyp t1 ++ toklistd typ ktyp t2.
  Proof.
    intros.
    unfold toklistd, compose.
    rewrite rw_tolistmd_type3.
    now autorewrite with tea_list.
  Qed.

  Lemma rw_toklistd_ktyp_type4: forall (body: typ A), toklistd typ ktyp (ty_univ body) = map (F:= list) (incr [ktyp]) (toklistd typ ktyp body).
  Proof. intros. unfold toklistd, compose. rewrite rw_tolistmd_type4. now rewrite filterk_incr. Qed.

End rw_toklistd_ktyp_type.

#[export] Hint Rewrite @rw_toklistd_ktyp_type1 @rw_toklistd_ktyp_type2 @rw_toklistd_ktyp_type3 @rw_toklistd_ktyp_type4: sysf_rw.

(** *** <<toklistd>> with <<ktrm>> *)
(******************************************************************************)
Section rw_toklistd_ktrm_type.

  Context
    (A: Type).

  Lemma rw_toklistd_ktrm_type1: forall c, toklistd (A:= A) typ ktrm (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_ktrm_type2: forall (a: A), toklistd typ ktrm (ty_v a) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_ktrm_type3: forall (t1 t2: typ A), toklistd typ ktrm (ty_ar t1 t2) = toklistd typ ktrm t1 ++ toklistd typ ktrm t2.
  Proof. intros. unfold toklistd, compose. rewrite rw_tolistmd_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklistd_ktrm_type4: forall (body: typ A), toklistd typ ktrm (ty_univ body) = map (F:= list) (incr [ktyp]) (toklistd typ ktrm body).
  Proof. intros. unfold toklistd, compose. rewrite rw_tolistmd_type4. now rewrite filterk_incr. Qed.

End rw_toklistd_ktrm_type.

#[export] Hint Rewrite @rw_toklistd_ktrm_type1 @rw_toklistd_ktrm_type2 @rw_toklistd_ktrm_type3 @rw_toklistd_ktrm_type4: sysf_rw.

(** *** <<tolistm>> *)
(******************************************************************************)
Section rw_tolistm_type.

  Context
    (A: Type).

  Lemma rw_tolistm_type1: forall c, tolistm (A:= A) typ (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_tolistm_type2: forall (a: A), tolistm typ (ty_v a) = [ (ktyp, a) ].
  Proof. reflexivity. Qed.

  Lemma rw_tolistm_type3: forall (t1 t2: typ A), tolistm typ (ty_ar t1 t2) = tolistm typ t1 ++ tolistm typ t2.
  Proof. intros. unfold tolistm, compose. rewrite rw_tolistmd_type3. now autorewrite with tea_list. Qed.

  Lemma rw_tolistm_type4: forall (body: typ A), tolistm typ (ty_univ body) = (tolistm typ body).
  Proof. intros. unfold tolistm, compose. rewrite rw_tolistmd_type4.
         compose near (tolistmd typ body) on left. rewrite (fun_map_map (F:= list)).
         fequal. now ext [w a].
  Qed.

End rw_tolistm_type.

#[export] Hint Rewrite @rw_tolistm_type1 @rw_tolistm_type2 @rw_tolistm_type3 @rw_tolistm_type4: sysf_rw.

(** *** <<toklist>> with <<ktyp>> *)
(******************************************************************************)
Section rw_toklist_ktyp_type.

  Context
    (A: Type).

  Lemma rw_toklist_ktyp_type1: forall c, toklist (A:= A) typ ktyp (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_ktyp_type2: forall (a: A), toklist typ ktyp (ty_v a) = [ a ].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_ktyp_type3: forall (t1 t2: typ A), toklist typ ktyp (ty_ar t1 t2) = toklist typ ktyp t1 ++ toklist typ ktyp t2.
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_ktyp_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklist_ktyp_type4: forall (body: typ A), toklist typ ktyp (ty_univ body) = (toklist typ ktyp body).
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_ktyp_type4.
         compose near (toklistd typ ktyp body) on left. rewrite (fun_map_map (F:= list)).
         fequal. now ext [w a]. Qed.

End rw_toklist_ktyp_type.

#[export] Hint Rewrite @rw_toklist_ktyp_type1 @rw_toklist_ktyp_type2 @rw_toklist_ktyp_type3 @rw_toklist_ktyp_type4: sysf_rw.

(** *** <<toklist>> with <<ktrm>> *)
(******************************************************************************)
Section rw_toklist_ktrm_type.

  Context
    (A: Type).

  Lemma rw_toklist_ktrm_type1: forall c, toklist (A:= A) typ ktrm (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_ktrm_type2: forall (a: A), toklist typ ktrm (ty_v a) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_ktrm_type3: forall (t1 t2: typ A), toklist typ ktrm (ty_ar t1 t2) = toklist typ ktrm t1 ++ toklist typ ktrm t2.
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_ktrm_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklist_ktrm_type4: forall (body: typ A), toklist typ ktrm (ty_univ body) = (toklist typ ktrm body).
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_ktrm_type4.
         compose near (toklistd typ ktrm body) on left. rewrite (fun_map_map (F:= list)).
         fequal. now ext [w a]. Qed.

End rw_toklist_ktrm_type.

#[export] Hint Rewrite @rw_toklist_ktrm_type1 @rw_toklist_ktrm_type2 @rw_toklist_ktrm_type3 @rw_toklist_ktrm_type4: sysf_rw.

Corollary rw_toklist_ktrm_type: forall A (τ: typ A), toklist typ ktrm τ = nil.
Proof.
  intros. induction τ; autorewrite with sysf_rw.
  - trivial.
  - trivial.
  - now rewrite IHτ1, IHτ2.
  - now rewrite IHτ.
Qed.

(** *** Variable occurrence with context *)
(******************************************************************************)
Section rw_tosetmd_type.

  Context
    (A: Type)
    (k: K2).

  Implicit Types
           (w: list K) (a: A).

  Lemma rw_tosetmd_type1: forall c w a, (w, (k, a)) ∈md (ty_c c) <-> False.
  Proof.
    intros. unfold tosetmd, compose. autorewrite with sysf_rw. easy.
  Qed.

  Lemma rw_tosetmd_type2: forall w a a', (w, (k, a)) ∈md (ty_v a') <-> w = nil /\ k = ktyp /\ a = a'.
  Proof.
    intros. unfold tosetmd, compose.
    autorewrite with sysf_rw.
    rewrite tosubset_list_one.
    split.
    - now inversion 1.
    - firstorder. now subst.
  Qed.

  Lemma rw_tosetmd_type3: forall w a (t1 t2: typ A), (w, (k, a)) ∈md ty_ar t1 t2 <-> ((w, (k, a)) ∈md t1 \/ (w, (k, a)) ∈md t2).
  Proof.
    intros. unfold tosetmd, compose.
    now autorewrite with sysf_rw tea_list tea_set.
  Qed.

  Lemma rw_tosetmd_type4: forall w a (body: typ A), (w, (k, a)) ∈md (ty_univ body) <-> exists w', (w', (k, a)) ∈md body /\ w = (cons ktyp w').
  Proof.
    intros. unfold tosetmd, compose. autorewrite with sysf_rw.
    rewrite (tosubset_map_iff).
    splits.
    - intros [[w'' [j a']] [rest1 rest2]]. cbn in *. inverts rest2. eauto.
    - intros [w' rest]. exists (w', (k, a)). now inverts rest.
  Qed.

End rw_tosetmd_type.

#[export] Hint Rewrite @rw_tosetmd_type1 @rw_tosetmd_type2 @rw_tosetmd_type3 @rw_tosetmd_type4: sysf_rw.

Corollary rw_tosetmd_type_ktrm: forall w A a (τ: typ A), (w, (ktrm, a)) ∈md τ <-> False.
Proof.
  intros. generalize dependent w.
  induction τ; intro w; autorewrite with sysf_rw; try easy.
  - rewrite IHτ1, IHτ2. tauto.
  - split; try tauto.
    intros [w' [rest1 rest2]]. now rewrite IHτ in rest1.
Qed.

(** *** Variable occurrence without context *)
(******************************************************************************)
Section rw_tosetm_type.

  Context
    (A: Type)
    (k: K2).

  Implicit Types (a: A).

  Lemma rw_tosetm_type1: forall c a, (k, a) ∈m (ty_c c) <-> False.
  Proof.
    intros.
    rewrite inmd_iff_in.
    firstorder eauto.
  Qed.

  Lemma rw_tosetm_type2: forall a a', (k, a) ∈m (ty_v a') <-> k = ktyp /\ a = a'.
  Proof.
    intros.
    rewrite inmd_iff_in.
    setoid_rewrite rw_tosetmd_type2.
    firstorder eauto.
  Qed.

  Lemma rw_tosetm_type3: forall a (t1 t2: typ A), (k, a) ∈m ty_ar t1 t2 <-> (k, a) ∈m t1 \/ (k, a) ∈m t2.
  Proof.
    intros.
    repeat rewrite inmd_iff_in.
    setoid_rewrite rw_tosetmd_type3.
    firstorder eauto.
  Qed.

  Lemma rw_tosetm_type4: forall a (body: typ A), (k, a) ∈m (ty_univ body) <-> (k, a) ∈m body.
  Proof.
    intros.
    repeat rewrite inmd_iff_in.
    setoid_rewrite rw_tosetmd_type4.
    firstorder eauto.
  Qed.

End rw_tosetm_type.

#[export] Hint Rewrite @rw_tosetm_type1 @rw_tosetm_type2 @rw_tosetm_type3 @rw_tosetm_type4: sysf_rw.

(** ** <<free>> and <<FV>> *)
(******************************************************************************)

(** *** <<free>> with <<ktyp>> *)
(******************************************************************************)
Section rw_free_ktyp_type.

  Lemma rw_free_ktyp_type11: forall (x: atom), free typ ktyp (ty_v (Fr x)) = [x].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_ktyp_type12: forall (n: nat), free typ ktyp (ty_v (Bd n)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_ktyp_type2: forall (c: base_typ), free typ ktyp (ty_c c) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_ktyp_type3: forall t1 t2, free typ ktyp (ty_ar t1 t2) = free typ ktyp t1 ++ free typ ktyp t2.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_ktyp_type4: forall t, free typ ktyp (ty_univ t) = free typ ktyp t.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_free_ktyp_type.

#[export] Hint Rewrite rw_free_ktyp_type11 rw_free_ktyp_type12 rw_free_ktyp_type2 rw_free_ktyp_type3 rw_free_ktyp_type4: sysf_rw.

(** *** <<FV>> with <<ktyp>> *)
(******************************************************************************)
Section rw_fv_ktyp_type.

  #[local] Open Scope set_scope.

  Lemma rw_fv_ktyp_type11: forall (x: atom), FV typ ktyp (ty_v (Fr x)) [=] {{ x }}.
  Proof.
    unfold FV. intros. autorewrite with sysf_rw tea_rw_atoms. fsetdec.
  Qed.

  Lemma rw_fv_ktyp_type12: forall (n: nat), FV typ ktyp (ty_v (Bd n)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_fv_ktyp_type2: forall (c: base_typ), FV typ ktyp (ty_c c) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_fv_ktyp_type3: forall t1 t2, FV typ ktyp (ty_ar t1 t2) [=] FV typ ktyp t1 ∪ FV typ ktyp t2.
  Proof.
    intros. unfold FV. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_fv_ktyp_type4: forall t, FV typ ktyp (ty_univ t) [=] FV typ ktyp t.
  Proof.
    intros. unfold FV. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_fv_ktyp_type.

#[export] Hint Rewrite rw_fv_ktyp_type11 rw_fv_ktyp_type12 rw_fv_ktyp_type2 rw_fv_ktyp_type3 rw_fv_ktyp_type4: sysf_rw.

(** *** <<free>> with <<ktrm>> *)
(******************************************************************************)
Section rw_free_ktrm_type.

  Lemma rw_free_ktrm_type11: forall (x: atom), free typ ktrm (ty_v (Fr x)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_ktrm_type12: forall (n: nat), free typ ktrm (ty_v (Bd n)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_ktrm_type2: forall (c: base_typ), free typ ktrm (ty_c c) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_ktrm_type3: forall t1 t2, free typ ktrm (ty_ar t1 t2) = free typ ktrm t1 ++ free typ ktrm t2.
  Proof. intros. unfold free. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_free_ktrm_type4: forall t, free typ ktrm (ty_univ t) = free typ ktrm t.
  Proof. intros. unfold free. now autorewrite with sysf_rw tea_list. Qed.

End rw_free_ktrm_type.

#[export] Hint Rewrite rw_free_ktrm_type11 rw_free_ktrm_type12 rw_free_ktrm_type2 rw_free_ktrm_type3 rw_free_ktrm_type4: sysf_rw.

Corollary rw_free_ktrm_type: forall (τ: typ LN), free typ ktrm τ = [].
Proof.
  intros. induction τ; autorewrite with sysf_rw.
  - trivial.
  - trivial.
  - now rewrite IHτ1, IHτ2.
  - now rewrite IHτ.
Qed.

(** *** <<FV>> with <<ktrm>> *)
(******************************************************************************)
Section rw_fv_ktrm_type.

  #[local] Open Scope set_scope.

  Lemma rw_fv_ktrm_type11: forall (x: atom), FV typ ktrm (ty_v (Fr x)) [=] ∅.
  Proof.
    unfold FV. intros. rewrite rw_free_ktrm_type11. autorewrite with tea_rw_atoms. fsetdec. Qed.

  Lemma rw_fv_ktrm_type12: forall (n: nat), FV typ ktrm (ty_v (Bd n)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_fv_ktrm_type2: forall (c: base_typ), FV typ ktrm (ty_c c) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_fv_ktrm_type3: forall t1 t2, FV typ ktrm (ty_ar t1 t2) [=] FV typ ktrm t1 ∪ FV typ ktrm t2.
  Proof.
    intros. unfold FV. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_fv_ktrm_type4: forall t, FV typ ktrm (ty_univ t) [=] FV typ ktrm t.
  Proof.
    intros. unfold FV. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_fv_ktrm_type.

#[export] Hint Rewrite rw_fv_ktrm_type11 rw_fv_ktrm_type12 rw_fv_ktrm_type2 rw_fv_ktrm_type3 rw_fv_ktrm_type4: sysf_rw.

Corollary rw_fv_ktrm_type: forall (τ: typ LN), (FV typ ktrm τ [=] ∅)%set.
Proof.
  intros. induction τ.
  - autorewrite with sysf_rw. fsetdec.
  - cbn. fsetdec.
  - autorewrite with sysf_rw. fsetdec.
  - autorewrite with sysf_rw. fsetdec.
Qed.

#[export] Hint Rewrite rw_fv_ktrm_type: sysf_rw.

(** ** Locally nameless operations *)
(******************************************************************************)

(** *** <<open>> *)
(******************************************************************************)
Section rw_open_type.

  Context
    (u: typ LN).

  Lemma rw_open_type1: forall c, open typ ktyp u (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_open_type2: forall (l: LN), open typ ktyp u (ty_v l) = open_loc ktyp u (nil, l).
  Proof. reflexivity. Qed.

  Lemma rw_open_type3: forall (t1 t2: typ LN), open typ ktyp u (ty_ar t1 t2) = ty_ar (open typ ktyp u t1) (open typ ktyp u t2).
  Proof. reflexivity. Qed.

End rw_open_type.

#[export] Hint Rewrite @rw_open_type1 @rw_open_type2 @rw_open_type3: sysf_rw.

(** *** <<subst>> with <<ktyp>> *)
(******************************************************************************)
Section rw_subst_ktyp_type.

  Context
    (x: atom)
    (u: typ LN).

  Lemma rw_subst_ktyp_type1: forall c, subst typ ktyp x u (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktyp_type2: forall (l: LN), subst typ ktyp x u (ty_v l) = subst_loc ktyp x u l.
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktyp_type3: forall (t1 t2: typ LN), subst typ ktyp x u (ty_ar t1 t2) = ty_ar (subst typ ktyp x u t1) (subst typ ktyp x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktyp_type4: forall (t: typ LN), subst typ ktyp x u (ty_univ t) = ty_univ (subst typ ktyp x u t).
  Proof.
    intros.
    unfold subst.
    unfold kbind.
    unfold mbind.
    unfold mbindd.
    simplify.
    simplify.
    simplify.
    simplify.
    reflexivity.
  Qed.

End rw_subst_ktyp_type.

#[export] Hint Rewrite @rw_subst_ktyp_type1 @rw_subst_ktyp_type2 @rw_subst_ktyp_type3 @rw_subst_ktyp_type4: sysf_rw.

(** *** <<subst>> with <<ktrm>> *)
(******************************************************************************)
Section rw_subst_ktrm_type.

  Context
    (x: atom)
    (u: term LN).

  Lemma rw_subst_ktrm_type1: forall c, subst typ ktrm x u (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktrm_type2: forall (l: LN), subst typ ktrm x u (ty_v l) = ty_v l.
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktrm_type3: forall (t1 t2: typ LN), subst typ ktrm x u (ty_ar t1 t2) = ty_ar (subst typ ktrm x u t1) (subst typ ktrm x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktrm_type4: forall (t: typ LN), subst typ ktrm x u (ty_univ t) = ty_univ (subst typ ktrm x u t).
  Proof.
    intros.
    unfold subst.
    unfold kbind.
    unfold mbind.
    unfold mbindd.
    simplify.
    simplify.
    simplify.
    simplify.
    reflexivity.
  Qed.

End rw_subst_ktrm_type.

#[export] Hint Rewrite @rw_subst_ktrm_type1 @rw_subst_ktrm_type2 @rw_subst_ktrm_type3 @rw_subst_ktrm_type4: sysf_rw.

Corollary rw_subst_ktrm_type: forall (τ: typ LN) (x: atom) (u: term LN), subst typ ktrm x u τ = τ.
Proof.
  intros; induction τ; try easy.
  - cbn. now rewrite IHτ1, IHτ2.
  - autorewrite with sysf_rw.
    now rewrite IHτ.
Qed.

#[export] Hint Rewrite @rw_subst_ktrm_type: sysf_rw.

(** *** <<locally_closed>> with <<ktyp>> *)
(******************************************************************************)
Section rw_lc_ktyp_type.

  Lemma rw_lc_ktyp_type1: forall c, locally_closed typ ktyp (ty_c c).
  Proof.
    intros. unfold locally_closed, locally_closed_gap; introv hyp.
    now rewrite rw_tosetmd_type1 in hyp.
  Qed.

  Lemma rw_lc_ktyp_type2: forall (l: LN), locally_closed typ ktyp (ty_v l) <-> exists x, l = Fr x.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_type2. split.
    - introv hyp. destruct l.
      + eauto.
      + enough (n < 0). lia. now apply (hyp [] (Bd n)).
    - intros [x heq]. subst. introv hyp. inversion hyp.
      inverts H0. cbn; trivial.
  Qed.

  Lemma rw_lc_ktyp_type3: forall (t1 t2: typ LN), locally_closed typ ktyp (ty_ar t1 t2) <-> (locally_closed typ ktyp t1 /\ locally_closed typ ktyp t2).
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_type3. firstorder.
  Qed.

  #[local] Open Scope nat_scope.

  Lemma rw_lc_ktyp_type4: forall (t: typ LN), locally_closed typ ktyp (ty_univ t) <-> locally_closed_gap typ ktyp 1 t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_type4. split.
    - intros hyp w l Hin.
      specialize (hyp (ktyp:: w) l). cbn in *.
      assert (rw: S (countk (@ktyp: K) w + 0) = (countk ktyp w + 1)) by lia.
      rewrite <- rw. apply hyp. eauto.
    - intros hyp w l [w' [H1 H2]]. subst.
      specialize (hyp w' l H1). cbn in *. destruct l.
      + easy.
      + lia.
  Qed.

End rw_lc_ktyp_type.

#[export] Hint Rewrite @rw_lc_ktyp_type1 @rw_lc_ktyp_type2 @rw_lc_ktyp_type3 @rw_lc_ktyp_type4: sysf_rw.

(** *** <<locally_closed>> with <<ktrm>> *)
(******************************************************************************)
Section rw_lc_ktrm_type.

  Lemma rw_lc_ktrm_type: forall τ, locally_closed typ ktrm τ <-> True.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_type_ktrm. intuition.
  Qed.

  Lemma lc_ktrm_type: forall τ, locally_closed typ ktrm τ.
  Proof.
    intros. now rewrite rw_lc_ktrm_type.
  Qed.

End rw_lc_ktrm_type.

#[export] Hint Rewrite @rw_lc_ktrm_type: sysf_rw.

(** *** <<scoped>> with <<ktrm>> *)
(******************************************************************************)
Section rw_scoped_ktrm_type.

  Lemma rw_scoped_ktrm_type: forall τ (vars: Atosetm.t), scoped typ ktrm τ vars.
  Proof.
    intros. unfold scoped. autorewrite with sysf_rw. fsetdec.
  Qed.

End rw_scoped_ktrm_type.

(** ** <<ok_type>> *)
(******************************************************************************)
Lemma ok_type_ar: forall Δ τ1 τ2,
    ok_type Δ (ty_ar τ1 τ2) <->
    ok_type Δ τ1 /\ ok_type Δ τ2.
Proof.
  intros. unfold ok_type.
  unfold scoped.
  autorewrite with sysf_rw.
  intuition fsetdec.
Qed.

Lemma ok_type_univ: forall Δ τ,
    ok_type Δ (ty_univ τ) <->
    scoped typ ktyp τ (AssocList.domset Δ) /\
    locally_closed_gap typ ktyp 1 τ.
Proof.
  intros. unfold ok_type.
  unfold scoped.
  now autorewrite with sysf_rw.
Qed.

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

(** *** <<mbindd>> *)
(******************************************************************************)
Section rw_mbindd_term.

  Context
    (A B: Type)
    (f: forall k, list K * A -> SystemF k B).

  Lemma rw_mbindd_term1: forall (a: A), mbindd term f (tm_var a) = f ktrm (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_term2: forall (τ: typ A) (t: term A), mbindd term f (tm_abs τ t) = tm_abs (mbindd typ f τ) (mbindd term (fun k => f k ∘ incr [ktrm]) t).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_term3: forall (t1 t2: term A), mbindd term f (tm_app t1 t2) = tm_app (mbindd term f t1) (mbindd term f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_term4: forall (t: term A), mbindd term f (tm_tab t) = tm_tab (mbindd term (fun k => f k ∘ incr [ktyp]) t).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_term5: forall (t: term A) (τ: typ A), mbindd term f (tm_tap t τ) = tm_tap (mbindd term f t) (mbindd typ f τ).
  Proof. reflexivity. Qed.

End rw_mbindd_term.

#[export] Hint Rewrite @rw_mbindd_term1 @rw_mbindd_term2 @rw_mbindd_term3 @rw_mbindd_term4 @rw_mbindd_term5: sysf_rw.

(** *** <<mbind>> *)
(******************************************************************************)
Section rw_mbind_term.

  Context
    (A B: Type)
    (f: forall k, A -> SystemF k B).

  Lemma rw_mbind_term1: forall (a: A), mbind term f (tm_var a) = f ktrm a.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_term2: forall (τ: typ A) (t: term A), mbind term f (tm_abs τ t) = tm_abs (mbind typ f τ) (mbind term f t).
  Proof. intros. unfold mbind. autorewrite with sysf_rw. repeat fequal. now ext k [w a]. Qed.

  Lemma rw_mbind_term3: forall (t1 t2: term A), mbind term f (tm_app t1 t2) = tm_app (mbind term f t1) (mbind term f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbind_term4: forall (t: term A), mbind term f (tm_tab t) = tm_tab (mbind term f t).
  Proof. intros. unfold mbind. autorewrite with sysf_rw. repeat fequal. now ext k [w a]. Qed.

  Lemma rw_mbind_term5: forall (t: term A) (τ: typ A), mbind term f (tm_tap t τ) = tm_tap (mbind term f t) (mbind typ f τ).
  Proof. reflexivity. Qed.

End rw_mbind_term.

#[export] Hint Rewrite @rw_mbind_term1 @rw_mbind_term2 @rw_mbind_term3 @rw_mbind_term4 @rw_mbind_term5: sysf_rw.

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

(** ** List and occurrence operations *)
(******************************************************************************)

(** *** <<tolistmd>> *)
(******************************************************************************)
Section rw_tolistmd_type.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_tolistmd_term1: forall (a: A), tolistmd term (tm_var a) = [ (nil, (ktrm, a)) ].
  Proof. reflexivity. Qed.

  Lemma rw_tolistmd_term2: forall τ t, tolistmd term (tm_abs τ t) = tolistmd typ τ ++ map (F:= list) (incr [ktrm]) (tolistmd term t).
  Proof.
    intros. unfold tolistmd, tolistmd_gen. rewrite rw_mmapdt_term2. fequal.
    compose near t on right. unfold mmapdt.
    rewrite (dtp_mbinddt_morphism
               (list (@K I2)) term SystemF (const (list (list K2 * (K * A))))
               (const (list _)) (ϕ:= (fun _ => map (F:= list) (incr [ktrm])))
               (fun (k: @K I2) => map (F:= const (list (list K2 * (K * A))))
                                  (mret SystemF k) ∘ (fun '(w, a) => [(w, (k, a))]))).
    fequal. now ext k [w a].
  Qed.

  Lemma rw_tolistmd_term3: forall t1 t2, tolistmd term (tm_app t1 t2) = tolistmd term t1 ++ tolistmd term t2.
  Proof. reflexivity. Qed.

  Lemma rw_tolistmd_term4: forall t, tolistmd term (tm_tab t) = map (F:= list) (incr [ktyp]) (tolistmd term t).
  Proof.
    intros. unfold tolistmd, tolistmd_gen.
    rewrite rw_mmapdt_term4. cbn.
    compose near t on right. unfold mmapdt.
    rewrite (dtp_mbinddt_morphism
               (list (@K I2)) term SystemF (const (list _)) (const (list _)) (ϕ:= (fun _ => map (F:= list) (incr [ktyp])))
               (fun (k: @K I2) => map (F:= const (list (list K2 * (K2 * A)))) (mret SystemF k) ∘ (fun '(w, a) => [(w, (k, a))]))).
    fequal. now ext k [w a].
  Qed.

  Lemma rw_tolistmd_term5: forall t τ, tolistmd term (tm_tap t τ) = tolistmd term t ++ tolistmd typ τ.
  Proof. reflexivity. Qed.

End rw_tolistmd_type.

#[export] Hint Rewrite @rw_tolistmd_term1 @rw_tolistmd_term2 @rw_tolistmd_term3 @rw_tolistmd_term4 @rw_tolistmd_term5: sysf_rw.

(** *** <<toklistd>> with <<ktyp>> *)
(******************************************************************************)
Section rw_toklistd_ktyp_type.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_toklistd_ktyp_term1: forall (a: A), toklistd term ktyp (tm_var a) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_ktyp_term2: forall τ t, toklistd term ktyp (tm_abs τ t) = toklistd typ ktyp τ ++ map (F:= list) (incr [ktrm]) (toklistd term ktyp t).
  Proof. intros. unfold toklistd, compose. rewrite rw_tolistmd_term2. rewrite filterk_app. now rewrite filterk_incr. Qed.

  Lemma rw_toklistd_ktyp_term3: forall t1 t2, toklistd term ktyp (tm_app t1 t2) = toklistd term ktyp t1 ++ toklistd term ktyp t2.
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_app. Qed.

  Lemma rw_toklistd_ktyp_term4: forall t, toklistd term ktyp (tm_tab t) = map (F:= list) (incr [ktyp]) (toklistd term ktyp t).
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_incr. Qed.

  Lemma rw_toklistd_ktyp_term5: forall t τ, toklistd term ktyp (tm_tap t τ) = toklistd term ktyp t ++ toklistd typ ktyp τ.
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_app. Qed.

End rw_toklistd_ktyp_type.

#[export] Hint Rewrite @rw_toklistd_ktyp_term1 @rw_toklistd_ktyp_term2 @rw_toklistd_ktyp_term3 @rw_toklistd_ktyp_term4 @rw_toklistd_ktyp_term5: sysf_rw.

(** *** <<toklistd>> with <<ktrm>> *)
(******************************************************************************)
Section rw_toklistd_ktrm_term.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_toklistd_ktrm_term1: forall (a: A), toklistd term ktrm (tm_var a) = [ (nil, a) ].
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_ktrm_term2: forall τ t, toklistd term ktrm (tm_abs τ t) = toklistd typ ktrm τ ++ map (F:= list) (incr [ktrm]) (toklistd term ktrm t).
  Proof. intros. unfold toklistd, compose. rewrite rw_tolistmd_term2. rewrite filterk_app. now rewrite filterk_incr. Qed.

  Lemma rw_toklistd_ktrm_term3: forall t1 t2, toklistd term ktrm (tm_app t1 t2) = toklistd term ktrm t1 ++ toklistd term ktrm t2.
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_app. Qed.

  Lemma rw_toklistd_ktrm_term4: forall t, toklistd term ktrm (tm_tab t) = map (F:= list) (incr [ktyp]) (toklistd term ktrm t).
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_incr. Qed.

  Lemma rw_toklistd_ktrm_term5: forall t τ, toklistd term ktrm (tm_tap t τ) = toklistd term ktrm t ++ toklistd typ ktrm τ.
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_app. Qed.

End rw_toklistd_ktrm_term.

#[export] Hint Rewrite @rw_toklistd_ktrm_term1 @rw_toklistd_ktrm_term2 @rw_toklistd_ktrm_term3 @rw_toklistd_ktrm_term4 @rw_toklistd_ktrm_term5: sysf_rw.

(** *** <<tolistm>> *)
(******************************************************************************)
Section rw_tolistm_term.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_tolistm_term1: forall (a: A), tolistm term (tm_var a) = [ (ktrm, a) ].
  Proof. reflexivity. Qed.

  Lemma rw_tolistm_term2: forall τ t, tolistm term (tm_abs τ t) = tolistm typ τ ++ tolistm term t.
  Proof.
    intros.
    unfold tolistm, tolistmd.
    unfold tolistmd_gen.
    unfold compose.
    rewrite mmapdt_to_mbinddt.
    rewrite mmapdt_to_mbinddt.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    change (?l1 ● ?l2) with (l1 ++ l2).
    autorewrite with tea_list.
    fequal.

    (*
    autorewrite with sysf_rw tea_list.
    compose near (tolistmd term t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.
     *)
  Admitted.

  Lemma rw_tolistm_term3: forall t1 t2, tolistm term (tm_app t1 t2) = tolistm term t1 ++ tolistm term t2.
  Proof. intros. unfold tolistm, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_tolistm_term4: forall t, tolistm term (tm_tab t) = tolistm term t.
  Proof.
    intros. unfold tolistm, compose. autorewrite with sysf_rw.
    compose near (tolistmd term t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_tolistm_term5: forall t τ, tolistm term (tm_tap t τ) = tolistm term t ++ tolistm typ τ.
  Proof. intros. unfold tolistm, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_tolistm_term.

#[export] Hint Rewrite @rw_tolistm_term1 @rw_tolistm_term2 @rw_tolistm_term3 @rw_tolistm_term4 @rw_tolistm_term5: sysf_rw.

(** *** <<toklist>> with <<ktyp>> *)
(******************************************************************************)
Section rw_toklist_ktyp_term.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_toklist_ktyp_term1: forall (a: A), toklist term ktyp (tm_var a) = [ ].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_ktyp_term2: forall τ t, toklist term ktyp (tm_abs τ t) = toklist typ ktyp τ ++ toklist term ktyp t.
  Proof.
    intros. unfold toklist, compose.
    autorewrite with sysf_rw tea_list.
    compose near (toklistd term ktyp t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_toklist_ktyp_term3: forall t1 t2, toklist term ktyp (tm_app t1 t2) = toklist term ktyp t1 ++ toklist term ktyp t2.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_toklist_ktyp_term4: forall t, toklist term ktyp (tm_tab t) = toklist term ktyp t.
  Proof.
    intros. unfold toklist, compose. autorewrite with sysf_rw.
    compose near (toklistd term ktyp t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_toklist_ktyp_term5: forall t τ, toklist term ktyp (tm_tap t τ) = toklist term ktyp t ++ toklist typ ktyp τ.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_toklist_ktyp_term.

#[export] Hint Rewrite @rw_toklist_ktyp_term1 @rw_toklist_ktyp_term2 @rw_toklist_ktyp_term3 @rw_toklist_ktyp_term4 @rw_toklist_ktyp_term5: sysf_rw.

(** *** <<toklist>> with <<ktrm>> *)
(******************************************************************************)
Section rw_toklist_ktrm_term.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_toklist_ktrm_term1: forall (a: A), toklist term ktrm (tm_var a) = [ a ].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_ktrm_term2: forall τ t, toklist term ktrm (tm_abs τ t) = toklist typ ktrm τ ++ toklist term ktrm t.
  Proof.
    intros. unfold toklist, compose. autorewrite with sysf_rw tea_list.
    compose near (toklistd term ktrm t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_toklist_ktrm_term3: forall t1 t2, toklist term ktrm (tm_app t1 t2) = toklist term ktrm t1 ++ toklist term ktrm t2.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_toklist_ktrm_term4: forall t, toklist term ktrm (tm_tab t) = toklist term ktrm t.
  Proof.
    intros. unfold toklist, compose. autorewrite with sysf_rw.
    compose near (toklistd term ktrm t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_toklist_ktrm_term5: forall t τ, toklist term ktrm (tm_tap t τ) = toklist term ktrm t ++ toklist typ ktrm τ.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_toklist_ktrm_term.

#[export] Hint Rewrite @rw_toklist_ktrm_term1 @rw_toklist_ktrm_term2 @rw_toklist_ktrm_term3 @rw_toklist_ktrm_term4 @rw_toklist_ktrm_term5: sysf_rw.

(** *** Variable occurrence with context *)
(******************************************************************************)
Section rw_tosetmd_type.

  Context
    (A: Type)
    (k: K2).

  Implicit Types (w: list K) (a: A).

  Lemma rw_tosetmd_term1: forall w a a', (w, (k, a)) ∈md (tm_var a') <->  w = nil /\ k = ktrm /\ a = a'.
    intros. unfold tosetmd, compose. autorewrite with sysf_rw.
    rewrite tosubset_list_one.
    split.
    - now inversion 1.
    - intros [? [? ?]]; now subst.
  Qed.

  Lemma rw_tosetmd_term2: forall τ t w a,
      (w, (k, a)) ∈md (tm_abs τ t) <->
      (w, (k, a)) ∈md τ \/ exists w', (w', (k, a)) ∈md t /\ w = ktrm:: w'.
  Proof.
    intros. unfold tosetmd, compose. autorewrite with sysf_rw tea_list.
    rewrite (tosubset_map_iff). split.
    - intros [hyp | hyp].
      + now left.
      + right. destruct hyp as [[w' [j a'']] [hyp1 hyp2]].
        exists w'. inverts hyp2. easy.
    - intros [hyp | hyp].
      + now left.
      + right. destruct hyp as [w' [hyp1 hyp2]]. subst.
        exists (w', (k, a)). auto.
  Qed.

  Lemma rw_tosetmd_term3: forall w a (t1 t2: term A), (w, (k, a)) ∈md tm_app t1 t2 <-> ((w, (k, a)) ∈md t1 \/ (w, (k, a)) ∈md t2).
  Proof.
    intros. unfold tosetmd, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_tosetmd_term4: forall w a (t: term A), (w, (k, a)) ∈md (tm_tab t) <-> exists w', (w', (k, a)) ∈md t /\ w = ktyp:: w'.
  Proof.
    intros. unfold tosetmd, compose. autorewrite with sysf_rw.
    rewrite (tosubset_map_iff). splits.
    - intros [[w'' [j a']] [rest1 rest2]]. cbn in *. inverts rest2. eauto.
    - intros [w' rest]. exists (w', (k, a)). now inverts rest.
  Qed.

  Lemma rw_tosetmd_term5: forall w a (t: term A) (τ: typ A), (w, (k, a)) ∈md (tm_tap t τ) <-> (w, (k, a)) ∈md t \/ (w, (k, a)) ∈md τ.
  Proof.
    intros. unfold tosetmd, compose. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_tosetmd_type.

#[export] Hint Rewrite @rw_tosetmd_term1 @rw_tosetmd_term2 @rw_tosetmd_term3 @rw_tosetmd_term4 @rw_tosetmd_term5: sysf_rw.

(** *** Variable occurrence without context *)
(******************************************************************************)
Section rw_tosetm_type.

  Context
    (A: Type)
    (k: K2).

  Implicit Types (a: A).

  Lemma rw_tosetm_term1: forall a a', (k, a) ∈m tm_var a' <-> k = ktrm /\ a = a'.
    intros. unfold tosetm, compose. autorewrite with sysf_rw.
    rewrite tosubset_list_one.
    split. inversion 1; easy. inversion 1; now subst.
  Qed.

  Lemma rw_tosetm_term2: forall τ t a a',
      (k, a) ∈m (tm_abs τ t) <-> (k, a) ∈m τ \/ (k, a) ∈m t.
  Proof.
    intros. unfold tosetm, compose. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_tosetm_term3: forall a (t1 t2: term A), (k, a) ∈m tm_app t1 t2 <-> (k, a) ∈m t1 \/ (k, a) ∈m t2.
  Proof.
    intros. unfold tosetm, compose. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_tosetm_term4: forall a (t: term A), (k, a) ∈m tm_tab t <-> (k, a) ∈m t.
  Proof.
    intros. unfold tosetm, compose. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_tosetm_term5: forall a (t: term A) (τ: typ A), (k, a) ∈m tm_tap t τ <-> (k, a) ∈m t \/ (k, a) ∈m τ.
  Proof.
    intros. unfold tosetm, compose. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_tosetm_type.

#[export] Hint Rewrite @rw_tosetm_term1 @rw_tosetm_term2 @rw_tosetm_term3 @rw_tosetm_term4 @rw_tosetm_term5: sysf_rw.

(** ** <<free>> and <<FV>> *)
(******************************************************************************)

(** *** <<free>> with <<ktyp>> *)
(******************************************************************************)
Section rw_free_ktyp_term.

  Lemma rw_free_ktyp_term1: forall (l: LN), free term ktyp (tm_var l) = [].
  Proof. reflexivity. Qed.

  Lemma rw_free_ktyp_term2: forall τ t, free term ktyp (tm_abs τ t) = free typ ktyp τ ++ free term ktyp t.
  Proof.
    introv. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_ktyp_term3: forall t1 t2, free term ktyp (tm_app t1 t2) = free term ktyp t1 ++ free term ktyp t2.
  Proof.
    introv. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_ktyp_term4: forall t, free term ktyp (tm_tab t) = free term ktyp t.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_free_ktyp_term5: forall t τ, free term ktyp (tm_tap t τ) = free term ktyp t ++ free typ ktyp τ.
  Proof.
    dup. { intros. unfold free. now autorewrite with sysf_rw tea_list. }
    intros.
    unfold free.
    unfold toklist.
    unfold compose.
    unfold toklistd.
    unfold tolistmd.
    unfold tolistmd_gen.
    rewrite mmapdt_to_mbinddt.
    unfold compose.
  Admitted.

End rw_free_ktyp_term.

#[export] Hint Rewrite rw_free_ktyp_term1 rw_free_ktyp_term2 rw_free_ktyp_term3 rw_free_ktyp_term4 rw_free_ktyp_term5: sysf_rw.

(** *** <<FV>> with <<ktyp>> *)
(******************************************************************************)
Section rw_fv_ktyp_term.

  #[local] Open Scope set_scope.

  Lemma rw_fv_ktyp_term1: forall (l: LN), FV term ktyp (tm_var l) [=] ∅.
  Proof. reflexivity. Qed.

  Lemma rw_fv_ktyp_term2: forall τ t, FV term ktyp (tm_abs τ t) [=] FV typ ktyp τ ∪ FV term ktyp t.
  Proof.
    introv. unfold FV. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

  Lemma rw_fv_ktyp_term3: forall t1 t2, FV term ktyp (tm_app t1 t2) [=] FV term ktyp t1 ∪ FV term ktyp t2.
  Proof.
    introv. unfold FV. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

  Lemma rw_fv_ktyp_term4: forall t, FV term ktyp (tm_tab t) [=] FV term ktyp t.
  Proof.
    intros. unfold FV. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_fv_ktyp_term5: forall t τ, FV term ktyp (tm_tap t τ) [=] FV term ktyp t ∪ FV typ ktyp τ.
  Proof.
    intros. unfold FV. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

End rw_fv_ktyp_term.

#[export] Hint Rewrite rw_fv_ktyp_term1 rw_fv_ktyp_term2 rw_fv_ktyp_term3 rw_fv_ktyp_term4 rw_fv_ktyp_term5: sysf_rw.

(** *** <<free>> with <<ktrm>> *)
(******************************************************************************)
Section rw_free_ktrm_term.

  Lemma rw_free_ktrm_term11: forall (x: atom), free term ktrm (tm_var (Fr x)) = [ x ].
  Proof. reflexivity. Qed.

  Lemma rw_free_ktrm_term12: forall (n: nat), free term ktrm (tm_var (Bd n)) = [ ].
  Proof. reflexivity. Qed.

  Lemma rw_free_ktrm_term2: forall τ t, free term ktrm (tm_abs τ t) = free typ ktrm τ ++ free term ktrm t.
  Proof.
    introv. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_ktrm_term3: forall t1 t2, free term ktrm (tm_app t1 t2) = free term ktrm t1 ++ free term ktrm t2.
  Proof.
    introv. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_ktrm_term4: forall t, free term ktrm (tm_tab t) = free term ktrm t.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_free_ktrm_term5: forall t τ, free term ktrm (tm_tap t τ) = free term ktrm t ++ free typ ktrm τ.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_free_ktrm_term.

#[export] Hint Rewrite rw_free_ktrm_term11 rw_free_ktrm_term12 rw_free_ktrm_term2 rw_free_ktrm_term3 rw_free_ktrm_term4 rw_free_ktrm_term5: sysf_rw.

(** *** <<FV>> with <<ktrm>> *)
(******************************************************************************)
Section rw_fv_ktrm_term.

  #[local] Open Scope set_scope.

  Lemma rw_fv_ktrm_term11: forall (x: atom), FV term ktrm (tm_var (Fr x)) [=] {{ x }}.
  Proof.
    introv. unfold FV. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_fv_ktrm_term12: forall (n: nat), FV term ktrm (tm_var (Bd n)) [=] ∅.
  Proof. reflexivity. Qed.

  Lemma rw_fv_ktrm_term2: forall τ t, FV term ktrm (tm_abs τ t) [=] FV typ ktrm τ ∪ FV term ktrm t.
  Proof.
    introv. unfold FV. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

  Lemma rw_fv_ktrm_term3: forall t1 t2, FV term ktrm (tm_app t1 t2) [=] FV term ktrm t1 ∪ FV term ktrm t2.
  Proof.
    introv. unfold FV. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

  Lemma rw_fv_ktrm_term4: forall t, FV term ktrm (tm_tab t) [=] FV term ktrm t.
  Proof.
    intros. unfold FV. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_fv_ktrm_term5: forall t τ, FV term ktrm (tm_tap t τ) [=] FV term ktrm t ∪ FV typ ktrm τ.
  Proof.
    intros. unfold FV. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

End rw_fv_ktrm_term.

#[export] Hint Rewrite rw_fv_ktrm_term11 rw_fv_ktrm_term12 rw_fv_ktrm_term2 rw_fv_ktrm_term3 rw_fv_ktrm_term4 rw_fv_ktrm_term5: sysf_rw.

(** ** Locally nameless operations *)
(******************************************************************************)

(** *** <<subst>> with <<ktyp>> *)
(******************************************************************************)
Section rw_subst_ktyp_term.

  Context
    (x: atom)
    (u: typ LN).

  Lemma rw_subst_ktyp_term1: forall l, subst term ktyp x u (tm_var l) = tm_var l.
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktyp_term2: forall τ t, subst term ktyp x u (tm_abs τ t) = tm_abs (subst typ ktyp x u τ) (subst term ktyp x u t).
  Proof.
    introv. unfold subst. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_subst_ktyp_term3: forall t1 t2, subst term ktyp x u (tm_app t1 t2) = tm_app (subst term ktyp x u t1) (subst term ktyp x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktyp_term4: forall t, subst term ktyp x u (tm_tab t) = tm_tab (subst term ktyp x u t).
  Proof.
    introv. unfold subst. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_subst_ktyp_term5: forall t τ, subst term ktyp x u (tm_tap t τ) = tm_tap (subst term ktyp x u t) (subst typ ktyp x u τ).
  Proof. reflexivity. Qed.

End rw_subst_ktyp_term.

#[export] Hint Rewrite @rw_subst_ktyp_term1 @rw_subst_ktyp_term2 @rw_subst_ktyp_term3 @rw_subst_ktyp_term4 @rw_subst_ktyp_term5: sysf_rw.

(** *** <<subst>> with <<ktrm>> *)
(******************************************************************************)
Section rw_subst_ktrm_term.

  Context
    (x: atom)
    (u: term LN).

  Lemma rw_subst_ktrm_term11: subst term ktrm x u (tm_var (Fr x)) = u.
  Proof. unfold subst. autorewrite with sysf_rw. cbn. compare values x and x. Qed.

  Lemma rw_subst_ktrm_term12: forall (y: atom), x <> y -> subst term ktrm x u (tm_var (Fr y)) = tm_var (Fr y).
  Proof. intros. unfold subst. autorewrite with sysf_rw. cbn. compare values x and y. Qed.

  Lemma rw_subst_ktrm_term13: forall (n: nat), subst term ktrm x u (tm_var (Bd n)) = tm_var (Bd n).
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktrm_term2: forall τ t, subst term ktrm x u (tm_abs τ t) = tm_abs (subst typ ktrm x u τ) (subst term ktrm x u t).
  Proof.
    introv. unfold subst. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_subst_ktrm_term3: forall t1 t2, subst term ktrm x u (tm_app t1 t2) = tm_app (subst term ktrm x u t1) (subst term ktrm x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_ktrm_term4: forall t, subst term ktrm x u (tm_tab t) = tm_tab (subst term ktrm x u t).
  Proof.
    introv. unfold subst. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_subst_ktrm_term5: forall t τ, subst term ktrm x u (tm_tap t τ) = tm_tap (subst term ktrm x u t) (subst typ ktrm x u τ).
  Proof. reflexivity. Qed.

End rw_subst_ktrm_term.

#[export] Hint Rewrite @rw_subst_ktrm_term11 @rw_subst_ktrm_term12 @rw_subst_ktrm_term13 @rw_subst_ktrm_term2 @rw_subst_ktrm_term3 @rw_subst_ktrm_term4 @rw_subst_ktrm_term5: sysf_rw.

#[local] Open Scope nat_scope.

(** *** <<locally_closed>> with <<ktyp>> *)
(******************************************************************************)
Section rw_lc_ktyp_term.

  Lemma rw_lc_ktyp_term1: forall l, locally_closed term ktyp (tm_var l).
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    introv. autorewrite with sysf_rw. introv [? [? ?]]; now subst.
  Qed.

  Lemma rw_lc_ktyp_term2: forall (τ: typ LN) (t: term LN), locally_closed term ktyp (tm_abs τ t) <-> locally_closed typ ktyp τ /\ locally_closed term ktyp t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_term2. split.
    - introv hyp. split.
      + intros. apply (hyp w l). now left.
      + intros. apply (hyp (ktrm:: w) l). right. eauto.
    - introv [hyp1 hyp2]. introv [hyp | hyp].
      + auto.
      + inverts hyp. inverts H. cbn. now apply hyp2.
  Qed.

  Lemma rw_lc_ktyp_term3: forall (t1 t2: term LN), locally_closed term ktyp (tm_app t1 t2) <-> locally_closed term ktyp t1 /\ locally_closed term ktyp t2.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_term3. firstorder.
  Qed.

  #[local] Open Scope nat_scope.

  Lemma rw_lc_ktyp_term4: forall t, locally_closed term ktyp (tm_tab t) <-> locally_closed_gap term ktyp 1 t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_term4. split.
    - intros hyp w l Hin.
      specialize (hyp (ktyp:: w) l). cbn in *.
      assert (rw: S (countk (@ktyp: K) w + 0) = (countk ktyp w + 1)) by lia.
      rewrite <- rw. apply hyp. eauto.
    - intros hyp w l [w' [H1 H2]]. subst.
      specialize (hyp w' l H1). cbn in *. destruct l.
      + easy.
      + lia.
  Qed.

  Lemma rw_lc_ktyp_term5: forall t τ, locally_closed term ktyp (tm_tap t τ) <-> locally_closed term ktyp t /\ locally_closed typ ktyp τ.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_term5. split.
    - introv hyp1. split.
      + introv hyp2. apply hyp1. now left.
      + introv hyp2. apply hyp1. now right.
    - introv [hyp1 hyp2] [hyp | hyp]; auto.
  Qed.

End rw_lc_ktyp_term.

#[export] Hint Rewrite @rw_lc_ktyp_term1 @rw_lc_ktyp_term2 @rw_lc_ktyp_term3 @rw_lc_ktyp_term4 @rw_lc_ktyp_term5: sysf_rw.

(** *** <<locally_closed>> with <<ktrm>> *)
(******************************************************************************)
Section rw_lc_ktrm_term.

  Lemma rw_lc_ktrm_term11: forall x, locally_closed term ktrm (tm_var (Fr x)).
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    introv. autorewrite with sysf_rw. introv [? [? ?]]; now subst.
  Qed.

  Lemma rw_lc_ktrm_term12: forall n, locally_closed term ktrm (tm_var (Bd n)) <-> False.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    split; [ |intuition]. introv hyp. cbn in hyp.
    specialize (hyp [] (Bd n) ltac:(auto)). cbn in hyp. lia.
  Qed.

  Lemma rw_lc_ktrm_term2: forall (τ: typ LN) (t: term LN), locally_closed term ktrm (tm_abs τ t) <-> locally_closed typ ktrm τ /\ locally_closed_gap term ktrm 1 t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_term2. split.
    - introv hyp. split.
      + intros. apply (hyp w l). now left.
      + intros. specialize (hyp (ktrm:: w) l). cbn in *.
      assert (rw: S (countk (@ktrm: K) w + 0) = (countk ktrm w + 1)) by lia.
      rewrite <- rw. apply hyp. eauto.
    - introv [hyp1 hyp2]. introv [hyp | hyp].
      + auto.
      + destruct hyp as [w' [hyp' hyp'']]. subst. cbn in *.
      assert (rw: S (countk (@ktrm: K) w' + 0) = (countk ktrm w' + 1)) by lia.
      rewrite rw. apply hyp2. auto.
  Qed.

  Lemma rw_lc_ktrm_term3: forall (t1 t2: term LN), locally_closed term ktrm (tm_app t1 t2) <-> locally_closed term ktrm t1 /\ locally_closed term ktrm t2.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_term3. firstorder.
  Qed.

  #[local] Open Scope nat_scope.

  Lemma rw_lc_ktrm_term4: forall t, locally_closed term ktrm (tm_tab t) <-> locally_closed term ktrm t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_term4. split.
    - intros hyp w l Hin. specialize (hyp (ktyp:: w) l).
      apply hyp. eauto.
    - intros hyp w l [w' [rest1 rest2]]. subst.
      cbn. apply hyp; auto.
  Qed.

  Lemma rw_lc_ktrm_term5: forall t τ, locally_closed term ktrm (tm_tap t τ) <-> locally_closed term ktrm t /\ locally_closed typ ktrm τ.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tosetmd_term5. split.
    - introv hyp1. split.
      + introv hyp2. apply hyp1. now left.
      + introv hyp2. apply hyp1. now right.
    - introv [hyp1 hyp2] [hyp | hyp]; auto.
  Qed.

End rw_lc_ktrm_term.

#[export] Hint Rewrite @rw_lc_ktrm_term11 @rw_lc_ktrm_term12 @rw_lc_ktrm_term2 @rw_lc_ktrm_term3 @rw_lc_ktrm_term4 @rw_lc_ktrm_term5: sysf_rw.

(** * Rewriting principles for <<ok_term>> *)
(******************************************************************************)
Lemma ok_term_abs: forall Δ Γ τ t,
    ok_term Δ Γ (tm_abs τ t) <->
    ok_type Δ τ /\
    scoped term ktrm t (AssocList.domset Γ) /\
    scoped term ktyp t (AssocList.domset Δ) /\
    locally_closed term ktyp t /\
    locally_closed_gap term ktrm 1 t.
Proof.
  intros. unfold ok_type, ok_term.
  unfold scoped.
  autorewrite with sysf_rw.
  intuition fsetdec.
Qed.

Lemma ok_term_app: forall Δ Γ t1 t2,
    ok_term Δ Γ (tm_app t1 t2) <-> ok_term Δ Γ t1 /\ ok_term Δ Γ t2.
Proof.
  intros. unfold ok_term, scoped.
  autorewrite with sysf_rw.
  intuition fsetdec.
Qed.
