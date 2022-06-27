From Tealeaves Require Import
     Functors.List
     LN.Leaf LN.Atom LN.AtomSet LN.AssocList
     LN.Multisorted.Operations.

From Multisorted Require Import
     Classes.DTM
     Theory.DTMContainer
     Theory.DTMSchedule.

From Tealeaves.Examples Require Import
     SystemF.Language.

Import DTMContainer.Notations.
Import AtomSet.Notations.
Import Tealeaves.Classes.Monoid.Notations.
Import Tealeaves.Theory.Product.Notations.
Import Tealeaves.Classes.Applicative.Notations.
Import Multisorted.Classes.DTM.Notations.
Import List.ListNotations.
Import SetlikeFunctor.Notations.

Open Scope set_scope.
Open Scope list_scope.
Open Scope tealeaves_scope.
Open Scope tealeaves_multi_scope.

(** * Rewriting rules for operations *)
(******************************************************************************)

Create HintDb sysf_rw.
Tactic Notation "simpl_F" := autorewrite with sysf_rw.

(** * Rewriting operations on <<typ>> *)
(******************************************************************************)

(** ** Fundamental operations *)
(******************************************************************************)

(** *** <<mbinddt>> *)
(******************************************************************************)
Section rw_mbinddt_type.

  Context
    (A B : Type)
    `{Applicative F}
    (f : forall k, list K * A -> F (SystemF k B)).

  Lemma rw_mbinddt_type1 : forall c, mbinddt typ F f (ty_c c) = pure F (ty_c c).
  Proof. reflexivity. Qed.

  Lemma rw_mbinddt_type2 : forall (a : A), mbinddt typ F f (ty_v a) = f KType (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_mbinddt_type3 : forall (t1 t2 : typ A), mbinddt typ F f (ty_ar t1 t2) = pure F (ty_ar) <⋆> (mbinddt typ F f t1) <⋆> (mbinddt typ F f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbinddt_type4 : forall (body : typ A), mbinddt typ F f (ty_univ body) = pure F (ty_univ) <⋆> (mbinddt typ F (fun k => f k ∘ incr [KType]) body).
  Proof. reflexivity. Qed.

End rw_mbinddt_type.

Hint Rewrite @rw_mbinddt_type1 @rw_mbinddt_type2 @rw_mbinddt_type3 @rw_mbinddt_type4 : sysf_rw.

(** *** <<mfmapdt>> *)
(******************************************************************************)
Section rw_mfmapdt_type.

  Context
    (A B : Type)
    `{Applicative F}
    (f : K -> list K * A -> F B).

  Lemma rw_mfmapdt_type1 : forall c, mfmapdt typ F f (ty_c c) = pure F (ty_c c).
  Proof. reflexivity. Qed.

  Lemma rw_mfmapdt_type2 : forall (a : A), mfmapdt typ F f (ty_v a) = pure F ty_v <⋆> (f KType (nil, a)).
  Proof.
    intros. rewrite <- fmap_to_ap.
    unfold mfmapdt. now rewrite rw_mbinddt_type2.
  Qed.

  Lemma rw_mfmapdt_type3 : forall (t1 t2 : typ A), mfmapdt typ F f (ty_ar t1 t2) = pure F (ty_ar) <⋆> (mfmapdt typ F f t1) <⋆> (mfmapdt typ F f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mfmapdt_type4 : forall (body : typ A), mfmapdt typ F f (ty_univ body) = pure F (ty_univ) <⋆> (mfmapdt typ F (fun k => f k ∘ incr [KType]) body).
  Proof. reflexivity. Qed.

End rw_mfmapdt_type.

Hint Rewrite @rw_mfmapdt_type1 @rw_mfmapdt_type2 @rw_mfmapdt_type3 @rw_mfmapdt_type4 : sysf_rw.

(** *** <<mbindd>> *)
(******************************************************************************)
Section rw_mbindd_type.

  Context
    (A B : Type)
    (f : forall k, list K * A -> SystemF k B).

  Lemma rw_mbindd_type1 : forall c, mbindd typ f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type2 : forall (a : A), mbindd typ f (ty_v a) = f KType (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type3 : forall (t1 t2 : typ A), mbindd typ f (ty_ar t1 t2) = ty_ar (mbindd typ f t1) (mbindd typ f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type4 : forall (body : typ A), mbindd typ f (ty_univ body) = ty_univ (mbindd typ (fun k => f k ∘ incr [KType]) body).
  Proof. reflexivity. Qed.

End rw_mbindd_type.

Hint Rewrite @rw_mbindd_type1 @rw_mbindd_type2 @rw_mbindd_type3 @rw_mbindd_type4 : sysf_rw.

(** *** <<mbind>> *)
(******************************************************************************)
Section rw_mbind_type.

  Context
    (A B : Type)
    (f : forall k, A -> SystemF k B).

  Lemma rw_mbind_type1 : forall c, mbind typ f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type2 : forall (a : A), mbind typ f (ty_v a) = f KType a.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type3 : forall (t1 t2 : typ A), mbind typ f (ty_ar t1 t2) = ty_ar (mbind typ f t1) (mbind typ f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type4 : forall (body : typ A), mbind typ f (ty_univ body) = ty_univ (mbind typ f body).
  Proof.
    intros. unfold mbind. rewrite rw_mbindd_type4. repeat fequal. now ext k [w a].
  Qed.

End rw_mbind_type.

Hint Rewrite @rw_mbind_type1 @rw_mbind_type2 @rw_mbind_type3 @rw_mbind_type4 : sysf_rw.

(** *** <<kbindd>> with <<KType>> *)
(******************************************************************************)
Section rw_kbindd_type.

  Context
    (A : Type)
    (f : list K * A -> typ A).

  Lemma rw_kbindd_KType_type1 : forall c, kbindd typ KType f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type2 : forall a, kbindd typ KType f (ty_v a) = f (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type3 : forall (t1 t2 : typ A), kbindd typ KType f (ty_ar t1 t2) = ty_ar (kbindd typ KType f t1) (kbindd typ KType f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type4 : forall (body : typ A), kbindd typ KType f (ty_univ body) = ty_univ (kbindd typ KType (f ∘ incr [KType]) body).
  Proof.
    intros. unfold kbindd. simpl_F.
    do 2 fequal. now ext j [w a].
  Qed.

End rw_kbindd_type.

Hint Rewrite @rw_kbindd_KType_type1 @rw_kbindd_KType_type2 @rw_kbindd_KType_type3 @rw_kbindd_KType_type4 : sysf_rw.

(** *** <<kbindd>> with <<KTerm>> *)
(******************************************************************************)
Section rw_kbindd_type.

  Context
    (A : Type)
    (f : list K * A -> term A).

  Lemma rw_kbindd_KTerm_type1 : forall c, kbindd typ KTerm f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type2 : forall a, kbindd typ KTerm f (ty_v a) = ty_v a.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type3 : forall (t1 t2 : typ A), kbindd typ KTerm f (ty_ar t1 t2) = ty_ar (kbindd typ KTerm f t1) (kbindd typ KTerm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type4 : forall (body : typ A), kbindd typ KTerm f (ty_univ body) = ty_univ (kbindd typ KTerm (f ∘ incr [KType]) body).
  Proof.
    intros. unfold kbindd. simpl_F.
    do 2 fequal. now ext j [w a].
  Qed.

End rw_kbindd_type.

Hint Rewrite @rw_kbindd_KTerm_type1 @rw_kbindd_KTerm_type2 @rw_kbindd_KTerm_type3 @rw_kbindd_KTerm_type4 : sysf_rw.

(** *** <<kbind>> with <<KType>> *)
(******************************************************************************)
Section rw_kbind_type.

  Context
    (A : Type)
    (f : A -> typ A).

  Lemma rw_kbind_KType_type1 : forall c, kbind typ KType f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type2 : forall a, kbind typ KType f (ty_v a) = f a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type3 : forall (t1 t2 : typ A), kbind typ KType f (ty_ar t1 t2) = ty_ar (kbind typ KType f t1) (kbind typ KType f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type4 : forall (body : typ A), kbind typ KType f (ty_univ body) = ty_univ (kbind typ KType f body).
  Proof.
    intros. unfold kbind. now simpl_F.
  Qed.

End rw_kbind_type.

Hint Rewrite @rw_kbind_KType_type1 @rw_kbind_KType_type2 @rw_kbind_KType_type3 @rw_kbind_KType_type4 : sysf_rw.

(** *** <<kbind>> with <<KTerm>> *)
(******************************************************************************)
Section rw_kbind_type.

  Context
    (A : Type)
    (f : A -> term A).

  Lemma rw_kbind_KTerm_type1 : forall c, kbind typ KTerm f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type2 : forall a, kbind typ KTerm f (ty_v a) = ty_v a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type3 : forall (t1 t2 : typ A), kbind typ KTerm f (ty_ar t1 t2) = ty_ar (kbind typ KTerm f t1) (kbind typ KTerm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type4 : forall (body : typ A), kbind typ KTerm f (ty_univ body) = ty_univ (kbind typ KTerm f body).
  Proof.
    intros. unfold kbind. now simpl_F.
  Qed.

End rw_kbind_type.

Hint Rewrite @rw_kbind_KTerm_type1 @rw_kbind_KTerm_type2 @rw_kbind_KTerm_type3 @rw_kbind_KTerm_type4 : sysf_rw.

(** ** List and occurrence operations *)
(******************************************************************************)

(** *** <<tomlistd>> *)
(******************************************************************************)
Section rw_tomlistd_type.

  Context
    (A : Type).

  Lemma rw_tomlistd_type1 : forall c, tomlistd (A := A) typ (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_tomlistd_type2 : forall (a : A), tomlistd typ (ty_v a) = [ (nil, (KType, a)) ].
  Proof. reflexivity. Qed.

  Lemma rw_tomlistd_type3 : forall (t1 t2 : typ A), tomlistd typ (ty_ar t1 t2) = tomlistd typ t1 ++ tomlistd typ t2.
  Proof. reflexivity. Qed.

  Lemma rw_tomlistd_type4 : forall (body : typ A), tomlistd typ (ty_univ body) = fmap list (incr [KType]) (tomlistd typ body).
  Proof.
    intros. unfold tomlistd, tomlistd_gen.
    rewrite rw_mfmapdt_type4. cbn.
    compose near body on right. unfold mfmapdt.
    rewrite (dtp_mbinddt_morphism
               (list (@K I2)) typ SystemF (const (list _)) (const (list _)) (ϕ := (fun _ => fmap list (incr [KType])))
               (fun (k : @K I2) => fmap (const (list (list K2 * (K2 * A)))) (mret SystemF k) ∘ (fun '(w, a) => [(w, (k, a))]))).
    fequal. now ext k [w a].
  Qed.

End rw_tomlistd_type.

Hint Rewrite @rw_tomlistd_type1 @rw_tomlistd_type2 @rw_tomlistd_type3 @rw_tomlistd_type4 : sysf_rw.

(** *** <<toklistd>> with <<KType>> *)
(******************************************************************************)
Section rw_toklistd_KType_type.

  Context
    (A : Type).

  Lemma rw_toklistd_KType_type1 : forall c, toklistd (A := A) typ KType (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_KType_type2 : forall (a : A), toklistd typ KType (ty_v a) = [ (nil, a) ].
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_KType_type3 : forall (t1 t2 : typ A), toklistd typ KType (ty_ar t1 t2) = toklistd typ KType t1 ++ toklistd typ KType t2.
  Proof. intros. unfold toklistd, compose. rewrite rw_tomlistd_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklistd_KType_type4 : forall (body : typ A), toklistd typ KType (ty_univ body) = fmap list (incr [KType]) (toklistd typ KType body).
  Proof. intros. unfold toklistd, compose. rewrite rw_tomlistd_type4.
         induction (tomlistd typ body).
         - reflexivity.
         - destruct a as [w [k a]]. compare values k and KType.
           + cbn. now rewrite <- IHl.
           + repeat (autorewrite with tea_list; auto).
             rewrite <- IHl.
             change (incr [KType] (w, (k, a))) with (KType :: w, (k, a)).
             rewrite filterk_cons_neq; auto.
  Qed.

End rw_toklistd_KType_type.

Hint Rewrite @rw_toklistd_KType_type1 @rw_toklistd_KType_type2 @rw_toklistd_KType_type3 @rw_toklistd_KType_type4 : sysf_rw.

(** *** <<toklistd>> with <<KTerm>> *)
(******************************************************************************)
Section rw_toklistd_KTerm_type.

  Context
    (A : Type).

  Lemma rw_toklistd_KTerm_type1 : forall c, toklistd (A := A) typ KTerm (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_KTerm_type2 : forall (a : A), toklistd typ KTerm (ty_v a) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_KTerm_type3 : forall (t1 t2 : typ A), toklistd typ KTerm (ty_ar t1 t2) = toklistd typ KTerm t1 ++ toklistd typ KTerm t2.
  Proof. intros. unfold toklistd, compose. rewrite rw_tomlistd_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklistd_KTerm_type4 : forall (body : typ A), toklistd typ KTerm (ty_univ body) = fmap list (incr [KType]) (toklistd typ KTerm body).
  Proof.
    intros. unfold toklistd, compose. rewrite rw_tomlistd_type4.
    induction (tomlistd typ body).
    - reflexivity.
    - destruct a as [w [k a]]. compare values k and KTerm.
      + cbn. now rewrite <- IHl.
      + repeat (autorewrite with tea_list; auto).
        rewrite <- IHl.
        change (incr [KType] (w, (k, a))) with (KType :: w, (k, a)).
        rewrite filterk_cons_neq; auto.
  Qed.

End rw_toklistd_KTerm_type.

Hint Rewrite @rw_toklistd_KTerm_type1 @rw_toklistd_KTerm_type2 @rw_toklistd_KTerm_type3 @rw_toklistd_KTerm_type4 : sysf_rw.

Corollary rw_toklistd_KTerm_type : forall A (τ : typ A), toklistd typ KTerm τ = nil.
Proof.
  intros. induction τ; autorewrite with sysf_rw.
  - trivial.
  - trivial.
  - now rewrite IHτ1, IHτ2.
  - now rewrite IHτ.
Qed.

(** *** <<tomlist>> *)
(******************************************************************************)
Section rw_tomlist_type.

  Context
    (A : Type).

  Lemma rw_tomlist_type1 : forall c, tomlist (A := A) typ (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_type2 : forall (a : A), tomlist typ (ty_v a) = [ (KType, a) ].
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_type3 : forall (t1 t2 : typ A), tomlist typ (ty_ar t1 t2) = tomlist typ t1 ++ tomlist typ t2.
  Proof. intros. unfold tomlist, compose. rewrite rw_tomlistd_type3. now autorewrite with tea_list. Qed.

  Lemma rw_tomlist_type4 : forall (body : typ A), tomlist typ (ty_univ body) = (tomlist typ body).
  Proof. intros. unfold tomlist, compose. rewrite rw_tomlistd_type4.
         compose near (tomlistd typ body) on left. rewrite (fun_fmap_fmap list).
         fequal. now ext [w a].
  Qed.

End rw_tomlist_type.

Hint Rewrite @rw_tomlist_type1 @rw_tomlist_type2 @rw_tomlist_type3 @rw_tomlist_type4 : sysf_rw.

(** *** <<toklist>> with <<KType>> *)
(******************************************************************************)
Section rw_toklist_KType_type.

  Context
    (A : Type).

  Lemma rw_toklist_KType_type1 : forall c, toklist (A := A) typ KType (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_type2 : forall (a : A), toklist typ KType (ty_v a) = [ a ].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_type3 : forall (t1 t2 : typ A), toklist typ KType (ty_ar t1 t2) = toklist typ KType t1 ++ toklist typ KType t2.
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_KType_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklist_KType_type4 : forall (body : typ A), toklist typ KType (ty_univ body) = (toklist typ KType body).
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_KType_type4.
         compose near (toklistd typ KType body) on left. rewrite (fun_fmap_fmap list).
         fequal. now ext [w a]. Qed.

End rw_toklist_KType_type.

Hint Rewrite @rw_toklist_KType_type1 @rw_toklist_KType_type2 @rw_toklist_KType_type3 @rw_toklist_KType_type4 : sysf_rw.

(** *** <<toklist>> with <<KTerm>> *)
(******************************************************************************)
Section rw_toklist_KTerm_type.

  Context
    (A : Type).

  Lemma rw_toklist_KTerm_type1 : forall c, toklist (A := A) typ KTerm (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_type2 : forall (a : A), toklist typ KTerm (ty_v a) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_type3 : forall (t1 t2 : typ A), toklist typ KTerm (ty_ar t1 t2) = toklist typ KTerm t1 ++ toklist typ KTerm t2.
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_KTerm_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklist_KTerm_type4 : forall (body : typ A), toklist typ KTerm (ty_univ body) = (toklist typ KTerm body).
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_KTerm_type4.
         compose near (toklistd typ KTerm body) on left. rewrite (fun_fmap_fmap list).
         fequal. now ext [w a]. Qed.

End rw_toklist_KTerm_type.

Hint Rewrite @rw_toklist_KTerm_type1 @rw_toklist_KTerm_type2 @rw_toklist_KTerm_type3 @rw_toklist_KTerm_type4 : sysf_rw.

Corollary rw_toklist_KTerm_type : forall A (τ : typ A), toklist typ KTerm τ = nil.
Proof.
  intros. induction τ; autorewrite with sysf_rw.
  - trivial.
  - trivial.
  - now rewrite IHτ1, IHτ2.
  - now rewrite IHτ.
Qed.

(** *** Variable occurrence with context *)
(******************************************************************************)
Section rw_tomsetd_type.

  Context
    (A : Type)
    (k : K2).

  Implicit Types
           (w : list K) (a : A).

  Lemma rw_tomsetd_type1 : forall c w a, (w, (k, a)) ∈md (ty_c c) <-> False.
  Proof.
    intros. unfold tomsetd, compose. autorewrite with sysf_rw. easy.
  Qed.

  Lemma rw_tomsetd_type2 : forall w a a', (w, (k, a)) ∈md (ty_v a') <-> w = nil /\ k = KType /\ a = a'.
  Proof.
    intros. unfold tomsetd, compose. autorewrite with sysf_rw tea_list.
    splits.
    - now inversion 1.
    - firstorder. now subst.
  Qed.

  Lemma rw_tomsetd_type3 : forall w a (t1 t2 : typ A), (w, (k, a)) ∈md ty_ar t1 t2 <-> ((w, (k, a)) ∈md t1 \/ (w, (k, a)) ∈md t2).
  Proof.
    intros. unfold tomsetd, compose.
    now autorewrite with sysf_rw tea_list tea_set.
  Qed.

  Lemma rw_tomsetd_type4 : forall w a (body : typ A), (w, (k, a)) ∈md (ty_univ body) <-> exists w', (w', (k, a)) ∈md body /\ w = (cons KType w').
  Proof.
    intros. unfold tomsetd, compose. autorewrite with sysf_rw.
    rewrite (in_fmap_iff list). splits.
    - intros [[w'' [j a']] [rest1 rest2]]. cbn in *. inverts rest2. eauto.
    - intros [w' rest]. exists (w', (k, a)). now inverts rest.
  Qed.

End rw_tomsetd_type.

Hint Rewrite @rw_tomsetd_type1 @rw_tomsetd_type2 @rw_tomsetd_type3 @rw_tomsetd_type4 : sysf_rw.

Corollary rw_tomsetd_type_KTerm : forall w A a (τ : typ A), (w, (KTerm, a)) ∈md τ <-> False.
Proof.
  intros. generalize dependent w.
  induction τ; intro w; autorewrite with sysf_rw; try easy.
  - rewrite IHτ1, IHτ2. tauto.
  - split; try tauto.
    intros [w' [rest1 rest2]]. now rewrite IHτ in rest1.
Qed.

(** *** Variable occurrence without context *)
(******************************************************************************)
Section rw_tomset_type.

  Context
    (A : Type)
    (k : K2).

  Implicit Types (a : A).

  Lemma rw_tomset_type1 : forall c a, (k, a) ∈m (ty_c c) <-> False.
  Proof. intros. rewrite ind_iff_in. firstorder eauto. Qed.

  Lemma rw_tomset_type2 : forall a a', (k, a) ∈m (ty_v a') <-> k = KType /\ a = a'.
  Proof. intros. rewrite ind_iff_in. setoid_rewrite rw_tomsetd_type2. firstorder eauto.  Qed.

  Lemma rw_tomset_type3 : forall a (t1 t2 : typ A), (k, a) ∈m ty_ar t1 t2 <-> (k, a) ∈m t1 \/ (k, a) ∈m t2.
  Proof. intros. repeat rewrite ind_iff_in. setoid_rewrite rw_tomsetd_type3. firstorder eauto. Qed.

  Lemma rw_tomset_type4 : forall a (body : typ A), (k, a) ∈m (ty_univ body) <-> (k, a) ∈m body.
  Proof. intros. repeat rewrite ind_iff_in. setoid_rewrite rw_tomsetd_type4. firstorder eauto.  Qed.

End rw_tomset_type.

Hint Rewrite @rw_tomset_type1 @rw_tomset_type2 @rw_tomset_type3 @rw_tomset_type4 : sysf_rw.

(** ** <<free>> and <<freeset>> *)
(******************************************************************************)

(** *** <<free>> with <<KType>> *)
(******************************************************************************)
Section rw_free_KType_type.

  Lemma rw_free_KType_type11 : forall (x : atom), free typ KType (ty_v (Fr x)) = [x].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type12 : forall (n : nat), free typ KType (ty_v (Bd n)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type2 : forall (c : base_typ), free typ KType (ty_c c) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type3 : forall t1 t2, free typ KType (ty_ar t1 t2) = free typ KType t1 ++ free typ KType t2.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KType_type4 : forall t, free typ KType (ty_univ t) = free typ KType t.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_free_KType_type.

Hint Rewrite rw_free_KType_type11 rw_free_KType_type12 rw_free_KType_type2 rw_free_KType_type3 rw_free_KType_type4 : sysf_rw.

(** *** <<freeset>> with <<KType>> *)
(******************************************************************************)
Section rw_freeset_KType_type.

  Lemma rw_freeset_KType_type11 : forall (x : atom), freeset typ KType (ty_v (Fr x)) [=] {{ x }}.
  Proof.
    unfold freeset. intros. autorewrite with sysf_rw tea_rw_atoms. fsetdec.
  Qed.

  Lemma rw_freeset_KType_type12 : forall (n : nat), freeset typ KType (ty_v (Bd n)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KType_type2 : forall (c : base_typ), freeset typ KType (ty_c c) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KType_type3 : forall t1 t2, freeset typ KType (ty_ar t1 t2) [=] freeset typ KType t1 ∪ freeset typ KType t2.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KType_type4 : forall t, freeset typ KType (ty_univ t) [=] freeset typ KType t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_freeset_KType_type.

Hint Rewrite rw_freeset_KType_type11 rw_freeset_KType_type12 rw_freeset_KType_type2 rw_freeset_KType_type3 rw_freeset_KType_type4 : sysf_rw.

(** *** <<free>> with <<KTerm>> *)
(******************************************************************************)
Section rw_free_KTerm_type.

  Lemma rw_free_KTerm_type11 : forall (x : atom), free typ KTerm (ty_v (Fr x)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type12 : forall (n : nat), free typ KTerm (ty_v (Bd n)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type2 : forall (c : base_typ), free typ KTerm (ty_c c) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type3 : forall t1 t2, free typ KTerm (ty_ar t1 t2) = free typ KTerm t1 ++ free typ KTerm t2.
  Proof. intros. unfold free. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_free_KTerm_type4 : forall t, free typ KTerm (ty_univ t) = free typ KTerm t.
  Proof. intros. unfold free. now autorewrite with sysf_rw tea_list. Qed.

End rw_free_KTerm_type.

Hint Rewrite rw_free_KTerm_type11 rw_free_KTerm_type12 rw_free_KTerm_type2 rw_free_KTerm_type3 rw_free_KTerm_type4 : sysf_rw.

Corollary rw_free_KTerm_type : forall (τ : typ leaf), free typ KTerm τ = [].
Proof.
  intros. induction τ; autorewrite with sysf_rw.
  - trivial.
  - trivial.
  - now rewrite IHτ1, IHτ2.
  - now rewrite IHτ.
Qed.

(** *** <<freeset>> with <<KTerm>> *)
(******************************************************************************)
Section rw_freeset_KTerm_type.

  Lemma rw_freeset_KTerm_type11 : forall (x : atom), freeset typ KTerm (ty_v (Fr x)) [=] ∅.
  Proof.
    unfold freeset. intros. rewrite rw_free_KTerm_type11. autorewrite with tea_rw_atoms. fsetdec. Qed.

  Lemma rw_freeset_KTerm_type12 : forall (n : nat), freeset typ KTerm (ty_v (Bd n)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type2 : forall (c : base_typ), freeset typ KTerm (ty_c c) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type3 : forall t1 t2, freeset typ KTerm (ty_ar t1 t2) [=] freeset typ KTerm t1 ∪ freeset typ KTerm t2.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type4 : forall t, freeset typ KTerm (ty_univ t) [=] freeset typ KTerm t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_freeset_KTerm_type.

Hint Rewrite rw_freeset_KTerm_type11 rw_freeset_KTerm_type12 rw_freeset_KTerm_type2 rw_freeset_KTerm_type3 rw_freeset_KTerm_type4 : sysf_rw.

Corollary rw_freeset_KTerm_type : forall (τ : typ leaf), freeset typ KTerm τ [=] ∅.
Proof.
  intros. induction τ.
  - autorewrite with sysf_rw. fsetdec.
  - cbn. fsetdec.
  - autorewrite with sysf_rw. fsetdec.
  - autorewrite with sysf_rw. fsetdec.
Qed.

Hint Rewrite rw_freeset_KTerm_type : sysf_rw.

(** ** Locally nameless operations *)
(******************************************************************************)

(** *** <<open>> *)
(******************************************************************************)
Section rw_open_type.

  Context
    (u : typ leaf).

  Lemma rw_open_type1 : forall c, open typ KType u (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_open_type2 : forall (l : leaf), open typ KType u (ty_v l) = open_loc KType u (nil, l).
  Proof. reflexivity. Qed.

  Lemma rw_open_type3 : forall (t1 t2 : typ leaf), open typ KType u (ty_ar t1 t2) = ty_ar (open typ KType u t1) (open typ KType u t2).
  Proof. reflexivity. Qed.

End rw_open_type.

Hint Rewrite @rw_open_type1 @rw_open_type2 @rw_open_type3 : sysf_rw.

(** *** <<subst>> *)
(******************************************************************************)
Section rw_subst_type.

  Context
    (x : atom)
    (u : typ leaf).

  Lemma rw_subst_type1 : forall c, subst typ KType x u (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_subst_type2 : forall (l : leaf), subst typ KType x u (ty_v l) = subst_loc KType x u l.
  Proof. reflexivity. Qed.

  Lemma rw_subst_type3 : forall (t1 t2 : typ leaf), subst typ KType x u (ty_ar t1 t2) = ty_ar (subst typ KType x u t1) (subst typ KType x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_type4 : forall (t : typ leaf), subst typ KType x u (ty_univ t) = ty_univ (subst typ KType x u t).
  Proof.
    intros. unfold subst. now autorewrite with sysf_rw.
  Qed.

End rw_subst_type.

Hint Rewrite @rw_subst_type1 @rw_subst_type2 @rw_subst_type3 @rw_subst_type4 : sysf_rw.

(** *** <<locally_closed>> with <<KType>> *)
(******************************************************************************)
Section rw_lc_KType_type.

  Lemma rw_lc_KType_type1 : forall c, locally_closed typ KType (ty_c c).
  Proof.
    intros. unfold locally_closed, locally_closed_gap; introv hyp.
    now rewrite rw_tomsetd_type1 in hyp.
  Qed.

  Lemma rw_lc_KType_type2 : forall (l : leaf), locally_closed typ KType (ty_v l) <-> exists x, l = Fr x.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_type2. split.
    - introv hyp. destruct l.
      + eauto.
      + enough (n < 0). lia. now apply (hyp [] (Bd n)).
    - intros [x heq]. subst. introv hyp. inversion hyp.
      inverts H0. cbn; trivial.
  Qed.

  Lemma rw_lc_KType_type3 : forall (t1 t2 : typ leaf), locally_closed typ KType (ty_ar t1 t2) <-> (locally_closed typ KType t1 /\ locally_closed typ KType t2).
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_type3. firstorder.
  Qed.

  #[local] Open Scope nat_scope.

  Lemma rw_lc_KType_type4 : forall (t : typ leaf), locally_closed typ KType (ty_univ t) <-> locally_closed_gap typ KType 1 t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_type4. split.
    - intros hyp w l Hin.
      specialize (hyp (KType :: w) l). cbn in *.
      assert (rw : S (countk (@KType : K) w + 0) = (countk KType w + 1)) by lia.
      rewrite <- rw. apply hyp. eauto.
    - intros hyp w l [w' [H1 H2]]. subst.
      specialize (hyp w' l H1). cbn in *. destruct l.
      + easy.
      + lia.
  Qed.

End rw_lc_KType_type.

Hint Rewrite @rw_lc_KType_type1 @rw_lc_KType_type2 @rw_lc_KType_type3 @rw_lc_KType_type4 : sysf_rw.

(** *** <<locally_closed>> with <<KTerm>> *)
(******************************************************************************)
Section rw_lc_KTerm_type.

  Lemma rw_lc_KTerm_type : forall τ, locally_closed typ KTerm τ.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    intros. now rewrite rw_tomsetd_type_KTerm in H.
  Qed.

End rw_lc_KTerm_type.

Hint Rewrite @rw_lc_KTerm_type : sysf_rw.

(** *** <<locally_closed>> with <<KTerm>> *)
(******************************************************************************)
Section rw_scoped_KTerm_type.

  Lemma rw_scoped_KTerm_type : forall τ (vars : AtomSet.t), scoped typ KTerm τ vars.
  Proof.
    intros. unfold scoped. autorewrite with sysf_rw. fsetdec.
  Qed.

End rw_scoped_KTerm_type.

(** * Rewriting principles for <<ok_type>> *)
(******************************************************************************)
Lemma ok_type_ar : forall Δ τ1 τ2,
    ok_type Δ (ty_ar τ1 τ2) <->
    ok_type Δ τ1 /\ ok_type Δ τ2.
Proof.
  intros. unfold ok_type.
  unfold scoped.
  autorewrite with sysf_rw.
  intuition fsetdec.
Qed.

Lemma ok_type_univ : forall Δ τ,
    ok_type Δ (ty_univ τ) <->
    scoped typ KType τ (domset Δ) /\
    locally_closed_gap typ KType 1 τ.
Proof.
  intros. unfold ok_type.
  unfold scoped.
  now autorewrite with sysf_rw.
Qed.

(** * Rewriting principles for <<ok_term>> *)
(******************************************************************************)
Lemma ok_term_abs : forall Δ Γ τ t,
    ok_term Δ Γ (tm_abs τ t) <->
    ok_type Δ τ /\
    scoped term KTerm t (domset Γ) /\
    scoped term KType t (domset Δ) /\
    locally_closed term KType t /\
    locally_closed_gap term KTerm 1 t.
Proof.
  intros. unfold ok_type, ok_term.
  unfold scoped.
  repeat autorewrite with sysf_rw.
  (*
  rewrite rw_freeset_KTerm_type.
  intuition fsetdec.
*)
Admitted.

Lemma ok_term_app : forall Δ Γ t1 t2,
    ok_term Δ Γ (tm_app t1 t2) <-> ok_term Δ Γ t1 /\ ok_term Δ Γ t2.
Proof.
  intros. unfold ok_term, scoped.
  (*
  simpl_F. intuition fsetdec.
   *)
Admitted.
