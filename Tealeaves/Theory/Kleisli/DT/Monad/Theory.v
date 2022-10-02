From Tealeaves Require Export
  Algebraic.Functors.Applicative
  Algebraic.Functors.Listable
  Algebraic.Functors.Setlike
  Kleisli.Monads.DT.Monad
  Kleisli.Monads.DT.DerivedInstances
  Functors.List
  Functors.Constant.

Import Monad.Monad.Notations.
Import Product.Notations.
Import DT.Functor.Notations.
Import Decorated.Monad.Notations.
Import Traversable.Monad.Notations.
Import DT.Monad.Notations.

Import Setlike.Notations.
Import Functors.Sets.Notations.
Import Product.Notations.
Import Monoid.Notations.

Import List.ListNotations.
#[local] Open Scope list_scope.

(** * Shape and contents *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section shape_and_contents.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.


End shape_and_contents.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  (*
  Notation "x ∈ t" :=
    (toset _ t x) (at level 50) : tealeaves_scope.
   *)

End Notations.

Import Notations.

(** ** Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Lemma binddt_constant_applicative1
        `{Monoid M} {B : Type}
        `(f : W * A -> const M (T B)) :
    binddt (B := B) T (const M) f =
    binddt (B := False) T (const M) (f : W * A -> const M (T False)).
  Proof.
    change_right (fmap (B := T B) (const M) (fmap T exfalso)
                    ∘ (binddt (B := False) T (const M) (f : W * A -> const M (T False)))).
    rewrite (fmap_binddt T (G1 := const M)).
    reflexivity.
  Qed.

  Lemma binddt_constant_applicative2 (fake1 fake2 : Type) `{Monoid M}
        `(f : W * A -> const M (T B)) :
    binddt (B := fake1) T (const M)
            (f : W * A -> const M (T fake1))
    = binddt (B := fake2) T (const M)
              (f : W * A -> const M (T fake2)).
  Proof.
    intros. rewrite (binddt_constant_applicative1 (B := fake1)).
    rewrite (binddt_constant_applicative1 (B := fake2)). easy.
  Qed.

  Lemma tolistd_equiv1 : forall (fake : Type) (A : Type),
      tolistd_gen T (A := A) False = tolistd_gen T fake.
  Proof.
    intros. unfold tolistd_gen at 2.
    unfold_ops @Fmapdt_Binddt.
    now rewrite (binddt_constant_applicative2 fake False).
  Qed.

  Lemma tolistd_equiv2 : forall (fake1 fake2 : Type) (A : Type),
      tolistd_gen T (A := A) fake1 = tolistd_gen T fake2.
  Proof.
    intros. rewrite <- tolistd_equiv1.
    rewrite <- (tolistd_equiv1 fake2).
    easy.
  Qed.

End lemmas.

(** ** Characterizing membership in list operations *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Lemma ind_iff_in_tolistd : forall (A : Type) (a : A) (w : W) (t : T A),
      (w, a) ∈d t <-> Setlike.toset list (tolistd T t) (w, a).
  Proof.
    reflexivity.
  Qed.

  Lemma in_iff_in_tolistd : forall (A : Type) (a : A) (t : T A),
      (a ∈ t) <-> Setlike.toset list (tolist T t) a.
  Proof.
    reflexivity.
  Qed.

End DTM_tolist.

(** ** Characterizing occurrences post-operation *)
(******************************************************************************)
Section DTM_membership.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  (** *** Occurrences in <<ret>> *)
  (******************************************************************************)
  Lemma ind_ret_iff : forall (A : Type) (a1 a2 : A) (w : W),
      (w, a2) ∈d ret T a1 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros. rewrite (tosetd_ret T).
    simpl_set. split.
    - inversion 1; now subst.
    - introv [? ?]. now subst.
  Qed.

  Corollary in_ret_iff : forall (A : Type) (a1 a2 : A),
      a2 ∈ ret T a1 <-> a1 = a2.
  Proof.
    intros. rewrite ind_iff_in. setoid_rewrite ind_ret_iff.
    firstorder.
  Qed.

  (** *** Occurrences in <<bindd>> with context *)
  (******************************************************************************)
  Lemma ind_bindd_iff1 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd T f t ->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold tosetd, compose in *.
    (*
    rewrite (tolistd_bindd S) in hyp. induction (tolistd S t).
    - inversion hyp.
    - destruct a as [w [k a]]. rewrite binddt_list_cons in hyp.
      rewrite in_list_app in hyp. destruct hyp as [hyp1 | hyp2].
      + rewrite (in_fmap_iff list) in hyp1.
        destruct hyp1 as [[w2 [k2' b']] [hyp1 hyp2]].
        inversion hyp2; subst. exists k w w2 a. splits.
        { rewrite in_list_cons. now left. }
        { auto. }
        { easy. }
      + apply IHl in hyp2. clear IHl.
        destruct hyp2 as [k1 [w1 [w2 [a' [hyp1 [hyp2 hyp3]] ]]]].
        subst. repeat eexists.
        { rewrite in_list_cons. right. eauto. }
        { auto. }
     *)
  Admitted.

  Lemma ind_bindd_iff2 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
    (exists (w1 w2 : W) (a : A),
      (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2) ->
      (wtotal, b) ∈d bindd T f t.
  Proof.
    introv [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]. subst.
    unfold tosetd, compose in *. (* rewrite (tolistd_bindd S).
    induction (tolistd S t).
    - inversion hyp1.
    - destruct a0 as [w [k' a']]. rewrite binddt_list_cons.
      simpl_list. rewrite in_list_cons in hyp1. destruct hyp1 as [hyp1 | hyp1].
      + inverts hyp1. left. rewrite (in_fmap_iff list). exists (w2, (k2, b)).
        now splits.
      + right. now apply IHl in hyp1.
                                  *)
  Admitted.

  Theorem ind_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd T f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using ind_bindd_iff1, ind_bindd_iff2.
  Qed.

  (** *** Corollaries for other operations *)
  (******************************************************************************)
  Corollary ind_bind_iff :
    forall `(f : A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bind T f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f a
        /\ wtotal = w1 ● w2.
  Proof.
    intros. rewrite bind_to_bindd. apply ind_bindd_iff.
  Qed.

  Corollary ind_fmapd_iff :
    forall `(f : W * A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d fmapd T f t <->
      exists (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros. unfold fmapd, compose. setoid_rewrite ind_bindd_iff.
    unfold_ops @Fmap_I. setoid_rewrite ind_ret_iff.
    split.
    - intros [w1 [w2 [a [hyp1 [[hyp2 hyp3] hyp4]]]]].
      subst. exists a. simpl_monoid. auto.
    - intros [a [hyp1 hyp2]]. subst. repeat eexists.
      easy. now simpl_monoid.
  Qed.

  Corollary ind_fmap_iff :
    forall `(f : A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d fmap T f t <->
      exists (a : A), (w, a) ∈d t /\ f a = b.
  Proof.
    intros. rewrite (fmap_to_fmapd).
    rewrite ind_fmapd_iff. easy.
  Qed.

  (** *** Occurrences without context *)
  (******************************************************************************)
  Theorem in_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (b : B),
      b ∈ bindd T f t <->
      exists (w1 : W) (a : A),
        (w1, a) ∈d t
        /\ b ∈ f (w1, a).
  Proof.
    intros.
    rewrite ind_iff_in. setoid_rewrite ind_bindd_iff. split.
    - intros [wtotal [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]].
      exists w1 a. split; [auto|].
      apply (ind_implies_in) in hyp2. auto.
    - intros [w1 [a [hyp1 hyp2]]].
      rewrite ind_iff_in in hyp2. destruct hyp2 as [w2 rest].
      exists (w1 ● w2) w1 w2 a. intuition.
  Qed.

  (** *** Corollaries for other operations *)
  (******************************************************************************)
  Corollary in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T f t <->
      exists (a : A), a ∈ t /\ b ∈ f a.
  Proof.
    intros. unfold bind, compose. setoid_rewrite ind_iff_in.
    setoid_rewrite ind_bindd_iff. cbn. split.
    - firstorder.
    - intros [a [[w1 hyp1] [w hyp2]]].
      repeat eexists; eauto.
  Qed.

  Corollary in_fmapd_iff :
    forall `(f : W * A -> B) (t : T A) (b : B),
      b ∈ fmapd T f t <->
      exists (w : W) (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros. setoid_rewrite ind_iff_in.
    now setoid_rewrite ind_fmapd_iff.
  Qed.

  Corollary in_fmap_iff :
    forall `(f : A -> B) (t : T A) (b : B),
      b ∈ fmap T f t <->
      exists (a : A), a ∈ t /\ f a = b.
  Proof.
    intros. setoid_rewrite ind_iff_in.
    setoid_rewrite ind_fmap_iff.
    firstorder.
  Qed.

End DTM_membership.
