From Tealeaves Require Export
     Classes.Applicative
     Classes.ListableFunctor.

From Multisorted Require Import
     Classes.DTM
     Functors.Tag
     Functors.MList2.

Import Classes.SetlikeFunctor.Notations.
Import Functors.Sets.Notations.
Import Product.Notations. (* for (W ×) *)
Import Monoid.Notations.
Import List.ListNotations.
Import Multisorted.Theory.Category.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.
#[local] Open Scope list_scope.

(* TODO This is only for <<exfalso>> *)
Require Tealeaves.Classes.TraversableFunctor.

(** * Shape and contents *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section shape_and_contents.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Definition shape {A} : S A -> S unit :=
    mfmap S (const (const tt)).

  Definition tomlistd_gen {A} (fake : Type) : S A -> list (W * Tag A) :=
    mfmapdt (B := fake) S (const (list (W * Tag A))) (fun k '(w, a) => [(w, (k, a))]).

  Definition tomlistd {A} : S A -> list (W * Tag A) :=
    tomlistd_gen False.

  Definition tomsetd {A} : S A -> W * Tag A -> Prop :=
    toset list ∘ tomlistd.

  Definition tomlist {A} : S A -> list (Tag A) :=
    fmap list snd ∘ tomlistd.

  Definition tomset {A} : S A -> Tag A -> Prop :=
    toset list ∘ tomlist.

  Fixpoint filterk {A}  (l : list (W * Tag A)) : list (W * A) :=
    match l with
    | nil => nil
    | cons (w, (j, a)) ts =>
      if k == j then (w, a) :: filterk k ts else filterk k ts
    end.

  Definition toklistd {A} (k : K) : S A -> list (W * A) :=
    filterk k ∘ tomlistd.

  Definition toksetd {A} (k : K) : S A -> W * A -> Prop :=
    toset list ∘ toklistd k.

  Definition toklist {A} (k : K) : S A -> list A :=
    fmap list (extract (W ×)) ∘ @toklistd A k.

End shape_and_contents.

(** ** Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mbinddt_constant_applicative1
        `{Monoid M} {B : Type}
        `(f : forall (k : K), W * A -> const M (T k B)) :
    mbinddt (B := B) S (const M) f =
    mbinddt (B := False) S (const M) (f : forall (k : K), W * A -> const M (T k False)).
  Proof.
    change_right (fmap (B := S B) (const M) (mfmap S (const TraversableFunctor.exfalso))
                       ∘ (mbinddt (B := False) S (const M) (f : forall (k : K), W * A -> const M (T k False)))).
    rewrite (mfmap_mbinddt S (F := const M)).
    fequal. ext k [w a]. easy.
  Qed.

  Lemma mbinddt_constant_applicative2 (fake1 fake2 : Type) `{Monoid M}
        `(f : forall (k : K), W * A -> const M (T k B)) :
    mbinddt (B := fake1) S (const M)
            (f : forall (k : K), W * A -> const M (T k fake1))
    = mbinddt (B := fake2) S (const M)
              (f : forall (k : K), W * A -> const M (T k fake2)).
  Proof.
    intros. rewrite (mbinddt_constant_applicative1 (B := fake1)).
    rewrite (mbinddt_constant_applicative1 (B := fake2)). easy.
  Qed.

  Lemma tomlistd_equiv1 : forall (fake : Type) (A : Type),
      tomlistd_gen S (A := A) False = tomlistd_gen S fake.
  Proof.
    intros. unfold tomlistd_gen at 2, mfmapdt.
    now rewrite (mbinddt_constant_applicative2 fake False).
  Qed.

  Lemma tomlistd_equiv : forall (fake1 fake2 : Type) (A : Type),
      tomlistd_gen S (A := A) fake1 = tomlistd_gen S fake2.
  Proof.
    intros. rewrite <- tomlistd_equiv1.
    rewrite <- (tomlistd_equiv1 fake2).
    easy.
  Qed.

End lemmas.

(** ** Interaction between <<tomlistd>> and <<mret>>/<<mbindd>> *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma tomlistd_gen_mret : forall (A B : Type) (a : A) (k : K),
      tomlistd_gen (T k) B (mret T k a) = [ (Ƶ, (k, a)) ].
  Proof.
    intros. unfold tomlistd_gen.
    now rewrite mfmapdt_comp_mret.
  Qed.

  Corollary tomlistd_mret : forall (A : Type) (a : A) (k : K),
      tomlistd (T k) (mret T k a) = [ (Ƶ, (k, a)) ].
  Proof.
    intros. unfold tomlistd. apply tomlistd_gen_mret.
  Qed.

  Corollary tomsetd_mret : forall (A : Type) (a : A) (k : K),
      tomsetd (T k) (mret T k a) = {{ (Ƶ, (k, a)) }}.
  Proof.
    intros. unfold tomsetd, compose. rewrite tomlistd_mret.
    solve_basic_set.
  Qed.

  Corollary tomlist_mret : forall (A : Type) (a : A) (k : K),
      tomlist (T k) (mret T k a) = [ (k, a) ].
  Proof.
    intros. unfold tomlist, compose.
    rewrite tomlistd_mret. easy.
  Qed.

  Corollary tomset_mret : forall (A : Type) (a : A) (k : K),
      tomset (T k) (mret T k a) = {{ (k, a) }}.
  Proof.
    intros. unfold tomset, compose.
    rewrite tomlist_mret. solve_basic_set.
  Qed.

  Lemma tomlistd_gen_mbindd :
    forall (fake : Type)
      `(f : forall k, W * A -> T k B) (t : S A),
      tomlistd_gen S fake (mbindd S f t) =
      mbinddt_list (fun k '(w, a) => tomlistd_gen (T k) fake (f k (w, a))) (tomlistd_gen S fake t).
  Proof.
    intros. unfold tomlistd_gen, mfmapdt.
    compose near t on left.
    rewrite (mbinddt_mbindd S).
    compose near t on right.
    change (mbinddt_list ?f) with (const (mbinddt_list f) (S fake)).
    #[local] Set Keyed Unification. (* TODO figure out why this is here. *)
    rewrite (dtp_mbinddt_morphism W S T
                                  (const (list (W * Tag A)))
                                  (const (list (W * Tag B)))
                                  (A := A) (B := fake)).
    #[local] Unset Keyed Unification.
    fequal. ext k [w a].
    cbn.
    change (fmap list ?f) with (const (fmap list f) (S B)).
    List.simpl_list.
    compose near (f k (w, a)) on right.
    (* for some reason I can't rewrite without posing first. *)
    pose (rw := dtp_mbinddt_morphism
                  W (T k) T
                  (const (list (W * Tag B)))
                  (const (list (W * Tag B)))
                  (ϕ := (const (fmap list (incr w))))
                  (A := B) (B := fake)).
    rewrite rw. fequal. now ext k2 [w2 b].
  Qed.

  Corollary tomlistd_mbindd : forall
      `(f : forall k, W * A -> T k B) (t : S A),
      tomlistd S (mbindd S f t) =
      mbinddt_list (fun k '(w, a) => tomlistd (T k) (f k (w, a))) (tomlistd S t).
  Proof.
    intros. unfold tomlistd. apply tomlistd_gen_mbindd.
  Qed.

End DTM_tolist.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈md t" :=
    (tomsetd _ t x) (at level 50) : tealeaves_multi_scope.

  Notation "x ∈m t" :=
    (tomset _ t x) (at level 50) : tealeaves_multi_scope.

End Notations.

Import Notations.

(** ** Relating <<∈m>> and <<∈md>> *)
(******************************************************************************)
Section DTM_membership_lemmas.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma ind_iff_in : forall (k : K) (A : Type) (a : A) (t : S A),
      (k, a) ∈m t <-> exists w, (w, (k, a)) ∈md t.
  Proof.
    intros. unfold tomset, tomsetd, tomlist, compose.
    induction (tomlistd S t).
    - cbv; split; intros []; easy.
    - rewrite fmap_list_cons, in_list_cons. rewrite IHl.
      setoid_rewrite in_list_cons.
      split; [ intros [Hfst|[w Hrest]] | intros [w [rest1|rest2]]].
      + destruct a0 as [w [k' a']]. exists w. left.
        rewrite Hfst. easy.
      + exists w. now right.
      + left. now rewrite <- rest1.
      + right. rewrite <- IHl.
        rewrite (in_fmap_iff list). now exists (w, (k, a)).
  Qed.

  Corollary ind_implies_in : forall (k : K) (A : Type) (a : A) (w : W) (t : S A),
      (w, (k, a)) ∈md t -> (k, a) ∈m t.
  Proof.
    intros. rewrite ind_iff_in. eauto.
  Qed.

End DTM_membership_lemmas.

(** ** Characterizing occurrences post-operation *)
(******************************************************************************)
Section DTM_membership.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Occurrences in <<mret>> *)
  (******************************************************************************)
  Lemma ind_mret_iff : forall (A : Type) (a1 a2 : A) (k1 k2 : K) (w : W),
      (w, (k2, a2)) ∈md mret T k1 a1 <-> w = Ƶ /\ k1 = k2 /\ a1 = a2.
  Proof.
    intros. rewrite (tomsetd_mret (T k1)).
    simpl_set. split.
    - inversion 1; now subst.
    - introv [? [? ?]]. now subst.
  Qed.

  Corollary in_mret_iff : forall (A : Type) (a1 a2 : A) (k1 k2 : K),
      (k2, a2) ∈m mret T k1 a1 <-> k1 = k2 /\ a1 = a2.
  Proof.
    intros. rewrite ind_iff_in. setoid_rewrite ind_mret_iff.
    firstorder.
  Qed.

  (** *** Occurrences in <<mbindd>> with context *)
  (******************************************************************************)
  Lemma ind_mbindd_iff1 :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbindd S f t ->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold tomsetd, compose in *.
    rewrite (tomlistd_mbindd S) in hyp. induction (tomlistd S t).
    - inversion hyp.
    - destruct a as [w [k a]]. rewrite mbinddt_list_cons in hyp.
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
  Qed.

  Lemma ind_mbindd_iff2 :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
    (exists (k1 : K) (w1 w2 : W) (a : A),
      (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2) ->
      (wtotal, (k2, b)) ∈md mbindd S f t.
  Proof.
    introv [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]. subst.
    unfold tomsetd, compose in *. rewrite (tomlistd_mbindd S).
    induction (tomlistd S t).
    - inversion hyp1.
    - destruct a0 as [w [k' a']]. rewrite mbinddt_list_cons.
      simpl_list. rewrite in_list_cons in hyp1. destruct hyp1 as [hyp1 | hyp1].
      + inverts hyp1. left. rewrite (in_fmap_iff list). exists (w2, (k2, b)).
        now splits.
      + right. now apply IHl in hyp1.
  Qed.

  Theorem ind_mbindd_iff :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbindd S f t <->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using ind_mbindd_iff1, ind_mbindd_iff2.
  Qed.

  Corollary ind_mbind_iff :
    forall `(f : forall k, A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbind S f t <->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 a
        /\ wtotal = w1 ● w2.
  Proof.
    intros. rewrite mbind_to_mbindd. apply ind_mbindd_iff.
  Qed.

  Corollary ind_mfmapd_iff :
    forall `(f : forall k, W * A -> B) (t : S A) (k : K) (w : W) (b : B),
      (w, (k, b)) ∈md mfmapd S f t <->
      exists (a : A), (w, (k, a)) ∈md t /\ b = f k (w, a).
  Proof.
    intros. unfold mfmapd, compose. setoid_rewrite ind_mbindd_iff.
    unfold_ops @Fmap_I. setoid_rewrite ind_mret_iff.
    split.
    - intros [k1 [w1 [w2 [a [hyp1 [[hyp2 [hyp2' hyp2'']] hyp3]]]]]].
      subst. exists a. simpl_monoid. auto.
    - intros [a [hyp1 hyp2]]. subst. repeat eexists.
      easy. now simpl_monoid.
  Qed.

  Corollary ind_mfmap_iff :
    forall `(f : K -> A -> B) (t : S A) (k : K) (w : W) (b : B),
      (w, (k, b)) ∈md mfmap S f t <->
      exists (a : A), (w, (k, a)) ∈md t /\ b = f k a.
  Proof.
    intros.
  Abort.

  (** *** Occurrences without context *)
  (******************************************************************************)
  Corollary in_mbindd_iff :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (b : B),
      (k2, b) ∈m mbindd S f t <->
      exists (k1 : K) (w1 : W) (a : A),
        (w1, (k1, a)) ∈md t
        /\ (k2, b) ∈m (f k1 (w1, a)).
  Proof.
    intros.
    rewrite ind_iff_in. setoid_rewrite ind_mbindd_iff. split.
    - intros [wtotal [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]].
      exists k1 w1 a. split; [auto|].
      apply (ind_implies_in) in hyp2. auto.
    - intros [k1 [w1 [a [hyp1 hyp2]]]].
      rewrite ind_iff_in in hyp2. destruct hyp2 as [w2 rest].
      exists (w1 ● w2) k1 w1 w2 a. intuition.
  Qed.

  Corollary in_mbind_iff :
    forall `(f : forall k, A -> T k B) (t : S A) (k2 : K) (b : B),
      (k2, b) ∈m mbind S f t <->
      exists (k1 : K) (a : A), (k1, a) ∈m t /\ (k2, b) ∈m f k1 a.
  Proof.
    intros. unfold mbind, compose. setoid_rewrite ind_iff_in.
    setoid_rewrite ind_mbindd_iff. cbn. split.
    - firstorder.
    - intros [k1 [a [[w1 hyp1] [w hyp2]]]].
      repeat eexists; eauto.
  Qed.

  Corollary in_mfmapd_iff :
    forall `(f : forall k, W * A -> B) (t : S A) (k : K) (b : B),
      (k, b) ∈m mfmapd S f t <->
      exists (w : W) (a : A), (w, (k, a)) ∈md t /\ b = f k (w, a).
  Proof.
    intros. setoid_rewrite ind_iff_in.
    now setoid_rewrite ind_mfmapd_iff.
  Qed.

  Corollary in_mfmap_iff :
    forall `(f : forall k, A -> B) (t : S A) (k : K) (b : B),
      (k, b) ∈m mfmap S f t <->
      exists (a : A), (k, a) ∈m t /\ b = f k a.
  Proof.
    intros. setoid_rewrite ind_iff_in.
    Fail now setoid_rewrite ind_mfmap_iff.
  Abort.

End DTM_membership.
