From Tealeaves Require Export
     Classes.Applicative
     Classes.ListableFunctor.

From Multisorted Require Import
     Classes.DTM
     Functors.Schedule
     Theory.DTMContainer.

Import Applicative.Notations.
Import Functors.Sets.Notations.
Import List.ListNotations.
Import Product.Notations.
Import Multisorted.Theory.Category.Notations.
Import Multisorted.Functors.Schedule.Notations.
Import Multisorted.Theory.DTMContainer.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.
#[local] Open Scope list_scope.

(** * Iterating over a DTM *)
(******************************************************************************)
Section schedule_operation.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Definition schedule {A : Type} (B : Type) : forall (k : K), W * A -> @Schedule _ T W A B (T k B) :=
    fun k '(w, a) => Go (@id (T k B)) ⧆ (w, a).
  Definition iterate {A : Type} (B : Type) : S A -> @Schedule _ T W A B (S B) :=
    mbinddt S (@Schedule _ T W A B) (schedule B).

End schedule_operation.

(** ** Representing <<mbinddt>> with <<runSchedule>> *)
(******************************************************************************)

Section iterate.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Theorem mbinddt_to_runSchedule :
    forall `{Applicative F} (A B : Type) (t : S A)
      (f : forall k, W * A -> F (T k B)),
      mbinddt S F f t = runSchedule f (iterate S B t).
  Proof.
    intros. unfold iterate.
    compose near t on right.
    rewrite (dtp_mbinddt_morphism W S T Schedule F).
    fequal. ext k [w a]. cbn.
    now rewrite ap1.
  Qed.

  Corollary mbindd_to_runSchedule :
    forall (A B : Type) (t : S A)
      (f : forall k, W * A -> T k B),
      mbindd S f t = runSchedule (F := fun A => A) f (iterate S B t).
  Proof.
    intros. rewrite mbindd_to_mbinddt. now rewrite mbinddt_to_runSchedule.
  Qed.

  Corollary mbindt_to_runSchedule :
    forall `{Applicative F} (A B : Type) (t : S A)
      (f : forall k, A -> F (T k B)),
      mbindt S F f t = runSchedule (f ◻ const (extract (W ×))) (iterate S B t).
  Proof.
    intros. rewrite mbindt_to_mbinddt. now rewrite mbinddt_to_runSchedule.
  Qed.

  Corollary mfmapdt_to_runSchedule  :
    forall `{Applicative F} (A B : Type) (t : S A)
      `(f : K -> W * A -> F B),
      mfmapdt S F f t = runSchedule (fun k => fmap F (mret T k) ∘ f k) (iterate S B t).
  Proof.
    intros. rewrite mfmapdt_to_mbinddt. now rewrite mbinddt_to_runSchedule.
  Qed.

  Corollary mbind_to_runSchedule :
    forall (A B : Type) (t : S A)
      (f : forall k, A -> T k B),
      mbind S f t = runSchedule (F := fun A => A) (f ◻ const (extract (W ×))) (iterate S B t).
  Proof.
    intros. rewrite mbind_to_mbinddt. now rewrite mbinddt_to_runSchedule.
  Qed.

  Corollary mfmapd_to_runBatch `(f : K -> W * A -> B) (t : S A) :
    mfmapd S f t = runSchedule (F := fun A => A) (mret T ◻ f) (iterate S B t).
  Proof.
    rewrite mfmapd_to_mbinddt. now rewrite mbinddt_to_runSchedule.
  Qed.

  Corollary mfmapt_to_runBatch `{Applicative F} `(f : K -> A -> F B) (t : S A) :
    mfmapt S F f t = runSchedule (fun k => fmap F (mret T k) ∘ f k ∘ extract (W ×)) (iterate S B t).
  Proof.
    rewrite mfmapt_to_mbinddt. now rewrite mbinddt_to_runSchedule.
  Qed.

  Corollary mfmap_to_runBatch `(f : K -> A -> B) (t : S A) :
    mfmap S f t = runSchedule (F := fun A => A) (mret T ◻ f ◻ const (extract (W ×))) (iterate S B t).
  Proof.
    rewrite mfmap_to_mbinddt. now rewrite mbinddt_to_runSchedule.
  Qed.

  (** ** Identities for <<tolist>> and <<foldMap>> *)
  (******************************************************************************)
  Lemma tomlistd_gen_to_runSchedule (fake : Type) `(t : S A) :
    tomlistd_gen S fake t = runSchedule (fun k '(w, a) => [(w, (k, a))]) (iterate S fake t).
  Proof.
    unfold tomlistd_gen. now rewrite mfmapdt_to_runSchedule.
  Qed.

  Lemma tomlistd_to_runSchedule  (fake : Type) `(t : S A) :
    tomlistd S t = runSchedule (fun k '(w, a) => [(w, (k, a))]) (iterate S fake t).
  Proof.
    unfold tomlistd. rewrite (tomlistd_equiv S False fake).
    now rewrite tomlistd_gen_to_runSchedule.
  Qed.

  Lemma tomsetd_to_runSchedule  (fake : Type) `(t : S A) :
    tomsetd S t = runSchedule (F := (@const Type Type (set (W * (K * A)))))
                              (fun k '(w, a) => {{(w, (k, a))}}) (iterate S fake t).
  Proof.
    unfold tomsetd, compose. rewrite (tomlistd_to_runSchedule fake).
    change (toset list (A := W * (K * A))) with (const (toset (A := W * (K * A)) list) (S fake)).
    cbn. (* <- needed for implicit arguments. *)
    rewrite (runSchedule_morphism (F := const (list (W * (K * A)))) (G := const (set (W * (K * A))))).
    unfold compose. fequal. ext k [w a].
    solve_basic_set.
  Qed.

  Lemma tomlist_to_runSchedule (fake : Type) `(t : S A) :
    tomlist S t = runSchedule (fun k '(w, a) => [(k, a)]) (iterate S fake t).
  Proof.
    unfold tomlist. unfold compose. rewrite (tomlistd_to_runSchedule fake).
    change (fmap list ?f) with (const (fmap list f) (S fake)).
    rewrite (runSchedule_morphism (F := const (list (W * (K * A))))
                                  (G := const (list (K * A)))
                                  (ψ := const (fmap list (extract (prod W))))).
    fequal. now ext k [w a].
  Qed.

  (** ** Other identities *)
  (******************************************************************************)
  Lemma id_to_runBatch `(t : S A) :
    t = runSchedule (F := fun A => A) (mret T ◻ const (extract (W ×))) (iterate S A t).
  Proof.
    change t with (id t) at 1.
    rewrite <- (dtp_mbinddt_mret W S T).
    rewrite mbinddt_to_runSchedule.
    reflexivity.
  Qed.

End iterate.

(** ** Respectfulness for <<mbindd>> *)
(******************************************************************************)
Section mbindd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Theorem mbindd_respectful :
    forall A B (t : S A) (f g : forall k, W * A -> T k B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k (w, a))
      -> mbindd S f t = mbindd S g t.
  Proof.
    introv hyp.
    rewrite (tomsetd_to_runSchedule S B t) in hyp.
    do 2 rewrite (mbindd_to_runSchedule S).
    induction (iterate S B t).
    - easy.
    - destruct p. do 2 rewrite runSchedule_rw2.
      rewrite runSchedule_rw2 in hyp.
      fequal.
      + apply IHs. intros. apply hyp.
        cbn. now left.
      + apply hyp. now right.
  Qed.

  (** *** For equalities with special cases *)
  (** Corollaries with conclusions of the form <<mbindd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mbindd_respectful_mbind :
    forall A B (t : S A) (f : forall k, W * A -> T k B) (g : forall k, A -> T k B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k a)
      -> mbindd S f t = mbind S g t.
  Proof.
    introv hyp. rewrite mbind_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_mfmapd :
    forall A B (t : S A) (f : forall k, W * A -> T k B) (g : K -> W * A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k (g k (w, a)))
      -> mbindd S f t = mfmapd S g t.
  Proof.
    introv hyp. rewrite mfmapd_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_mfmap :
    forall A B (t : S A) (f : forall k, W * A -> T k B) (g : K -> A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k (g k a))
      -> mbindd S f t = mfmap S g t.
  Proof.
    introv hyp. rewrite mfmap_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_id :
    forall A (t : S A) (f : forall k, W * A -> T k A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k a)
      -> mbindd S f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mbindd_id S).
    eapply mbindd_respectful.
    unfold compose; cbn. auto.
  Qed.

End mbindd_respectful.

(** ** Respectfulness for <<mbindd>> *)
(******************************************************************************)
Section mbind_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mbind_respectful :
    forall A B (t : S A) (f g : forall k, A -> T k B),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = g k a)
      -> mbind S f t = mbind S g t.
  Proof.
    introv hyp. rewrite mbind_to_mbindd.
    apply mbindd_respectful. introv premise. apply ind_implies_in in premise.
    unfold compose; cbn. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mbind t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mbind_respectful_mfmapd :
    forall A B (t : S A) (f : forall k, A -> T k B) (g : K -> W * A -> B),
      (forall (k : K) (w : W) (a : A), (w, (k, a)) ∈md t -> f k a = mret T k (g k (w, a)))
      -> mbind S f t = mfmapd S g t.
  Proof.
    intros. rewrite mfmapd_to_mbindd.
    symmetry. apply mbindd_respectful_mbind.
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary mbind_respectful_mfmap :
    forall A B (t : S A) (f : forall k, A -> T k B) (g : K -> A -> B),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = mret T k (g k a))
      -> mbind S f t = mfmap S g t.
  Proof.
    intros. rewrite mfmap_to_mbind.
    symmetry. apply mbind_respectful.
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary mbind_respectful_id : forall A (t : S A) (f : forall k, A -> T k A),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = mret T k a)
      -> mbind S f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mbind_id S).
    eapply mbind_respectful.
    unfold compose; cbn. auto.
  Qed.

End mbind_respectful.

(** ** Respectfulness for <<mfmapd>> *)
(******************************************************************************)
Section mfmapd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mfmapd_respectful :
    forall A B (t : S A) (f g : K -> W * A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k (w, a))
      -> mfmapd S f t = mfmapd S g t.
  Proof.
    introv hyp. do 2 rewrite mfmapd_to_mbindd.
    apply mbindd_respectful. introv premise.
    unfold compose; cbn. fequal. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mfmapd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mfmapd_respectful_mfmap :
    forall A (t : S A) (f : K -> W * A -> A) (g : K -> A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k a)
      -> mfmapd S f t = mfmap S g t.
  Proof.
    intros. rewrite mfmap_to_mfmapd.
    apply mfmapd_respectful. introv Hin.
    unfold compose; cbn; auto.
  Qed.

  Corollary mfmapd_respectful_id : forall A (t : S A) (f g : K -> W * A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = a)
      -> mfmapd S f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mfmapd_id S).
    eapply mfmapd_respectful.
    cbn. auto.
  Qed.

End mfmapd_respectful.

(** ** Respectfulness for <<mfmap>> *)
(******************************************************************************)
Section mfmap_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mfmap_respectful :
    forall A B (t : S A) (f g : K -> A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k a = g k a)
      -> mfmap S f t = mfmap S g t.
  Proof.
    introv hyp. do 2 rewrite mfmap_to_mfmapd.
    now apply mfmapd_respectful.
  Qed.

  Corollary mfmap_respectful_id :
    forall A (t : S A) (f : K -> A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k a = a)
      -> mfmap S f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mfmap_id S).
    eapply mfmap_respectful.
    auto.
  Qed.

End mfmap_respectful.

(** ** Respectfulness for <<kbindd>> *)
(******************************************************************************)
Section kbindd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Lemma kbindd_respectful :
    forall A (t : S A) (f g : W * A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g (w, a))
      -> kbindd S j f t = kbindd S j g t.
  Proof.
    introv hyp. unfold kbindd. apply mbindd_respectful.
    introv premise. compare values j and k.
    - do 2 rewrite btgd_eq. auto.
    - do 2 (rewrite btgd_neq; auto).
  Qed.

  (** *** For equalities with special cases *)
  (******************************************************************************)
  Corollary kbindd_respectful_kbind :
    forall A (t : S A) (f : W * A -> T j A) (g : A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g a)
      -> kbindd S j f t = kbind S j g t.
  Proof.
    introv hyp. rewrite kbind_to_kbindd.
    apply kbindd_respectful. introv Hin.
    apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_kfmapd :
    forall A (t : S A) (f : W * A -> T j A) (g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j (g (w, a)))
      -> kbindd S j f t = kfmapd S j g t.
  Proof.
    introv hyp. rewrite kfmapd_to_kbindd.
    apply kbindd_respectful. introv Hin.
    apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_kfmap :
    forall A (t : S A) (f : W * A -> T j A) (g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j (g a))
      -> kbindd S j f t = kfmap S j g t.
  Proof.
    introv hyp. rewrite kfmap_to_kfmapd.
    apply kbindd_respectful_kfmapd.
    introv Hin. apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_id :
    forall A (t : S A) (f : W * A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j a)
      -> kbindd S j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    erewrite <- (kbindd_id S).
    apply kbindd_respectful.
    auto.
  Qed.

End kbindd_respectful.

(** ** Respectfulness for mixed structures *)
(******************************************************************************)
Section mixed_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Corollary kbind_respectful_kfmapd :
    forall A (t : S A) (f : A -> T j A) (g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = mret T j (g (w, a)))
      -> kbind S j f t = kfmapd S j g t.
  Proof.
    introv hyp. rewrite kfmapd_to_kbindd.
    rewrite kbind_to_kbindd. apply kbindd_respectful.
    introv Hin. apply hyp. auto.
  Qed.

End mixed_respectful.

(** ** Respectfulness for <<kbind>> *)
(******************************************************************************)
Section kbindd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Lemma kbind_respectful :
    forall A (t : S A) (f g : A -> T j A),
      (forall (a : A), (j, a) ∈m t -> f a = g a)
      -> kbind S j f t = kbind S j g t.
  Proof.
    introv hyp. unfold kbind. apply mbind_respectful.
    introv premise. compare values j and k.
    - do 2 rewrite btg_eq. auto.
    - do 2 (rewrite btg_neq; auto).
  Qed.

  (** *** For equalities with special cases *)
  (******************************************************************************)
  Corollary kbind_respectful_kfmap :
    forall A (t : S A) (f : A -> T j A) (g : A -> A),
      (forall (a : A), (j, a) ∈m t -> f a = mret T j (g a))
      -> kbind S j f t = kfmap S j g t.
  Proof.
    introv hyp. rewrite kfmap_to_kbind.
    apply kbind_respectful.
    introv Hin. apply hyp. auto.
  Qed.

  Corollary kbind_respectful_id :
    forall A (t : S A) (f : A -> T j A),
      (forall (a : A), (j, a) ∈m t -> f a = mret T j a)
      -> kbind S j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kbind_id S (j := j)).
    now apply kbind_respectful.
  Qed.

End kbindd_respectful.

(** ** Respectfulness for <<kfmapd>> *)
(******************************************************************************)
Section kfmapd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Lemma kfmapd_respectful :
    forall A (t : S A) (f g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g (w, a))
      -> kfmapd S j f t = kfmapd S j g t.
  Proof.
    introv hyp. unfold kfmapd.
    apply mfmapd_respectful. introv premise.
    compare values j and k.
    - do 2 rewrite tgtd_eq. auto.
    - do 2 (rewrite tgtd_neq; auto).
  Qed.

  (** *** For equalities with other operations *)
  (******************************************************************************)
  Corollary kfmapd_respectful_kfmap :
    forall A (t : S A) (f : W * A -> A) (g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g a)
      -> kfmapd S j f t = kfmap S j g t.
  Proof.
    introv hyp. rewrite kfmap_to_kfmapd.
    apply kfmapd_respectful. auto.
  Qed.

  Corollary kfmapd_respectful_id : forall A (t : S A) (f : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = a)
      -> kfmapd S j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kfmapd_id (j := j) S).
    apply kfmapd_respectful. auto.
  Qed.

End kfmapd_respectful.

(** ** Respectfulness for <<kfmap>> *)
(******************************************************************************)
Section kfmap_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Lemma kfmap_respectful :
    forall A (t : S A) (f g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = g a)
      -> kfmap S j f t = kfmap S j g t.
  Proof.
    introv hyp. unfold kfmap. apply mfmap_respectful.
    introv premise. compare values j and k.
    - autorewrite with tea_tgt. eauto.
    - autorewrite with tea_tgt_neq. auto.
  Qed.

  Corollary kfmap_respectful_id :
    forall A (t : S A) (f : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = a)
      -> kfmap S j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kfmap_id (j := j) S).
    apply kfmap_respectful. auto.
  Qed.

End kfmap_respectful.
