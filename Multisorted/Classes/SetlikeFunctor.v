From Multisorted Require Import
     Classes.Functor
     Classes.DecoratedFunctor
     Functors.MSets
     Functors.Row.

Import Classes.Monoid.Notations.
Import Theory.Product.Notations.
Import Multisorted.Category.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

(** * The [tomset] operation *)
(******************************************************************************)
Class Tomset `{ix : Index} (F : Type -> Type) :=
  tomset : forall (A : Type), F A -> mset A.

Arguments tomset {ix} F%function_scope {Tomset} {A}%type_scope _ _.

#[local] Notation "x ∈m t" :=
  (tomset _ t x) (at level 50) : tealeaves_multi_scope.

(** * Typeclasses for set-like functors *)
(******************************************************************************)
Section SetlikeMultisortedFunctor.

  Context
    `{ix : Index}
    (F : Type -> Type) `{! MFmap F} `{! Tomset F}.

  Class SetlikeMultisortedFunctor :=
    { qmfun_functor :> MultisortedFunctor F;
      qmfun_natural :> MultisortedNatural (@tomset ix F _);
      qmfun_respectful : forall A B (t : F A) (f g : A -k-> B),
          (forall k a, (k, a) ∈m t -> f k a = g k a) -> mfmap F f t = mfmap F g t
    }.

  Class MSetPreservingTransformation
        {F G : Type -> Type}
        `{! MFmap F} `{! Tomset F}
        `{! MFmap G} `{! Tomset G}
        (η : forall A, F A -> G A) :=
    { qtrans_natural : MultisortedNatural η;
      qtrans_commute : forall A, tomset F = tomset G ∘ η A;
    }.

End SetlikeMultisortedFunctor.

(** * Notations and tactics *)
(******************************************************************************)
Ltac preimage t name :=
  match type of t with
  | mfmap mset ?f ?s ?x =>
    let hyp1 := fresh "img_in_" name in
    let hyp2 := fresh "img_eq_" name in
    destruct (proj1 preimage_fmap t) as [name [hyp1 hyp2]]
  | _ => fail "Not of the right form"
  end.

(** * Theory of multisorted set-like functors *)
(******************************************************************************)
Section SetlikeMultisortedFunctor_theory.

  Context
    (F : Type -> Type)
    `{SetlikeMultisortedFunctor F}.

  (** ** Respectfulness conditions for <<mfmap>> *)
  (******************************************************************************)
  Corollary mfmap_proper_id : forall A (t : F A) (f : A -k-> A),
      (forall k a, (k, a) ∈m t -> f k a = a) -> mfmap F f t = t.
  Proof.
    intros. replace t with (mfmap F kid t) at 2
      by now (rewrite (mfun_mfmap_id F)).
    now apply (qmfun_respectful F).
  Qed.

  (** ** Respectfulness conditions for <<fmapk>> *)
  (******************************************************************************)
  Corollary fmapk_respectful : forall A (t : F A) k (f g : A -> A),
      (forall a, (k, a) ∈m t -> f a = g a) -> fmapk F k f t = fmapk F k g t.
  Proof.
    intros. unfold fmapk. apply (qmfun_respectful F).
    intros j ? ?. compare values k and j;
                    simpl_tgt_fallback; auto.
  Qed.

  Corollary fmapk_respectful_id : forall A k (t : F A) (f : A -> A),
      (forall a, (k, a) ∈m t -> f a = a) -> fmapk F k f t = t.
  Proof.
    intros. replace t with (fmapk F k id t) at 2
      by now rewrite (fmapk_id F).
    now apply fmapk_respectful.
  Qed.

  (** ** Interaction between [tomset] and [mfmap] *)
  (******************************************************************************)
  Theorem in_mfmap_iff {A B} : forall (k : K) (t : F A) (b : B) (f : K -> A -> B),
      (k, b) ∈m mfmap F f t <-> exists a, (k, a) ∈m t /\ f k a = b.
  Proof.
    intros ? t ? f. compose near t on left.
    rewrite <- (mnaturality f). unfold compose.
    now rewrite preimage_fmap.
  Qed.

  Corollary in_mfmap_mono {A B} : forall (k : K) (t : F A)(a : A) (f : K -> A -> B),
      (k, a) ∈m t -> (k, f k a) ∈m mfmap F f t.
  Proof.
    intros ? ? a ? hyp. rewrite in_mfmap_iff. now exists a.
  Qed.

  (** ** Interaction between [tomset] and [fmapk] *)
  (******************************************************************************)
  Theorem in_fmapk_eq_iff {A} : forall k b (t : F A) (f : A -> A),
      (k, b) ∈m fmapk F k f t <-> exists a, (k, a) ∈m t /\ f a = b.
  Proof.
    introv. unfold fmapk. rewrite in_mfmap_iff.
    now autorewrite* with tea_tgt.
  Qed.

  Theorem in_fmapk_neq_iff {A} : forall k1 k2 b (t : F A) (f : A -> A),
      k1 <> k2 ->
      (k2, b) ∈m fmapk F k1 f t <-> (k2, b) ∈m t.
  Proof.
    intros ? ? b ? ? neq. unfold fmapk.
    rewrite in_mfmap_iff. autorewrite with tea_tgt. split.
    - intros [? [? ?]]; now subst.
    - intros ?. now (exists b).
  Qed.

  Corollary in_fmapk_mono_eq {A} : forall k t a (f : A -> A),
      (k, a) ∈m t -> (k, f a) ∈m fmapk F k f t.
  Proof.
    intros ? ? a ? hyp. unfold fmapk.
    rewrite in_mfmap_iff. autorewrite* with tea_tgt.
    now exists a.
  Qed.

End SetlikeMultisortedFunctor_theory.

(** * Theory of decorated multisorted set-like functors *)
(******************************************************************************)

(** ** Derived operation <<tomsetd>> *)
(******************************************************************************)
Definition tomsetd (F : Type -> Type) `{Tomset F} `{Decorate W F} {A} :
  F A -> mset (W * A) := tomset F ∘ decorate F.

#[local] Notation "x ∈md t" :=
  (tomsetd _ t x) (at level 50) : tealeaves_multi_scope.

(** ** Corollaries of respectfulness *)
(******************************************************************************)
Section DecoratedSetlikeMultisortedFunctor_respectfulness.

  Context
    (F : Type -> Type)
    `{SetlikeMultisortedFunctor F}
    `{! Decorate W F} `{! DecoratedMultisortedFunctor W F}.

  (** *** Parallel context-sensitive maps *)
  (******************************************************************************)
  Lemma mfmapd_respectful {A B} : forall (t : F A) (f g : W * A -k-> B),
      (forall k w a, (k, (w, a)) ∈md t -> f k (w, a) = g k (w, a)) ->
      mfmapd F f t = mfmapd F g t.
  Proof.
    intros. apply (qmfun_respectful F).
    intros ? [? ?]; auto.
  Qed.

  Corollary mfmapd_respectful_id {A} : forall (t : F A) (f : W * A -k-> A),
      (forall k w a, (k, (w, a)) ∈md t -> f k (w, a) = a) ->
      mfmapd F f t = t.
  Proof.
    intros. replace t with (mfmapd F (const snd) t) at 2
      by (now rewrite (mfmapd_id F)).
    now apply mfmapd_respectful.
  Qed.

  (** *** Targeted context-sensitive maps *)
  (******************************************************************************)
  Lemma fmapkd_respectful {A} : forall k (t : F A) (f g : W * A -> A),
      (forall w a, (k, (w, a)) ∈md t -> f (w, a) = g (w, a)) ->
      fmapkd F k f t = fmapkd F k g t.
  Proof.
    intros. unfold fmapkd. apply mfmapd_respectful.
    intros j ? ? ?. compare values k and j;
                      simpl_tgt_fallback; auto.
  Qed.

  Corollary fmapkd_respectful_id {A} : forall k (t : F A) (f : W * A -> A),
      (forall w a, (k, (w, a)) ∈md t -> f (w, a) = a) -> fmapkd F k f t = t.
  Proof.
    intros. replace t with (fmapkd F k snd t) at 2
      by (now rewrite (fmapkd_id F)).
    now apply fmapkd_respectful.
  Qed.

End DecoratedSetlikeMultisortedFunctor_respectfulness.

(** ** Theory of [tomsetd] and [mfmapd] *)
(******************************************************************************)
Section DecoratedSetlikeMultisortedFunctor_theory.

  Context
    (F : Type -> Type)
    `{SetlikeMultisortedFunctor F}
    `{! Decorate W F} `{! DecoratedMultisortedFunctor W F}
    `{Monoid W}.

  (* put these into their own section so the types can be generalized
     and used to prove corollaries *)
  Section central_results.

    Context
      {A B : Type}.

    Implicit Types (w : W) (a : A) (b : B) (k : K) (t : F A).

    (** ** Interaction between [tomsetd] and [mfmapd] *)
    (******************************************************************************)
    Theorem ind_mfmapd_iff : forall k w b t (f : W * A -k-> B),
        (k, (w, b)) ∈md mfmapd F f t <->
        exists (a : A), (k, (w, a)) ∈md t /\ f k (w, a) = b.
    Proof.
      intros ? w ? t ?.  unfold tomsetd.
      compose near t on left.
      reassociate -> on left.
      rewrite (dec_mfmapd F).
      unfold compose, mfmapd, compose.
      rewrite (in_mfmap_iff F). split; intro hyp.
      - destruct hyp as [[? a] [? heq]]. inverts heq. now (exists a).
      - destruct hyp as [a [? heq]]. inverts heq. now exists (w, a).
    Qed.

    Theorem ind_mfmapd_mono : forall k w a t (f : W * A -k-> B),
        (k, (w, a)) ∈md t ->
        (k, (w, f k (w, a))) ∈md mfmapd F f t.
    Proof.
      intros ? w a t f hyp. unfold tomsetd. compose near t.
      reassociate ->. rewrite (dec_mfmapd F f).
      unfold compose, mfmapd, compose.
      rewrite (in_mfmap_iff F). now exists (w, a).
    Qed.

    (** ** Theorems relating [tomset] and [tomsetd] *)
    (******************************************************************************)
    Theorem in_in_extract : forall k w a (t : F (W * A)),
        (k, (w, a)) ∈m t -> (k, a) ∈m mfmap F (const (extract (W ×))) t.
    Proof.
      intros ? w a ? hyp. apply (in_mfmap_iff F). now exists (w, a).
    Qed.

    Theorem in_of_ind : forall k w a t,
        (k, (w, a)) ∈md t -> (k, a) ∈m t.
    Proof.
      intros ? w a t hyp. replace t with (mfmap F (const (extract (W ×))) (decorate F t)).
      rewrite (in_mfmap_iff F). now (exists (w, a)).
      compose near t on left.
      now rewrite (decf_dec_extract W).
    Qed.

    Theorem ind_of_in : forall (t : F A) k a,
        (k, a) ∈m t <-> exists w, (k, (w, a)) ∈md t.
    Proof.
      intros t k a. split; intro hyp.
      - replace t with (mfmap F (const (extract (W ×))) (decorate F t)) in hyp
          by (now compose near t on left; rewrite (decf_dec_extract W)).
        rewrite (in_mfmap_iff F) in hyp. destruct hyp as [[w ?] [? heq]].
        inverts heq. now (exists w).
      - destruct hyp as [? hyp]. now apply in_of_ind in hyp.
    Qed.

    (** ** Interaction between [tomsetd] and [mfmap] *)
    (******************************************************************************)
    Corollary ind_mfmap_iff : forall k w b t f,
        (k, (w, b)) ∈md mfmap F f t <->
        exists a, (k, (w, a)) ∈md t /\ f k a = b.
    Proof.
      intros k w ? t f. rewrite (mfmap_to_mfmapd F).
      assert (rw : forall a, f k a = (f ⊙ const snd) k (w, a))
        by now introv.
      setoid_rewrite rw. apply ind_mfmapd_iff.
    Qed.

    Corollary ind_mfmap_mono : forall k w a t (f : A -k-> B),
        (k, (w, a)) ∈md t ->
        (k, (w, f k a)) ∈md mfmap F f t.
    Proof.
      intros k w a ? f. rewrite (mfmap_to_mfmapd F).
      change (f k a) with ((f ⊙ const snd) k (w, a)).
      apply ind_mfmapd_mono.
    Qed.

    (** ** Interaction between [tomset] and [mfmapd] *)
    (******************************************************************************)
    Corollary in_mfmapd_iff : forall k (b : B) (t : F A) f,
        (k, b) ∈m mfmapd F f t <->
        exists w a, (k, (w, a)) ∈md t /\ f k (w, a) = b.
    Proof.
      introv. unfold mfmapd, compose.
      rewrite (in_mfmap_iff F). split.
      - intros [[w a] [? ?]]. now (exists w a).
      - intros [w [a [? ?]]]. now exists (w, a).
    Qed.

    (** ** Interaction between [tomset] and [shift] *)
    (******************************************************************************)
    Theorem in_shift_iff {C} : forall k w w1 (a : C) (t : F (W * C)),
        (k, (w, a)) ∈m shift (w1, t) <->
        exists w2, (k, (w2, a)) ∈m t /\ w = w1 ● w2.
    Proof.
      intros ? ? w1 a ?. unfold shift, compose, mstrength.
      setoid_rewrite (in_mfmap_iff F). split.
      - intros [[? ?] [? ?]].
        preprocess. cbn in *. eauto.
      - intros [w2 [? ?]]. subst. eauto.
    Qed.

    Theorem in_shift_cobind_iff : forall k w b (f : W * A -> F (W * B)) (p : W * A),
        (k, (w, b)) ∈m shift (cobind (prod W) f p) <->
        exists w2, (k, (w2, b)) ∈m f p /\ w = (fst p) ● w2.
    Proof.
      introv. destruct p as [w1 a].
      change (cobind (prod W) f (w1, a)) with
          (w1, f (w1, a)).
      rewrite in_shift_iff.
      firstorder.
    Qed.

    Theorem in_shift_mono : forall k w1 w2 a (t : F (W * A)),
        (k, (w1, a)) ∈m t -> (k, (w2 ● w1, a)) ∈m shift (w2, t).
    Proof.
      introv hin. unfold shift.
      rewrite (in_mfmap_iff F). eauto.
    Qed.

  End central_results.

  Context
    {A B : Type}.

  Implicit Types (w : W) (a : A) (b : B) (k : K) (t : F A).

  (** ** Interaction between [tomset] and [fmapkd] *)
  (******************************************************************************)
  Corollary in_fmapkd_iff_eq : forall t a k (f : W * A -> A),
      (k, a) ∈m fmapkd F k f t <-> exists w a', (k, (w, a')) ∈md t /\ f (w, a') = a.
  Proof.
    intros ? ? k ?. unfold fmapkd.
    Set Printing Implicit.
    rewrite (in_mfmapd_iff k).
    now rewrite (tgtd_eq k).
  Qed.

  Corollary in_fmapkd_iff_neq : forall t a k k' (f : W * A -> A),
      k <> k' ->
      (k, a) ∈m fmapkd F k' f t <-> (k, a) ∈m t.
  Proof.
    intros ? a k ? ? ?. unfold fmapkd. rewrite (in_mfmapd_iff k).
    autorewrite with tea_tgt.
    rewrite (ind_of_in). split.
    - intros [w [? [? heq]]]. inverts heq. now (exists w).
    - intros [w ?]. now (exists w a).
  Qed.

  (** ** Interaction between [fmapkd] and [tomsetr] *)
  (******************************************************************************)
  Corollary ind_fmapkd_iff_eq : forall t (f : W * A -> A) w a k,
      (k, (w, a)) ∈md fmapkd F k f t <->
      exists (a' : A), (k, (w, a')) ∈md t /\ f (w, a') = a.
  Proof.
    intros ? ? ? ? k. unfold fmapkd.
    rewrite (ind_mfmapd_iff k).
    now rewrite tgtd_eq.
  Qed.

  Corollary ind_fmapkd_iff_neq : forall t (f : W * A -> A) w a k k',
      k' <> k ->
      (k, (w, a)) ∈md fmapkd F k' f t <-> (k, (w, a)) ∈md t.
  Proof.
    intros ? ? ? a k ? ?. unfold fmapkd. rewrite (ind_mfmapd_iff k).
    autorewrite with tea_tgt. cbn. split.
    intros [? [? heq]]. now inverts heq.
    now (exists a).
  Qed.

  Corollary ind_fmapkd_mono_eq : forall t w a k (f : W * A -> A),
      (k, (w, a)) ∈md t -> (k, (w, f (w, a))) ∈md fmapkd F k f t.
  Proof.
    intros ? w a k f. unfold fmapkd.
    replace (f (pair w a)) with (tgtd k f snd k (pair w a))
      by now autorewrite* with tea_tgt.
    auto using (ind_mfmapd_mono k).
  Qed.

  Corollary ind_fmapkd_mono_neq : forall t w a k k' (f : W * A -> A),
      k <> k' ->
      (k, (w, a)) ∈md t -> (k, (w, a)) ∈md fmapkd F k' f t.
  Proof.
    intros ? w a k k' f ? ?. unfold fmapkd.
    replace a with (tgtd k' f snd k (pair w a))
      by now autorewrite with tea_tgt.
    rewrite (ind_mfmapd_iff k). now (exists a).
  Qed.

End DecoratedSetlikeMultisortedFunctor_theory.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈m t" :=
    (tomset _ t x) (at level 50) : tealeaves_multi_scope.

  Notation "x ∈md t" :=
    (tomsetd _ t x) (at level 50) : tealeaves_multi_scope.

End Notations.
