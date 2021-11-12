From Tealeaves Require Export
     Monoid.

From Tealeaves.Multisorted Require Export
     Functors
     MSets
     Quantifiable
     MList
     Listable
     Decorated
     Properness.

(** Import notations *)
Import Monoid.Notations.
Import Multisorted.Category.Notations.
Import Multisorted.Functors.Notations.
Import Multisorted.Decorated.Notations.
Import Multisorted.Quantifiable.Notations.
Local Open Scope tealeaves_scope.
Local Open Scope tealeaves_multi_scope.

(** ** Notations module *)
(******************************************************************************)
Module Notations.

  Include Monoid.Notations.
  Include Multisorted.Category.Notations.
  Include Multisorted.Functors.Notations.
  Include Multisorted.Decorated.Notations.
  Include Multisorted.Quantifiable.Notations.

  Notation "x ∈mr t" :=
    (tomsetr _ t x) (at level 50) : tealeaves_multi_scope.

  Local Notation "x @ k ∈mr t" :=
    (tomsetr _ t (k, x)) (k at level 5, at level 50) : tealeaves_multi_scope.

End Notations.

Import Notations.

(** * Typeclasses for multisorted syntax functors *)
(** ** Syntax functors *)
(******************************************************************************)
Section syntax_functor_class.

  Context
    `{Index}
    (W : Type)
    (F : Type -> Type)
    {monoid_op : Monoid_op W}
    {monoid_unit : Monoid_unit W}
    `{! Mfmap F}
    `{Decorate (Row W) F}
    `{! Tomlist F}.

  Class SyntaxMFunctor : Type :=
    { synf_dec :> DecoratedMFunctor (Row W) F;
      synf_com :> ListableMFunctor F;
      synf_monoid : Monoid W;
    }.

End syntax_functor_class.

(** ** Syntax monads *)
(******************************************************************************)
Section syntax_monad_class.

  Context
    `{Index}
    (W : Type)
    {monoid_op : Monoid_op W}
    {monoid_unit : Monoid_unit W}
    (T : K -> Type -> Type)
    `{! Mreturn T}
    `{! forall k, Mbind (T k) T}
    `{forall k, Decorate (Row W) (T k)}
    `{! forall k, Tomlist (T k)}.

  Class SyntaxMMonad : Type :=
    { synm_dec :> DecoratedMMonad (Row W) T;
      synm_com :> ListableMMonad T;
      synm_monoid : Monoid W;
      synm_proper :> forall k, Mbind_proper (T k);
    }.

End syntax_monad_class.

(** ** Syntax modules *)
(******************************************************************************)
Section syntax_module_class.

  Context
    `{Index}
    (W : Type)
    (F : Type -> Type)
    (T : K -> Type -> Type)
    {monoid_op : Monoid_op W}
    {monoid_unit : Monoid_unit W}
    `{! Mreturn T}
    `{! forall k, Mbind (T k) T}
    `{forall k, Decorate (Row W) (T k)}
    `{! forall k, Tomlist (T k)}
    `{! Mbind F T}
    `{Decorate (Row W) F}
    `{! Tomlist F}.

  Class SyntaxModule : Type :=
    { synmod_dec :> DecoratedModule (Row W) F T;
      synmod_com :> ListableRightModule F T;
      synmod_monad :> SyntaxMMonad W T;
      synmod_proper :> Mbind_proper F;
    }.

  Existing Instance synm_monoid.

  #[global] Instance SyntaxMFunctor_module `{SyntaxModule} : SyntaxMFunctor W F.
  Proof.
    constructor; typeclasses eauto.
  Qed.

End syntax_module_class.

Section monad_to_module.

  Existing Instance synm_monoid.

  Instance SyntaxModule_Monad `{Hmon : SyntaxMMonad W T} k : SyntaxModule W (T k) T.
  Proof.
    constructor. all: try typeclasses eauto.
    - apply Decorated_Module_MMonad.
    - apply Listable_Module_MMonad.
  Qed.

End monad_to_module.

(** * Parallel maps over syntax functors, [fmapr] *)
(******************************************************************************)
Section syntax_functor_theory.

  Context
    (F : Type -> Type)
    `{SyntaxMFunctor W F}.

  (** ** Interaction between [tomsetr] and [fmapr] *)
  (******************************************************************************)
  Theorem inr_mfmapr_iff {A B} : forall k w b t (f : Row W * A -k-> B),
      (k, (w, b)) ∈mr mfmapr F f t <->
      exists (a : A), (k, (w, a)) ∈mr t /\ f k (w, a) = b.
  Proof.
    intros ? w ? t ?.  unfold tomsetr.
    compose near t on left.
    reassociate -> on left.
    rewrite (dec_mfmapr F).
    unfold compose, mfmapr, compose.
    rewrite (in_mfmap_iff F). split; intro hyp.
    - destruct hyp as [[? a] [? heq]]. inverts heq. now (exists a).
    - destruct hyp as [a [? heq]]. inverts heq. now exists (w, a).
  Qed.

  Theorem inr_mfmapr_mono {A B} : forall k w a t (f : Row W * A -k-> B),
      (k, (w, a)) ∈mr t ->
      (k, (w, f k (w, a))) ∈mr mfmapr F f t.
  Proof.
    intros ? w a t f hyp. unfold tomsetr. compose near t.
    reassociate ->. rewrite (dec_mfmapr F f).
    unfold compose, mfmapr, compose.
    rewrite (in_mfmap_iff F). now exists (w, a).
  Qed.

  Section corollaries.

    Context
      {A B : Type}.

    Implicit Types (w : Row W) (a : A) (b : B) (k : K) (t : F A).

    (** ** Corollaries: [tomsetr] and [fmap] *)
    (******************************************************************************)
    Corollary inr_mfmap_iff : forall k w b t f,
        (k, (w, b)) ∈mr mfmap F f t <->
        exists a, (k, (w, a)) ∈mr t /\ f k a = b.
    Proof.
      intros k w ? t f. rewrite (mfmap_to_mfmapr F).
      assert (rw : forall a, f k a = (f ⊙ const snd) k (w, a))
        by now introv.
      setoid_rewrite rw. apply inr_mfmapr_iff.
    Qed.

    Corollary inr_mfmap_mono : forall k w a t (f : A -k-> B),
        (k, (w, a)) ∈mr t ->
        (k, (w, f k a)) ∈mr mfmap F f t.
    Proof.
      intros k w a ? f. rewrite (mfmap_to_mfmapr F).
      change (f k a) with ((f ⊙ const snd) k (w, a)).
      apply inr_mfmapr_mono.
    Qed.

    (** ** Corollaries: [tomset] and [fmapr] *)
    (******************************************************************************)
    Corollary in_mfmapr_iff : forall k b t f,
        (k, b) ∈m mfmapr F f t <->
        exists w a, (k, (w, a)) ∈mr t /\ f k (w, a) = b.
    Proof.
      introv. unfold mfmapr, compose.
      rewrite (in_mfmap_iff F). split.
      - intros [[w a] [? ?]]. now (exists w a).
      - intros [w [a [? ?]]]. now exists (w, a).
    Qed.

    (** ** Interaction between [tomset] and [shift] *)
    (******************************************************************************)
    Theorem in_shift_iff {C} : forall k w w1 (a : C) (t : F (Row W * C)),
        (k, (w, a)) ∈m shift (w1, t) <->
        exists w2, (k, (w2, a)) ∈m t /\ w = w1 ● w2.
    Proof.
      intros ? ? w1 a ?. unfold shift, compose, Decorated.strength.
      setoid_rewrite (in_mfmap_iff F). split.
      - intros [[? ?] [? ?]].
        preprocess. cbn in *. eauto.
      - intros [w2 [? ?]]. subst. eauto.
    Qed.

    Theorem in_shift_cobind_iff : forall k w b (f : Row W * A -> F (Row W * B)) (p : Row W * A),
        (k, (w, b)) ∈m shift (cobind (prod (Row W)) f p) <->
        exists w2, (k, (w2, b)) ∈m f p /\ w = (fst p) ● w2.
    Proof.
      introv. destruct p as [w1 a].
      change (cobind (prod (Row W)) f (w1, a)) with
          (w1, f (w1, a)).
      rewrite in_shift_iff.
      firstorder.
    Qed.

    Theorem in_shift_mono : forall k w1 w2 a (t : F (Row W * A)),
        (k, (w1, a)) ∈m t -> (k, (w2 ● w1, a)) ∈m shift (w2, t).
    Proof.
      introv hin. unfold shift.
      rewrite (in_mfmap_iff F). eauto.
    Qed.

    (** ** Utility theorems *)
    (******************************************************************************)
    Theorem in_in_snd : forall k w a (t : F (Row W * A)),
        (k, (w, a)) ∈m t -> (k, a) ∈m mfmap F (const snd) t.
    Proof.
      intros ? w a ? hyp. apply (in_mfmap_iff F). now exists (w, a).
    Qed.

    Theorem in_of_inr : forall k w a t,
        (k, (w, a)) ∈mr t -> (k, a) ∈m t.
    Proof.
      intros ? w a t hyp. replace t with (mfmap F (const snd) (decorate F t)).
      rewrite (in_mfmap_iff F). now (exists (w, a)).
      compose near t on left.
      now rewrite (decf_read_proj (Row W)).
    Qed.

    Theorem inr_of_in : forall (t : F A) k a,
        (k, a) ∈m t <-> exists w, (k, (w, a)) ∈mr t.
    Proof.
      intros t k a. split; intro hyp.
      - replace t with (mfmap F (const snd) (decorate F t)) in hyp
          by (now compose near t on left; rewrite (decf_read_proj (Row W))).
        rewrite (in_mfmap_iff F) in hyp. destruct hyp as [[w ?] [? heq]].
        inverts heq. now (exists w).
      - destruct hyp as [? hyp]. now apply in_of_inr in hyp.
    Qed.

  End corollaries.

End syntax_functor_theory.

(** * Targeted maps over syntax functors, [fmaprk] *)
(******************************************************************************)
Section syntax_functor_targeted.

  Context
    (F : Type -> Type)
    `{SyntaxMFunctor W F}.

  (** ** Interaction between [fmapkr] and [tomsetr] *)
  (******************************************************************************)
  Corollary inr_fmapkr_iff_eq {A} : forall t (f : Row W * A -> A) w a k,
      (k, (w, a)) ∈mr fmapkr F k f t <->
      exists (a' : A), (k, (w, a')) ∈mr t /\ f (w, a') = a.
  Proof.
    intros ? ? ? ? k. unfold fmapkr.
    rewrite (inr_mfmapr_iff F k).
    now rewrite tgtd_eq.
  Qed.

  Corollary inr_fmapkr_iff_neq {A} : forall t (f : Row W * A -> A) w a k k',
      k' <> k ->
      (k, (w, a)) ∈mr fmapkr F k' f t <-> (k, (w, a)) ∈mr t.
  Proof.
    intros ? ? ? a k ? ?. unfold fmapkr. rewrite (inr_mfmapr_iff F k).
    autorewrite with tea_tgt. cbn. split.
    intros [? [? heq]]. now inverts heq.
    now (exists a).
  Qed.

  Corollary inr_fmapkr_mono_eq {A} : forall t w a k (f : Row W * A -> A),
      (k, (w, a)) ∈mr t -> (k, (w, f (w, a))) ∈mr fmapkr F k f t.
  Proof.
    intros ? w a k f. unfold fmapkr.
    replace (f (pair w a)) with (tgtd k f snd k (pair w a))
      by now autorewrite* with tea_tgt.
    auto using (inr_mfmapr_mono F k).
  Qed.

  Corollary inr_fmapkr_mono_neq {A} : forall t w a k k' (f : Row W * A -> A),
      k <> k' ->
      (k, (w, a)) ∈mr t -> (k, (w, a)) ∈mr fmapkr F k' f t.
  Proof.
    intros ? w a k k' f ? ?. unfold fmapkr.
    replace a with (tgtd k' f snd k (pair w a))
      by now autorewrite with tea_tgt.
    rewrite (inr_mfmapr_iff F k). now (exists a).
  Qed.
  (** ** Interaction between [fmapkr] and [tomset] *)
  (******************************************************************************)
  Corollary in_fmapkr_iff_eq {A} : forall t a k (f : Row W * A -> A),
      (k, a) ∈m fmapkr F k f t <-> exists w a', (k, (w, a')) ∈mr t /\ f (w, a') = a.
  Proof.
    intros ? ? k ?. unfold fmapkr. rewrite (in_mfmapr_iff F k).
    now rewrite (tgtd_eq k).
  Qed.

  Corollary in_fmapkr_iff_neq {A} : forall t a k k' (f : Row W * A -> A),
      k <> k' ->
      (k, a) ∈m fmapkr F k' f t <-> (k, a) ∈m t.
  Proof.
    intros ? a k ? ? ?. unfold fmapkr. rewrite (in_mfmapr_iff F k).
    autorewrite with tea_tgt.
    rewrite (inr_of_in F). split.
    - intros [w [? [? heq]]]. inverts heq. now (exists w).
    - intros [w ?]. now (exists w a).
  Qed.

End syntax_functor_targeted.

(** * Parallel substitution in syntax modules *)
(******************************************************************************)
Section syntax_module_theory.

  Context
    {W : Type}
    (F : Type -> Type)
    `{SyntaxModule W F T}.

  (** ** Interaction between [tomsetr] and [ret], [bindr] *)
  (******************************************************************************)
  Section with_types.

    Context
      {A B : Type}.

    Implicit Types (k : K) (w : Row W) (a : A) (b : B) (t : F A).

    Theorem inr_mret_iff : forall w k k' a a',
        (k, (w, a')) ∈mr mret T k' a <-> k = k' /\ w = Ƶ /\ a' = a.
    Proof.
      introv. unfold tomsetr, compose.
      compose near a on left.
      rewrite (dec_mret F). unfold compose.
      (* KLUDGE *)
      change ((@tomset_Listable H H (T k') (H2 k'))) with
          ((fun k => @tomset_Listable H H (T k) (H2 k)) k').
      rewrite (in_mret_iff F T). split.
      - intros [? hyp]; now inverts hyp.
      - intros [? [? ?]]; now subst.
    Qed.

    Corollary inr_mret_iff_eq : forall w k a a',
        (k, (w, a')) ∈mr mret T k a <-> w = Ƶ /\ a' = a.
    Proof.
      intros. rewrite inr_mret_iff. intuition.
    Qed.

    Corollary inr_mret_iff_neq : forall w k j a a',
        k <> j ->
        (j, (w, a')) ∈mr mret T k a <-> False.
    Proof.
      intros. rewrite inr_mret_iff. intuition.
    Qed.

    Existing Instance SyntaxModule_Monad.

    Theorem inr_mbindr_iff : forall t k w b (f : forall k, Row W * A -> T k B),
        (k, (w, b)) ∈mr mbindr F f t <->
        exists (k1 : K) (a : A) (w1 w2 : Row W),
          (k1, (w1, a)) ∈mr t /\ (k, (w2, b)) ∈mr f k1 (w1, a) /\ w = w1 ● w2.
    Proof.
      introv. unfold tomsetr.
      compose near t on left.
      reassociate -> on left. rewrite (dec_mbindr F).
      unfold mbindr. reassociate <- on left.
      unfold compose. rewrite (in_mbind_iff F T).
      split.
      - intros [k1 rest].
        setoid_rewrite (in_shift_cobind_iff (T k1)) in rest.
        preprocess. repeat eexists; eauto.
      - intros [k1 rest].
        exists k1. setoid_rewrite (in_shift_cobind_iff (T k1)).
        preprocess. eauto.
    Qed.

    (** ** Interaction between [tomsetr] and [bind] *)
    (******************************************************************************)
    Theorem inr_bind_iff : forall t k w b (f : forall k, A -> T k B),
        (k, (w, b)) ∈mr mbind F f t <->
        exists (k1 : K) (a : A) (w1 w2 : Row W),
          (k1, (w1, a)) ∈mr t /\ (k, (w2, b)) ∈mr f k1 a /\ w = w1 ● w2.
    Proof.
      introv. rewrite (mbind_to_mbindr F).
      now rewrite inr_mbindr_iff.
    Qed.

    (** ** Interaction between [tomset] and [bindr] *)
    (******************************************************************************)
    Existing Instance SyntaxModule_Monad.

    Theorem in_mbindr_iff : forall t k b f,
        (k, b) ∈m mbindr F f t <->
        exists (k1 : K) (a : A) (w1 : Row W),
          (k1, (w1, a)) ∈mr t /\ (k, b) ∈m f k1 (w1, a).
    Proof.
      introv. rewrite (inr_of_in F).
      setoid_rewrite inr_mbindr_iff. split.
      - intros [w [k1 [a [w1 [w2 [h1 [h2 h3]]]]]]].
        exists k1 a w1. split; auto.
        apply (in_of_inr (T k1)) in h2. auto.
      - intros [k1 [a [w1 [h1 h2]]]].
        rewrite (inr_of_in (T k1)) in h2.
        destruct h2 as [w2 h2].
        exists (w1 ● w2). exists k1 a w1 w2. now splits.
    Qed.

  End with_types.

End syntax_module_theory.

(** * Parallel substitution in syntax modules *)
(******************************************************************************)
Section syntax_module_targeted.

  Context
    {W : Type}
    (F : Type -> Type)
    `{SyntaxModule W F T}.

  Context
    {A : Type}.

  Implicit Types (k : K) (w : Row W) (a : A) (t : F A).


  (** ** Interaction between [tomsetr] and [bindkr] *)
  (******************************************************************************)
  Existing Instance SyntaxModule_Monad.

  Theorem inr_bindkr_iff_eq : forall k w a f (t : F A),
      (k, (w, a)) ∈mr bindkr F k f t <->
      exists a' w1 w2,
        (k, (w1, a')) ∈mr t /\ (k, (w2, a)) ∈mr f (w1, a') /\ w = w1 ● w2.
  Proof.
    introv. unfold bindkr.
    rewrite (inr_mbindr_iff F). split.
    - intros [k1 rest].
      compare values k and k1.
      + simpl_tgt in *. assumption.
      + simpl_tgt in *. false.
        { preprocess. unfold compose in *; cbn in *.
          rewrite (inr_mret_iff_neq (T k1)) in H6; auto. }
    - intros. exists k. now simpl_tgt.
  Qed.

  Theorem inr_bindkr_iff_neq : forall k j w a f (t : F A),
      j <> k ->
      (j, (w, a)) ∈mr bindkr F k f t <->
      (j, (w, a)) ∈mr t \/ exists a' w1 w2,
          (k, (w1, a')) ∈mr t /\ (j, (w2, a)) ∈mr f (w1, a') /\ w = w1 ● w2.
  Proof.
    introv. unfold bindkr.
    rewrite (inr_mbindr_iff F). split.
    - intros [k2 rest].
      compare values k and k2.
      + simpl_tgt in *. right; assumption.
      + simpl_tgt in *. compare values k2 and j.
        { preprocess. unfold compose in *; cbn in *.
          rewrite (inr_mret_iff_eq (T j)) in H7.
          destruct H7; subst. rewrite monoid_id_l.
          left; assumption. }
        { false. preprocess. unfold compose in *; cbn in *.
          rewrite (inr_mret_iff_neq (T j)) in H7; auto. }
    - intros [hyp | hyp].
      + exists j a w (Ƶ : Row W). simpl_monoid. simpl_tgt.
        unfold compose; cbn. rewrite (inr_mret_iff_eq (T j)).
        splits; auto.
      + exists k. simpl_tgt. assumption.
  Qed.

  (** ** Interaction between [tomset] and [bindkr] *)
  (******************************************************************************)
  Theorem in_bindkr_iff_eq : forall k a f (t : F A),
      (k, a) ∈m bindkr F k f t <->
      exists a' w1, (k, (w1, a')) ∈mr t /\ (k, a) ∈m f (w1, a').
  Proof.
    intros. rewrite (inr_of_in F).
    setoid_rewrite (inr_bindkr_iff_eq). split.
    - intros. preprocess. apply (in_of_inr (T k)) in H6.
      eauto.
    - intros. preprocess. apply (inr_of_in (T k)) in H6.
      preprocess. exists (x0 ● x1). repeat eexists; eauto.
  Qed.

  Theorem in_bindkr_iff_neq : forall k1 k2 a f (t : F A),
      k1 <> k2 ->
      (k1, a) ∈m bindkr F k2 f t <-> (k1, a) ∈m t \/ exists a' w1,
          (k2, (w1, a')) ∈mr t /\ (k1, a) ∈m f (w1, a').
  Proof.
    intros. rewrite (inr_of_in F).
    split.
    - intros. preprocess. setoid_rewrite (inr_bindkr_iff_neq) in H7; auto.
      destruct H7.
      + apply (in_of_inr F) in H6. auto.
      + right. preprocess. apply (in_of_inr (T k2)) in H7. eauto.
    - intros. preprocess. destruct H6.
      + apply (inr_of_in F) in H6.
        destruct H6 as [w ?]; exists w. rewrite (inr_bindkr_iff_neq); auto.
      + preprocess. apply (inr_of_in _) in H7.
        destruct H7 as [w ?]. exists (x0 ● w). rewrite (inr_bindkr_iff_neq); auto.
        right. exists x x0 w. splits; auto.
  Qed.

  (** ** Interaction between [tomsetkr] and [bindk] *)
  (******************************************************************************)
  Theorem inr_bindk_iff_eq : forall k w a (t : F A) (f : A -> T k A),
      (k, (w, a)) ∈mr bindk F k f t <->
      exists a' w1 w2, (k, (w1, a')) ∈mr t /\ (k, (w2, a)) ∈mr f a' /\ w = w1 ● w2.
  Proof.
    intros. rewrite (bindk_to_bindkr F).
    now rewrite (inr_bindkr_iff_eq).
  Qed.

  Theorem inr_bindk_iff_neq : forall k1 k2 w a (t : F A) (f : A -> T k2 A),
      k1 <> k2 ->
      (k1, (w, a)) ∈mr bindk F k2 f t <-> (k1, (w, a)) ∈mr t \/ exists a' w1 w2,
          (k2, (w1, a')) ∈mr t /\ (k1, (w2, a)) ∈mr f a' /\ w = w1 ● w2.
  Proof.
    intros. rewrite (bindk_to_bindkr F).
    now rewrite (inr_bindkr_iff_neq).
  Qed.

End syntax_module_targeted.
