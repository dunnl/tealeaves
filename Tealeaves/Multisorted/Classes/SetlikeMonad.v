From Tealeaves.Multisorted Require Export
     Classes.Monad
     Classes.DecoratedMonad
     Classes.SetlikeFunctor
     Functors.MSets.

Import Monoid.Notations.
Import Multisorted.Classes.SetlikeFunctor.Notations.
Import Multisorted.Category.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

(** * Set-like multisorted monads *)
(******************************************************************************)
Section SetlikeMultisortedMonad.

  Context
    `{ix : Index}
    (T : K -> Type -> Type)
    `{! MReturn T}
    `{forall k, MBind (T k) T}
    `{forall k, Tomset (T k)}.

  Class SetlikeMultisortedMonad :=
    { qmmon_monad :> MultisortedMonad T;
      qmmon_mret :
        `(tomset (T k) ∘ mret T k = mret (const mset) k (A := A));
      qmmon_mbind : forall `(f : A ~k~> T B) (k : K),
          tomset (T k) ∘ mbind (T k) f = mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset (T k);
      qmmon_respectful : forall k A B (t : T k A) (f g : A ~k~> T B),
          (forall k a, (k, a) ∈m t -> f k a = g k a) -> mbind (T k) f t = mbind (T k) g t;
    }.

End SetlikeMultisortedMonad.

(** * Set-like multisorted modules *)
(******************************************************************************)
Section SetlikeMultisortedModule.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{! MFmap F} `{! Tomset F} `{! MBind F T}
    `{! MReturn T} `{! forall k, MBind (T k) T} `{forall k, Tomset (T k)}.

  Class SetlikeMultisortedModule :=
    { qrmod_module :> MultisortedRightModule F T;
      qrmod_monad :> SetlikeMultisortedMonad T;
      qrmod_mbind : forall `(f : A ~k~> T B),
          tomset F ∘ mbind F f = mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset F;
      qrmod_respectful : forall A B (t : F A) (f g : A ~k~> T B),
          (forall k a, (k, a) ∈m t -> f k a = g k a) -> mbind F f t = mbind F g t;
    }.

End SetlikeMultisortedModule.

(** * Typeclass inclusions *)
(******************************************************************************)

(** ** Set-like monads are set-like right modules *)
(******************************************************************************)
Section SetlikeMultisortedModule_Monad.

  Context
    `{SetlikeMultisortedMonad T}
    (k : K).

  Instance SetlikeMultisortedModule_Monad :
    SetlikeMultisortedModule (T k) T :=
    {| qrmod_mbind := fun A B f => qmmon_mbind T f k;
       qrmod_module := MultisortedRightModule_Monad k;
       qrmod_respectful := qmmon_respectful T k;
    |}.

End SetlikeMultisortedModule_Monad.

(** ** Carriers of set-like modules form set-like functors *)
(******************************************************************************)
Section SetlikeMultisortedFunctor_Module.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{SetlikeMultisortedModule (ix := ix) F T}.

  #[global] Instance Natural_module_tomset : MultisortedNatural (@tomset _ F _).
  Proof.
    introv. unfold_ops @MFmap_rmod. ext t b.
    rewrite (qrmod_mbind F T).
    do 2 fequal. ext k.
    reassociate <- on right.
    now rewrite (qmmon_mret T).
  Qed.

  Theorem tomset_mfmap_proper_mbind :
    (forall A B (t : F A) (f g : A -k-> B),
          (forall k a, (k, a) ∈m t -> f k a = g k a) -> mfmap F f t = mfmap F g t).
  Proof.
    unfold_ops @MFmap_rmod. introv heq. apply (qrmod_respectful F T).
    intros. unfold compose. now rewrite heq.
  Qed.

  #[global] Instance SetlikeMultisortedFunctor_Module :
    SetlikeMultisortedFunctor F :=
    {| qmfun_respectful := tomset_mfmap_proper_mbind; |}.

End SetlikeMultisortedFunctor_Module.

(** * Properties of multisorted set-like modules *)
(******************************************************************************)
Section SetlikeMultisortedModule_theory.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{SetlikeMultisortedModule (ix:=ix) F T}.

  (** ** Respectfulness conditions for <<mbind>> *)
  (******************************************************************************)
  Theorem setlike_mbind_respectful_id {A} : forall (t : F A) (f : A ~k~> T A),
      (forall k a, (k, a) ∈m t -> f k a = mret T k a) -> mbind F f t = t.
  Proof.
    intros. replace t with (mbind F (mret T) t) at 2
      by (now rewrite (mbind_id F)).
    now apply (qrmod_respectful F T).
  Qed.

  Corollary setlike_mbind_respectful_mfmap {A B} :
    forall (t : F A) (f : A ~k~> T B) (g : A -k-> B),
      (forall k a, (k, a) ∈m t -> f k a = mret T k (g k a)) -> mbind F f t = mfmap F g t.
  Proof.
    intros. unfold mfmap, MFmap_rmod.
    now apply (qrmod_respectful F T).
  Qed.

  (** ** Respectfulness conditions for <<bindk>> *)
  (******************************************************************************)
  Theorem setlike_bindk_respectful : forall {A} k (t : F A) (f g : A -> T k A),
      (forall a, (k, a) ∈m t -> f a = g a) -> bindk F k f t = bindk F k g t.
  Proof.
    intros. apply (qrmod_respectful F T).
    intros j ? ?. compare values k and j; simpl_tgt_fallback; auto.
  Qed.

  Corollary setlike_bindk_respectful_id : forall {A} k (t : F A) (f : A -> T k A),
      (forall a, (k, a) ∈m t -> f a = mret T k a) -> bindk F k f t = t.
  Proof.
    intros. replace t with (bindk F k (mret T k) t) at 2
      by (now rewrite (bindk_mret F k)).
    now apply setlike_bindk_respectful.
  Qed.

  Corollary setlike_bindk_respectful_fmapk {A} k :
    forall (t : F A) (f : A -> T k A) (g : A -> A),
      (forall a, (k, a) ∈m t -> f a = mret T k (g a)) -> bindk F k f t = fmapk F k g t.
  Proof.
    intros. rewrite fmapk_to_bindk.
    now apply setlike_bindk_respectful.
  Qed.

  (** ** Interaction between [tomset] and [ret], [mbind] *)
  (******************************************************************************)
  Theorem in_mret_iff {A} : forall (k k' : K) (a a' : A),
      (k', a') ∈m mret T k a <-> k' = k /\ a' = a.
  Proof.
    intros ? ? a ?. compose near a on left.
    rewrite (qmmon_mret T).
    split; intro hyp; now inverts hyp.
  Qed.

  Corollary in_mret_iff_eq {A} : forall (k : K) (a a' : A),
      (k, a') ∈m mret T k a <-> a' = a.
  Proof.
    intros. rewrite in_mret_iff. intuition.
  Qed.

  Corollary in_mret_iff_neq {A} : forall (k k' : K) (a a' : A),
      k <> k' -> (k', a') ∈m mret T k a <-> False.
  Proof.
    introv. rewrite in_mret_iff. intuition.
  Qed.

  Theorem in_mbind_iff {A B} : forall (t : F A) (k : K) (b : B) (f : forall k, A -> T k B),
      (k, b) ∈m mbind F f t <->
      exists (k1 : K) (a : A), (k1, a) ∈m t /\ (k, b) ∈m f k1 a.
  Proof.
    introv. compose near t on left.
    now rewrite (qrmod_mbind F T), mbind_mset_spec.
  Qed.

  (** ** Interaction between [tomset] and [bindk] *)
  (******************************************************************************)
  Theorem in_bindk_iff_eq {A} : forall (t : F A) (k : K) (b : A) (f : A -> T k A),
      (k, b) ∈m bindk F k f t <->
      exists (a : A), (k, a) ∈m t /\ (k, b) ∈m f a.
  Proof.
    intros t k ? ?. unfold bindk. rewrite (in_mbind_iff). split.
    - intros [k' [a [h1 h2]]]. destruct_eq_args k k'.
      + rewrite btg_eq in h2. now (exists a).
      + rewrite btg_neq in h2; auto.
        rewrite (in_mret_iff) in h2.
        now inverts h2.
    - intros [a [h1 h2]]. exists k a. now rewrite btg_eq.
  Qed.

  Theorem in_bindk_iff_neq {A} : forall (t : F A) (k k' : K) (b : A) (f : A -> T k A),
      k <> k' ->
      (k', b) ∈m bindk F k f t <-> (k', b) ∈m t \/ exists (a : A),
          (k, a) ∈m t /\ (k', b) ∈m f a.
  Proof.
    intros t k k' b ? neq. unfold bindk. rewrite (in_mbind_iff). split.
    - intros [k'' [a [h1 h2]]]. destruct_eq_args k k''.
      + rewrite btg_eq in h2. now (right; exists a).
      + rewrite btg_neq in h2; auto.
        rewrite (in_mret_iff) in h2.
        left. now inverts h2.
    - intros [h | [a [h1 h2]]].
      + exists k' b.
        rewrite (btg_neq); auto.
        now rewrite (in_mret_iff).
      + exists k a. now rewrite (btg_eq).
  Qed.

End SetlikeMultisortedModule_theory.

(** * Interaction between [tomsetd] and [ret] *)
(******************************************************************************)
Section SetlikeMultisortedMonad_ret.

  Context
    `{ix : Index}
    (T : K -> Type -> Type)
    `{Monoid_op W} `{Monoid_unit W}
    `{SetlikeMultisortedMonad (ix:=ix) T}
    `{! forall k, Decorate W (T k)}
    `{! DecoratedMultisortedMonad W T}
    {A B : Type}.

  Implicit Types (k : K) (w : W) (a : A) (b : B).

  Theorem ind_mret_iff : forall w k k' a a',
      (k, (w, a')) ∈md mret T k' a <-> k = k' /\ w = Ƶ /\ a' = a.
  Proof.
    introv. unfold tomsetd, compose.
    compose near a on left.
    rewrite (dec_mret (T k')). unfold compose.
    rewrite (in_mret_iff F T). split.
    - intros [? hyp]; now inverts hyp.
    - intros [? [? ?]]; now subst.
  Qed.

  Corollary ind_mret_iff_eq : forall w k a a',
      (k, (w, a')) ∈md mret T k a <-> w = Ƶ /\ a' = a.
  Proof.
    intros. rewrite ind_mret_iff. intuition.
  Qed.

  Corollary ind_mret_iff_neq : forall w k j a a',
      k <> j ->
      (j, (w, a')) ∈md mret T k a <-> False.
  Proof.
    intros. rewrite ind_mret_iff. intuition.
  Qed.

End SetlikeMultisortedMonad_ret.

(** * Properties of decorated set-like modules *)
(******************************************************************************)
Section DecoratedSetlikeMultisortedModule_theory.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{Monoid_op W} `{Monoid_unit W}
    `{SetlikeMultisortedModule (ix:=ix) F T}
    `{! Decorate W F}  `{! forall k, Decorate W (T k)}
    `{! DecoratedMultisortedModule W F T}.

  Context
    {A B : Type}.

  Implicit Types (k : K) (w : W) (a : A) (b : B) (t : F A).

  Theorem ind_mret_iff : forall w k k' a a',
      (k, (w, a')) ∈md mret T k' a <-> k = k' /\ w = Ƶ /\ a' = a.
  Proof.
    introv. unfold tomsetd, compose.
    compose near a on left.
    rewrite (dec_mret F). unfold compose.
    rewrite (in_mret_iff F T). split.
    - intros [? hyp]; now inverts hyp.
    - intros [? [? ?]]; now subst.
  Qed.

  Corollary ind_mret_iff_eq : forall w k a a',
      (k, (w, a')) ∈md mret T k a <-> w = Ƶ /\ a' = a.
  Proof.
    intros. rewrite ind_mret_iff. intuition.
  Qed.

  Corollary ind_mret_iff_neq : forall w k j a a',
      k <> j ->
      (j, (w, a')) ∈md mret T k a <-> False.
  Proof.
    intros. rewrite ind_mret_iff. intuition.
  Qed.

End SetlikeMultisortedMonad_ret.

(** * Properties of decorated set-like modules *)
(******************************************************************************)
Section DecoratedSetlikeMultisortedModule_theory.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{Monoid_op W} `{Monoid_unit W}
    `{SetlikeMultisortedModule (ix:=ix) F T}
    `{! Decorate W F}  `{! forall k, Decorate W (T k)}
    `{! DecoratedMultisortedModule W F T}.

  (** ** Respectfulness conditions for <<mbindd>> *)
  (******************************************************************************)
  Theorem mbindd_respectful {A B} : forall (t : F A) (f g : forall k, W * A -> T k B),
      (forall k w a, (k, (w, a)) ∈md t -> f k (w, a) = g k (w, a)) ->
      mbindd F f t = mbindd F g t.
  Proof.
    intros. apply (qrmod_respectful F T).
    intros ? [? ?]; auto.
  Qed.

  Corollary mbindd_respectful_id {A} : forall (t : F A) (f : forall k, W * A -> T k A),
      (forall k w a, (k, (w, a)) ∈md t -> f k (w, a) = mret T k a) ->
      mbindd F f t = t.
  Proof.
    intros. replace t with (mbindd F (mret T ◻ const snd) t) at 2
      by (now rewrite (mbindd_id F)).
    now apply mbindd_respectful.
  Qed.

  Corollary mbindd_respectful_mfmapr {A B} : forall (t : F A) (f : forall k, W * A -> T k B) (g : W * A -k-> B),
      (forall k w a, (k, (w, a)) ∈md t -> f k (w, a) = mret T k (g k (w, a))) ->
      mbindd F f t = mfmapd F g t.
  Proof.
    introv. rewrite mfmapd_to_mbindd.
    now apply (mbindd_respectful _ _ (mret T ◻ g)).
  Qed.

  Corollary mbindd_respectful_mbind {A B} : forall (t : F A) (f : forall k, W * A -> T k B) (g : forall k, A -> T k B),
      (forall k w a, (k, (w, a)) ∈md t -> f k (w, a) = g k a) ->
      mbindd F f t = mbind F g t.
  Proof.
    introv. rewrite (mbind_to_mbindd F).
    now apply (mbindd_respectful _ _ (g ◻ const snd)).
  Qed.

  (** ** Respectfulness conditions for <<bindkd>> *)
  (******************************************************************************)
  Lemma bindkd_respectful {A} : forall k (t : F A) (f g : W * A -> T k A),
      (forall w a, (k, (w, a)) ∈md t -> f (w, a) = g (w, a)) ->
      bindkd F k f t = bindkd F k g t.
  Proof.
    intros. apply (qrmod_respectful F T).
    intros j [? ?] ?. destruct_eq_args k j.
    autorewrite with tea_tgt_eq using auto.
    autorewrite with tea_tgt_neq using auto.
  Qed.

  Lemma bindkd_respectful_id {A} : forall k (t : F A) (f : W * A -> T k A),
      (forall w a, (k, (w, a)) ∈md t -> f (w, a) = mret T k a) ->
      bindkd F k f t = t.
  Proof.
    intros. replace t with (bindkd F k (mret T k ∘ extract (prod W)) t) at 2
      by (now rewrite (bindkd_id F)).
    now apply bindkd_respectful.
  Qed.

  Corollary bindkd_respectful_fmapkr {A} : forall k (t : F A) (f : W * A -> T k A) (g : W * A -> A),
      (forall w a, (k, (w, a)) ∈md t -> f (w, a) = mret T k (g (w, a))) ->
      bindkd F k f t = fmapkd F k g t.
  Proof.
    intros. rewrite fmapkd_to_bindkd.
    now apply (bindkd_respectful).
  Qed.

  Corollary bindkd_respectful_bindk {A} : forall k (t : F A) (f : W * A -> T k A) (g : A -> T k A),
      (forall w a, (k, (w, a)) ∈md t -> f (w, a) = g a) ->
      bindkd F k f t = bindk F k g t.
  Proof.
    intros. rewrite (bindk_to_bindkd F).
    now apply bindkd_respectful.
  Qed.

  (** ** Interaction between [tomsetd] and [ret], [bindd] *)
  (******************************************************************************)
  Section with_types.

    Context
      {A B : Type}.

    Implicit Types (k : K) (w : W) (a : A) (b : B) (t : F A).

    Theorem ind_mret_iff : forall w k k' a a',
        (k, (w, a')) ∈md mret T k' a <-> k = k' /\ w = Ƶ /\ a' = a.
    Proof.
      introv. unfold tomsetd, compose.
      compose near a on left.
      rewrite (dec_mret F). unfold compose.
      rewrite (in_mret_iff F T). split.
      - intros [? hyp]; now inverts hyp.
      - intros [? [? ?]]; now subst.
    Qed.

    Corollary ind_mret_iff_eq : forall w k a a',
        (k, (w, a')) ∈md mret T k a <-> w = Ƶ /\ a' = a.
    Proof.
      intros. rewrite ind_mret_iff. intuition.
    Qed.

    Corollary ind_mret_iff_neq : forall w k j a a',
        k <> j ->
        (j, (w, a')) ∈md mret T k a <-> False.
    Proof.
      intros. rewrite ind_mret_iff. intuition.
    Qed.

    Existing Instance SetlikeMultisortedModule_Monad.
    Existing Instance DecoratedMultisortedModule_Monad.

    Theorem ind_mbindd_iff : forall t k w b (f : W * A ~k~> T B),
        (k, (w, b)) ∈md mbindd F f t <->
        exists (k1 : K) (a : A) (w1 w2 : W),
          (k1, (w1, a)) ∈md t /\ (k, (w2, b)) ∈md f k1 (w1, a) /\ w = w1 ● w2.
    Proof.
      introv. unfold tomsetd.
      compose near t on left.
      reassociate -> on left. rewrite (dec_mbindd F).
      unfold mbindd. reassociate <- on left.
      unfold compose. rewrite (in_mbind_iff F T).
      split.
      - intros [k1 rest].
        setoid_rewrite (in_shift_cobind_iff (T k1)) in rest.
        preprocess. repeat eexists; eauto.
      - intros [k1 rest].
        exists k1. setoid_rewrite (in_shift_cobind_iff (T k1)).
        preprocess. eauto.
    Qed.

    (** ** Interaction between [tomsetd] and [bind] *)
    (******************************************************************************)
    Theorem ind_bind_iff : forall t k w b (f : forall k, A -> T k B),
        (k, (w, b)) ∈md mbind F f t <->
        exists (k1 : K) (a : A) (w1 w2 : W),
          (k1, (w1, a)) ∈md t /\ (k, (w2, b)) ∈md f k1 a /\ w = w1 ● w2.
    Proof.
      introv. rewrite (mbind_to_mbindd F).
      now rewrite ind_mbindd_iff.
    Qed.

    (** ** Interaction between [tomset] and [bindd] *)
    (******************************************************************************)
    Theorem in_mbindd_iff : forall t k b f,
        (k, b) ∈m mbindd F f t <->
        exists (k1 : K) (a : A) (w1 : W),
          (k1, (w1, a)) ∈md t /\ (k, b) ∈m f k1 (w1, a).
    Proof.
      introv. rewrite (ind_of_in F).
      setoid_rewrite ind_mbindd_iff. split.
      - intros [w [k1 [a [w1 [w2 [h1 [h2 h3]]]]]]].
        exists k1 a w1. split; auto.
        apply (in_of_ind (T k1)) in h2. auto.
      - intros [k1 [a [w1 [h1 h2]]]].
        rewrite (ind_of_in (T k1)) in h2.
        destruct h2 as [w2 h2].
        exists (w1 ● w2). exists k1 a w1 w2. now splits.
    Qed.

  End with_types.

  Context
    {A : Type}.

  Implicit Types (k : K) (w : W) (a : A) (t : F A).

  (** ** Interaction between [tomsetd] and [bindkd] *)
  (******************************************************************************)

  Theorem ind_bindkd_iff_eq : forall k w a f (t : F A),
      (k, (w, a)) ∈md bindkd F k f t <->
      exists a' w1 w2,
        (k, (w1, a')) ∈md t /\ (k, (w2, a)) ∈md f (w1, a') /\ w = w1 ● w2.
  Proof.
    introv. unfold bindkd.
    rewrite (ind_mbindd_iff). split.
    - intros [k1 rest].
      compare values k and k1.
      + simpl_tgt in *. assumption.
      + simpl_tgt in *. false.
        { preprocess. unfold compose in *; cbn in *.
          rewrite (ind_mret_iff_neq) in H6; auto. }
    - intros. exists k. now simpl_tgt.
  Qed.

  Theorem ind_bindkd_iff_neq : forall k j w a f (t : F A),
      j <> k ->
      (j, (w, a)) ∈md bindkd F k f t <->
      (j, (w, a)) ∈md t \/ exists a' w1 w2,
          (k, (w1, a')) ∈md t /\ (j, (w2, a)) ∈md f (w1, a') /\ w = w1 ● w2.
  Proof.
    introv. unfold bindkd.
    rewrite (ind_mbindd_iff). split.
    - intros [k2 rest].
      compare values k and k2.
      + simpl_tgt in *. right; assumption.
      + simpl_tgt in *. compare values k2 and j.
        { preprocess. unfold compose in *; cbn in *.
          rewrite (ind_mret_iff_eq) in H7.
          destruct H7; subst. rewrite monoid_id_l.
          left; assumption. }
        { false. preprocess. unfold compose in *; cbn in *.
          rewrite (ind_mret_iff_neq) in H7; auto. }
    - intros [hyp | hyp].
      + exists j a w (Ƶ : W). simpl_monoid. simpl_tgt.
        unfold compose; cbn. rewrite (ind_mret_iff_eq).
        splits; auto.
      + exists k. simpl_tgt. assumption.
  Qed.

    Existing Instance SetlikeMultisortedModule_Monad.
    Existing Instance DecoratedMultisortedModule_Monad.

  (** ** Interaction between [tomset] and [bindkd] *)
  (******************************************************************************)
  Theorem in_bindkd_iff_eq : forall k a f (t : F A),
      (k, a) ∈m bindkd F k f t <->
      exists a' w1, (k, (w1, a')) ∈md t /\ (k, a) ∈m f (w1, a').
  Proof.
    intros. rewrite (ind_of_in F).
    setoid_rewrite (ind_bindkd_iff_eq). split.
    - intros. preprocess. eapply (in_of_ind (T k)) in H6.
      eauto.
    - intros. preprocess. apply (ind_of_in (T k)) in H6.
      preprocess. exists (x0 ● x1). repeat eexists; eauto.
  Qed.

  Theorem in_bindkd_iff_neq : forall k1 k2 a f (t : F A),
      k1 <> k2 ->
      (k1, a) ∈m bindkd F k2 f t <-> (k1, a) ∈m t \/ exists a' w1,
          (k2, (w1, a')) ∈md t /\ (k1, a) ∈m f (w1, a').
  Proof.
    intros. rewrite (ind_of_in F).
    split.
    - intros. preprocess. setoid_rewrite (ind_bindkd_iff_neq) in H7; auto.
      destruct H7.
      + apply (in_of_ind F) in H6. auto.
      + right. preprocess. apply (in_of_ind (T k2)) in H7. eauto.
    - intros. preprocess. destruct H6.
      + apply (ind_of_in F) in H6.
        destruct H6 as [w ?]; exists w. rewrite (ind_bindkd_iff_neq); auto.
      + preprocess. apply (ind_of_in _) in H7.
        destruct H7 as [w ?]. exists (x0 ● w). rewrite (ind_bindkd_iff_neq); auto.
        right. exists x x0 w. splits; auto.
  Qed.

  (** ** Interaction between [tomsetkd] and [bindk] *)
  (******************************************************************************)
  Theorem ind_bindk_iff_eq : forall k w a (t : F A) (f : A -> T k A),
      (k, (w, a)) ∈md bindk F k f t <->
      exists a' w1 w2, (k, (w1, a')) ∈md t /\ (k, (w2, a)) ∈md f a' /\ w = w1 ● w2.
  Proof.
    intros. rewrite (bindk_to_bindkd F).
    now rewrite (ind_bindkd_iff_eq).
  Qed.

  Theorem ind_bindk_iff_neq : forall k1 k2 w a (t : F A) (f : A -> T k2 A),
      k1 <> k2 ->
      (k1, (w, a)) ∈md bindk F k2 f t <-> (k1, (w, a)) ∈md t \/ exists a' w1 w2,
          (k2, (w1, a')) ∈md t /\ (k1, (w2, a)) ∈md f a' /\ w = w1 ● w2.
  Proof.
    intros. rewrite (bindk_to_bindkd F).
    now rewrite (ind_bindkd_iff_neq).
  Qed.

End DecoratedSetlikeMultisortedModule_theory.
