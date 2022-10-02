From Tealeaves Require Export
  Classes.Algebraic.Setlike.Functor
  Theory.Kleisli.Traversable.Monad.Container
  Theory.Kleisli.DT.Functor.Container
  Theory.Kleisli.DT.Monad.ToFunctor
  Theory.Kleisli.DT.Monad.DerivedInstances
  Functors.List
  Functors.Constant
  Functors.Schedule.

Import Applicative.Notations.
Import Sets.Notations.
Import Schedule.Notations.
Import Product.Notations.
Import Setlike.Functor.Notations.
Import Kleisli.DT.Monad.Notations.
Import Monoid.Notations.
Import List.ListNotations.
#[local] Open Scope list_scope.

#[local] Generalizable Variables T W F G M ϕ A B C.

Import DerivedInstances.Operations.

(** * Batch *)
(******************************************************************************)
Section with_functor.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Definition iterate_dm {A : Type} (B : Type) : T A -> @Batch (W * A) (T B) (T B) :=
    binddt T (Batch (W * A) (T B)) (batch (T B)).

End with_functor.

(** ** Expressing <<binddt>> with <<runBatch>> *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import DT.Monad.ToFunctor.Operation.
  Import DT.Monad.DerivedInstances.Instances.

  Theorem binddt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G (T B)) (t : T A),
      binddt T G f t = runBatch f (iterate_dm T B t).
  Proof.
    intros.
    unfold iterate_dm.
    compose near t on right.
    rewrite (kdtm_morph W T (Batch (W * A) (T B)) G).
    now rewrite (runBatch_batch).
  Qed.

  Theorem bindd_to_runBatch :
    forall (A B : Type) (f : W * A -> T B) (t : T A),
      bindd T f t = runBatch f (iterate_dm T B t).
  Proof.
    intros.
    unfold iterate_dm.
    compose near t on right.
    rewrite (kdtm_morph W T (Batch (W * A) (T B)) (fun A => A)).
    reflexivity.
  Qed.

  Theorem fmapdt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G B) (t : T A),
      fmapdt T G f t = runBatch f (iterate_d T B t).
  Proof.
    intros. apply (fmapdt_to_runBatch T).
  Qed.

  Theorem fmapd_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> B) (t : T A),
      fmapd T f t = runBatch f (iterate_d T B t).
  Proof.
    intros.
    change (@Fmapd_Binddt W T H H0) with
      (@DerivedInstances.Operations.Fmapd_Fmapdt T _ _).
    apply (fmapd_to_runBatch T).
  Qed.

  Theorem fmap_to_runBatch : forall (A B : Type) (f : A -> B),
      fmap T f = runBatch f ∘ iterate T B.
  Proof.
    intros.
    change (@Fmap_Binddt T W H0 H) with (@DerivedInstances.Operations.Fmap_Fmapdt T _ _).
    change (@Traverse_Binddt W T H H0) with (@DerivedInstances.Operations.Traverse_Fmapdt T _ _).
    apply (fmap_to_runBatch T).
  Qed.

End with_monad.

Section with_monad.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  (** *** Composition with monad operattions *)
  (******************************************************************************)
  Lemma foldMapd_ret `{Monoid M} : forall `(f : W * A -> M),
      foldMapd T f ∘ ret T = f ∘ ret (W ×).
  Proof.
    intros. unfold foldMapd. unfold_ops @Fmapdt_Binddt.
    rewrite (kdtm_binddt0 W T _ _ (G := const M)).
    reflexivity.
  Qed.

  Lemma foldMapd_binddt `{Applicative G} `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> G (T B)),
      fmap G (foldMapd T g) ∘ binddt T G f =
        foldMapd T (fun '(w, a) => fmap G (foldMapd T (prepromote w g)) (f (w, a))).
  Proof.
    intros. unfold foldMapd. unfold_ops @Fmapdt_Binddt.
    rewrite (kdtm_binddt2 W T _ _ _ (G1 := G) (G2 := const M)).
    fequal.
    - unfold Fmap_compose.
      ext A' B' f'.
      enough (hyp : fmap G (fmap (const M) f') = id).
      + rewrite hyp. reflexivity.
      + ext m. rewrite <- (fun_fmap_id G).
        reflexivity.
    - ext A' B' [t1 t2]. reflexivity.
  Qed.

  Corollary foldMapd_binddt_I `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd T g ∘ binddt T (fun A => A) f =
        foldMapd T (fun '(w, a) => foldMapd T (prepromote w g) (f (w, a))).
  Proof.
    intros. change (foldMapd T g) with (fmap (fun A => A) (foldMapd T g)).
    now rewrite (foldMapd_binddt (G := fun A => A)).
  Qed.


  (** *** Composition with lessor operations *)
  (******************************************************************************)
  Lemma foldMapd_bindd `{Applicative G} `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd T g ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMapd T (prepromote w g) (f (w, a))).
  Proof.
    intros. unfold_ops @Bindd_Binddt.
    change (foldMapd T g) with (fmap (fun A => A) (foldMapd T g)).
    now rewrite (foldMapd_binddt (G := fun A => A)).
  Qed.

End with_monad.

(** * Shape and contents *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import DT.Monad.ToFunctor.Operation.
  Import DT.Monad.DerivedInstances.Instances.

  (** ** Relating <<tolistd>> and <<binddt>> / <<ret>> *)
  (******************************************************************************)
  Lemma tolistd_ret : forall (A : Type) (a : A),
      tolistd T (ret T a) = [ (Ƶ, a) ].
  Proof.
    unfold tolistd.
    intros. compose near a.
    now rewrite (foldMapd_ret T).
  Qed.

  Lemma tolistd_binddt : forall `{Applicative G} `{Monoid M} `(f : W * A -> G (T B)),
      fmap G (tolistd T) ∘ binddt T G f =
        foldMapd T (fun '(w, a) => fmap G (foldMapd T (prepromote w (ret list))) (f (w, a))).
  Proof.
    intros. unfold tolistd. now rewrite (foldMapd_binddt T).
  Qed.

  (** ** Relating <<tolistd>> and lesser operations *)
  (******************************************************************************)
  Lemma tolistd_bindd : forall `{Monoid M} `(f : W * A -> T B),
      tolistd T ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMapd T (prepromote w (ret list)) (f (w, a))).
  Proof.
    intros. unfold_ops @Bindd_Binddt.
    change (@tolistd T _ _ B) with (fmap (fun A => A) (@tolistd T _ _ B)).
    rewrite (tolistd_binddt (G := fun A => A)).
    reflexivity.
  Qed.

  (** ** Corollaries for the rest *)
  (******************************************************************************)
  Corollary tosetd_ret : forall (A : Type) (a : A),
      tosetd T (ret T a) = {{ (Ƶ, a) }}.
  Proof.
    intros. unfold tosetd.
    compose near a.
    now rewrite (foldMapd_ret T).
  Qed.

  Corollary tolist_binddt : forall `{Applicative G} `{Monoid M} `(f : W * A -> G (T B)),
      fmap G (tolist T) ∘ binddt T G f =
        foldMapd T (fmap G (tolist T) ∘ f).
  Proof.
    intros.
    change (@Traverse_Binddt W T H H0)
      with (@DerivedInstances.Operations.Traverse_Fmapdt _ _ _).
    rewrite (tolist_to_tolistd T).
    rewrite <- (fun_fmap_fmap G).
    reassociate ->.
    rewrite tolistd_binddt.
    rewrite (foldMapd_morphism T).
    rewrite (fun_fmap_fmap G).
    fequal. unfold tolistd.
    ext [w a]. unfold compose at 1 2.
    compose near (f (w, a)) on left.
    rewrite (fun_fmap_fmap G).
    rewrite (foldMapd_morphism T).
    rewrite (foldMapd_morphism T).
    fequal. fequal.
    ext [w' b]. reflexivity.
  Qed.

  (** ** Relating <<tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma tolist_bindd : forall `{Monoid M} `(f : W * A -> T B),
      tolist T ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMap T (ret list) (f (w, a))).
  Proof.
    intros.
    change (@Traverse_Binddt W T H H0)
      with (@DerivedInstances.Operations.Traverse_Fmapdt _ _ _).
    rewrite (tolist_to_tolistd T).
    reassociate ->. rewrite (tolistd_bindd).
    rewrite (foldMapd_morphism T).
    fequal. ext [w a].
    cbn. compose near (f (w, a)) on left.
    rewrite (foldMapd_morphism T).
    rewrite (foldMap_to_foldMapd T).
    fequal. now ext [w' a'].
  Qed.

End DTM_tolist.

(** ** Characterizing membership in list operations *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import DT.Monad.ToFunctor.Operation.
  Import DT.Monad.DerivedInstances.Instances.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma ind_iff_in_tolistd : forall (A : Type) (a : A) (w : W) (t : T A),
      (w, a) ∈d t <-> toset list (tolistd T t) (w, a).
  Proof.
    intros. unfold tosetd, tolistd.
    compose near t on right.
    rewrite (foldMapd_morphism T (ϕ := toset list)).
    replace (@ret set (Return_set) (W * A)) with (toset (A := W * A) list ∘ ret list).
    reflexivity. ext [w' a']. solve_basic_set.
  Qed.

  Lemma in_iff_in_tolist : forall (A : Type) (a : A) (t : T A),
      (a ∈ t) <-> toset list (tolist T t) a.
  Proof.
    intros.
    change (@Traverse_Binddt W T H H0)
      with (@DerivedInstances.Operations.Traverse_Fmapdt _ _ _).
    rewrite (toset_to_tolist T).
    reflexivity.
  Qed.

End DTM_tolist.

(** * Characterizing <<∈d>> *)
(******************************************************************************)
Section section.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import DT.Monad.ToFunctor.Operation.
  Import DT.Monad.DerivedInstances.Instances.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Existing Instance Toset_set.
  Existing Instance SetlikeFunctor_set.
  Lemma ind_iff_in : forall (A : Type) (a : A) (t : T A),
      a ∈ t <-> exists w, (w, a) ∈d t.
  Proof.
    intros.
    change (@Traverse_Binddt W T H H0)
      with (@DerivedInstances.Operations.Traverse_Fmapdt T _ _).
    now rewrite (ind_iff_in T).
  Qed.

  Lemma ind_ret_iff : forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret T a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros. unfold tosetd.
    compose near a2 on left. rewrite (foldMapd_ret T).
    unfold compose. split.
    now inversion 1.
    inversion 1. subst. solve_basic_set.
  Qed.

  Lemma in_ret_iff : forall {A : Type} (a1 a2 : A),
      a1 ∈ ret T a2 <-> a1 = a2.
  Proof.
    intros.
    change (@Traverse_Binddt W T H H0)
      with (@Operations.Traverse_Bindt T _ _).
    now rewrite (in_ret_iff T).
  Qed.

  Lemma ind_bindd_iff1 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd T f t ->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold tosetd, compose in *.
    change (foldMapd T (ret set) (bindd T f t) (wtotal, b))
      with (((foldMapd T (ret set) ∘ bindd T f) t) (wtotal, b)) in hyp.
    rewrite (foldMapd_bindd T) in hyp.
    rewrite (foldMapd_to_runBatch T).
    rewrite (foldMapd_to_runBatch T) in hyp.
    induction (iterate T False t).
  Admitted.

  Lemma ind_bindd_iff2 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
    (exists (w1 w2 : W) (a : A),
      (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2) ->
      (wtotal, b) ∈d bindd T f t.
  Proof.
    introv [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]. subst.
    unfold tosetd, compose in *.
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

  Theorem ind_bind_iff :
    forall `(f : A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bind T f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f a
        /\ wtotal = w1 ● w2.
  Proof.
    intros. apply ind_bindd_iff.
  Qed.

  (** ** Characterizing <<∈>> with <<bindd>> *)
  (******************************************************************************)
  Corollary in_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (b : B),
      b ∈ bindd T f t <->
      exists (w1 : W) (a : A),
        (w1, a) ∈d t /\ b ∈ f (w1, a).
  Proof.
    intros.
    rewrite (ind_iff_in).
    setoid_rewrite ind_bindd_iff.
    setoid_rewrite (ind_iff_in).
    split; intros; preprocess; repeat eexists; eauto.
  Qed.

  Corollary in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T f t <-> exists (a : A), a ∈ t /\ b ∈ f a.
  Proof.
    change (@Traverse_Binddt W T H H0)
      with (@DerivedInstances.Operations.Traverse_Fmapdt _ _ _).
    intros. setoid_rewrite (ind_iff_in).
    setoid_rewrite (ind_bindd_iff).
    intuition.
    - preprocess. eexists; split; eauto.
    - preprocess. repeat eexists; eauto.
  Qed.

  Theorem in_fmapd_iff :
    forall `(f : W * A -> B) (t : T A) (b : B),
      b ∈ fmapd T f t <-> exists (w : W) (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros.
    change (@Traverse_Binddt W T H H0)
      with (@DerivedInstances.Operations.Traverse_Fmapdt _ _ _).
    rewrite (ind_iff_in).
    setoid_rewrite (ind_fmapd_iff T).
    reflexivity.
  Qed.

End section.

(** ** Respectfulness for <<bindd>> *)
(******************************************************************************)
Section bindd_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import DT.Monad.ToFunctor.Operation.
  Import DT.Monad.DerivedInstances.Instances.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Theorem bindd_respectful :
    forall A B (t : T A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd T f t = bindd T g t.
  Proof.
    introv hyp.
    unfold tosetd in hyp.
    unfold foldMapd in hyp.
    rewrite (fmapdt_constant_applicative2 T False B) in hyp.
    unfold fmapdt, Fmapdt_Binddt in hyp.
    rewrite (binddt_to_runBatch T) in hyp.
    do 2 rewrite (bindd_to_runBatch T).
    induction (iterate_dm T B t).
    - easy.
    - destruct x. do 2 rewrite runBatch_rw2.
      rewrite runBatch_rw2 in hyp.
      fequal.
      + apply IHb. intros. apply hyp.
        cbn. now left.
      + apply hyp. now right.
  Qed.

  (** *** For equalities with special cases *)
  (** Corollaries with conclusions of the form <<bindd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary bindd_respectful_bind :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> bindd T f t = bind T g t.
  Proof.
    introv hyp. rewrite bind_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_fmapd :
    forall A B (t : T A) (f : W * A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T (g (w, a)))
      -> bindd T f t = fmapd T g t.
  Proof.
    introv hyp. rewrite fmapd_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_fmap :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T (g a))
      -> bindd T f t = fmap T g t.
  Proof.
    introv hyp. rewrite fmap_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_id :
    forall A (t : T A) (f : W * A -> T A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T a)
      -> bindd T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (kmond_bindd1 T).
    eapply bindd_respectful.
    unfold compose; cbn. auto.
  Qed.

End bindd_respectful.

(** ** Respectfulness for <<bind>> *)
(******************************************************************************)
Section bind_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import DT.Monad.ToFunctor.Operation.
  Import DT.Monad.DerivedInstances.Instances.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma bind_respectful :
    forall A B (t : T A) (f g : A -> T B),
      (forall (a : A), a ∈ t -> f a = g a)
      -> bind T f t = bind T g t.
  Proof.
    introv hyp. rewrite bind_to_bindd.
    apply (bindd_respectful T). introv premise. apply (ind_implies_in T) in premise.
    unfold compose; cbn. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<bind t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary bind_respectful_fmapd :
    forall A B (t : T A) (f : A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = ret T (g (w, a)))
      -> bind T f t = fmapd T g t.
  Proof.
    intros. rewrite fmapd_to_bindd.
    symmetry. apply (bindd_respectful_bind T).
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary bind_respectful_fmap :
    forall A B (t : T A) (f : A -> T B) (g : A -> B),
      (forall (a : A), a ∈ t -> f a = ret T (g a))
      -> bind T f t = fmap T g t.
  Proof.
    intros. rewrite fmap_to_bind.
    symmetry. apply bind_respectful.
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary bind_respectful_id : forall A (t : T A) (f : A -> T A),
      (forall (a : A), a ∈ t -> f a = ret T a)
      -> bind T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (kmon_bind1 T).
    eapply bind_respectful.
    unfold compose; cbn. auto.
  Qed.

End bind_respectful.

(** ** Respectfulness for <<fmapd>> *)
(******************************************************************************)
Section fmapd_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import DT.Monad.ToFunctor.Operation.
  Import DT.Monad.DerivedInstances.Instances.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma fmapd_respectful :
    forall A B (t : T A) (f g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> fmapd T f t = fmapd T g t.
  Proof.
    introv hyp. do 2 rewrite fmapd_to_bindd.
    apply (bindd_respectful T). introv premise.
    unfold compose; cbn. fequal. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<fmapd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary fmapd_respectful_fmap :
    forall A (t : T A) (f : W * A -> A) (g : A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> fmapd T f t = fmap T g t.
  Proof.
    intros. rewrite fmap_to_fmapd.
    apply (fmapd_respectful). introv Hin.
    unfold compose; cbn; auto.
  Qed.

  Corollary fmapd_respectful_id : forall A (t : T A) (f : W * A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = a)
      -> fmapd T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (dfun_fmapd1 W T).
    eapply (fmapd_respectful).
    cbn. auto.
  Qed.

End fmapd_respectful.

(** ** Respectfulness for <<fmap>> *)
(******************************************************************************)
Section fmap_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import DT.Monad.ToFunctor.Operation.
  Import DT.Monad.ToFunctor.Instance.
  Import DT.Monad.DerivedInstances.Instances.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma fmap_respectful :
    forall A B (t : T A) (f g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = g a)
      -> fmap T f t = fmap T g t.
  Proof.
    introv hyp. do 2 rewrite fmap_to_fmapd.
    now apply (fmapd_respectful T).
  Qed.

  Corollary fmap_respectful_id :
    forall A (t : T A) (f : A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = a)
      -> fmap T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (fun_fmap_id T).
    eapply (fmap_respectful).
    auto.
  Qed.

End fmap_respectful.
