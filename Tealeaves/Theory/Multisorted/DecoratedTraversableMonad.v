 From Tealeaves Require Export
   Classes.Multisorted.DecoratedTraversableMonad
   Classes.Multisorted.Theory.Container
   Classes.Multisorted.Theory.Targeted
   Adapters.KleisliToCoalgebraic.Multisorted.DTM.

 Import ContainerFunctor.
Import Functors.List.

Import Subset.Notations.
Import TypeFamily.Notations.
Import Monoid.Notations.
Import Theory.Container.Notations.
Import List.ListNotations.
#[local] Open Scope list_scope.

#[local] Generalizable Variables A B C F G W T U K.

(** ** Identities for <<tolist>> and <<foldMap>> *)
(******************************************************************************)
Section toBatchM.

  Context
    (U : Type -> Type)
      `{MultiDecoratedTraversablePreModule W T U}
      `{! MultiDecoratedTraversableMonad W T}.

  Lemma tolistmd_gen_to_runBatchM (fake : Type) `(t : U A) :
    tolistmd_gen U fake t =
      runBatchM (F := const (list _))
        (fun k '(w, a) => [(w, (k, a))]) (toBatchM U fake t).
  Proof.
    unfold tolistmd_gen.
    rewrite mmapdt_to_runBatchM.
    reflexivity.
  Qed.

  Lemma tolistmd_to_runBatchM  (fake : Type) `(t : U A) :
    tolistmd U t = runBatchM (fun k '(w, a) => [(w, (k, a))]) (toBatchM U fake t).
  Proof.
    unfold tolistmd.
    rewrite (tolistmd_equiv U False fake).
    rewrite tolistmd_gen_to_runBatchM.
    reflexivity.
  Qed.

  Lemma tosetmd_to_runBatchM  (fake : Type) `(t : U A) :
    tosetmd U t = runBatchM (F := (@const Type Type (subset (W * (K * A)))))
                    (fun k '(w, a) => {{(w, (k, a))}}) (toBatchM U fake t).
  Proof.
    unfold tosetmd, compose. rewrite (tolistmd_to_runBatchM fake).
    change (tosubset (F := list)
              (A := W * (K * A))) with (const (tosubset (A := W * (K * A))) (U fake)).
    cbn. (* <- needed for implicit arguments. *)
    rewrite (runBatchM_morphism (G1 := const (list (W * (K * A))))
               (G2 := const (subset (W * (K * A))))).
    unfold compose. fequal. ext k [w a].
    unfold const.
    apply tosubset_list_one.
  Qed.

  Lemma tolistm_to_runBatchM (fake : Type) `(t : U A) :
    tolistm U t = runBatchM (fun k '(w, a) => [(k, a)]) (toBatchM U fake t).
  Proof.
    unfold tolistm. unfold compose. rewrite (tolistmd_to_runBatchM fake).
    change (map (F := list) ?f) with (const (map (F := list) f) (U fake)).
    rewrite (runBatchM_morphism (G1 := const (list (W * (K * A))))
               (G2 := const (list (K * A)))
               (ψ := const (map (F := list) extract))).
    fequal. now ext k [w a].
  Qed.


End toBatchM.

(** ** Respectfulness for <<mbindd>> *)
(******************************************************************************)
Section mbindd_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Theorem mbindd_respectful :
    forall A B (t : U A) (f g : forall k, W * A -> T k B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k (w, a))
      -> mbindd U f t = mbindd U g t.
  Proof.
    introv hyp.
    rewrite (tosetmd_to_runBatchM U B t) in hyp.
    rewrite mbindd_to_runBatchM.
    rewrite mbindd_to_runBatchM.
    induction (toBatchM U B t).
    - easy.
    - destruct p.
      rewrite runBatchM_rw2.
      rewrite runBatchM_rw2.
      rewrite runBatchM_rw2 in hyp.
      fequal.
      + apply IHb. intros. apply hyp.
        cbn. now left.
      + apply hyp. now right.
  Qed.

  (** *** For equalities with special cases *)
  (** Corollaries with conclusions of the form <<mbindd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mbindd_respectful_mbind :
    forall A B (t : U A) (f : forall k, W * A -> T k B) (g : forall k, A -> T k B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k a)
      -> mbindd U f t = mbind U g t.
  Proof.
    introv hyp. rewrite mbind_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold vec_compose, compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_mmapd :
    forall A B (t : U A) (f : forall k, W * A -> T k B) (g : K -> W * A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k (g k (w, a)))
      -> mbindd U f t = mmapd U g t.
  Proof.
    introv hyp. rewrite mmapd_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold vec_compose, compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_mmap :
    forall A B (t : U A) (f : forall k, W * A -> T k B) (g : K -> A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k (g k a))
      -> mbindd U f t = mmap U g t.
  Proof.
    introv hyp. rewrite mmap_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold vec_compose, compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_id :
    forall A (t : U A) (f : forall k, W * A -> T k A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k a)
      -> mbindd U f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mbindd_id U).
    eapply mbindd_respectful.
    unfold vec_compose, compose; cbn. auto.
  Qed.

End mbindd_respectful.

(** ** Respectfulness for <<mbindd>> *)
(******************************************************************************)
Section mbind_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma mbind_respectful :
    forall A B (t : U A) (f g : forall k, A -> T k B),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = g k a)
      -> mbind U f t = mbind U g t.
  Proof.
    introv hyp. rewrite mbind_to_mbindd.
    apply mbindd_respectful.
    introv premise.
    apply inmd_implies_in in premise.
    unfold vec_compose, compose; cbn. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mbind t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mbind_respectful_mmapd :
    forall A B (t : U A) (f : forall k, A -> T k B) (g : K -> W * A -> B),
      (forall (k : K) (w : W) (a : A), (w, (k, a)) ∈md t -> f k a = mret T k (g k (w, a)))
      -> mbind U f t = mmapd U g t.
  Proof.
    intros. rewrite mmapd_to_mbindd.
    symmetry. apply mbindd_respectful_mbind.
    introv Hin. symmetry.
    unfold vec_compose, compose; cbn. auto.
  Qed.

  Corollary mbind_respectful_mmap :
    forall A B (t : U A) (f : forall k, A -> T k B) (g : K -> A -> B),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = mret T k (g k a))
      -> mbind U f t = mmap U g t.
  Proof.
    intros. rewrite mmap_to_mbind.
    symmetry. apply mbind_respectful.
    introv Hin. symmetry.
    unfold vec_compose, compose; cbn. auto.
  Qed.

  Corollary mbind_respectful_id : forall A (t : U A) (f : forall k, A -> T k A),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = mret T k a)
      -> mbind U f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mbind_id U).
    eapply mbind_respectful.
    unfold compose; cbn. auto.
  Qed.

End mbind_respectful.

(** ** Respectfulness for <<mmapd>> *)
(******************************************************************************)
Section mmapd_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma mmapd_respectful :
    forall A B (t : U A) (f g : K -> W * A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k (w, a))
      -> mmapd U f t = mmapd U g t.
  Proof.
    introv hyp. do 2 rewrite mmapd_to_mbindd.
    apply mbindd_respectful. introv premise.
    unfold vec_compose, compose; cbn. fequal. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mmapd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mmapd_respectful_mmap :
    forall A (t : U A) (f : K -> W * A -> A) (g : K -> A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k a)
      -> mmapd U f t = mmap U g t.
  Proof.
    intros. rewrite mmap_to_mmapd.
    apply mmapd_respectful. introv Hin.
    unfold vec_compose, compose; cbn; auto.
  Qed.

  Corollary mmapd_respectful_id : forall A (t : U A) (f : K -> W * A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = a)
      -> mmapd U f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mmapd_id U).
    eapply mmapd_respectful.
    cbn. auto.
  Qed.

End mmapd_respectful.

(** ** Respectfulness for <<mmap>> *)
(******************************************************************************)
Section mmap_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma mmap_respectful :
    forall A B (t : U A) (f g : K -> A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k a = g k a)
      -> mmap U f t = mmap U g t.
  Proof.
    introv hyp. do 2 rewrite mmap_to_mmapd.
    now apply mmapd_respectful.
  Qed.

  Corollary mmap_respectful_id :
    forall A (t : U A) (f : K -> A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k a = a)
      -> mmap U f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mmap_id U).
    eapply mmap_respectful.
    auto.
  Qed.

End mmap_respectful.

(** ** Respectfulness for <<kbindd>> *)
(******************************************************************************)
Section kbindd_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} (j : K).

  Lemma kbindd_respectful :
    forall A (t : U A) (f g : W * A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g (w, a))
      -> kbindd U j f t = kbindd U j g t.
  Proof.
    introv hyp. unfold kbindd. apply mbindd_respectful.
    introv premise. compare values j and k.
    - do 2 rewrite btgd_eq. auto.
    - do 2 (rewrite btgd_neq; auto).
  Qed.

  (** *** For equalities with special cases *)
  (******************************************************************************)
  Corollary kbindd_respectful_kbind :
    forall A (t : U A) (f : W * A -> T j A) (g : A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g a)
      -> kbindd U j f t = kbind U j g t.
  Proof.
    introv hyp. rewrite kbind_to_kbindd.
    apply kbindd_respectful. introv Hin.
    apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_kmapd :
    forall A (t : U A) (f : W * A -> T j A) (g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j (g (w, a)))
      -> kbindd U j f t = kmapd U j g t.
  Proof.
    introv hyp. rewrite kmapd_to_kbindd.
    apply kbindd_respectful. introv Hin.
    apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_kmap :
    forall A (t : U A) (f : W * A -> T j A) (g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j (g a))
      -> kbindd U j f t = kmap U j g t.
  Proof.
    introv hyp. rewrite kmap_to_kmapd.
    apply kbindd_respectful_kmapd.
    introv Hin. apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_id :
    forall A (t : U A) (f : W * A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j a)
      -> kbindd U j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    erewrite <- (kbindd_id U).
    apply kbindd_respectful.
    auto.
  Qed.

End kbindd_respectful.

(** ** Respectfulness for mixed structures *)
(******************************************************************************)
Section mixed_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} (j : K).

  Corollary kbind_respectful_kmapd :
    forall A (t : U A) (f : A -> T j A) (g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = mret T j (g (w, a)))
      -> kbind U j f t = kmapd U j g t.
  Proof.
    introv hyp. rewrite kmapd_to_kbindd.
    rewrite kbind_to_kbindd. apply kbindd_respectful.
    introv Hin. apply hyp. auto.
  Qed.

End mixed_respectful.

(** ** Respectfulness for <<kbind>> *)
(******************************************************************************)
Section kbindd_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} (j : K).

  Lemma kbind_respectful :
    forall A (t : U A) (f g : A -> T j A),
      (forall (a : A), (j, a) ∈m t -> f a = g a)
      -> kbind U j f t = kbind U j g t.
  Proof.
    introv hyp. unfold kbind. apply mbind_respectful.
    introv premise. compare values j and k.
    - do 2 rewrite btg_eq. auto.
    - do 2 (rewrite btg_neq; auto).
  Qed.

  (** *** For equalities with special cases *)
  (******************************************************************************)
  Corollary kbind_respectful_kmap :
    forall A (t : U A) (f : A -> T j A) (g : A -> A),
      (forall (a : A), (j, a) ∈m t -> f a = mret T j (g a))
      -> kbind U j f t = kmap U j g t.
  Proof.
    introv hyp. rewrite kmap_to_kbind.
    apply kbind_respectful.
    introv Hin. apply hyp. auto.
  Qed.

  Corollary kbind_respectful_id :
    forall A (t : U A) (f : A -> T j A),
      (forall (a : A), (j, a) ∈m t -> f a = mret T j a)
      -> kbind U j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kbind_id U (j := j)).
    now apply kbind_respectful.
  Qed.

End kbindd_respectful.

(** ** Respectfulness for <<kmapd>> *)
(******************************************************************************)
Section kmapd_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} (j : K).

  Lemma kmapd_respectful :
    forall A (t : U A) (f g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g (w, a))
      -> kmapd U j f t = kmapd U j g t.
  Proof.
    introv hyp. unfold kmapd.
    apply mmapd_respectful. introv premise.
    compare values j and k.
    - do 2 rewrite tgtd_eq. auto.
    - do 2 (rewrite tgtd_neq; auto).
  Qed.

  (** *** For equalities with other operations *)
  (******************************************************************************)
  Corollary kmapd_respectful_kmap :
    forall A (t : U A) (f : W * A -> A) (g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g a)
      -> kmapd U j f t = kmap U j g t.
  Proof.
    introv hyp. rewrite kmap_to_kmapd.
    apply kmapd_respectful. auto.
  Qed.

  Corollary kmapd_respectful_id : forall A (t : U A) (f : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = a)
      -> kmapd U j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kmapd_id (j := j) U).
    apply kmapd_respectful. auto.
  Qed.

End kmapd_respectful.

(** ** Respectfulness for <<kmap>> *)
(******************************************************************************)
Section kmap_respectful.

  Context
    {U : Type -> Type}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} (j : K).

  Lemma kmap_respectful :
    forall A (t : U A) (f g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = g a)
      -> kmap U j f t = kmap U j g t.
  Proof.
    introv hyp. unfold kmap. apply mmap_respectful.
    introv premise. compare values j and k.
    - autorewrite with tea_tgt_eq. eauto.
    - autorewrite with tea_tgt_neq. auto.
  Qed.

  Corollary kmap_respectful_id :
    forall A (t : U A) (f : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = a)
      -> kmap U j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kmap_id (j := j) U).
    apply kmap_respectful. auto.
  Qed.

End kmap_respectful.
