From Tealeaves Require Export
  Functors.Constant
  Functors.Sets
  Theory.Sets.Kleisli
  Classes.Kleisli.Traversable.Monad
  Theory.Kleisli.Traversable.Functor.Container
  Theory.Kleisli.Traversable.Monad.DerivedInstances
  Theory.Algebraic.Applicative.Monoid.

Import Batch.Notations.
Import Sets.Notations.
Import Monoid.Notations.
Import Functor.Notations.
#[local] Generalizable Variables G M ϕ A B.

Import ToFunctor.Operation.
Import Traversable.Monad.DerivedInstances.Operations.

(** * Batch *)
(******************************************************************************)
Section with_functor.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  Lemma runBatch_batch : forall  `{Applicative G} (A B : Type) (f : A -> G (T B)),
      runBatch f ∘ (@batch A (T B)) = f.
  Proof.
    intros. ext a. cbn.
    now rewrite ap1.
  Qed.

  Definition iterate_tm {A : Type} (B : Type) : T A -> @Batch A (T B) (T B) :=
    bindt T (Batch A (T B)) (batch (T B)).

End with_functor.

Import DerivedInstances.Operations.
Import DerivedInstances.DerivedInstances.

(** * <<foldMap>> on monads *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  Import DerivedInstances.DerivedInstances.

  (** ** Composition with <<bindt>> *)
  (******************************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M} : forall `(g : B -> M) `(f : A -> G (T B)),
      fmap G (foldMap T g) ∘ bindt T G f =
        foldMap T (fmap G (foldMap T g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt T G (const M)).
    unfold_ops @Traverse_Bindt.
    fequal.
    - ext A' B' f' t. unfold_ops @Fmap_compose @Fmap_const.
      now rewrite (fun_fmap_id G).
    - ext A' B' [a b]. reflexivity.
  Qed.

  (** ** Composition with <<bind>> and <<ret>> *)
  (******************************************************************************)
  Lemma foldMap_bind `{Applicative G} `{Monoid M} : forall `(g : B -> M) `(f : A -> T B),
      foldMap T g ∘ bind T f =
        foldMap T (foldMap T g ∘ f).
  Proof.
    intros. unfold foldMap. rewrite (traverse_bind T (const M)).
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M} : forall `(f : A -> M),
      foldMap T f ∘ ret T = f.
  Proof.
    intros. unfold foldMap. unfold_ops @Traverse_Bindt.
    rewrite (ktm_bindt0 T _ _ (G := const M)).
    reflexivity.
  Qed.

End with_monad.

(** ** Expressing operations using <<runBatch>> *)
(******************************************************************************)
Section with_kleisli.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  Lemma bindt_to_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt T G f = runBatch f ∘ iterate_tm T B.
  Proof.
    unfold iterate_tm.
    rewrite (ktm_morph T (ϕ := @runBatch A G (T B) f _ _ _)).
    now rewrite (runBatch_batch T).
  Qed.

  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse T G f = runBatch f ∘ iterate T B.
  Proof.
    now rewrite (traverse_to_runBatch T).
  Qed.

  Corollary fmap_to_runBatch `(f : A -> B) :
    fmap T f = runBatch f ∘ iterate T B.
  Proof.
    change (@Fmap_Bindt T H0 H) with (@Operation.Fmap_Traverse T _).
    rewrite (fmap_to_traverse T).
    now rewrite traverse_to_runBatch.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
    @id (T A) = runBatch (@id A) ∘ iterate T A.
  Proof.
    intros. rewrite <- (trf_traverse_id T).
    rewrite traverse_to_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_to_runBatch : forall `{Monoid M} (fake : Type) `(f : A -> M),
      foldMap T f = runBatch f ∘ iterate_tm T fake.
  Proof.
    intros.
    unfold foldMap.
    rewrite (traverse_constant_applicative2 T f False fake).
    rewrite (traverse_to_bindt).
    rewrite (bindt_to_runBatch).
    reflexivity.
  Qed.

End with_kleisli.

(** * Characterizing <<∈>> *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  Import DerivedInstances.DerivedInstances.

  #[export] Instance Monad_Hom_Toset : Kleisli.Monad.Monad_Hom T set (@toset T _).
  Proof.
    constructor.
    - intros.
      unfold_ops @Toset_Traverse.
      rewrite (foldMap_bind T).
      unfold_ops @Traverse_Bindt.
      rewrite (foldMap_morphism T).
      rewrite (kmon_bind0 set).
      reflexivity.
    - intros.
      unfold_ops @Toset_Traverse.
      rewrite (foldMap_ret T).
      reflexivity.
  Qed.

  Theorem in_ret_iff :
    forall (A : Type) (a1 a2 : A), a1 ∈ ret T a2 <-> a1 = a2.
  Proof.
    intros. unfold_ops @Toset_Traverse.
    compose near a2 on left. rewrite (foldMap_ret T).
    solve_basic_set.
  Qed.

  Theorem in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros. compose near t on left.
    rewrite (kmon_hom_bind T set); try typeclasses eauto.
    unfold compose. now rewrite bind_set_spec.
  Qed.

End with_monad.

(** * Respectfulness properties *)
(******************************************************************************)
Section respectfulness_properties.

  Context
    (T : Type -> Type)
    `{Traversable.Monad.Monad T}.

  Lemma bindt_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G (T B)) `(f2 : A -> G (T B)) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> bindt T G f1 t = bindt T G f2 t.
  Proof.
    introv ? hyp. do 2 (rewrite (bindt_to_runBatch T); auto).
    unfold toset, Toset_Traverse in hyp.
    rewrite (foldMap_to_runBatch T B) in hyp.
    unfold compose in *.
    induction (iterate_tm T B t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros. apply hyp. now left.
      + apply hyp. now right.
  Qed.

  Lemma traverse_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse T G f1 t = traverse T G f2 t.
  Proof.
    apply (traverse_respectful T).
  Qed.

  Lemma traverse_respectful_pure : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = pure G a) -> traverse T G f1 t = pure G t.
  Proof.
    apply (traverse_respectful_pure T).
  Qed.

  Lemma traverse_respectful_fmap {A B} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure G (g a)) -> traverse T G f t = pure G (fmap T g t).
  Proof.
    change (@Fmap_Bindt T H0 H) with (@Operation.Fmap_Traverse T _).
    apply (traverse_respectful_fmap T).
  Qed.

  Corollary traverse_respectful_id {A} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G A),
      (forall a, a ∈ t -> f a = pure G a) -> traverse T G f t = pure G t.
  Proof.
    apply (traverse_respectful_id T).
  Qed.

  Corollary fmap_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> fmap T f1 t = fmap T f2 t.
  Proof.
    intros. change (@Fmap_Bindt T H0 H) with (@Operation.Fmap_Traverse T _).
    now apply (fmap_respectful T).
  Qed.

  Corollary fmap_respectful_id : forall `(f1 : A -> A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = a) -> fmap T f1 t = t.
  Proof.
    intros. change (@Fmap_Bindt T H0 H) with (@Operation.Fmap_Traverse T _).
    now apply (fmap_respectful_id T).
  Qed.

End respectfulness_properties.
