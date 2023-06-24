From Tealeaves Require Export
  Classes.Traversable.Monad
  Theory.Traversable.Functor.

#[local] Generalizable Variables T G A B C ϕ M.

Import Traversable.Functor.Notations.
Import Traversable.Monad.Notations.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments traverse T%function_scope {Traverse} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments bind (T)%function_scope {U}%function_scope {Bind} {A B}%type_scope _%function_scope _.
#[local] Arguments bindt (T)%function_scope {U}%function_scope {Bindt} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

Import Traversable.Monad.DerivedInstances.

(** * Batch *)
(******************************************************************************)
Section batch.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma runBatch_batch3 : forall `{Applicative G} (A B : Type) (f : A -> G (T B)),
      runBatch f ∘ (@batch A (T B)) = f.
  Proof.
    intros. apply (runBatch_batch G).
  Qed.

  Definition toBatch3 {A : Type} (B : Type) : T A -> @Batch A (T B) (T B) :=
    bindt T (Batch A (T B)) (batch (T B)).

End batch.

(** * <<foldMap>> on monads *)
(******************************************************************************)
Section foldMap.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments traverse T%function_scope {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bind (T)%function_scope {U}%function_scope {Bind} (A B)%type_scope _%function_scope _.
#[local] Arguments bindt (T)%function_scope {U}%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

  (** ** Composition with <<bindt>> *)
  (******************************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M} : forall `(g : B -> M) `(f : A -> G (T B)),
      map G _ _ (foldMap T g) ∘ bindt T G _ _ f =
        foldMap T (map G _ _ (foldMap T g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt T G (const M) A B False).
    rewrite (traverse_to_bindt T (const (G M))).
    fequal.
    - ext A' B' f'.
      unfold Map_compose, Map_const.
      unfold const in *.
      unfold map at 2.
      now rewrite (fun_map_id G).
    - ext A' B' [a b].
      unfold Mult_compose, Mult_const.
      unfold compose in *.
      unfold const in *.
      cbn.
      reflexivity.
  Qed.

  Lemma foldMap_bind `{Monoid M} : forall `(g : B -> M) `(f : A -> T B),
      foldMap T g ∘ bind T A B f =
        foldMap T (foldMap T g ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bind T (const M) A B False).
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M} : forall `(f : A -> M),
      foldMap T f ∘ ret T A = f.
  Proof.
    intros. unfold foldMap. unfold_ops @Traverse_Bindt.
    rewrite (ktm_bindt0 T (const M) A _).
    reflexivity.
  Qed.

End foldMap.

(** ** Expressing operations using <<runBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma bindt_to_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt T G f = runBatch f ∘ toBatch3 T B.
  Proof.
    unfold toBatch3.
    rewrite (ktm_morph T (ϕ := @runBatch A G (T B) f _ _ _)).
    now rewrite (runBatch_batch3 T).
  Qed.

  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse T G f = runBatch f ∘ toBatch T B.
  Proof.
    now rewrite (Traversable.Functor.traverse_to_runBatch T).
  Qed.

  Lemma bind_to_runBatch `(f : A -> T B) :
    bind T f = runBatch (F := fun A => A) f ∘ toBatch3 T B.
  Proof.
    rewrite (bind_to_bindt).
    rewrite bindt_to_runBatch.
    reflexivity.
  Qed.

  Corollary map_to_runBatch `(f : A -> B) :
    map T f = runBatch f ∘ toBatch T B.
  Proof.
    rewrite (map_to_traverse T).
    now rewrite traverse_to_runBatch.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
    @id (T A) = runBatch (@id A) ∘ toBatch T A.
  Proof.
    intros. rewrite <- (trf_traverse_id T).
    rewrite traverse_to_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_to_runBatch : forall `{Monoid M} (fake : Type) `(f : A -> M),
      foldMap T f = runBatch f ∘ toBatch3 T fake.
  Proof.
    intros.
    unfold foldMap.
    rewrite (traverse_const1 T fake).
    rewrite (traverse_to_bindt).
    rewrite (bindt_to_runBatch).
    reflexivity.
  Qed.

End runBatch.

Import Sets.Notations.
Import Sets.ElNotations.

(** * Characterizing <<∈>> *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma el_hom1 : forall (A : Type),
      el T A ∘ ret T A = ret set A.
  Proof.
    intros.
    unfold_ops @Toset_Traverse.
    rewrite (foldMap_ret T).
    reflexivity.
  Qed.

  Lemma el_hom2 : forall (A B : Type) (f : A -> T B),
      el T B ∘ bind T f = bind set (el T B ∘ f) ∘ el T A.
  Proof.
    intros.
      unfold_ops @Toset_Traverse.
      rewrite (foldMap_bind T (ret set B) f).
      rewrite (foldMap_morphism T).
      rewrite (kmon_bind0 set).
      reflexivity.
  Qed.

  #[export] Instance Monad_Hom_Toset : MonadHom T set (@el T _) :=
    {| kmon_hom_ret := el_hom1;
      kmon_hom_bind := el_hom2;
    |}.

  Theorem in_ret_iff :
    forall (A : Type) (a1 a2 : A), a1 ∈ ret T A a2 <-> a1 = a2.
  Proof.
    intros.
    compose near a2 on left.
    rewrite (kmon_hom_ret T set).
    solve_basic_set.
  Qed.

  Theorem in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros. compose near t on left.
    rewrite (kmon_hom_bind T set).
    reflexivity.
  Qed.

  Import Classes.Monad.DerivedInstances.

  Corollary in_map_iff :
    forall `(f : A -> B) (t : T A) (b : B),
      b ∈ map T f t <-> exists a, a ∈ t /\ f a = b.
  Proof.
    intros. compose near t on left.
    rewrite <- (natural (ϕ := el T)).
    reflexivity.
  Qed.

 Lemma in_iff_in_tolist : forall (A : Type) (a : A) (t : T A),
     (a ∈ t) <-> el list A (tolist T A t) a.
 Proof.
   intros.
   rewrite (toset_to_tolist T).
   reflexivity.
 Qed.

End with_monad.

(** * Respectfulness properties *)
(******************************************************************************)
Section respectfulness_properties.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma bindt_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G (T B)) `(f2 : A -> G (T B)) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> bindt T G f1 t = bindt T G f2 t.
  Proof.
    introv ? hyp. do 2 (rewrite (bindt_to_runBatch T); auto).
    unfold el, Toset_Traverse in hyp.
    rewrite (foldMap_to_runBatch T B) in hyp.
    unfold compose in *.
    induction (toBatch3 T B t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros. apply hyp. now left.
      + apply hyp. now right.
  Qed.

  Lemma traverse_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse T G f1 t = traverse T G f2 t.
  Proof.
    apply (Traversable.Functor.traverse_respectful T).
  Qed.

  Lemma traverse_respectful_pure : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = pure G a) -> traverse T G f1 t = pure G t.
  Proof.
    apply (Traversable.Functor.traverse_respectful_pure T).
  Qed.

  Lemma traverse_respectful_map {A B} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure G (g a)) -> traverse T G f t = pure G (map T g t).
  Proof.
    change (@Map_Bindt T H0 H) with (@DerivedInstances.Map_Traverse T _).
    apply (Traversable.Functor.traverse_respectful_map T).
  Qed.

  Corollary traverse_respectful_id {A} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G A),
      (forall a, a ∈ t -> f a = pure G a) -> traverse T G f t = pure G t.
  Proof.
    apply (Traversable.Functor.traverse_respectful_id T).
  Qed.

  Corollary map_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> map T f1 t = map T f2 t.
  Proof.
    intros. change (@Map_Bindt T H0 H) with (@DerivedInstances.Map_Traverse T _).
    now apply (Traversable.Functor.map_respectful T).
  Qed.

  Corollary map_respectful_id : forall `(f1 : A -> A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = a) -> map T f1 t = t.
  Proof.
    intros. change (@Map_Bindt T H0 H) with (@DerivedInstances.Map_Traverse T _).
    now apply (Traversable.Functor.map_respectful_id T).
  Qed.

End respectfulness_properties.
