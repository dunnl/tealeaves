From Tealeaves Require Export
  Classes.Kleisli.TraversableMonad
  Theory.TraversableFunctor.

#[local] Generalizable Variables T G A B C ϕ M.

Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.

(* Halfway explicit *)
#[local] Arguments bindt (U T)%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bind (U T)%function_scope {Bind} (A B)%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} A%type_scope _.

(** * Batch *)
(******************************************************************************)
Section batch.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma runBatch_batch3 : forall `{Applicative G} (A B : Type) (f : A -> G (T B)),
      runBatch G f (T B) ∘ batch A (T B) = f.
  Proof.
    intros. apply (runBatch_batch G).
  Qed.

  Definition toBatch3 (A : Type) (B : Type) : T A -> @Batch A (T B) (T B) :=
    bindt T T (Batch A (T B)) A B (batch A (T B)).

End batch.

(** * <<foldMap>> on monads *)
(******************************************************************************)
Section foldMap.

  Context
    (T : Type -> Type)
    `{TraversableMonadFull T}.

  (** ** Composition with <<bindt>> *)
  (******************************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M} : forall `(g : B -> M) `(f : A -> G (T B)),
      map G (T B) M (foldMap T g) ∘ bindt T T G A B f =
        foldMap T (map G (T B) M (foldMap T g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt T G (const M) A B False).
    rewrite 2(ktmf_traverse_to_bindt).
    fequal.
    - ext A' B' f'.
      unfold Map_compose, Map_const.
      unfold const in *.
      unfold map at 2.
      now rewrite (fun_map_id (F := G)).
    - ext A' B' [a b].
      unfold Mult_compose, Mult_const.
      unfold compose in *.
      unfold const in *.
      cbn.
      reflexivity.
  Qed.

  Lemma foldMap_bind `{Monoid M} : forall `(g : B -> M) `(f : A -> T B),
      foldMap T g ∘ bind T T A B f =
        foldMap T (foldMap T g ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bind T (const M) A B False).
    rewrite (ktmf_traverse_to_bindt (T := T) (const M) _ _ _ A False).
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M} : forall `(f : A -> M),
      foldMap T f ∘ ret T A = f.
  Proof.
    intros. unfold foldMap.
    rewrite (ktmf_traverse_to_bindt).
    rewrite (ktm_bindt0 (T := T) (const M) A _).
    reflexivity.
  Qed.

End foldMap.

(** ** Expressing operations using <<runBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    (T : Type -> Type)
    `{TraversableMonadFull T}.

  Lemma bindt_to_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt T T G A B f = runBatch G f (T B) ∘ toBatch3 T A B.
  Proof.
    unfold toBatch3.
    rewrite (ktm_morph (ϕ := runBatch G f)).
    now rewrite (runBatch_batch3 T).
  Qed.

  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse T G A B f = runBatch G f (T B) ∘ toBatch T A B.
  Proof.
    now rewrite (TraversableFunctor.traverse_to_runBatch T).
  Qed.

  Lemma bind_to_runBatch `(f : A -> T B) :
    bind T T A B f = runBatch (fun A => A) f (T B) ∘ toBatch3 T A B.
  Proof.
    rewrite (ktmf_bind_to_bindt).
    rewrite bindt_to_runBatch.
    reflexivity.
  Qed.

  Corollary map_to_runBatch `(f : A -> B) :
    map T A B f = runBatch (fun A => A) f (T B) ∘ toBatch T A B.
  Proof.
    rewrite (map_to_traverse T).
    now rewrite traverse_to_runBatch.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
    @id (T A) = runBatch (fun A => A) (@id A) (T A) ∘ toBatch T A A.
  Proof.
    intros. rewrite <- (trf_traverse_id).
    rewrite traverse_to_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_to_runBatch : forall `{Monoid M} (fake : Type) `(f : A -> M),
      foldMap T f = runBatch (const M) f (T fake) ∘ toBatch3 T A fake.
  Proof.
    intros.
    unfold foldMap.
    rewrite (traverse_const1 T fake).
    rewrite (ktmf_traverse_to_bindt).
    rewrite (bindt_to_runBatch).
    reflexivity.
  Qed.

End runBatch.

(*
(** * <<tolist>> *)
(******************************************************************************)
Section tolist.

  Context
    (T : Type -> Type)
    `{TraversableMonadFull T}.

  Import Monoid.Notations.

  #[export] Instance Tolist_Bindt `{Bindt T} : Tolist T :=
    fun A => foldMap T (ret list A).

  #[export] Instance Natural_Tolist_Traverse : Natural (@tolist T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Tolist_Traverse.
    rewrite (foldMap_morphism T (list A) (list B)).
    rewrite (foldMap_map T).
    rewrite (natural (ϕ := @ret list _)).
    reflexivity.
  Qed.

  Lemma foldMap_list_eq `{Monoid M} : forall (A : Type) (f : A -> M),
      foldMap list f = List.foldMap f.
  Proof.
    intros. ext l. induction l.
    - cbn. reflexivity.
    - cbn. change (monoid_op ?x ?y) with (x ● y).
      unfold_ops @Pure_const.
      rewrite (monoid_id_r).
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma tolist_to_foldMap : forall (A : Type),
      tolist T = foldMap T (ret list A).
  Proof.
    reflexivity.
  Qed.

  Corollary tolist_to_traverse1 : forall (A : Type),
      tolist T = traverse T (const (list A)) A False (ret list A).
  Proof.
    reflexivity.
  Qed.

  Corollary tolist_to_traverse2 : forall (A fake : Type),
      tolist T = traverse T (const (list A)) A fake (ret list A).
  Proof.
    intros.
    rewrite tolist_to_traverse1.
    rewrite (traverse_const1 T fake).
    reflexivity.
  Qed.

  Corollary tolist_to_runBatch {A : Type} (tag : Type) `(t : T A) :
    tolist T t =
      runBatch (const (list A))
        (ret list A : A -> const (list A) tag)
        (T tag) (toBatch T A tag t).
  Proof.
    rewrite (tolist_to_traverse2 A tag).
    now rewrite (traverse_to_runBatch T (const (list A))).
  Qed.

  Corollary foldMap_to_tolist `{Monoid M} : forall (A : Type) (f : A -> M),
      foldMap T f = foldMap list f ∘ tolist T.
  Proof.
    intros.
    rewrite (tolist_to_foldMap).
    rewrite (foldMap_list_eq).
    rewrite (foldMap_morphism T (list A) M).
    fequal. ext a. cbn. rewrite monoid_id_l.
    reflexivity.
  Qed.


End tolist.
*)

(** * Characterizing <<∈>> *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma el_hom1 : forall (A : Type),
      el T A ∘ ret T A = ret subset A.
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
