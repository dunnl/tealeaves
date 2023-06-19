From Tealeaves Require Export
  Classes.Traversable.Functor
  Functors.Sets
  Functors.List
  Functors.Batch.

Import Batch.Notations.

#[local] Generalizable Variable M.

#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

Import Traversable.Functor.DerivedInstances.

(** * Purity *)
(******************************************************************************)
Theorem traverse_id_purity :
  forall (T G : Type -> Type)
    `{TraversableFunctor T} `{Applicative G} (A : Type),
    traverse T G A A (pure G) = @pure G _ (T A).
Proof.
  intros.
  change (@pure G _ A) with (@pure G _ A ∘ id).
  rewrite <- (trf_traverse_morphism T (G1 := fun A => A) (G2 := G)).
  now rewrite (trf_traverse_id T).
Qed.


(** * Traversals as <<Batch>> coalgebras *)
(******************************************************************************)
Section traversals_coalgebras.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Definition batch {A : Type} (B : Type) : A -> @Batch A B B :=
    fun a => (Done (@id B)) ⧆ a.

  Definition toBatch {A : Type} (B : Type) : T A -> @Batch A B (T B) :=
    traverse T (Batch A B) A B (batch B).

  (** ** Basic lemmas for <<runBatch>> *)
  (******************************************************************************)
  Lemma runBatch_batch : forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G B),
      runBatch f ∘ batch B = f.
  Proof.
    intros. ext a. cbn.
    now rewrite ap1.
  Qed.

  Lemma extract_to_runBatch : forall (A X : Type) (j : @Batch A A X),
      extract_Batch j = runBatch (@id A) j.
  Proof.
    intros. induction j.
    - reflexivity.
    - cbn. now rewrite <- IHj.
  Qed.

  (** ** Expressing operations using <<runBatch>> *)
  (******************************************************************************)
  Lemma traverse_to_runBatch (G : Type -> Type)
    `{Applicative G} {A B : Type} (f : A -> G B) :
    traverse T G A B f = runBatch f ∘ toBatch B.
  Proof.
    unfold toBatch.
    rewrite (trf_traverse_morphism T (ϕ := @runBatch A G B f _ _ _)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary map_to_runBatch {A B : Type} (f : A -> B) :
    map T A B f = runBatch f ∘ toBatch B.
  Proof.
    rewrite (map_to_traverse).
    rewrite (traverse_to_runBatch (fun A => A)).
    reflexivity.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
      @id (T A) = runBatch (@id A) ∘ toBatch A.
  Proof.
    intros. rewrite <- (trf_traverse_id T).
    rewrite (traverse_to_runBatch (fun A => A)).
    reflexivity.
  Qed.

  (** ** A naturality property for <<toBatch>> *)
  (******************************************************************************)
  Lemma toBatch_mapfst {A B : Type} (f : A -> B) {C : Type} :
    toBatch C ∘ map T A B f = mapfst_Batch f ∘ toBatch C.
  Proof.
    unfold toBatch.
    rewrite (traverse_map T (Batch B C)).
    rewrite (traverse_to_runBatch (Batch B C)).
    rewrite (traverse_to_runBatch (Batch A C)).
    ext t.
    unfold compose. induction (toBatch C t).
    - cbv. reflexivity.
    - do 2 rewrite runBatch_rw2. rewrite IHb.
      now rewrite mapfst_Batch3.
  Qed.

End traversals_coalgebras.

(** ** Lemmas for traversals with constant applicative functors *)
(******************************************************************************)
Section constant_applicatives.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Monoid M}.

  Lemma traverse_const1: forall {A : Type} (B : Type) `(f : A -> M),
      traverse T (const M) A False f = traverse T (const M) A B f.
  Proof.
    intros.
    change_left (map (const M) (T False) (T B) (map T False B exfalso)
                    ∘ traverse T (const M) A False (f : A -> const M False)).
    rewrite (map_traverse T (const M)).
    reflexivity.
  Qed.

  Lemma traverse_const2: forall {A : Type} (f : A -> M) (fake1 fake2 : Type),
    traverse T (const M) A fake1 f = traverse T (const M) A fake2 f.
  Proof.
    intros.
    rewrite <- (traverse_const1 fake1).
    rewrite (traverse_const1 fake2).
    reflexivity.
  Qed.

End constant_applicatives.

(** * <<foldMap>> *)
(******************************************************************************)
Definition foldMap (T : Type -> Type)
  `{Monoid_op M} `{Monoid_unit M} `{Traverse T}
  {A : Type} (f : A -> M) : T A -> M := traverse T (const M) A False f.

(** ** Basic properties of <<foldMap>> *)
(******************************************************************************)
Section with_functor.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  #[local] Generalizable Variables A B ϕ.

  (** *** As a special case of <<traverse>> *)
  (******************************************************************************)
  Lemma foldMap_to_traverse1 (M : Type) `{Monoid M} : forall `(f : A -> M),
      foldMap T f = traverse T (const M) A False f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_to_traverse2 (M : Type) `{Monoid M} : forall (fake : Type) `(f : A -> M),
      foldMap T f = traverse T (const M) A fake f.
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    rewrite (traverse_const1 T fake f).
    reflexivity.
  Qed.

  (** *** As a special case of <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMap_to_runBatch1 `{Monoid M} : forall `(f : A -> M),
      foldMap T f = runBatch f ∘ toBatch T False.
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    rewrite (traverse_to_runBatch T (const M) f).
    reflexivity.
  Qed.

  Lemma foldMap_to_runBatch2 `{Monoid M} : forall (fake : Type) `(f : A -> M),
      foldMap T f = runBatch f ∘ toBatch T fake.
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    rewrite (traverse_const1 T fake).
    rewrite (traverse_to_runBatch T (const M) f).
    reflexivity.
  Qed.

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma foldMap_traverse `{Monoid M} (G : Type -> Type) {B : Type} `{Applicative G} : forall `(g : B -> M) `(f : A -> G B),
      map G (T B) M (foldMap T g) ∘ traverse T G A B f =
        foldMap T (map G B M g ∘ f).
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    rewrite (trf_traverse_traverse T G (const M) (B := B) (C := False)).
    rewrite (foldMap_to_traverse1 (G M)).
    fequal.  (* TODO abstract this step *)
    - ext A' B' f' t.
      unfold_ops @Map_compose @Map_const.
      rewrite (fun_map_id G).
      reflexivity.
    - ext A' B' [m1 m2].
      reflexivity.
  Qed.

  Corollary foldMap_traverse_I `{Monoid M} : forall `(g : B -> M) `(f : A -> B),
      foldMap T g ∘ traverse T (fun A => A) A B f = foldMap T (g ∘ f).
  Proof.
    intros.
    change (foldMap T g) with (map (fun A => A) (T B) M (foldMap T g)).
    rewrite (foldMap_traverse (fun A => A)).
    reflexivity.
  Qed.

  (** *** Composition with <<map>> *)
  (******************************************************************************)
  Corollary foldMap_map `{Monoid M} : forall `(g : B -> M) `(f : A -> B),
      foldMap T g ∘ map T A B f = foldMap T (g ∘ f).
  Proof.
    intros. apply foldMap_traverse_I.
  Qed.

  (** *** Homomorphism law *)
  (******************************************************************************)
  Lemma foldMap_morphism `{Monoid_Morphism M1 M2 ϕ} : forall `(f : A -> M1),
      ϕ ∘ foldMap T f = foldMap T (ϕ ∘ f).
  Proof.
    intros.
    inversion H5.
    rewrite (foldMap_to_traverse1 M1).
    change ϕ with (const (ϕ) (T False)).
    rewrite (trf_traverse_morphism T (G1 := const M1) (G2 := const M2)).
    reflexivity.
  Qed.

End with_functor.

Section foldMap_list.

  Import Monoid.Notations.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Monoid M} {A : Type}.

  #[export] Instance foldMap_list_morphism `{Monoid M} `(f : A -> M) : Monoid_Morphism (foldMap list f).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - cbn. reflexivity.
    - intros.
      unfold_ops @Monoid_op_list.
      rewrite (foldMap_to_traverse1 list M).
      unfold TraversableFunctor_list.
      rewrite (DerivedInstances.traverse_to_bindt list).
      rewrite (bindt_list_app (const M)).
      cbn.
      simpl_monoid.
      unfold pure, Pure_const.
      rewrite (monoid_id_r).
      reflexivity.
  Qed.

End foldMap_list.

Import Traversable.Monad.DerivedInstances.

(** * <<tolist>> and <<toset>> / <<∈>>*)
(******************************************************************************)
Section tolist.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  #[export] Instance Tolist_Traverse `{Traverse T} : Tolist T :=
    fun A => foldMap T (ret list A).

  #[export] Instance Natural_Tolist_Traverse : Natural (@tolist T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Tolist_Traverse.
    rewrite (foldMap_morphism T).
    rewrite (foldMap_map T).
    rewrite (natural (ϕ := @ret list _)).
    reflexivity.
  Qed.

  Corollary tolist_to_runBatch {A : Type} (tag : Type) `(t : T A) :
    tolist T A t = runBatch (F := const (list A)) (ret list A : A -> const (list A) tag) (toBatch T tag t).
  Proof.
    unfold_ops @Tolist_Traverse.
    rewrite (foldMap_to_runBatch2 T tag).
    reflexivity.
  Qed.

  Lemma length_to_Batch_length : forall (A B : Type) (t : T A),
      length (tolist T A t) = length_Batch _ _ (T B) (toBatch T B t).
  Proof.
    intros.
    rewrite (tolist_to_runBatch B).
    induction (toBatch T B t).
    - cbn. reflexivity.
    - cbn.
      unfold_ops @Monoid_op_list.
      rewrite (List.app_length).
      rewrite <- IHb.
      cbn.
      rewrite PeanoNat.Nat.add_1_r.
      reflexivity.
  Qed.

End tolist.

(** ** Shapeliness *)
(******************************************************************************)
Section traversal_shapeliness.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Lemma shapeliness_tactical : forall A (b1 b2 : @Batch A A (T A)),
      runBatch (F := const (list A)) (ret list A) b1 = runBatch (F := const (list A)) (ret list A) b2 ->
      mapfst_Batch (const tt) b1 = mapfst_Batch (const tt) b2 ->
      runBatch id b1 = runBatch id b2.
  Proof.
    intros.
    induction b1, b2; cbn in *.
    - now inversion H2.
    - now inversion H1.
    - now inversion H1.
    - unfold monoid_op, Monoid_op_list in *.
      specialize (list_app_inv_l2 _ _ _ _ _ H1).
      specialize (list_app_inv_r2 _ _ _ _ _ H1).
      introv hyp1 hyp2. subst.
      erewrite IHb1. eauto. eauto.
      now inversion H2.
  Qed.

  Theorem shapeliness : forall A (t1 t2 : T A),
      shape T t1 = shape T t2 /\
      tolist T A t1 = tolist T A t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    assert (hyp1' : (toBatch T A ∘ shape T) t1 = (toBatch T A ∘ shape T) t2).
    { unfold compose, shape in *. now rewrite hyp1. }
    clear hyp1; rename hyp1' into hyp1.
    unfold shape in hyp1.
    rewrite (toBatch_mapfst T) in hyp1.
    rewrite (tolist_to_runBatch T A t1) in hyp2.
    rewrite (tolist_to_runBatch T A t2) in hyp2.
    change (id t1 = id t2).
    rewrite (id_to_runBatch T).
    unfold compose. auto using shapeliness_tactical.
  Qed.

End traversal_shapeliness.

(*
(** ** Listable/set-like instances *)
(******************************************************************************)
Section listable.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  #[export] Instance Listable_Traversable : ListableFunctor T.
  Proof.
    constructor; try typeclasses eauto.
    - unfold Listable.Functor.shapeliness. auto using (shapeliness T).
  Qed.

End listable.
 *)

Import Sets.Notations.
Import Sets.ElNotations.
Import Classes.Monad.DerivedInstances. (* Naturality of ret *)

Section toset.

  Context
    (T : Type -> Type)
    `{Traverse T}.

  #[export] Instance Toset_Traverse (T : Type -> Type) `{Traverse T} : El T :=
    fun A => foldMap T (ret set A).

  Context
    `{! TraversableFunctor T}.

  Lemma toset_to_tolist : forall (A : Type),
      @el T _ A = el list A ∘ tolist T A.
  Proof.
    intros.
    unfold_ops @Toset_Traverse.
    unfold_ops @Tolist_Traverse.
    rewrite (foldMap_morphism T).
    fequal. ext a. solve_basic_set.
  Qed.

  Theorem in_map_iff :
    forall (A B : Type) (f : A -> B) (t : T A) (b : B),
      b ∈ map T A B f t <-> exists (a : A), a ∈ t /\ f a = b.
  Proof.
    intros. unfold_ops @Toset_Traverse.
    compose near t.
    rewrite (foldMap_map T).
    change f with (map (fun A => A) A B f).
    rewrite <- (natural (F := (fun A => A)) (G := set)).
    rewrite <- (foldMap_morphism T).
    reflexivity.
  Qed.

End toset.

(** * Respectfulness properties *)
(******************************************************************************)
Section respectfulness_properties.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  #[local] Generalizable Variables A B.

  Lemma traverse_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse T G A B f1 t = traverse T G A B f2 t.
  Proof.
    introv ? hyp. do 2 (rewrite traverse_to_runBatch; auto).
    unfold el, Toset_Traverse in hyp.
    rewrite (foldMap_to_runBatch2 T B) in hyp.
    unfold compose in *.
    induction (toBatch T B t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros.
        apply hyp. now left.
      + apply hyp. now right.
  Qed.

  Lemma traverse_respectful_pure : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = pure G a) -> traverse T G A A f1 t = pure G t.
  Proof.
    intros.
    rewrite <- (traverse_id_purity T G).
    now apply (traverse_respectful G).
  Qed.

  Lemma traverse_respectful_map {A B} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure G (g a)) -> traverse T G A B f t = pure G (map T A B g t).
  Proof.
    intros. rewrite <- (traverse_id_purity T G).
    compose near t on right.
    rewrite (Traversable.Functor.DerivedInstances.traverse_map T G).
    apply (traverse_respectful); auto.
  Qed.

  Corollary traverse_respectful_id {A} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G A),
      (forall a, a ∈ t -> f a = pure G a) -> traverse T G A A f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity T G).
    now apply traverse_respectful.
  Qed.

  Corollary map_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> map T A B f1 t = map T A B f2 t.
  Proof.
    introv hyp. unfold_ops @Map_Traverse.
    apply (traverse_respectful (fun A => A)).
    assumption.
  Qed.


  Corollary map_respectful_id : forall `(f1 : A -> A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = a) -> map T A A f1 t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (fun_map_id T).
    apply map_respectful.
    assumption.
  Qed.

End respectfulness_properties.

(*
TODO: Prove reassembly is the opposite of disassembly

(** ** Reassembly operation *)
(******************************************************************************)
Section traversal_reassemble.

  Context
    `{TraversableGunctor T}.

  Fixpoint add_elements `(s : @Batch i1 o X) `(l : list i2) : @Batch (Maybe i2) o X :=
    match s with
    | Go t' => Go t'
    | Ap rest a =>
      match l with
      | nil => Ap (add_elements rest nil) None
      | cons a l' => Ap (add_elements rest l') (Just a)
      end
    end.

  Definition reassemble `(t : T X) `(l : list A) : Maybe (T A) :=
    runBatch id (add_elements (toBatch _ t) l).

End traversal_reassemble.
*)
