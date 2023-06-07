From Tealeaves Require Export
  Classes.Applicative
  Functors.Batch.

#[local] Generalizable Variable G A B C ϕ.

(** * "Kleisi"-style presentation of traversable functors *)
(******************************************************************************)
Section operations.

  Class Traverse
    (T : Type -> Type) := traverse :
      forall (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G} (A B : Type)
        (f : A -> G B), T A -> G (T B).

End operations.

(* We don't give a dedicated name or notation to the composition
   operation <<g ⋆ f = fmap F g ∘ f>> because it is trivial and one
   wants to avoid making up too many notations. *)

#[local] Arguments traverse (T)%function_scope {Traverse}
  G%function_scope {H H0 H1} (A B)%type_scope f%function_scope _.

Section class.

  Context
    (T : Type -> Type)
    `{Traverse T}.

  Class TraversableFunctor :=
    { trf_traverse_id : forall (A : Type),
        traverse T (fun A => A) A A id = @id (T A);
      trf_traverse_traverse :
      forall (G1 G2 : Type -> Type)
        `(Applicative G2) `(Applicative G1)
          `(g : B -> G2 C) `(f : A -> G1 B),
          fmap G1 (traverse T G2 B C g) ∘ traverse T G1 A B f =
            traverse T (G1 ∘ G2) A C (fmap G1 g ∘ f);
      trf_traverse_morphism : forall `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : A -> G1 B),
          ϕ (T B) ∘ traverse T G1 A B f = traverse T G2 A B (ϕ B ∘ f);
    }.

End class.

#[global] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} {A B}%type_scope f%function_scope _.


(** * Kleisli traversable functor to functor *)
(******************************************************************************)

(** ** <<Functor>> instance *)
(******************************************************************************)
Module ToFunctor.

  Section operation.

    Context
      (T : Type -> Type)
      `{Traverse T}.

  #[export] Instance Fmap_Traverse : Fmap T :=
      fun (A B : Type) (f : A -> B) => traverse T (fun A => A) f.

  End operation.

  Section properties.

    Context
      (T : Type -> Type)
      `{TraversableFunctor T}.

    Lemma fmap_id : forall (A : Type),
        fmap T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Fmap_Traverse.
      now rewrite (trf_traverse_id T).
    Qed.

    Lemma fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Traverse.
      change (traverse T (fun A : Type => A) g)
        with (fmap (fun A => A) (traverse T (fun A => A) g)).
      rewrite (trf_traverse_traverse T (fun A => A));
        try typeclasses eauto.
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_fmap_id := fmap_id;
        fun_fmap_fmap := fmap_fmap;
      |}.

    (** *** Specification for <<fmap>> *)
    (******************************************************************************)
    Corollary fmap_to_traverse : forall (A B : Type) (f : A -> B),
        fmap T f = traverse T (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    (** *** Purity laws *)
    (******************************************************************************)
    Corollary traverse_purity {G1 G2} `{Applicative G2} `{Applicative G1} : forall A B (f : A -> G1 B),
        traverse T (G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ traverse T G1 f.
    Proof.
      intros.
      assert (ApplicativeMorphism G1 (G2 ∘ G1) (@pure G2 H2 ○ G1)).
      { constructor; try typeclasses eauto.
        - intros. unfold_ops @Fmap_compose.
          now rewrite (app_pure_natural G2).
        - intros. reflexivity.
        - intros. unfold_ops @Mult_compose. cbn.
          rewrite <- (appmor_mult (fun A => A) G2 (G1 A0) (G1 B0) x y (ϕ := @pure G2 _ )).
          change ((mult (fun A1 : Type => A1) (x, y))) with (x, y).
          now rewrite (app_pure_natural G2). }
      now rewrite (trf_traverse_morphism T f (G1 := G1) (G2 := G2 ∘ G1) (ϕ := (fun A => @pure G2 _ (G1 A)))).
    Qed.

    (** *** Composition between <<traverse>> and <<fmap>> *)
    (******************************************************************************)
    Lemma fmap_traverse : forall (G1 : Type -> Type) (A B C : Type) `{Applicative G1}
                            (g : B -> C)
                            (f : A -> G1 B),
        fmap G1 (fmap T g) ∘ traverse T G1 f =
          traverse T G1 (fmap G1 g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Traverse.
      rewrite (trf_traverse_traverse T G1 (fun A => A));
        try typeclasses eauto.
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    Lemma traverse_fmap: forall (G2 : Type -> Type) (A B C : Type) `{Applicative G2}
                           (g : B -> G2 C)
                           (f : A -> B),
        traverse T G2 g ∘ fmap T f =
          traverse T G2 (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Traverse.
      change (traverse T G2 g)
        with (fmap (fun A => A) (traverse T G2 g)).
      rewrite (trf_traverse_traverse T (fun A => A) G2);
        try typeclasses eauto.
      fequal. now rewrite Mult_compose_identity2.
    Qed.

  End properties.

End ToFunctor.

Import Batch.Notations.
Import ToFunctor.

(** * Traversals as <<Batch>> coalgebras *)
(******************************************************************************)
Section traversals_coalgebras.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Definition batch {A : Type} (B : Type) : A -> @Batch A B B :=
    fun a => (Done (@id B)) ⧆ a.

  Definition toBatch {A : Type} (B : Type) : T A -> @Batch A B (T B) :=
    traverse T (Batch A B) (batch B).

End traversals_coalgebras.

(** ** Basic lemmas for <<runBatch>> *)
(******************************************************************************)
Lemma runBatch_batch : forall  `{Applicative G} (A B : Type) (f : A -> G B),
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
Section with_kleisli.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse T G f = runBatch f ∘ toBatch T B.
  Proof.
    unfold toBatch.
    rewrite (trf_traverse_morphism T (ϕ := @runBatch A G B f _ _ _)).
    fequal. ext a. cbn. now rewrite ap1.
  Qed.

  Corollary fmap_to_runBatch `(f : A -> B) :
    fmap T f = runBatch f ∘ toBatch T B.
  Proof.
    unfold_ops @Fmap_Traverse.
    now rewrite traverse_to_runBatch.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
      @id (T A) = runBatch (@id A) ∘ toBatch T A.
  Proof.
    intros. rewrite <- (trf_traverse_id T).
    rewrite traverse_to_runBatch.
    reflexivity.
  Qed.

End with_kleisli.

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

(** ** Naturality properties for <<toBatch>> *)
(******************************************************************************)
Section naturality.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  (** *** A naturality property for <<toBatch>> *)
  (******************************************************************************)
  Lemma toBatch_mapfst `(f : A -> B) {C : Type} :
    toBatch T C ∘ fmap T f = mapfst_Batch f ∘ toBatch T C.
  Proof.
    unfold toBatch.
    rewrite (traverse_fmap T); try typeclasses eauto.
    do 2 rewrite (traverse_to_runBatch T). ext t.
    unfold compose. induction (toBatch T C t).
    - cbv. reflexivity.
    - do 2 rewrite runBatch_rw2. rewrite IHb.
      now rewrite mapfst_Batch3.
  Qed.

End naturality.

#[local] Generalizable Variable M.

(** * <<foldMap>> *)
(******************************************************************************)
Definition foldMap (T : Type -> Type) `{Monoid_op M}
  `{Monoid_unit M} `{Traverse T} {A : Type} :
  (A -> M) -> T A -> M := fun f => traverse (B := False) T (const M) f.

(** ** Lemmas for traversals with constant applicative functors *)
(******************************************************************************)
Section constant_applicatives.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Monoid M}
    `(f : A -> M).

  Lemma traverse_constant_applicative1: forall (B : Type),
      traverse (B := B) T (const M) f = traverse (B := False) T (const M) f.
  Proof.
    intros.
    change_right (fmap (B := T B) (const M) (fmap T exfalso)
                    ∘ traverse (B := False) T (const M) (f : A -> const M False)).
    rewrite (fmap_traverse T (const M)).
    - reflexivity.
    - typeclasses eauto.
  Qed.

  Lemma traverse_constant_applicative2 : forall (fake1 fake2 : Type),
    traverse (B := fake1) T (const M) f = traverse (B := fake2) T (const M) f.
  Proof.
    intros. rewrite (traverse_constant_applicative1 fake1).
    rewrite (traverse_constant_applicative1 fake2).
    reflexivity.
  Qed.

End constant_applicatives.

(** ** Basic properties of <<foldMap>> *)
(******************************************************************************)
Section with_functor.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Monoid M}.

  (** *** As a special case of <<traverse>> *)
  (******************************************************************************)
  Lemma foldMap_to_traverse : forall (fake : Type) `(f : A -> M),
      foldMap T f = traverse (B := fake) T (const M) f.
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_constant_applicative2 T f False fake).
    now rewrite (traverse_constant_applicative2 T f fake False).
  Qed.

  (** *** As a special case of <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMap_to_runBatch : forall (fake : Type) `(f : A -> M),
      foldMap T f = runBatch f ∘ toBatch T fake.
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_constant_applicative2 T f False fake).
    now rewrite (traverse_to_runBatch T (G := const M) f).
  Qed.

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma foldMap_traverse `{Applicative G} : forall `(g : B -> M) `(f : A -> G B),
      fmap G (foldMap T g) ∘ traverse T G f =
        foldMap T (fmap G g ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (trf_traverse_traverse T G (const M) _ _ (B := B) (C := False)).
    fequal.
    - ext A' B' f' t. unfold_ops @Fmap_compose @Fmap_const.
      now rewrite (fun_fmap_id G).
    - ext A' B' [m1 m2]. reflexivity.
  Qed.

  Corollary foldMap_traverse_I : forall `(g : B -> M) `(f : A -> B),
      foldMap T g ∘ traverse T (fun A => A) f = foldMap T (g ∘ f).
  Proof.
    intros. change (foldMap T g) with (fmap (fun A => A) (foldMap T g)).
    rewrite (foldMap_traverse (G := fun A => A)).
    reflexivity.
  Qed.

  (** *** Composition with <<fmap>> *)
  (******************************************************************************)
  Corollary foldMap_fmap : forall `(g : B -> M) `(f : A -> B),
      foldMap T g ∘ fmap T f = foldMap T (g ∘ f).
  Proof.
    intros. apply foldMap_traverse_I.
  Qed.

  (** *** Homomorphism law *)
  (******************************************************************************)
  Lemma foldMap_morphism `{Monoid_Morphism M1 M2 ϕ} : forall `(f : A -> M1),
      ϕ ∘ foldMap T f = foldMap T (ϕ ∘ f).
  Proof.
    intros. inversion H6. unfold foldMap.
    change ϕ with (const (ϕ) (T False)).
    rewrite (trf_traverse_morphism T (G1 := const M1) (G2 := const M2)).
    reflexivity.
  Qed.

End with_functor.

Import Sets.Notations.
Import Setlike.Functor.Notations.

(** * <<tolist>> and <<toset>> / <<∈>>*)
(******************************************************************************)
Section tolist.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  #[export] Instance Tolist_Traverse `{Traverse T} : Tolist T :=
    fun A => foldMap T (ret list).

  #[export] Instance Toset_Traverse `{Traverse T} : Toset T :=
    fun A => foldMap T (ret set).

  Lemma toset_to_tolist : forall (A : Type),
      @toset T _ A = toset list ∘ tolist T.
  Proof.
    intros. unfold_ops @Toset_Traverse @Tolist_Traverse.
    rewrite (foldMap_morphism T).
    fequal. ext a. solve_basic_set.
  Qed.

  #[export] Instance Natural_Tolist_Traverse : Natural (@tolist T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Tolist_Traverse.
    rewrite (foldMap_morphism T).
    rewrite (foldMap_fmap T).
    rewrite (natural (ϕ := @ret list _)).
    reflexivity.
  Qed.

  Corollary tolist_to_runBatch (tag : Type) `(t : T A) :
    tolist T t = runBatch (F := const (list A)) (ret list : A -> const (list A) tag) (toBatch T tag t).
  Proof.
    unfold_ops @Tolist_Traverse.
    rewrite (foldMap_to_runBatch T tag).
    reflexivity.
  Qed.

  Theorem in_fmap_iff :
    forall `(f : A -> B) (t : T A) (b : B),
      b ∈ fmap T f t <-> exists (a : A), a ∈ t /\ f a = b.
  Proof.
    intros. unfold_ops @Toset_Traverse.
    compose near t.
    rewrite (foldMap_fmap T).
    change f with (fmap (fun A => A) f).
    rewrite <- (natural (F := (fun A => A)) (G := set)).
    rewrite <- (foldMap_morphism T).
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
      runBatch (F := const (list A)) (ret list) b1 = runBatch (F := const (list A)) (ret list) b2 ->
      mapfst_Batch (const tt) b1 = mapfst_Batch (const tt) b2 ->
      runBatch id b1 = runBatch id b2.
  Proof.
    intros. induction b1, b2; cbn in *.
    - now inversion H2.
    - now inversion H1.
    - now inversion H1.
    - specialize (list_app_inv_l2 _ _ _ _ _ H1).
      specialize (list_app_inv_r2 _ _ _ _ _ H1).
      introv hyp1 hyp2. subst.
      erewrite IHb1. eauto. eauto.
      now inversion H2.
  Qed.

  Theorem shapeliness : forall A (t1 t2 : T A),
      shape T t1 = shape T t2 /\
      tolist T t1 = tolist T t2 ->
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

(** * Purity *)
(* TODO Move me *)
(******************************************************************************)
Theorem traverse_id_purity : forall T `{TraversableFunctor T} `{Applicative G} (A : Type),
    traverse T G (pure G) = @pure G _ (T A).
Proof.
  intros.
  change (@pure G _ A) with (@pure G _ A ∘ id).
  rewrite <- (trf_traverse_morphism T (G1 := fun A => A) (G2 := G)).
  now rewrite (trf_traverse_id T).
Qed.

(** * Respectfulness properties *)
(******************************************************************************)
Section respectfulness_properties.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Lemma traverse_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse T G f1 t = traverse T G f2 t.
  Proof.
    introv ? hyp. do 2 (rewrite traverse_to_runBatch; auto).
    unfold toset, Toset_Traverse in hyp.
    rewrite (foldMap_to_runBatch T B) in hyp.
    unfold compose in *.
    induction (toBatch T B t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros. apply hyp. now left.
      + apply hyp. now right.
  Qed.

  Lemma traverse_respectful_pure : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = pure G a) -> traverse T G f1 t = pure G t.
  Proof.
    intros.
    rewrite <- (traverse_id_purity T).
    now apply (traverse_respectful G).
  Qed.

  Lemma traverse_respectful_fmap {A B} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure G (g a)) -> traverse T G f t = pure G (fmap T g t).
  Proof.
    intros. rewrite <- (traverse_id_purity T). compose near t on right.
    rewrite (traverse_fmap T G); auto. apply (traverse_respectful); auto.
  Qed.

  Corollary traverse_respectful_id {A} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G A),
      (forall a, a ∈ t -> f a = pure G a) -> traverse T G f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity T).
    now apply traverse_respectful.
  Qed.

  Corollary fmap_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> fmap T f1 t = fmap T f2 t.
  Proof.
    introv hyp. unfold_ops @Fmap_Traverse.
    apply (traverse_respectful (fun A => A)).
    assumption.
  Qed.

  Corollary fmap_respectful_id : forall `(f1 : A -> A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = a) -> fmap T f1 t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (fun_fmap_id T).
    apply fmap_respectful.
    assumption.
  Qed.

End respectfulness_properties.
