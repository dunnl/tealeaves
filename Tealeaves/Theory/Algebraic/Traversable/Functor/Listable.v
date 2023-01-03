From Tealeaves Require Export
  Classes.Algebraic.Listable.Functor
  Theory.Algebraic.Traversable.Functor.ToKleisli.
From Tealeaves Require Import
  Theory.Algebraic.Traversable.Functor.Const
  Theory.Algebraic.Listable.Functor.Properties
  Functors.Batch.

#[local] Generalizable Variables T G A.

(** ** The [tolist] operation *)
(** We only define this operation and prove it forms a natural
transformation. This does not immediately give a [ListableFunctor]
instance until we prove the shapeliness property in another section
below. *)
(******************************************************************************)
(* set <<tag := False>> to emphasize this type is arbitrary *)
#[global] Instance Tolist_Traversable `{Fmap T} `{Dist T} : Tolist T :=
  fun A => unconst ∘ dist T (Const (list A)) ∘
                fmap T (mkConst (tag := False) ∘ ret list (A := A)).

#[global] Instance Natural_tolist_Traversable
         `{TraversableFunctor T} : Natural (@tolist T Tolist_Traversable).
Proof.
  constructor; try typeclasses eauto.
  intros. unfold_ops @Tolist_Traversable.
  repeat reassociate <-.
  rewrite (mapConst_2 (fmap list f)).
  repeat reassociate -> on left;
    reassociate <- near (mapConst (fmap list f)).
  rewrite <- (dist_morph T).
  repeat reassociate ->.
  repeat rewrite (fun_fmap_fmap T).
  reflexivity.
Qed.

(** ** Specifications for <<tolist>> and <<foldMap>> *)
(******************************************************************************)
Section TraversableFunctor_fold_spec.

  Context
    (T : Type -> Type)
      `{TraversableFunctor T}.

  Import ToKleisli.Operation.
  Import ToKleisli.Instance.

  (** *** Specification for <<Tolist_Traversable>> *)
  (******************************************************************************)
  Theorem traversable_tolist_spec {A : Type} (tag : Type) :
    @tolist T Tolist_Traversable A
    = @traverse T _ (const (list A))
        (Fmap_const)
        (Pure_const)
        (Mult_const) A tag (ret list).
  Proof.
    intros. unfold tolist, Tolist_Traversable;
      unfold traverse, Traverse_alg.
    rewrite <- (fun_fmap_fmap T). reassociate <- on left.
    rewrite (traversable_const_spec T (M := list A) False).
    now rewrite (dist_const1 T tag).
  Qed.

  Theorem traversable_tolist_spec2 {A : Type} :
    @tolist T Tolist_Traversable A
    = foldMap (ret list).
  Proof.
    intros. unfold foldMap. unfold fold.
    reassociate -> on right. rewrite <- (natural (ϕ := @tolist T _)).
    reassociate <- on right.
    ext t. unfold compose.
    induction (tolist T t).
    - easy.
    - cbn. now rewrite <- IHl.
  Qed.

  Lemma tolist_to_runBatch `{Applicative G} `(t : T A) :
    tolist T t = runBatch (ret list : A -> const (list A) A) (iterate A t).
  Proof.
    unfold iterate. compose near t on right.
    rewrite (traverse_morphism T (ϕ := @runBatch A (const (list A)) _ (ret list) _ _ _)).
    rewrite (traversable_tolist_spec A).
    reflexivity.
  Qed.

  (** *** Specification for folding over traversables *)
  (******************************************************************************)
  Theorem traversable_fold_spec (tag : Type) `{Monoid M} :
    @fold T Tolist_Traversable M _ _
    = @dist T _ (const M)
            (Fmap_const)
            (Pure_const)
            (Mult_const) tag.
  Proof.
    unfold fold. rewrite (traversable_tolist_spec tag). unfold traverse.
    reassociate <- on left.
    change (@List.fold M _ _) with (const (@List.fold M _ _) (T tag)).
    rewrite <- (dist_morph T (ϕ := const (@List.fold M _ _))).
    reassociate -> on left.
    rewrite (fun_fmap_fmap T).
    replace (const List.fold tag ∘ ret list) with (@id M).
    - now rewrite (fun_fmap_id T).
    - ext m. cbn. now simpl_monoid.
  Qed.

  Theorem traversable_foldMap_spec (tag : Type) `{Monoid M} `{f : A -> M} :
    @foldMap T _ Tolist_Traversable A M _ _  f =
    @traverse T (const M) _ _ (Fmap_const) (Pure_const) (Mult_const) A tag f.
  Proof.
    unfold foldMap. now rewrite (traversable_fold_spec tag).
  Qed.

  Lemma foldMap_to_runBatch
    `{Monoid M} `(f : A -> M) (t : T A) (B : Type) :
    foldMap f t = runBatch_monoid f (iterate B t).
  Proof.
    rewrite runBatch_monoid1.
    rewrite (traversable_foldMap_spec B).
    unfold traverse. rewrite dist_to_runBatch'.
    unfold compose. rewrite iterate_mapfst.
    induction (iterate B t).
    - reflexivity.
    - cbn. fequal. now rewrite IHb.
  Qed.

  Lemma tolist_to_runBatch2 `(t : T A) (B : Type) :
    tolist T t = runBatch_monoid (ret list) (iterate B t).
  Proof.
    rewrite traversable_tolist_spec2.
    now rewrite <- foldMap_to_runBatch.
  Qed.

End TraversableFunctor_fold_spec.

(** * Shapeliness *)
(******************************************************************************)
Section traversal_shapeliness.

  Import Batch.Notations.

  Context
    `{TraversableFunctor T}.

  Lemma shapeliness_tactical : forall A (b1 b2 : @Batch A A (T A)),
      runBatch_monoid (ret list) b1 = runBatch_monoid (ret list) b2 ->
      mapfst_Batch (const tt) b1 = mapfst_Batch (const tt) b2 ->
      runBatch id b1 = runBatch id b2.
  Proof.
    intros. induction b1, b2; cbn in *.
    - now inversion H3.
    - now inversion H2.
    - now inversion H2.
    - specialize (list_app_inv_l2 _ _ _ _ _ H2).
      specialize (list_app_inv_r2 _ _ _ _ _ H2).
      introv hyp1 hyp2. subst.
      erewrite IHb1. eauto. eauto.
      now inversion H3.
  Qed.

  Theorem shapeliness : forall A (t1 t2 : T A),
      shape T t1 = shape T t2 /\
      tolist T t1 = tolist T t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    assert (hyp1' : iterate A (shape T t1) = iterate A (shape T t2)).
    { unfold shape in *. now rewrite hyp1. }
    clear hyp1; rename hyp1' into hyp1.
    unfold shape in hyp1.
    do 2 rewrite iterate_mapfst in hyp1.
    rewrite (tolist_to_runBatch2 T t1 A) in hyp2.
    rewrite (tolist_to_runBatch2 T t2 A) in hyp2.
    rewrite (id_to_runBatch t1).
    rewrite (id_to_runBatch t2).
    auto using shapeliness_tactical.
  Qed.

End traversal_shapeliness.

#[global] Instance ListableFunctor_Traversable `{TraversableFunctor T} : ListableFunctor T :=
  {| lfun_shapeliness := shapeliness (T := T) |}.

(** * Respectfulness properties *)
(******************************************************************************)
Section TraversableFunctor_respectfulness.

  Import Setlike.Notations.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G}.

End TraversableFunctor_respectfulness.
