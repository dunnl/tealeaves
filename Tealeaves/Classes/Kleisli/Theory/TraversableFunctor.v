From Tealeaves Require Export
  Classes.Kleisli.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor
  Classes.Categorical.Monad (Return, ret)
  Functors.Backwards
  Functors.Constant
  Functors.Identity
  Functors.Early.List
  Functors.ProductFunctor
  Misc.Prop.

From Tealeaves Require Import
  Classes.Categorical.ApplicativeCommutativeIdempotent.

From Tealeaves Require
  Classes.Coalgebraic.TraversableFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor.

Import Kleisli.TraversableFunctor.Notations.
Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import Subset.Notations.
Import Categorical.Applicative.Notations.
Import ProductFunctor.Notations. (* ◻ *)

#[local] Generalizable Variable T G M ϕ A B C.

(** * Miscellaneous Properties of Traversable Functors *)
(**********************************************************************)

(** ** Interaction between <<traverse>> and <<pure>> *)
(**********************************************************************)
Section traversable_purity.

  Context
    `{TraversableFunctor T}.

  Theorem traverse_purity1:
    forall `{Applicative G},
      `(traverse (G := G) pure = @pure G _ (T A)).
  Proof.
    intros.
    change (@pure G _ A) with (@pure G _ A ∘ id).
    rewrite <- (trf_traverse_morphism (G1 := fun A => A) (G2 := G)).
    rewrite trf_traverse_id.
    reflexivity.
  Qed.

  Lemma traverse_purity2:
    forall `{Applicative G2}
      `{Applicative G1}
      `(f: A -> G1 B),
      traverse (G := G2 ∘ G1) (pure (F := G2) ∘ f) =
        pure (F := G2) ∘ traverse f.
  Proof.
    intros.
    rewrite <- (trf_traverse_morphism (G1 := G1) (G2 := G2 ∘ G1)
                 (ϕ := fun A => @pure G2 _ (G1 A))).
    reflexivity.
  Qed.

  Context
    `{Map T}
    `{! Compat_Map_Traverse T}.

  Lemma traverse_purity3:
    forall `{Applicative G2}
      `(f: A -> B),
      traverse (T := T) (G := G2) (pure (F := G2) ∘ f) =
        pure (F := G2) ∘ map f.
  Proof.
    intros.
    rewrite <- (trf_traverse_morphism (G1 := fun A => A) (G2 := G2)
                 (ϕ := fun A => @pure G2 _ (A))).
    rewrite map_to_traverse.
    reflexivity.
  Qed.

End traversable_purity.

(** * Factorizing Operations through <<runBatch>> *)
(**********************************************************************)
Section factorize_operations.

  Import Coalgebraic.TraversableFunctor.
  Import Adapters.KleisliToCoalgebraic.TraversableFunctor.

  Context
    `{Map T}
    `{ToBatch T}
    `{Traverse T}
    `{! Kleisli.TraversableFunctor.TraversableFunctor T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  (** ** Factoring operations through <<toBatch>> *)
  (********************************************************************)
  Lemma traverse_through_runBatch
    `{Applicative G} `(f: A -> G B):
    traverse f = runBatch f ∘ toBatch.
  Proof.
    rewrite toBatch_to_traverse.
    rewrite trf_traverse_morphism.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary map_through_runBatch {A B: Type} (f: A -> B):
    map f = runBatch (G := fun A => A) f ∘ toBatch.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch: forall (A: Type),
      id = runBatch (G := fun A => A) id ∘ toBatch (T := T) (A' := A).
  Proof.
    intros.
    rewrite <- trf_traverse_id.
    rewrite (traverse_through_runBatch (G := fun A => A)).
    reflexivity.
  Qed.

  (** ** Naturality of <<toBatch>> *)
  (********************************************************************)
  Lemma toBatch_mapfst: forall (A B A': Type) (f: A -> B),
      toBatch (A := B) (A' := A') ∘ map f =
        mapfst_Batch f ∘ toBatch (A := A) (A' := A').
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite traverse_map.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism
               (morphism := ApplicativeMorphism_mapfst_Batch f)).
    rewrite ret_natural.
    reflexivity.
  Qed.

  Lemma toBatch_mapsnd: forall (X A A': Type) (f: A -> A'),
      mapsnd_Batch f ∘ toBatch =
        map (map f) ∘ toBatch (A := X) (A' := A).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism
               (morphism := ApplicativeMorphism_mapsnd_Batch f)).
    rewrite ret_dinatural.
    rewrite toBatch_to_traverse.
    rewrite map_traverse.
    reflexivity.
  Qed.

End factorize_operations.

(** * Traversals by Particular Applicative Functors *)
(**********************************************************************)

(** ** Product of Two Applicative Functors *)
(**********************************************************************)
Section traverse_applicative_product.

  Definition applicative_arrow_combine {F G A B}
    `(f: A -> F B) `(g: A -> G B): A -> (F ◻ G) B :=
    fun a => product (f a) (g a).

  #[local] Notation "f <◻> g" :=
    (applicative_arrow_combine f g) (at level 60): tealeaves_scope.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{Applicative G1}
    `{Applicative G2}.

  Variables
    (A B: Type)
    (f: A -> G1 B)
    (g: A -> G2 B).

  Lemma traverse_product1: forall (t: T A),
      pi1 (traverse (f <◻> g) t) = traverse f t.
  Proof.
    intros.
    pose (ApplicativeMorphism_pi1 G1 G2).
    compose near t on left.
    rewrite trf_traverse_morphism.
    reflexivity.
  Qed.

  Lemma traverse_product2: forall (t: T A),
      pi2 (traverse (f <◻> g) t) = traverse g t.
  Proof.
    intros.
    pose (ApplicativeMorphism_pi2 G1 G2).
    compose near t on left.
    rewrite trf_traverse_morphism.
    reflexivity.
  Qed.

  Theorem traverse_product_spec:
    traverse (f <◻> g) = traverse f <◻> traverse g.
  Proof.
    intros.
    ext t.
    unfold applicative_arrow_combine at 2.
    erewrite <- traverse_product1.
    erewrite <- traverse_product2.
    rewrite <- product_eta.
    reflexivity.
  Qed.

End traverse_applicative_product.

(** ** Constant Applicative Functors *)
(**********************************************************************)
Section constant_applicatives.

  Context
    `{Kleisli.TraversableFunctor.TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{Monoid M}.

  Lemma traverse_const1:
    forall {A: Type} (B: Type) `(f: A -> M),
      traverse (G := const M) (B := False) f =
        traverse (G := const M) (B := B) f.
  Proof.
    intros.
    change_left
      (map (F := const M) (A := T False)
         (B := T B) (map (F := T) (A := False) (B := B) exfalso)
         ∘ traverse (T := T) (G := const M)
         (B := False) (f: A -> const M False)).
    rewrite (map_traverse (G1 := const M)).
    reflexivity.
  Qed.

  Lemma traverse_const2:
    forall {A: Type} (f: A -> M) (fake1 fake2: Type),
      traverse (G := const M) (B := fake1) f =
        traverse (G := const M) (B := fake2) f.
  Proof.
    intros.
    rewrite <- (traverse_const1 fake1).
    rewrite -> (traverse_const1 fake2).
    reflexivity.
  Qed.

End constant_applicatives.

(** ** Traversals by Commutative Applicatives *)
(**********************************************************************)
Section traversals_commutative.

  Import Coalgebraic.TraversableFunctor.
  Import KleisliToCoalgebraic.TraversableFunctor.

  Lemma traverse_commutative:
    forall `{Kleisli.TraversableFunctor.TraversableFunctor T}
      `{ToBatch T}
      `{! Compat_ToBatch_Traverse T}
      `{ApplicativeCommutative G}
      (A B: Type) (f: A -> G B),
      forwards ∘ traverse (T := T)
        (G := Backwards G) (mkBackwards ∘ f) =
        traverse (T := T) f.
  Proof.
    intros. ext t. unfold compose.
    do 2 rewrite traverse_through_runBatch.
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - (*LHS *)
      rewrite runBatch_rw2.
      rewrite forwards_ap.
      rewrite IHb.
      (* RHS *)
      rewrite runBatch_rw2.
      rewrite <- (ap_swap (a := f a)).
      reflexivity.
  Qed.

End traversals_commutative.

(*
(** ** Traversals by Subset *)
(**********************************************************************)
Section traversals_by_subset.

  Import Coalgebraic.TraversableFunctor.
  Import KleisliToCoalgebraic.TraversableFunctor.

  Lemma traverse_by_subset:
    forall `{Kleisli.TraversableFunctor.TraversableFunctor T}
      `{ToBatch T}
      `{! Compat_ToBatch_Traverse T}
      (A B: Type) (f: A -> subset B),
      forwards ∘ traverse (T := T)
        (G := Backwards subset) (mkBackwards ∘ f) =
        traverse (T := T) f.
  Proof.
    intros.
    rewrite traverse_commutative.
    intros. ext t. unfold compose.
    do 2 rewrite traverse_through_runBatch.
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn. rewrite IHb.
      unfold ap.
      ext c.
      unfold_ops @Mult_subset.
      unfold_ops @Map_subset.
      propext.
      { intros [[mk b'] [[[b'' c'] [rest1 rest2]] Heq]].
        cbn in rest2.
        inversion rest2. subst.
        exists (mk, b'). tauto. }
      { intros [[mk b'] [rest1 rest2]].
        subst. exists (mk, b'). split; auto.
        exists (b', mk). tauto. }
  Qed.

End traversals_by_subset.
*)

(** * Derived Operation: <<foldmap>> *)
(**********************************************************************)

(** ** Operation <<foldMap>> *)
(**********************************************************************)
Definition foldMap
  {T: Type -> Type}
  `{Traverse T}
  `{op: Monoid_op M} `{unit: Monoid_unit M}
  {A: Type} (f: A -> M): T A -> M :=
  traverse (G := const M) (B := False) f.

Section foldMap.

  (** ** As a Special Case of <<traverse>> *)
  (********************************************************************)
  Lemma foldMap_to_traverse1
    `{Traverse T}
    `{Monoid M}: forall `(f: A -> M),
      foldMap (T := T) f =
        traverse (G := const M) (B := False) f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_to_traverse2
    `{Traverse T}
    `{! TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{Monoid M}: forall (fake: Type) `(f: A -> M),
      foldMap (T := T) f = traverse (G := const M) (B := fake) f.
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite (traverse_const1 fake f).
    reflexivity.
  Qed.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}.

  (** ** Composition with <<map>> and <<traverse>> *)
  (********************************************************************)
  Lemma foldMap_traverse
    `{Monoid M} (G: Type -> Type) {B: Type} `{Applicative G}:
    forall `(g: B -> M) `(f: A -> G B),
      map (A := T B) (B := M) (foldMap g) ∘ traverse f =
        foldMap (map g ∘ f).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite (trf_traverse_traverse (G1 := G) (G2 := const M) A B False).
    rewrite foldMap_to_traverse1.
    rewrite map_compose_const.
    rewrite mult_compose_const.
    reflexivity.
  Qed.

  Corollary foldMap_map `{Monoid M}: forall `(g: B -> M) `(f: A -> B),
      foldMap g ∘ map f = foldMap (g ∘ f).
  Proof.
    intros.
    rewrite map_to_traverse.
    change (foldMap g) with
      (map (F := fun A => A) (A := T B) (B := M) (foldMap g)).
    now rewrite (foldMap_traverse (fun X => X)).
  Qed.

  (** ** Composition with Homomorphisms *)
  (********************************************************************)
  Lemma foldMap_morphism (M1 M2: Type)
    `{morphism: Monoid_Morphism M1 M2 ϕ}:
    forall `(f: A -> M1), ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
  Proof.
    intros.
    inversion morphism.
    rewrite foldMap_to_traverse1.
    change ϕ with (const ϕ (T False)).
    rewrite (trf_traverse_morphism (T := T)
               (G1 := const M1) (G2 := const M2) A False).
    reflexivity.
  Qed.

  (** ** Factorizing through <<runBatch>> *)
  (********************************************************************)
  Import Coalgebraic.TraversableFunctor.
  Import KleisliToCoalgebraic.TraversableFunctor.

  Lemma foldMap_through_runBatch1
      `{ToBatch T}
      `{! Compat_ToBatch_Traverse T}
      {A: Type} `{Monoid M}: forall `(f: A -> M),
      foldMap f = runBatch (G := const M) f (B := False) ∘
                    toBatch (A := A) (A' := False).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_through_runBatch2
      `{ToBatch T}
      `{! Compat_ToBatch_Traverse T}
      `{Monoid M}: forall (A fake: Type) `(f: A -> M),
      foldMap f = runBatch (G := const M) f (B := fake) ∘
                    toBatch (A' := fake).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    change (fun _: Type => M) with (const (A := Type) M).
    rewrite (traverse_const1 fake).
    rewrite (traverse_through_runBatch (G := const M)).
    reflexivity.
  Qed.

  (** ** Factorizing through <<toBatch>> *)
  (********************************************************************)
  Lemma foldMap_through_toBatch
      `{ToBatch T}
      `{! Compat_ToBatch_Traverse T}
      `{Monoid M}: forall (A fake: Type) `(f: A -> M) (t: T A),
      foldMap f t = foldMap f (toBatch (A' := fake) t).
  Proof.
    intros.
    rewrite (foldMap_through_runBatch2 A fake).
    rewrite runBatch_via_traverse.
    unfold_ops @Map_const.
    unfold compose.
    rewrite (foldMap_to_traverse2 fake).
    reflexivity.
  Qed.

End foldMap.

(** * <<foldmap>> Corollary: <<tolist>> *)
(**********************************************************************)

(** ** Operation <<tolist>> *)
(**********************************************************************)
#[export] Instance Tolist_Traverse `{Traverse T}: Tolist T :=
  fun A => foldMap (ret (T := list)).

Class Compat_Tolist_Traverse
  (T: Type -> Type)
  `{Tolist_inst: Tolist T}
  `{Traverse_inst: Traverse T}: Prop :=
  compat_tolist_traverse:
    Tolist_inst = @Tolist_Traverse T Traverse_inst.

#[export] Instance Compat_Tolist_Traverse_Self
  `{Traverse_T: Traverse T}:
  @Compat_Tolist_Traverse T Tolist_Traverse Traverse_T
  := ltac:(reflexivity).

Lemma tolist_to_traverse
  `{Tolist_inst: Tolist T}
  `{Traverse_T: Traverse T}
  `{! Compat_Tolist_Traverse T}:
  forall (A: Type),
    tolist = foldMap (ret (T := list) (A := A)).
Proof.
  intros.
  rewrite compat_tolist_traverse.
  reflexivity.
Qed.

(** ** Relating <<foldMap (T := list)>> to <<foldMap_list>> *)
(**********************************************************************)
Lemma foldMap_eq_foldMap_list `{Monoid M}: forall (A: Type) (f: A -> M),
    foldMap (T := list) f = foldMap_list f.
Proof.
  intros. ext l. induction l.
  - cbn. reflexivity.
  - cbn. change (monoid_op ?x ?y) with (x ● y).
    unfold_ops @Pure_const.
    rewrite monoid_id_r.
    rewrite IHl.
    reflexivity.
Qed.

(** The <<tolist>> operation provided by the traversability of
    <<list>> is the identity. *)
Lemma Tolist_list_id: forall (A: Type),
    @tolist list (@Tolist_Traverse list Traverse_list) A = @id (list A).
Proof.
  intros.
  unfold_ops @Tolist_Traverse.
  rewrite foldMap_eq_foldMap_list.
  rewrite foldMap_list_ret_id.
  reflexivity.
Qed.

Section tolist.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}.

  (** ** Naturality *)
  (********************************************************************)
  #[export] Instance Natural_Tolist_Traverse: Natural (@tolist T _).
  Proof.
    constructor; try typeclasses eauto.
    - apply DerivedInstances.Functor_TraversableFunctor.
    - intros.
      unfold_ops @Tolist_Traverse.
      rewrite (foldMap_morphism (list A) (list B)).
      rewrite foldMap_map.
      rewrite (natural (ϕ := @ret list _)).
      reflexivity.
  Qed.

  (** ** Rewriting <<tolist>> to <<traverse>> *)
  (********************************************************************)
  Corollary tolist_to_foldMap: forall (A: Type),
      tolist (F := T) = foldMap (ret (T := list) (A := A)).
  Proof.
    reflexivity.
  Qed.

  Corollary tolist_to_traverse1: forall (A: Type),
      tolist =
        traverse (G := const (list A)) (B := False) (ret (T := list)).
  Proof.
    reflexivity.
  Qed.

  Corollary tolist_to_traverse2: forall (A fake: Type),
      tolist =
        traverse (G := const (list A)) (B := fake) (ret (T := list)).
  Proof.
    intros.
    rewrite tolist_to_traverse1.
    rewrite (traverse_const1 fake).
    reflexivity.
  Qed.

  (** ** Factoring <<tolist>> through <<runBatch>> and <<toBatch>> *)
  (********************************************************************)
  Import Coalgebraic.TraversableFunctor.
  Import KleisliToCoalgebraic.TraversableFunctor.

  Corollary tolist_through_toBatch
  `{ToBatch T}
  `{! Compat_ToBatch_Traverse T}
    {A: Type} (tag: Type) `(t: T A):
    tolist t = tolist (toBatch (A' := tag) t).
  Proof.
    rewrite (tolist_to_foldMap).
    rewrite (foldMap_through_toBatch A tag).
    reflexivity.
  Qed.

  Corollary tolist_through_runBatch
  `{ToBatch T}
  `{! Compat_ToBatch_Traverse T}
    {A: Type} (tag: Type) `(t: T A):
    tolist t =
      runBatch (G := const (list A))
        (ret (T := list): A -> const (list A) tag)
        (B := tag) (toBatch (A' := tag) t).
  Proof.
    rewrite (tolist_to_traverse2 A tag).
    rewrite (traverse_through_runBatch (G := const (list A))).
    reflexivity.
  Qed.

  (** ** Factoring any <<foldMap>> through <<tolist>> *)
  (********************************************************************)
  Corollary foldMap_through_tolist
    `{Monoid M}: forall (A: Type) (f: A -> M),
    foldMap (T := T) f = foldMap (T := list) f ∘ tolist.
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_eq_foldMap_list.
    rewrite (foldMap_morphism (list A) M).
    rewrite foldMap_list_ret.
    reflexivity.
  Qed.

End tolist.

(** * <<foldmap>> Corollary: <<tosubset>> *)
(**********************************************************************)

(** ** The <<tosubset>> Operation *)
(**********************************************************************)
#[local] Instance ToSubset_Traverse `{Traverse T}:
  ToSubset T :=
  fun A => foldMap (ret (T := subset)).

(** ** Compatibility *)
(**********************************************************************)
Class Compat_ToSubset_Traverse
  (T: Type -> Type)
  `{ToSubset_inst: ToSubset T}
  `{Traverse_inst: Traverse T}: Prop :=
  compat_tosubset_traverse:
    ToSubset_inst = @ToSubset_Traverse T Traverse_inst.

#[export] Instance Compat_ToSubset_Traverse_Self
  `{Traverse_T: Traverse T}:
  @Compat_ToSubset_Traverse T ToSubset_Traverse Traverse_T
  := ltac:(reflexivity).

Lemma tosubset_to_traverse
  `{ToSubset_inst: ToSubset T}
  `{Traverse_inst: Traverse T}
  `{! Compat_ToSubset_Traverse T}:
  forall (A: Type), tosubset (A := A) = foldMap (ret (T := subset)).
Proof.
  intros.
  rewrite compat_tosubset_traverse.
  reflexivity.
Qed.

Section elements.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{ToSubset T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}.

  (** ** Naturality *)
  (********************************************************************)
  #[export] Instance Natural_Element_Traverse:
    Natural (@tosubset T ToSubset_Traverse).
  Proof.
    constructor; try typeclasses eauto.
    - apply DerivedInstances.Functor_TraversableFunctor.
    - intros A B f.
      unfold tosubset, ToSubset_Traverse.
      rewrite (foldMap_morphism (subset A) (subset B)).
      rewrite foldMap_map.
      rewrite (natural (ϕ := @ret subset _)).
      reflexivity.
  Qed.

  (** ** Rewriting <<tosubset>> to <<foldMap>> *)
  (********************************************************************)
  Lemma tosubset_to_foldMap `{Compat_ToSubset_Traverse T}:
    forall (A: Type),
      @tosubset T _ A =
        foldMap (ret (T := subset)) (A := A).
  Proof.
    rewrite compat_tosubset_traverse.
    reflexivity.
  Qed.

  (** ** Factoring <<tosubset>> through <<tolist>> *)
  (********************************************************************)
  Corollary tosubset_through_tolist: forall A:Type,
      tosubset (F := T) (A := A) =
        tosubset (F := list) ∘ tolist (A := A).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_through_tolist.
    ext t. unfold compose; induction (tolist t).
    - reflexivity.
    - cbn. rewrite IHl.
      unfold transparent tcs.
      now simpl_subset.
  Qed.

  (** ** Rewriting <<a ∈ t>> to <<foldMap>> *)
  (********************************************************************)
  Lemma element_of_to_foldMap:
    forall (A: Type) (a: A),
      element_of a =
        foldMap (op := Monoid_op_or)
          (unit := Monoid_unit_false) {{a}}.
  Proof.
    intros.
    unfold element_of.
    rewrite tosubset_to_foldMap.
    ext t.
    change_left (evalAt a (foldMap (ret (T := subset)) t)).
    compose near t on left.
    rewrite (foldMap_morphism
               (subset A) Prop (ϕ := evalAt a)
               (ret (T := subset))).
    fequal. ext b. cbv. now propext.
  Qed.

  (** ** Factoring <<a ∈ t>> through <<tolist>> *)
  (********************************************************************)
  Corollary element_of_through_tolist:
    forall (A: Type) (a: A),
      element_of (F := T) a =
        element_of (F := list) a ∘ tolist (F := T).
  Proof.
    intros.
    ext t.
    unfold compose at 1.
    unfold element_of.
    rewrite tosubset_through_tolist.
    reflexivity.
  Qed.

  Corollary in_iff_in_tolist:
    forall (A: Type) (a: A) (t: T A),
      a ∈ t <-> a ∈ tolist t.
  Proof.
    intros.
    now rewrite element_of_through_tolist.
  Qed.

  (** ** Factoring <<tosubset>> through <<runBatch>> *)
  (********************************************************************)
  Import Coalgebraic.TraversableFunctor.
  Import KleisliToCoalgebraic.TraversableFunctor.

  Lemma tosubset_through_runBatch1
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse T}
  : forall (A: Type),
      tosubset =
        runBatch (G := const (A -> Prop))
          (ret (T := subset) (A := A)) (B := False) ∘
          toBatch (A' := False).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_through_runBatch1.
    reflexivity.
  Qed.

  Lemma tosubset_through_runBatch2
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse T}
  : forall (A tag: Type),
      tosubset =
        runBatch (G := const (A -> Prop))
          (ret (T := subset)) (B := tag) ∘
          toBatch (A' := tag).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite (foldMap_through_runBatch2 A tag).
    reflexivity.
  Qed.

End elements.

#[export] Instance Compat_ToSubset_Tolist_Traverse
  `{TraversableFunctor T}:
  @Compat_ToSubset_Tolist T
    (@ToSubset_Traverse T _)
    (@Tolist_Traverse T _).
Proof.
  hnf.
  unfold_ops @ToSubset_Traverse.
  unfold_ops @ToSubset_Tolist.
  unfold_ops @Tolist_Traverse.
  ext A.
  rewrite (foldMap_morphism (list A) (subset A)
             (ϕ := @tosubset list ToSubset_list A)).
  rewrite tosubset_list_hom1.
  reflexivity.
Qed.

(** * <<foldmap>> Corollary: <<Forall, Forany>> *)
(**********************************************************************)
Section quantification.

  Context
    `{TraversableFunctor T}
    `{! ToSubset T}
    `{! Compat_ToSubset_Traverse T}.

  (** ** Operations <<Forall>> and <<Forany>> *)
  (********************************************************************)
  Definition Forall `(P: A -> Prop): T A -> Prop :=
    @foldMap T _ Prop Monoid_op_and Monoid_unit_true A P.

  Definition Forany `(P: A -> Prop): T A -> Prop :=
    @foldMap T _ Prop Monoid_op_or Monoid_unit_false A P.

  (** ** Specification via <<element_of>> *)
  (********************************************************************)
  Lemma forall_iff `(P: A -> Prop) (t: T A):
    Forall P t <-> forall (a: A), a ∈ t -> P a.
  Proof.
    unfold Forall.
    rewrite foldMap_through_tolist.
    unfold compose at 1.
    setoid_rewrite in_iff_in_tolist.
    rewrite foldMap_eq_foldMap_list.
    induction (tolist t).
    - simpl_list.
      unfold_ops @Monoid_unit_true.
      unfold_ops @Monoid_unit_subset.
      setoid_rewrite element_of_list_nil.
      intuition.
    - simpl_list.
      unfold_ops @Monoid_op_and.
      unfold_ops @Monoid_op_subset.
      unfold_ops @Return_subset.
      rewrite IHl.
      setoid_rewrite element_of_list_cons.
      firstorder. now subst.
  Qed.

  Lemma forany_iff `(P: A -> Prop) (t: T A):
    Forany P t <-> exists (a: A), a ∈ t /\ P a.
  Proof.
    unfold Forany.
    rewrite foldMap_through_tolist.
    rewrite foldMap_eq_foldMap_list.
    unfold compose at 1.
    setoid_rewrite in_iff_in_tolist.
    induction (tolist t).
    - rewrite foldMap_list_nil.
      unfold_ops @Monoid_unit_false.
      setoid_rewrite element_of_list_nil.
      firstorder.
    - simpl_list.
      unfold_ops @Monoid_op_or.
      unfold_ops @Monoid_op_subset.
      unfold_ops @Return_subset.
      rewrite IHl.
      setoid_rewrite element_of_list_cons.
      split.
      + intros [hyp|hyp].
        * eauto.
        * firstorder.
      + intros [a' [[hyp|hyp] rest]].
        * subst. now left.
        * right. exists a'. auto.
  Qed.

End quantification.

(** * <<foldmap>> Corollary: <<plength>> *)
(**********************************************************************)
From Tealeaves Require Import Misc.NaturalNumbers.

Definition plength `{Traverse T}: forall {A}, T A -> nat :=
  fun A => foldMap (fun _ => 1).

(** ** <<plength>> of a <<list>> *)
(**********************************************************************)
Lemma list_plength_length: forall (A: Type) (l: list A),
    plength l = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - cbn. now rewrite IHl.
Qed.

(** ** Factoring <<plength>> through <<list>> *)
(**********************************************************************)
Lemma plength_through_tolist `{TraversableFunctor T}:
  forall (A: Type) (t: T A),
    plength t = length (tolist t).
Proof.
  intros.
  unfold plength.
  rewrite foldMap_through_tolist.
  unfold compose at 1.
  rewrite <- list_plength_length.
  reflexivity.
Qed.

(** ** Naturality of <<plength>> *)
(**********************************************************************)
From Tealeaves Require Import
  Classes.Categorical.ShapelyFunctor (shape, shape_map).

Section naturality_plength.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}.

  Lemma natural_plength
    {A B: Type}:
    forall (f: A -> B) (t: T A),
      plength (map f t) = plength t.
  Proof.
    intros.
    compose near t on left.
    unfold plength.
    rewrite (foldMap_map).
    reflexivity.
  Qed.

  Corollary plength_shape
    {A: Type}:
    forall (t: T A),
      plength (shape t) = plength t.
  Proof.
    intros.
    unfold shape.
    rewrite natural_plength.
    reflexivity.
  Qed.

  Corollary same_shape_implies_plength
    {A B: Type}:
    forall (t: T A) (u: T B),
      shape t = shape u ->
      plength t = plength u.
  Proof.
    introv Hshape.
    rewrite <- plength_shape.
    rewrite <- (plength_shape u).
    rewrite Hshape.
    reflexivity.
  Qed.

End naturality_plength.

(** * <<foldMap>> by a Commutative Monoid *)
(**********************************************************************)
Section foldMap_commutative_monoid.

  Import List.ListNotations.

  #[local] Arguments foldMap {T}%function_scope {H} {M}%type_scope
    (op) {unit} {A}%type_scope f%function_scope _.

  Lemma foldMap_opposite_list
    `{unit: Monoid_unit M}
    `{op: Monoid_op M}
    `{! Monoid M} {A}: forall (f: A -> M) (l: list A),
      foldMap op f l = foldMap (Monoid_op_Opposite op) f (List.rev l).
  Proof.
    intros.
    do 2 rewrite foldMap_eq_foldMap_list.
    induction l.
    - reflexivity.
    - rewrite foldMap_list_cons.
      change (List.rev (a :: l)) with (List.rev l ++ [a]).
      rewrite foldMap_list_app.
      rewrite IHl.
      unfold_ops @Monoid_op_Opposite.
      rewrite foldMap_list_one.
      reflexivity.
  Qed.

  Lemma foldMap_comm_list
    `{unit: Monoid_unit M}
    `{op: Monoid_op M}
    `{! Monoid M}
    {A: Type}
    `{comm: ! CommutativeMonoidOp op}
  : forall (f: A -> M) (l: list A),
      foldMap op f l = foldMap op f (List.rev l).
  Proof.
    intros.
    induction l.
    - reflexivity.
    - rewrite foldMap_eq_foldMap_list.
      rewrite foldMap_list_cons.
      rewrite (comm_mon_swap (f a)).
      change (List.rev (a :: l)) with (List.rev l ++ [a]).
      rewrite foldMap_list_app.
      rewrite foldMap_list_one.
      rewrite <- foldMap_eq_foldMap_list.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma foldMap_comm
    `{unit: Monoid_unit M}
    `{op: Monoid_op M}
    `{! Monoid M}
    `{comm: ! CommutativeMonoidOp op}
    `{TraversableFunctor T} {A: Type}:
    forall (f: A -> M) (t: T A),
      foldMap op f t =
        foldMap (Monoid_op_Opposite op) f t.
  Proof.
    intros.
    rewrite (foldMap_through_tolist _ f).
    rewrite (foldMap_through_tolist (op := Monoid_op_Opposite op)).
    unfold compose.
    rewrite foldMap_opposite_list.
    rewrite <- foldMap_comm_list.
    reflexivity.
  Qed.

End foldMap_commutative_monoid.

(** * Notations *)
(**********************************************************************)
Module Notations.
  Notation "f <◻> g" := (applicative_arrow_combine f g)
                          (at level 60): tealeaves_scope.
End Notations.
