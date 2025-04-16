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

From Coq Require Import Logic.Decidable.

Import Kleisli.TraversableFunctor.Notations.
Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import Subset.Notations.
Import Categorical.Applicative.Notations.
Import ProductFunctor.Notations. (* ◻ *)

#[local] Generalizable Variable T G M ϕ A B C.

(** * Miscellaneous Properties of Traversable Functors *)
(**********************************************************************)

(** ** Traversing in the Idempotent Center stays in the Idempotent Center *)
(**********************************************************************)
Section traverse_comm_idem.

  Context
    `{TraversableFunctor T}
    `{Applicative G}.


  Context `{f: A -> G B}
    (Hyp: forall a, IdempotentCenter G B (f a)).

  Lemma traverse_idem_center: forall (t: T A),
      IdempotentCenter G (T B) (traverse (G := G) f t).
  Proof.
    (* Actually, this requires the representation theorem *)
  Abort.

End traverse_comm_idem.

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
    `{Monoid M}.

  Import Kleisli.TraversableFunctor.DerivedOperations.

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
  Import KleisliToCoalgebraic.TraversableFunctor.DerivedOperations.

  Lemma traverse_commutative:
    forall `{Kleisli.TraversableFunctor.TraversableFunctor T}
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

(** * Derived Operation: <<mapReduce>> *)
(**********************************************************************)

(** ** Operation <<mapReduce>> *)
(**********************************************************************)
Definition mapReduce
  {T: Type -> Type}
  `{Traverse T}
  `{op: Monoid_op M} `{unit: Monoid_unit M}
  {A: Type} (f: A -> M): T A -> M :=
  traverse (G := const M) (B := False) f.

Section mapReduce.

  (** ** As a Special Case of <<traverse>> *)
  (********************************************************************)
  Section to_traverse.

    Context
      `{Traverse T}
      `{! TraversableFunctor T}.

    Lemma mapReduce_to_traverse1 `{Monoid M}:
      forall `(f: A -> M),
        mapReduce (T := T) f =
          traverse (G := const M) (B := False) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mapReduce_to_traverse2 `{Monoid M}:
      forall (fake: Type) `(f: A -> M),
        mapReduce (T := T) f = traverse (G := const M) (B := fake) f.
    Proof.
      intros.
      rewrite mapReduce_to_traverse1.
      rewrite (traverse_const1 fake f).
      reflexivity.
    Qed.

    (** ** Composition with <<map>> and <<traverse>> *)
    (******************************************************************)
    Lemma mapReduce_traverse
      `{Monoid M} (G: Type -> Type) {B: Type} `{Applicative G}:
      forall `(g: B -> M) `(f: A -> G B),
        map (A := T B) (B := M) (mapReduce g) ∘ traverse f =
          mapReduce (map g ∘ f).
    Proof.
      intros.
      rewrite mapReduce_to_traverse1.
      rewrite (trf_traverse_traverse (G1 := G) (G2 := const M) A B False).
      rewrite mapReduce_to_traverse1.
      rewrite map_compose_const.
      rewrite mult_compose_const.
      reflexivity.
    Qed.

    Corollary mapReduce_map `{Map T} `{! Compat_Map_Traverse T}
      `{Monoid M}: forall `(g: B -> M) `(f: A -> B),
        mapReduce (T := T) g ∘ map f = mapReduce (g ∘ f).
    Proof.
      intros.
      rewrite map_to_traverse.
      change (mapReduce g) with
        (map (F := fun A => A) (A := T B) (B := M) (mapReduce g)).
      now rewrite (mapReduce_traverse (fun X => X)).
    Qed.

    (** ** Composition with Homomorphisms *)
    (******************************************************************)
    Lemma mapReduce_morphism (M1 M2: Type)
      `{morphism: Monoid_Morphism M1 M2 ϕ}:
      forall `(f: A -> M1), ϕ ∘ mapReduce f = mapReduce (ϕ ∘ f).
    Proof.
      intros.
      inversion morphism.
      rewrite mapReduce_to_traverse1.
      change ϕ with (const ϕ (T False)).
      rewrite (trf_traverse_morphism (T := T)
                 (G1 := const M1) (G2 := const M2) A False).
      reflexivity.
    Qed.

  End to_traverse.

  (** ** Factorizing through <<runBatch>> *)
  (********************************************************************)
  Section runBatch.

    Import Coalgebraic.TraversableFunctor.
    Import KleisliToCoalgebraic.TraversableFunctor.

    Context
      `{Traverse T}
      `{! Kleisli.TraversableFunctor.TraversableFunctor T}
      `{ToBatch T}
      `{! Compat_ToBatch_Traverse T}.

    Lemma mapReduce_through_runBatch1
      {A: Type} `{Monoid M}: forall `(f: A -> M),
        mapReduce f = runBatch (G := const M) f (B := False) ∘
                      toBatch (A := A) (A' := False).
    Proof.
      intros.
      rewrite mapReduce_to_traverse1.
      rewrite traverse_through_runBatch.
      reflexivity.
    Qed.

    Lemma mapReduce_through_runBatch2
      `{Monoid M}: forall (A fake: Type) `(f: A -> M),
        mapReduce f = runBatch (G := const M) f (B := fake) ∘
                      toBatch (A' := fake).
    Proof.
      intros.
      rewrite mapReduce_to_traverse1.
      change (fun _: Type => M) with (const (A := Type) M).
      rewrite (traverse_const1 fake).
      rewrite (traverse_through_runBatch (G := const M)).
      reflexivity.
    Qed.

    (** ** Factorizing through <<toBatch>> *)
    (******************************************************************)
    Lemma mapReduce_through_toBatch
      `{Monoid M}: forall (A fake: Type) `(f: A -> M) (t: T A),
        mapReduce (T := T) f t = mapReduce f (toBatch (A' := fake) t).
    Proof.
      intros.
      rewrite (mapReduce_through_runBatch2 A fake).
      rewrite runBatch_via_traverse.
      unfold_ops @Map_const.
      unfold compose.
      rewrite (mapReduce_to_traverse2 fake).
      reflexivity.
    Qed.

  End runBatch.

End mapReduce.

(** * <<mapReduce>> Corollary: <<tolist>> *)
(**********************************************************************)

(** ** Operation <<tolist>> *)
(**********************************************************************)
#[export] Instance Tolist_Traverse `{Traverse T}: Tolist T :=
  fun A => mapReduce (ret (T := list)).

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
    tolist = mapReduce (ret (T := list) (A := A)).
Proof.
  intros.
  rewrite compat_tolist_traverse.
  reflexivity.
Qed.

(** ** Relating <<mapReduce (T := list)>> to <<mapReduce_list>> *)
(**********************************************************************)
Lemma mapReduce_eq_mapReduce_list `{Monoid M}: forall (A: Type) (f: A -> M),
    mapReduce (T := list) f = mapReduce_list f.
Proof.
  intros. ext l. induction l.
  - cbn. reflexivity.
  - cbn. change (monoid_op ?x ?y) with (x ● y).
    unfold_ops @Pure_const.
    rewrite monoid_id_l.
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
  rewrite mapReduce_eq_mapReduce_list.
  rewrite mapReduce_list_ret_id.
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
      rewrite (mapReduce_morphism (list A) (list B)).
      rewrite mapReduce_map.
      rewrite (natural (ϕ := @ret list _)).
      reflexivity.
  Qed.

  (** ** Rewriting <<tolist>> to <<traverse>> *)
  (********************************************************************)
  Corollary tolist_to_mapReduce: forall (A: Type),
      tolist (F := T) = mapReduce (ret (T := list) (A := A)).
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
    rewrite (tolist_to_mapReduce).
    rewrite (mapReduce_through_toBatch A tag).
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

  (** ** Factoring any <<mapReduce>> through <<tolist>> *)
  (********************************************************************)
  Corollary mapReduce_through_tolist
    `{Monoid M}: forall (A: Type) (f: A -> M),
    mapReduce (T := T) f = mapReduce (T := list) f ∘ tolist.
  Proof.
    intros.
    rewrite tolist_to_mapReduce.
    rewrite mapReduce_eq_mapReduce_list.
    rewrite (mapReduce_morphism (list A) M).
    rewrite mapReduce_list_ret.
    reflexivity.
  Qed.

End tolist.

(** * <<mapReduce>> Corollary: <<tosubset>> *)
(**********************************************************************)

(** ** The <<tosubset>> Operation *)
(**********************************************************************)
#[local] Instance ToSubset_Traverse `{Traverse T}:
  ToSubset T :=
  fun A => mapReduce (ret (T := subset)).

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
  forall (A: Type), tosubset (A := A) = mapReduce (ret (T := subset)).
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
      rewrite (mapReduce_morphism (subset A) (subset B)).
      rewrite mapReduce_map.
      rewrite (natural (ϕ := @ret subset _)).
      reflexivity.
  Qed.

  (** ** Rewriting <<tosubset>> to <<mapReduce>> *)
  (********************************************************************)
  Lemma tosubset_to_mapReduce `{Compat_ToSubset_Traverse T}:
    forall (A: Type),
      @tosubset T _ A =
        mapReduce (ret (T := subset)) (A := A).
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
    rewrite tosubset_to_mapReduce.
    rewrite mapReduce_through_tolist.
    ext t. unfold compose; induction (tolist t).
    - reflexivity.
    - cbn. rewrite IHl.
      unfold transparent tcs.
      now simpl_subset.
  Qed.

  (** ** Rewriting <<a ∈ t>> to <<mapReduce>> *)
  (********************************************************************)
  Lemma element_of_to_mapReduce:
    forall (A: Type) (a: A),
      element_of a =
        mapReduce (op := Monoid_op_or)
          (unit := Monoid_unit_false) {{a}}.
  Proof.
    intros.
    unfold element_of.
    rewrite tosubset_to_mapReduce.
    ext t.
    change_left (evalAt a (mapReduce (ret (T := subset)) t)).
    compose near t on left.
    rewrite (mapReduce_morphism
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
    rewrite tosubset_to_mapReduce.
    rewrite mapReduce_through_runBatch1.
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
    rewrite tosubset_to_mapReduce.
    rewrite (mapReduce_through_runBatch2 A tag).
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
  rewrite (mapReduce_morphism (list A) (subset A)
             (ϕ := @tosubset list ToSubset_list A)).
  rewrite tosubset_list_hom1.
  reflexivity.
Qed.

(** * <<mapReduce>> Corollary: <<Forall, Forany>> *)
(**********************************************************************)
Section quantification.

  Context
    `{TraversableFunctor T}
    `{! ToSubset T}
    `{! Compat_ToSubset_Traverse T}.

  (** ** Operations <<Forall>> and <<Forany>> *)
  (********************************************************************)
  Definition Forall `(P: A -> Prop): T A -> Prop :=
    @mapReduce T _ Prop Monoid_op_and Monoid_unit_true A P.

  Definition Forany `(P: A -> Prop): T A -> Prop :=
    @mapReduce T _ Prop Monoid_op_or Monoid_unit_false A P.

  (** ** Specification via <<element_of>> *)
  (********************************************************************)
  Lemma forall_iff `(P: A -> Prop) (t: T A):
    Forall P t <-> forall (a: A), a ∈ t -> P a.
  Proof.
    unfold Forall.
    rewrite mapReduce_through_tolist.
    unfold compose at 1.
    setoid_rewrite in_iff_in_tolist.
    rewrite mapReduce_eq_mapReduce_list.
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

  (* More useful for rewriting *)
  Lemma forall_iff_eq `(P: A -> Prop) (t: T A):
    Forall P t = forall (a: A), a ∈ t -> P a.
  Proof.
    apply propositional_extensionality.
    apply forall_iff.
  Qed.

  Lemma forany_iff `(P: A -> Prop) (t: T A):
    Forany P t <-> exists (a: A), a ∈ t /\ P a.
  Proof.
    unfold Forany.
    rewrite mapReduce_through_tolist.
    rewrite mapReduce_eq_mapReduce_list.
    unfold compose at 1.
    setoid_rewrite in_iff_in_tolist.
    induction (tolist t).
    - rewrite mapReduce_list_nil.
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

  (* More useful for rewriting *)
  Lemma forany_iff_eq `(P: A -> Prop) (t: T A):
    Forany P t = exists (a: A), a ∈ t /\ P a.
  Proof.
    apply propositional_extensionality.
    apply forany_iff.
  Qed.

  (** ** Decidability of <<Forall>> and <<Forany>> *)
  (**********************************************************************)
  Section decidability.

    Definition decidable_pred {A: Type} (P: A -> Prop) :=
      forall a, decidable (P a).

    Lemma decidable_pred_not_and `(P: A -> Prop) (X: decidable_pred P) (a1 a2: A):
      (~ (P a1 /\ P a2)) = ~ (P a1) \/ ~ P a2.
    Proof.
      apply propositional_extensionality; split.
      - apply not_and. apply (X a1).
      - intros [Case1|Case2]; intuition.
    Qed.

    Lemma decidable_Forall `(P: A -> Prop) `(Dec: decidable_pred P):
      decidable_pred (Forall P).
    Proof.
      intro t.
      unfold decidable.
      unfold Forall.
      rewrite mapReduce_through_tolist.
      rewrite mapReduce_eq_mapReduce_list.
      unfold compose. induction (tolist t) as [|a rest IHrest].
      - now left.
      - simpl_list.
        simplify_monoid_conjunction.
        destruct IHrest as [yes_rest | no_rest];
          destruct (Dec a) as [yes_a | no_a]; tauto.
    Qed.

    Lemma decidable_Forany `(P: A -> Prop) `(Dec: decidable_pred P):
      decidable_pred (Forany P).
    Proof.
      intro t.
      unfold decidable.
      unfold Forany.
      rewrite mapReduce_through_tolist.
      rewrite mapReduce_eq_mapReduce_list.
      unfold compose. induction (tolist t) as [|a rest IHrest].
      - now right.
      - simpl_list.
        simplify_monoid_disjunction.
        destruct IHrest as [yes_rest | no_rest];
          destruct (Dec a) as [yes_a | no_a]; tauto.
    Qed.

    Lemma decidable_Forall_element
      `(P: A -> Prop) `(Dec: decidable_pred P) (t: T A):
      decidable (forall (a: A), a ∈ t -> P a).
    Proof.
      rewrite <- forall_iff_eq.
      apply decidable_Forall.
      assumption.
    Qed.

    Lemma decidable_Forany_element
      `(P: A -> Prop) `(Dec: decidable_pred P) (t: T A):
      decidable (exists (a: A), a ∈ t /\ P a).
    Proof.
      rewrite <- forany_iff_eq.
      apply decidable_Forany.
      assumption.
    Qed.

  End decidability.

  (** ** Corollaries of decidability *)
  (**********************************************************************)
  Lemma not_Forall_Forany_lemma1
    `(P: A -> Prop) (Dec: decidable_pred P) (t: T A):
      ~ (Forall P t) -> Forany (not ∘ P) t.
  Proof.
    unfold Forall, Forany.
    rewrite mapReduce_through_tolist.
    rewrite (mapReduce_through_tolist _ (not ∘ P)).
    unfold compose.
    induction (tolist t).
    - cbv. firstorder.
    - do 2 rewrite mapReduce_eq_mapReduce_list in *.
      simpl_list.
      simplify_monoid_conjunction.
      simplify_monoid_disjunction.
      firstorder.
  Qed.

  Lemma not_Forall_Forany
    `(P: A -> Prop) (Dec: decidable_pred P) (t: T A):
      ~ (Forall P t) <-> Forany (not ∘ P) t.
  Proof.
    unfold not at 2, compose at 1.
    destruct (decidable_Forall P Dec t) as [YesAll | NotAll].
    - split.
      + contradiction.
      + rewrite forall_iff, forany_iff in *.
        intros [a [Hin HP]] _.
        intuition.
    - split.
      + apply not_Forall_Forany_lemma1.
        assumption.
      + easy.
  Qed.

End quantification.

(** * <<mapReduce>> Corollary: <<plength>> *)
(**********************************************************************)
From Tealeaves Require Import Misc.NaturalNumbers.

Definition plength `{Traverse T}: forall {A}, T A -> nat :=
  fun A => mapReduce (fun _ => 1).

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
  rewrite mapReduce_through_tolist.
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
    rewrite (mapReduce_map).
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

(** * <<mapReduce>> by a Commutative Monoid *)
(**********************************************************************)
Section mapReduce_commutative_monoid.

  Import List.ListNotations.

  #[local] Arguments mapReduce {T}%function_scope {H} {M}%type_scope
    (op) {unit} {A}%type_scope f%function_scope _.

  Lemma mapReduce_opposite_list
    `{unit: Monoid_unit M}
    `{op: Monoid_op M}
    `{! Monoid M} {A}: forall (f: A -> M) (l: list A),
      mapReduce op f l = mapReduce (Monoid_op_Opposite op) f (List.rev l).
  Proof.
    intros.
    do 2 rewrite mapReduce_eq_mapReduce_list.
    induction l.
    - reflexivity.
    - rewrite mapReduce_list_cons.
      change (List.rev (a :: l)) with (List.rev l ++ [a]).
      rewrite mapReduce_list_app.
      rewrite IHl.
      unfold_ops @Monoid_op_Opposite.
      rewrite mapReduce_list_one.
      reflexivity.
  Qed.

  Lemma mapReduce_comm_list
    `{unit: Monoid_unit M}
    `{op: Monoid_op M}
    `{! Monoid M}
    {A: Type}
    `{comm: ! CommutativeMonoidOp op}
: forall (f: A -> M) (l: list A),
      mapReduce op f l = mapReduce op f (List.rev l).
  Proof.
    intros.
    induction l.
    - reflexivity.
    - rewrite mapReduce_eq_mapReduce_list.
      rewrite mapReduce_list_cons.
      rewrite (comm_mon_swap (f a)).
      change (List.rev (a :: l)) with (List.rev l ++ [a]).
      rewrite mapReduce_list_app.
      rewrite mapReduce_list_one.
      rewrite <- mapReduce_eq_mapReduce_list.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma mapReduce_comm
    `{unit: Monoid_unit M}
    `{op: Monoid_op M}
    `{! Monoid M}
    `{comm: ! CommutativeMonoidOp op}
    `{TraversableFunctor T} {A: Type}:
    forall (f: A -> M) (t: T A),
      mapReduce op f t =
        mapReduce (Monoid_op_Opposite op) f t.
  Proof.
    intros.
    rewrite (mapReduce_through_tolist _ f).
    rewrite (mapReduce_through_tolist (op := Monoid_op_Opposite op)).
    unfold compose.
    rewrite mapReduce_opposite_list.
    rewrite <- mapReduce_comm_list.
    reflexivity.
  Qed.

End mapReduce_commutative_monoid.

(** * Notations *)
(**********************************************************************)
Module Notations.
  Notation "f <◻> g" := (applicative_arrow_combine f g)
                          (at level 60): tealeaves_scope.
End Notations.
