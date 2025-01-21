From Tealeaves Require Export
  Classes.Kleisli.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor (Tolist, tolist)
  Classes.Categorical.Monad (Return, ret)
  Functors.Early.List
  Functors.ProductFunctor
  Functors.Constant
  Functors.Identity
  Misc.Prop.

Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import Subset.Notations.
Import Categorical.Applicative.Notations.
Import ProductFunctor.Notations. (* ◻ *)

#[local] Generalizable Variable T G M ϕ A B C.

(** * Miscellaneous Properties of Traversable Functors *)
(******************************************************************************)

(** ** Interaction between <<traverse>> and <<pure>> *)
(******************************************************************************)
Section traversable_purity.

  Context
    `{TraversableFunctor T}.

  Theorem traverse_purity1 :
    forall `{Applicative G},
      `(traverse (G := G) pure = @pure G _ (T A)).
  Proof.
    intros.
    change (@pure G _ A) with (@pure G _ A ∘ id).
    rewrite <- (trf_traverse_morphism (G1 := fun A => A) (G2 := G)).
    rewrite trf_traverse_id.
    reflexivity.
  Qed.

  Lemma traverse_purity2 :
    forall `{Applicative G2}
      `{Applicative G1}
      `(f : A -> G1 B),
      traverse (G := G2 ∘ G1) (pure (F := G2) ∘ f) =
        pure (F := G2) ∘ traverse f.
  Proof.
    intros.
    rewrite <- (trf_traverse_morphism (G1 := G1) (G2 := G2 ∘ G1)
                 (ϕ := fun A => @pure G2 _ (G1 A))).
    reflexivity.
  Qed.

End traversable_purity.

(** * Traversals by Particular Applicative Functors *)
(******************************************************************************)

(** ** Product of Two Applicative Functors *)
(******************************************************************************)
Section traverse_applicative_product.

  Definition applicative_arrow_combine {F G A B}
    `(f : A -> F B) `(g : A -> G B) : A -> (F ◻ G) B :=
    fun a => product (f a) (g a).

  #[local] Notation "f <◻> g" :=
    (applicative_arrow_combine f g) (at level 60) : tealeaves_scope.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{Applicative G1}
    `{Applicative G2}.

  Variables
    (A B : Type)
    (f : A -> G1 B)
    (g : A -> G2 B).

  Lemma traverse_product1 : forall (t : T A),
      pi1 (traverse (f <◻> g) t) = traverse f t.
  Proof.
    intros.
    pose (ApplicativeMorphism_pi1 G1 G2).
    compose near t on left.
    rewrite trf_traverse_morphism.
    reflexivity.
  Qed.

  Lemma traverse_product2 : forall (t : T A),
      pi2 (traverse (f <◻> g) t) = traverse g t.
  Proof.
    intros.
    pose (ApplicativeMorphism_pi2 G1 G2).
    compose near t on left.
    rewrite trf_traverse_morphism.
    reflexivity.
  Qed.

  Theorem traverse_product_spec :
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
(******************************************************************************)
Section constant_applicatives.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{Monoid M}.

  Lemma traverse_const1: forall {A : Type} (B : Type) `(f : A -> M),
      traverse (G := const M) (B := False) f =
        traverse (G := const M) (B := B) f.
  Proof.
    intros.
    change_left (map (F := const M) (A := T False)
                   (B := T B) (map (F := T) (A := False) (B := B) exfalso)
                   ∘ traverse (T := T) (G := const M)
                   (B := False) (f : A -> const M False)).
    rewrite (map_traverse (G1 := const M)).
    reflexivity.
  Qed.

  Lemma traverse_const2: forall {A : Type} (f : A -> M) (fake1 fake2 : Type),
      traverse (G := const M) (B := fake1) f =
        traverse (G := const M) (B := fake2) f.
  Proof.
    intros.
    rewrite <- (traverse_const1 fake1).
    rewrite -> (traverse_const1 fake2).
    reflexivity.
  Qed.

End constant_applicatives.

(** * Derived Operation: <<foldmap>> *)
(******************************************************************************)

(** ** The <<foldmap>> Operation *)
(******************************************************************************)
Section foldMap.

  Definition foldMap
    {T : Type -> Type}
    `{Traverse T}
    `{op : Monoid_op M} `{unit : Monoid_unit M}
    {A : Type} (f : A -> M) : T A -> M :=
    traverse (G := const M) (B := False) f.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}.

  (** *** As a special case of <<traverse>> *)
  (******************************************************************************)
  Lemma foldMap_to_traverse1 `{Monoid M} : forall `(f : A -> M),
      foldMap (T := T) f =
        traverse (G := const M) (B := False) f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_to_traverse2 `{Monoid M} : forall (fake : Type) `(f : A -> M),
      foldMap f = traverse (G := const M) (B := fake) f.
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite (traverse_const1 fake f).
    reflexivity.
  Qed.

  (** *** Composition with <<map>> and <<traverse>> *)
  (******************************************************************************)
  Lemma foldMap_traverse `{Monoid M} (G : Type -> Type) {B : Type} `{Applicative G} :
    forall `(g : B -> M) `(f : A -> G B),
      map (A := T B) (B := M) (foldMap g) ∘ traverse f =
        foldMap (map g ∘ f).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite (trf_traverse_traverse (T := T) (G1 := G) (G2 := const M) A B False).
    rewrite foldMap_to_traverse1.
    rewrite map_compose_const.
    rewrite mult_compose_const.
    reflexivity.
  Qed.

  Corollary foldMap_map `{Monoid M} : forall `(g : B -> M) `(f : A -> B),
      foldMap g ∘ map f = foldMap (g ∘ f).
  Proof.
    intros.
    rewrite map_to_traverse.
    change (foldMap g) with (map (F := fun A => A) (A := T B) (B := M) (foldMap g)).
    now rewrite (foldMap_traverse (fun X => X)).
  Qed.

  (** *** Composition with Homomorphisms *)
  (******************************************************************************)
  Lemma foldMap_morphism (M1 M2 : Type) `{morphism : Monoid_Morphism M1 M2 ϕ} :
    forall `(f : A -> M1), ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
  Proof.
    intros.
    inversion morphism.
    rewrite foldMap_to_traverse1.
    change ϕ with (const ϕ (T False)).
    rewrite (trf_traverse_morphism (T := T)
               (G1 := const M1) (G2 := const M2) A False).
    reflexivity.
  Qed.

End foldMap.


(** * <<foldmap>> Corollary: <<tolist>> *)
(******************************************************************************)

(** ** The <<tolist>> Operation *)
(******************************************************************************)
(* TODO Generalize this with a compatibility class or something *)
#[export] Instance Tolist_Traverse `{Traverse T}: Tolist T :=
  fun A => foldMap (ret (T := list)).

(** ** Relating <<foldMap (T := list)>> to <<foldMap_list>> *)
(******************************************************************************)
Lemma foldMap_eq_foldMap_list `{Monoid M} : forall (A : Type) (f : A -> M),
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

(** The <<tolist>> operation provided by the traversability of <<list>> is the identity. *)
Lemma Tolist_list_id : forall (A : Type),
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
  (******************************************************************************)
  #[export] Instance Natural_Tolist_Traverse : Natural (@tolist T _).
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
  (******************************************************************************)
  Corollary tolist_to_foldMap : forall (A : Type),
      tolist (F := T) = foldMap (ret (T := list) (A := A)).
  Proof.
    reflexivity.
  Qed.

  Corollary tolist_to_traverse1 : forall (A : Type),
      tolist = traverse (G := const (list A)) (B := False) (ret (T := list)).
  Proof.
    reflexivity.
  Qed.

  Corollary tolist_to_traverse2 : forall (A fake : Type),
      tolist = traverse (G := const (list A)) (B := fake) (ret (T := list)).
  Proof.
    intros.
    rewrite tolist_to_traverse1.
    rewrite (traverse_const1 fake).
    reflexivity.
  Qed.

  (** ** Factoring any <<foldMap>> through <<tolist>> *)
  (******************************************************************************)
  Corollary foldMap_through_tolist `{Monoid M} : forall (A : Type) (f : A -> M),
      foldMap f = foldMap (T := list) f ∘ tolist.
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
(******************************************************************************)

(** ** The <<toSubset>> Operation *)
(******************************************************************************)
#[local] Instance ToSubset_Traverse `{Traverse T}:
  ToSubset T :=
  fun A => foldMap (ret (T := subset)).

Class Compat_ToSubset_Traverse
  (T : Type -> Type)
  `{ToSubset_inst : ToSubset T}
  `{Traverse_inst : Traverse T} : Prop :=
  compat_tosubset_traverse :
    @tosubset T ToSubset_inst =
      @tosubset T (@ToSubset_Traverse T Traverse_inst).

#[export] Instance Compat_ToSubset_Traverse_Self
  `{Traverse_T: Traverse T}:
  @Compat_ToSubset_Traverse T ToSubset_Traverse Traverse_T
  := ltac:(reflexivity).

Section elements.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{ToSubset T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}.

  (** ** Naturality *)
  (******************************************************************************)
  #[export] Instance Natural_Element_Traverse :
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
  (*******************************************************************************)
  Lemma tosubset_to_foldMap `{Compat_ToSubset_Traverse T}:
    forall (A : Type),
      @tosubset T _ A =
        foldMap (ret (T := subset)) (A := A).
  Proof.
    rewrite compat_tosubset_traverse.
    reflexivity.
  Qed.

  (** ** Factoring <<tosubset>> through <<tolist>> *)
  (*******************************************************************************)
  Corollary tosubset_through_tolist: forall A:Type,
      tosubset (F := T) (A := A) =
        tosubset (F := list) ∘ tolist (A := A).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_through_tolist.
    reflexivity.
  Qed.

  (** ** Rewriting <<a ∈ t>> to <<foldMap>> *)
  (******************************************************************************)
  Lemma element_of_to_foldMap:
    forall (A : Type) (a : A),
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
  (*******************************************************************************)
  Corollary element_of_through_tolist:
    forall (A : Type) (a : A),
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

(*
#[export] Instance Compat_ToSubset_Tolist_Traverse
  `{TraversableFunctor T} :
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

#[export] Instance Compat_ToSubset_Traverse_List :
  @Compat_ToSubset_Traverse list ToSubset_list Traverse_list.
Proof.
  unfold Compat_ToSubset_Traverse.
  ext A l a.
  induction l.
  - cbn. reflexivity.
  - apply propositional_extensionality.
    autorewrite with tea_list tea_set.
    cbn.
    unfold_ops @Pure_const.
    unfold_ops @Monoid_op_subset.
    autorewrite with tea_set.
    rewrite IHl.
    firstorder.
Qed.
 *)

End elements.

(** * <<foldmap>> Corollary: <<Forall, Forany>> *)
(******************************************************************************)
Section quantification.

  Context
    `{TraversableFunctor T}
    `{! ToSubset T}
     `{! Compat_ToSubset_Traverse T}.

  (** ** Operations <<Forall>> and <<Forany>> *)
  (******************************************************************************)
  Definition Forall `(P : A -> Prop) : T A -> Prop :=
    @foldMap T _ Prop Monoid_op_and Monoid_unit_true A P.

  Definition Forany `(P : A -> Prop) : T A -> Prop :=
    @foldMap T _ Prop Monoid_op_or Monoid_unit_false A P.

  (** ** Specification via <<element_of>> *)
  (******************************************************************************)
  Lemma forall_iff `(P : A -> Prop) (t : T A) :
    Forall P t <-> forall (a : A), a ∈ t -> P a.
  Proof.
    unfold Forall.
    rewrite foldMap_through_tolist.
    unfold compose at 1.
    unfold element_of at 1.
    rewrite tosubset_through_tolist.
    unfold compose at 1.
    (*
       change_right (forall a : A, a ∈ (tolist t) -> P a).
     *)
    rewrite tosubset_to_foldMap.
    rewrite foldMap_eq_foldMap_list.
    rewrite foldMap_eq_foldMap_list.
    induction (tolist t).
    - simpl_list.
      unfold_ops @Monoid_unit_true.
      unfold_ops @Monoid_unit_subset.
      setoid_rewrite subset_in_empty.
      intuition.
    - simpl_list.
      unfold_ops @Monoid_op_and.
      unfold_ops @Monoid_op_subset.
      unfold_ops @Return_subset.
      rewrite IHl.
      setoid_rewrite subset_in_add.
      firstorder. now subst.
  Qed.

  Lemma forany_iff `(P : A -> Prop) (t : T A) :
    Forany P t <-> exists (a : A), a ∈ t /\ P a.
  Proof.
    unfold Forany.
    rewrite foldMap_through_tolist.
    unfold compose at 1.
    unfold element_of at 1.
    rewrite tosubset_through_tolist.
    unfold compose at 1.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_eq_foldMap_list.
    rewrite foldMap_eq_foldMap_list.
    induction (tolist t).
    - simpl_list.
      unfold_ops @Monoid_unit_false.
      unfold_ops @Monoid_unit_subset.
      setoid_rewrite subset_in_empty.
      firstorder.
    - simpl_list.
      unfold_ops @Monoid_op_or.
      unfold_ops @Monoid_op_subset.
      unfold_ops @Return_subset.
      rewrite IHl.
      setoid_rewrite subset_in_add.
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
(******************************************************************************)
From Tealeaves Require Import Misc.NaturalNumbers.

Definition plength `{Traverse T}: forall {A}, T A -> nat :=
  fun A => foldMap (fun _ => 1).

(** ** <<plength>> of a <<list>> *)
(******************************************************************************)
Lemma list_plength_length: forall (A: Type) (l: list A),
    plength l = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - cbn. now rewrite IHl.
Qed.

(** ** Factoring <<plength>> through <<list>> *)
(******************************************************************************)
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

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "f <◻> g" := (applicative_arrow_combine f g) (at level 60) : tealeaves_scope.
End Notations.
