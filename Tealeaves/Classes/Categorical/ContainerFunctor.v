From Tealeaves Require Export
  Classes.Functor
  Functors.Subset
  Functors.List.

From Coq Require Import
  Relations.Relation_Definitions
  Classes.Morphisms.

Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

(** * Set-like functors *)
(******************************************************************************)
Class Elements (F : Type -> Type) :=
  element_of : F ⇒ subset.

(* Mark the type argument of <<toset>> implicit *)
#[global] Arguments element_of {F}%function_scope {Elements} {A}%type_scope.

#[local] Notation "x ∈ t" :=
  (element_of t x) (at level 50) : tealeaves_scope.

Class ContainerFunctor
  (F : Type -> Type)
  `{Map F} `{Elements F} :=
  { cont_natural :> Natural (@element_of F _);
    cont_functor :> Functor F;
    cont_pointwise : forall (A B : Type) (t : F A) (f g : A -> B),
      (forall a, a ∈ t -> f a = g a) -> map F f t = map F g t;
  }.

(** ** [Elements]-preserving natural transformations *)
(******************************************************************************)
Class ContainerTransformation
  {F G : Type -> Type}
  `{Map F} `{Elements F}
  `{Map G} `{Elements G}
  (η : F ⇒ G) :=
  { cont_trans_natural : Natural η;
    cont_trans_commute : forall A, element_of (F := F) = element_of (F := G) ∘ η A;
  }.

(** ** Container Instance for <<subset>> *)
(******************************************************************************)
Section Container_subset.

  Instance Toset_set : Elements subset :=
    fun (A : Type) (s : subset A) => s.

  Instance Natural_toset_set : Natural (@element_of subset _).
  Proof.
    constructor; try typeclasses eauto.
    intros. ext S b. reflexivity.
  Qed.

  Lemma subset_pointwise : forall (A B : Type) (t : A -> Prop) (f g : A -> B),
      (forall a : A, a ∈ t -> f a = g a) -> map subset f t = map subset g t.
  Proof.
    intros. ext b. cbv. propext.
    intros. preprocess. setoid_rewrite H. firstorder. auto.
    intros. preprocess. setoid_rewrite <- H. firstorder. auto.
  Qed.

  Instance ContainerFunctor_subset : ContainerFunctor subset :=
    {| cont_pointwise := subset_pointwise;
    |}.

End Container_subset.

(** ** Basic properties of containers *)
(******************************************************************************)
Section setlike_functor_theory.

  Context
    (F : Type -> Type)
    `{ContainerFunctor F}
    {A B : Type}.

  Implicit Types (t : F A) (b : B) (a : A) (f g : A -> B).

  (** Naturality relates elements before and after a map. *)
  Theorem in_map_iff : forall t f b,
      b ∈ map F f t <-> exists a : A, a ∈ t /\ f a = b.
  Proof.
    introv. compose near t on left.
    now rewrite <- (natural (G:=(-> Prop))).
  Qed.

  (** This next property says that applying <<f>> (or on the
      right-hand side, appling <<map f>>) is monotone with respect to
      the <<∈>> relation. *)
  Corollary in_map_mono : forall t f a,
      a ∈ t -> f a ∈ map F f t.
  Proof.
    introv. rewrite in_map_iff. now exists a.
  Qed.

  Corollary map_respectful_id : forall t (f : A -> A),
      (forall a, a ∈ t -> f a = a) -> map F f t = t.
  Proof.
    intros. replace t with (map F id t) at 2
      by now rewrite (fun_map_id (F := F)).
    now apply (cont_pointwise (F := F)).
  Qed.

End setlike_functor_theory.

(** ** Properness conditions *)
(******************************************************************************)
Definition pointwise_equal_on
  (F : Type -> Type) {A B} `{Elements F} :
  F A -> relation (A -> B) :=
  fun t f g => (forall a : A, a ∈ t -> f a = g a).

Definition respectively_equal_at {A B} : A -> A -> relation (A -> B) :=
  fun (a1 a2 : A) (f g : A -> B) => f a1 = g a2.

Definition equal_at {A B} : A -> relation (A -> B) :=
  fun (a : A) (f g : A -> B) => f a = g a.

Definition injective_relation {A B} (R : relation A) (R' : relation B) : relation (A -> B) :=
  fun f g => forall a1 a2 : A, R' (f a1) (g a2) -> R a1 a2.

Infix "<++" := injective_relation (at level 55).

Definition rigid_relation {A B} (R : relation A) (R' : relation B) : relation (A -> B) :=
  fun f g => forall a1 a2 : A, R' (f a1) (g a2) <-> R a1 a2.

Infix "<++>" := rigid_relation (at level 55).

#[export] Instance Proper_Container_Map
  (F : Type -> Type) `{ContainerFunctor F} :
  (forall (A B : Type) (t : F A),
      Proper (pointwise_equal_on F t (B := B) ++> equal_at t) (map F)).
Proof.
  intros.
  unfold Proper.
  intros f g Hpw.
  unfold pointwise_equal_on, equal_at in *.
  now apply cont_pointwise.
Qed.

(** * List instance *)
(******************************************************************************)

(** ** <<elements_of>> *)
(******************************************************************************)
#[export] Instance Elements_list : Elements list :=
  fun (A : Type) (l : list A) => (fun a : A => @List.In A a l).

Lemma elements_list_nil : forall (A : Type),
    element_of (@nil A) = ∅.
Proof.
  intros. extensionality a. reflexivity.
Qed.

Lemma elements_list_one : forall (A : Type) (a : A),
    element_of [a] = {{ a }}.
Proof.
  intros. solve_basic_subset.
Qed.

Lemma elements_list_ret : forall (A : Type) (a : A),
    element_of (ret list a) = {{ a }}.
Proof.
  intros. solve_basic_subset.
Qed.

Lemma elements_list_cons :
  forall (A : Type) (a : A) (l : list A),
    element_of (a :: l) = {{ a }} ∪ element_of l.
Proof.
  intros. extensionality a'. reflexivity.
Qed.

Lemma elements_list_app : forall (A : Type) (l1 l2 : list A),
    element_of (l1 ++ l2) = element_of l1 ∪ element_of l2.
Proof.
  intros. induction l1.
  - cbn. rewrite elements_list_nil.
    solve_basic_subset.
  - cbn.
    do 2 rewrite elements_list_cons.
    rewrite IHl1. solve_basic_subset.
Qed.

#[export] Hint Rewrite
  elements_list_nil elements_list_one elements_list_ret
  elements_list_cons elements_list_app : tea_list.

#[export] Instance Natural_Elements_list : Natural (@element_of list _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. ext l.
  unfold compose at 1 2.
  induction l.
  - solve_basic_subset.
  - rewrite elements_list_cons.
    autorewrite with tea_set tea_list.
    rewrite IHl.
    solve_basic_subset.
Qed.

(** ** [element_of] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monoid_Morphism_elements_list (A : Type) :
  Monoid_Morphism (list A) (subset A) (element_of (A := A)) :=
  {| monmor_unit := @elements_list_nil A;
     monmor_op := @elements_list_app A;
  |}.

(** ** <<∈>> for lists *)
(******************************************************************************)
Lemma in_list_nil {A} : forall (p : A), p ∈ @nil A <-> False.
Proof.
  reflexivity.
Qed.

Lemma in_list_cons {A} : forall (a1 a2 : A) (xs : list A),
    a1 ∈ (a2 :: xs) <-> a1 = a2 \/ a1 ∈ xs.
Proof.
  intros; simpl_list; simpl_subset.
  intuition congruence.
Qed.

Lemma in_list_one {A} (a1 a2 : A) : a1 ∈ [ a2 ] <-> a1 = a2.
Proof.
  intros. simpl_list. simpl_subset. intuition congruence.
Qed.

Lemma in_list_ret {A} (a1 a2 : A) : a1 ∈ ret list a2 <-> a1 = a2.
Proof.
  intros. simpl_list; simpl_subset. intuition.
Qed.

Lemma in_list_app {A} : forall (a : A) (xs ys : list A),
    a ∈ (xs ++ ys) <-> a ∈ xs \/ a ∈ ys.
Proof.
  intros. simpl_list. simpl_subset. reflexivity.
Qed.

#[export] Hint Rewrite @in_list_nil @in_list_cons
  @in_list_one @in_list_ret @in_list_app : tea_list.


(** ** [x ∈] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monoid_Morphism_element_list (A : Type) (a : A) :
  Monoid_Morphism (list A) Prop (tgt_op := or) (tgt_unit := False)
    (fun l => element_of l a).
Proof.
  constructor; try typeclasses eauto.
  - reflexivity.
  - intros. unfold_ops @Monoid_op_list.
    apply propositional_extensionality.
    now rewrite in_list_app.
Qed.

(** ** Relation with <<foldMap>> *)
(******************************************************************************)
Lemma foldMap_list_elements1 : forall (A : Type),
    element_of = foldMap (ret subset (A := A)).
Proof.
  intros. ext l. induction l.
  - reflexivity.
  - cbn. autorewrite with tea_list.
    rewrite IHl.
    reflexivity.
Qed.

Lemma foldMap_list_elements2 : forall (A : Type) (l : list A) (a : A),
    element_of l a = foldMap (op := or) (unit := False) (eq a) l.
Proof.
  intros. rewrite foldMap_list_elements1. induction l.
  - reflexivity.
  - rewrite foldMap_list_cons.
    rewrite foldMap_list_cons.
    rewrite <- IHl.
    replace (a = a0) with (a0 = a) by (propext; auto).
    reflexivity.
Qed.

(** * Quantification over elements *)
(******************************************************************************)
Section quantification.

  #[local] Generalizable Variables A.

  Definition Forall `(P : A -> Prop) : list A -> Prop :=
    foldMap (op := Monoid_op_and) (unit := Monoid_unit_true) P.

  Definition Forany `(P : A -> Prop) : list A -> Prop :=
    foldMap (op := Monoid_op_or) (unit := Monoid_unit_false) P.

  Lemma forall_iff `(P : A -> Prop) (l : list A) :
    Forall P l <-> forall (a : A), a ∈ l -> P a.
  Proof.
    unfold Forall.
    induction l; autorewrite with tea_list tea_set.
    - split.
      + intros tt a contra. inversion contra.
      + intros. exact I.
    - setoid_rewrite subset_in_add.
      unfold subset_one.
      rewrite IHl. split.
      + intros [Hpa Hrest].
        intros x [Heq | Hin].
        now subst. auto.
      + intros H. split; auto.
  Qed.

  Lemma forany_iff `(P : A -> Prop) (l : list A) :
    Forany P l <-> exists (a : A), a ∈ l /\ P a.
  Proof.
    unfold Forany.
    induction l.
    - split.
      + intros [].
      + intros [x [contra Hrest]]. inversion contra.
    - autorewrite with tea_list tea_set.
      setoid_rewrite subset_in_add.
      unfold subset_one.
      rewrite IHl. split.
      + intros [Hpa | Hrest].
        exists a. auto.
        destruct Hrest as [x [H1 H2]].
        exists x. auto.
      + intros [x [[H1 | H2] H3]].
        subst. now left.
        right. eexists; eauto.
  Qed.

End quantification.

(** ** Specification of <<Permutation>> *)
(******************************************************************************)
From Coq Require Import Sorting.Permutation.

Theorem permutation_spec : forall {A} {l1 l2 : list A},
    Permutation l1 l2 -> (forall a, a ∈ l1 <-> a ∈ l2).
Proof.
  introv perm. induction perm; firstorder.
Qed.

(** ** Respectfulness conditions *)
(******************************************************************************)
Theorem map_rigidly_respectful_list : forall A B (f g : A -> B) (l : list A),
    (forall (a : A), a ∈ l -> f a = g a) <-> map list f l = map list g l.
Proof.
  intros. induction l.
  - simpl_list. setoid_rewrite subset_in_empty. tauto.
  - simpl_list. setoid_rewrite subset_in_add.
    setoid_rewrite set_in_ret.
    destruct IHl. split.
    + intro; fequal; auto.
    + injection 1; intuition (subst; auto).
Qed.

Corollary map_respectful_list : forall A B (l : list A) (f g : A -> B),
    (forall (a : A), a ∈ l -> f a = g a) -> map list f l = map list g l.
Proof.
  intros. now rewrite <- map_rigidly_respectful_list.
Qed.

(* We might not need to export this if we provide a shapely functor instance *)
#[local] Instance ContainerFunctor_list : ContainerFunctor list :=
  {| cont_pointwise := map_respectful_list;
  |}.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "x ∈ t" :=
    (element_of t x) (at level 50) : tealeaves_scope.
End Notations.
