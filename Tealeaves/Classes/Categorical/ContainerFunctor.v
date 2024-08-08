From Tealeaves Require Export
  Classes.Functor
  Misc.Subset
  Misc.List.

From Coq Require Import
  Relations.Relation_Definitions
  Classes.Morphisms.

Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.

#[local] Generalizable Variables F T A.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.

(** * Container-like functors *)
(******************************************************************************)

(** ** <<tosubset>> operation *)
(******************************************************************************)
Class ToSubset (F : Type -> Type) :=
  tosubset : F ⇒ subset.

#[global] Arguments tosubset {F}%function_scope {ToSubset} {A}%type_scope.

Definition element_of `{ToSubset F} {A: Type}:
  A -> F A -> Prop := fun a t => tosubset t a.

Lemma element_of_tosubset `{ToSubset F} {A: Type}:
  forall (a:A), element_of a = evalAt a ∘ tosubset.
Proof.
  reflexivity.
Qed.
#[local] Notation "x ∈ t" :=
  (element_of x t) (at level 50) : tealeaves_scope.

(** ** Functor typeclass *)
(******************************************************************************)
Class ContainerFunctor
  (F : Type -> Type)
  `{Map F} `{ToSubset F} :=
  { cont_natural :> Natural (@tosubset F _);
    cont_functor :> Functor F;
    cont_pointwise : forall (A B : Type) (t : F A) (f g : A -> B),
      (forall a, a ∈ t -> f a = g a) -> map F f t = map F g t;
  }.

(** ** [ToSubset]-preserving natural transformations *)
(******************************************************************************)
Class ContainerTransformation
  {F G : Type -> Type}
  `{Map F} `{ToSubset F}
  `{Map G} `{ToSubset G}
  (η : F ⇒ G) :=
  { cont_trans_natural : Natural η;
    cont_trans_commute : forall A, tosubset (F := F) = tosubset (F := G) ∘ η A;
  }.

(** * Container instance for <<subset>> *)
(******************************************************************************)
Section Container_subset.

  Instance ToSubset_set : ToSubset subset :=
    fun (A : Type) (s : subset A) => s.

  Instance Natural_elements_set : Natural (@tosubset subset _).
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

(** * Basic properties of containers *)
(******************************************************************************)
Section setlike_functor_theory.

  Context
    (F : Type -> Type)
    `{ContainerFunctor F}
    {A B : Type}.

  Implicit Types (t : F A) (b : B) (a : A) (f g : A -> B).

  (** ** Interaction between (∈) and <<map>> *)
  (******************************************************************************)
  (** Naturality relates elements before and after a map. *)
  Theorem in_map_iff : forall t f b,
      b ∈ map F f t <-> exists a : A, a ∈ t /\ f a = b.
  Proof.
    introv. compose near t on left.
    rewrite element_of_tosubset.
    reassociate -> on left.
    unfold element_of.
    rewrite <- (natural (G:=(-> Prop))).
    reflexivity.
  Qed.

  (** This next property says that applying <<f>> (or on the
      right-hand side, appling <<map f>>) is monotone with respect to
      the <<∈>> relation. *)
  Corollary in_map_mono : forall t f a,
      a ∈ t -> f a ∈ map F f t.
  Proof.
    introv. rewrite in_map_iff. now exists a.
  Qed.

  (** ** Respectfulness conditions *)
  (******************************************************************************)
  (** Renaming to keep consistent name scheme *)
  Corollary map_respectful : forall t (f g : A -> B),
      (forall a, a ∈ t -> f a = g a) -> map F f t = map F g t.
  Proof.
    apply (cont_pointwise (F := F)).
  Qed.

  Corollary map_respectful_id : forall t (f : A -> A),
      (forall a, a ∈ t -> f a = a) -> map F f t = t.
  Proof.
    intros. replace t with (map F id t) at 2
      by now rewrite (fun_map_id (F := F)).
    now apply (cont_pointwise (F := F)).
  Qed.

End setlike_functor_theory.

(** * Properness conditions *)
(******************************************************************************)
Definition pointwise_equal_on
  (F : Type -> Type) {A B} `{ToSubset F} :
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

(** * Quantification over elements *)
(******************************************************************************)
Section quantification.

  Context `{ContainerFunctor T}.

  Definition Forall `(P : A -> Prop) (t : T A) : Prop :=
    forall (a : A), a ∈ t -> P a.

  Definition Forany `(P : A -> Prop) (t :T A): Prop :=
    exists (a : A), a ∈ t /\ P a.

End quantification.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "x ∈ t" :=
    (element_of x t) (at level 50) : tealeaves_scope.
End Notations.
