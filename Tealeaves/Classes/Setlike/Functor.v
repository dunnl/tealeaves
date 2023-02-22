From Tealeaves Require Export
  Classes.Functor
  Functors.Sets.

From Coq Require Import
  Relations.Relation_Definitions
  Classes.Morphisms.

Import Monoid.Notations.
Import Functor.Notations.
Import Sets.Notations.

(** * Set-like functors *)
(******************************************************************************)
Section SetlikeFunctor_operations.

  Context
    (F : Type -> Type).

  Class Toset :=
    toset : F ⇒ set.

End SetlikeFunctor_operations.

(* Mark the type argument of <<toset>> implicit *)
Arguments toset F%function_scope {Toset} {A}%type_scope.

#[local] Notation "x ∈ t" :=
  (toset _ t x) (at level 50) : tealeaves_scope.

Section SetlikeFunctor.

  Context
    (F : Type -> Type)
      `{Fmap F} `{Toset F}.

  Class SetlikeFunctor :=
    { xfun_natural :> Natural (@toset F _);
      xfun_functor :> Functor F;
      xfun_respectful : forall A B (t : F A) (f g : A -> B),
        (forall a, a ∈ t -> f a = g a) -> fmap F f t = fmap F g t;
    }.

End SetlikeFunctor.

(** ** [toset]-preserving natural transformations *)
(******************************************************************************)
Class SetPreservingTransformation
  {F G : Type -> Type}
  `{Fmap F} `{Toset F}
  `{Fmap G} `{Toset G}
  (η : F ⇒ G) :=
  { xtrans_natural : Natural η;
    xtrans_commute : forall A, toset F = toset G ∘ η A;
  }.

(** ** Instance for <<set>> *)
(******************************************************************************)
Section SetlikeFunctor_set_instance.

  Instance Toset_set : Toset set :=
    fun A s => s.

  Instance Natural_toset_set : Natural (@toset set _).
  Proof.
    constructor; try typeclasses eauto.
    intros. ext S b. reflexivity.
  Qed.

  Lemma toset_set_respectful : forall (A B : Type) (t : A -> Prop) (f g : A -> B),
      (forall a : A, a ∈ t -> f a = g a) -> fmap set f t = fmap set g t.
  Proof.
    intros. ext b. cbv. propext.
    intros. preprocess. setoid_rewrite H. firstorder. auto.
    intros. preprocess. setoid_rewrite <- H. firstorder. auto.
  Qed.

  Instance SetlikeFunctor_set : SetlikeFunctor set :=
    {| xfun_respectful := toset_set_respectful;
    |}.

End SetlikeFunctor_set_instance.

(** ** Basic properties of set-like functors *)
(******************************************************************************)
Section setlike_functor_theory.

  Context
    (F : Type -> Type)
    `{SetlikeFunctor F}
    {A B : Type}.

  Implicit Types (t : F A) (b : B) (a : A) (f g : A -> B).

  (** Naturality relates the leaf sets before and after mapping a
  function over <<F>>. *)
  Theorem in_fmap_iff : forall t f b,
      b ∈ fmap F f t <-> exists a : A, a ∈ t /\ f a = b.
  Proof.
    introv. compose near t on left.
    now rewrite <- (natural (G:=(-> Prop))).
  Qed.

  (** This next property says that applying <<f>> (or on the
      right-hand side, appling <<fmap f>>) is monotone with respect to
      the <<∈>> relation. *)
  Corollary in_fmap_mono : forall t f a,
      a ∈ t -> f a ∈ fmap F f t.
  Proof.
    introv. rewrite in_fmap_iff. now exists a.
  Qed.

  Corollary fmap_respectful : forall t f g,
      (forall a, a ∈ t -> f a = g a) -> fmap F f t = fmap F g t.
  Proof.
    apply (xfun_respectful F).
  Qed.

  Corollary fmap_respectful_id : forall t (f : A -> A),
      (forall a, a ∈ t -> f a = a) -> fmap F f t = t.
  Proof.
    intros. replace t with (fmap F id t) at 2
      by now rewrite (fun_fmap_id F).
    now apply (xfun_respectful F).
  Qed.

End setlike_functor_theory.

(*
(** * Formalization as properness conditions *)
(******************************************************************************)

(** ** Relations *)
(******************************************************************************)
Definition ext_rel {A B} `{Toset F} : F A -> relation (A -> B) :=
  fun t f g => (forall a : A, a ∈ t -> f a = g a).

Definition eq_at {A B} : A -> A -> relation (A -> B) :=
  fun (t1 t2 : A) (f g : A -> B) => f t1 = g t2.

Definition injective {A B} (R : relation A) (R' : relation B) : relation (A -> B) :=
  fun f g => forall a1 a2 : A, R' (f a1) (g a2) -> R a1 a2.

Infix "<++" := injective (at level 55).

Definition rigid {A B} (R : relation A) (R' : relation B) : relation (A -> B) :=
  fun f g => forall a1 a2 : A, R' (f a1) (g a2) <-> R a1 a2.

Infix "<++>" := rigid (at level 55).
 *)

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "x ∈ t" :=
    (toset _ t x) (at level 50) : tealeaves_scope.
End Notations.

