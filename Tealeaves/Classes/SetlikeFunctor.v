From Tealeaves Require Export
     Classes.Functor
     Classes.DecoratedFunctor
     Functors.Sets.

From Coq Require Import
     Relations.Relation_Definitions
     Classes.Morphisms.

Import Monoid.Notations.
Import Functor.Notations.
Import Sets.Notations.
#[local] Open Scope tealeaves_scope.

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

  Instance toset_set : Toset set :=
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

(** * Decorated set-like functors *)
(******************************************************************************)

(** ** Derived operation [tosetd] *)
(******************************************************************************)
Definition tosetd F `{Toset F} `{Decorate W F} {A} :
  F A -> (W * A -> Prop) := toset F ∘ dec F.

#[local] Notation "x ∈d t" :=
  (tosetd _ t x) (at level 50) : tealeaves_scope.

(** ** Utility lemmas for [shift] *)
(******************************************************************************)
Section shift_utility_lemmas.

  Context
    (F : Type -> Type)
    `{SetlikeFunctor F}
    `{Monoid W}.

  Theorem in_shift_iff {A} : forall w w1 a (t : F (W * A)),
      (w, a) ∈ shift F (w1, t) <->
      exists w2, (w2, a) ∈ t /\ w = w1 ● w2.
  Proof.
    introv. unfold shift, compose, strength.
    rewrite (in_fmap_iff F). split.
    - intros [ [w1' [w2' a']] [hin heq]].
      rewrite (in_fmap_iff F) in hin.
      destruct hin as [ [w_ a_] [hin' heq']].
      inverts heq'. inverts heq. now (exists w2').
    - intros [w2 [? ?]]. exists (w1, (w2, a)).
      rewrite (in_fmap_iff F). subst. split.
      + now (exists (w2, a)).
      + reflexivity.
  Qed.

  Theorem in_shift_mono {A} : forall w1 w2 a (t : F (W * A)),
      (w1, a) ∈ t -> (w2 ● w1, a) ∈ shift F (w2, t).
  Proof.
    introv. unfold shift, compose, strength.
    rewrite (in_fmap_iff F). exists (w2, (w1, a)).
    rewrite (in_fmap_iff F). split.
    - now (exists (w1, a)).
    - easy.
  Qed.

End shift_utility_lemmas.

(** ** Utility lemmas for [toset] and [tosetd] *)
(******************************************************************************)
Section tosetd_utility_lemmas.

  Context
    (F : Type -> Type)
    `{SetlikeFunctor F}
    `{Monoid W}
    `{Decorate W F}
    `{! DecoratedFunctor W F}
    {A : Type}.

  Implicit Types (w : W) (a : A) (t : F A).

  Theorem in_in_extract : forall w a (t : F (W * A)),
      (w, a) ∈ t -> a ∈ fmap F (extract (prod W)) t.
  Proof.
    introv hyp. apply (in_fmap_iff F). now exists (w, a).
  Qed.

  Theorem in_of_ind : forall w a t,
      (w, a) ∈d t -> a ∈ t.
  Proof.
    introv hyp. replace t with (fmap F (extract (prod W)) (dec F t)).
    rewrite (in_fmap_iff F). now (exists (w, a)).
    compose near t on left.
    now rewrite (dfun_dec_extract W F).
  Qed.

  Theorem ind_of_in : forall t a,
      a ∈ t <-> exists w, (w, a) ∈d t.
  Proof.
    introv. split; intro hyp.
    - replace t with (fmap F (extract (prod W)) (dec F t)) in hyp
        by (now compose near t on left; rewrite (dfun_dec_extract W F)).
      rewrite (in_fmap_iff F) in hyp. destruct hyp as [[w ?] [? heq]].
      inverts heq. now (exists w).
    - destruct hyp as [? hyp]. now apply in_of_ind in hyp.
  Qed.

End tosetd_utility_lemmas.

(** ** Respectfulness properties for [fmapd] *)
(******************************************************************************)
Section decorated_setlike_respectfulness.

  Context
    (F : Type -> Type)
    `{Monoid W}
    `{Fmap F} `{Decorate W F} `{Toset F}
    `{! DecoratedFunctor W F}
    `{! SetlikeFunctor F}.

  Lemma fmapd_respectful {A B} : forall (t : F A) (f g : W * A -> B),
      (forall w a, (w, a) ∈d t -> f (w, a) = g (w, a)) ->
      fmapd F f t = fmapd F g t.
  Proof.
    intros. unfold fmapd, compose.
    apply (fmap_respectful F); auto.
    intros [? ?]; auto.
  Qed.

  Corollary fmapd_respectful_id {A} : forall (t : F A) (f : W * A -> A),
      (forall w a, (w, a) ∈d t -> f (w, a) = a) ->
      fmapd F f t = t.
  Proof.
    intros. replace t with (fmapd F (extract (prod W)) t) at 2
      by (now rewrite (fmapd_id F)).
    now apply fmapd_respectful.
  Qed.

End decorated_setlike_respectfulness.

(** ** Basic properties of [tosetd] and [fmapd] *)
(******************************************************************************)
Section decorated_setlike_properties.

  Context
    (F : Type -> Type)
    `{Monoid W}
    `{Fmap F} `{Decorate W F} `{Toset F}
    `{! DecoratedFunctor W F}
    `{! SetlikeFunctor F}.

  (** *** Interaction between [tosetd] and [fmapd] *)
  (******************************************************************************)
  Theorem ind_fmapd_iff {A B} : forall w b t (f : W * A -> B),
      (w, b) ∈d fmapd F f t <->
      exists (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    introv. compose near t on left.
    unfold tosetd. reassociate -> on left.
    rewrite (dec_fmapd F).
    unfold compose, fmapd, compose.
    rewrite (in_fmap_iff F). split; intro hyp.
    - destruct hyp as [[? a] [? heq]]. inverts heq. now (exists a).
    - destruct hyp as [a [? heq]]. inverts heq. now exists (w, a).
  Qed.

  Theorem ind_fmapd_mono {A B} : forall w a t (f : W * A -> B),
      (w, a) ∈d t ->
      (w, f (w, a)) ∈d fmapd F f t.
  Proof.
    introv. unfold tosetd. compose near t.
    reassociate ->. rewrite (dec_fmapd F).
    unfold compose, fmapd, compose.
    rewrite (in_fmap_iff F). now exists (w, a).
  Qed.

  Section corollaries.

    Context
      {A B : Type}.

    Implicit Types (w : W) (a : A) (b : B) (t : F A).

    (** *** Corollaries: [tosetd] and [fmap] *)
    (******************************************************************************)
    Corollary ind_fmap_iff : forall w b t f,
        (w, b) ∈d fmap F f t <->
        exists a, (w, a) ∈d t /\ f a = b.
    Proof.
      introv. rewrite (fmap_to_fmapd F).
      assert (rw : forall a, f a = (f ∘ snd) (w, a))
        by now introv.
      setoid_rewrite rw. apply ind_fmapd_iff.
    Qed.

    Corollary ind_fmap_mono : forall w a t (f : A -> B),
        (w, a) ∈d t ->
        (w, f a) ∈d fmap F f t.
    Proof.
      introv. rewrite (fmap_to_fmapd F).
      change (f a) with ((f ∘ snd) (w, a)).
      apply ind_fmapd_mono.
    Qed.

    (** *** Corollaries: [toset] and [fmapd] *)
    (******************************************************************************)
    Corollary in_fmapd_iff : forall b t f,
        b ∈ fmapd F f t <->
        exists w a, (w, a) ∈d t /\ f (w, a) = b.
    Proof.
      introv. unfold fmapd, compose.
      rewrite (in_fmap_iff F). split.
      - intros [[w a] [? ?]]. now (exists w a).
      - intros [w [a [? ?]]]. now exists (w, a).
    Qed.

  End corollaries.

End decorated_setlike_properties.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "x ∈ t" :=
    (toset _ t x) (at level 50) : tealeaves_scope.
  Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.
End Notations.
