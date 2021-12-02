From Tealeaves Require Export
     Classes.Monoid
     Classes.SetlikeModule.

From Coq Require Import
     Relations.Relation_Definitions
     Classes.Morphisms.

Import Monoid.Notations.
Import Functor.Notations.
Import Sets.Notations.
Import SetlikeFunctor.Notations.
#[local] Open Scope tealeaves_scope.

Class Respectful F `{Fmap F} `{Toset F} :=
  respectful_proof : forall A B (t : F A) (f g : A -> B),
    (forall a, a ∈ t -> f a = g a) -> fmap F f t = fmap F g t.

Class RespectfulStrong F `{Fmap F} `{Toset F} :=
  respectful_strong_proof : forall A B (t : F A) (f g : A -> B),
    (forall a, a ∈ t -> f a = g a) <-> fmap F f t = fmap F g t.

(** ** Respectfulness conditions and [fmap] *)
(******************************************************************************)
Section fmap_respectful_theorems.

  Context
    (F : Type -> Type)
    `{SetlikeFunctor F}.

  (** *** Corollaries of respectfulness for [fmap] *)
  (******************************************************************************)
  Section weak.

    Context
      `{! Respectful F}.

    Corollary fmap_respectful : forall A B (t : F A) (f g : A -> B),
        (forall a, a ∈ t -> f a = g a) -> fmap F f t = fmap F g t.
    Proof.
      apply (respectful_proof).
    Qed.

    Corollary fmap_respectful_id : forall A (t : F A) (f : A -> A),
        (forall a, a ∈ t -> f a = a) -> fmap F f t = t.
    Proof.
      intros. replace t with (fmap F id t) at 2
        by now rewrite (fun_fmap_id F).
      now apply fmap_respectful.
    Qed.

  End weak.

  (** *** Corollaries of strong respectfulness for [fmap] *)
  (******************************************************************************)
  Section strong.

    Context
      `{! RespectfulStrong F}.

    Corollary fmap_respectful_strong : forall A B (t : F A) (f g : A -> B),
        (forall a, a ∈ t -> f a = g a) -> fmap F f t = fmap F g t.
    Proof.
      apply (respectful_strong_proof).
    Qed.

    Corollary fmap_respectful_strong_id : forall A (t : F A) (f : A -> A),
        (forall a, a ∈ t -> f a = a) -> fmap F f t = t.
    Proof.
      intros. replace t with (fmap F id t) at 2
        by now rewrite (fun_fmap_id F).
      now apply fmap_respectful_strong.
    Qed.

  End strong.

End fmap_respectful_theorems.

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

Local Infix "<++" := injective (at level 55).

Definition rigid {A B} (R : relation A) (R' : relation B) : relation (A -> B) :=
  fun f g => forall a1 a2 : A, R' (f a1) (g a2) <-> R a1 a2.

Local Infix "<++>" := rigid (at level 55).

(** ** Respectfulness for <<fmap>> and <<bind>> are equivalent. *)
(******************************************************************************)
Section toset_resp_bind_equiv_fmap.

  Context
    F `{RightModule F T} `{Toset F}.

  #[global] Instance toset_bind_resp_of_fmap :
      (forall A B (t : F A), Proper (ext_rel t ++> eq_at t t) (fmap F (B:=B))) ->
      (forall A B (t : F A), Proper (ext_rel t ++> eq_at t t) (bind F (B:=B))).
  Proof.
    intros Hproper. unfold Proper, respectful, ext_rel, eq_at in *.
    intros A B t f g Heq. unfold transparent tcs. unfold compose.
    specialize (Hproper _ _ t f g). rewrite Hproper; auto.
  Qed.

  #[global] Instance toset_fmap_resp_of_bind :
    (forall A B (t : F A), Proper (ext_rel t ++> eq_at t t) (bind F (B:=B))) ->
    (forall A B (t : F A), Proper (ext_rel t ++> eq_at t t) (fmap F (B:=B))).
  Proof.
    unfold transparent tcs. intros Hproper.
    unfold Proper, respectful, ext_rel, eq_at, compose in *.
    intros A B t f g Heq. rewrite 2(fmap_to_bind F T). unfold compose.
    apply Hproper. intros; fequal; auto.
  Qed.

End toset_resp_bind_equiv_fmap.

(** ** Injective <<bind>> implies <<fmap>> if <<ret>> is injective. *)
(** We show elsewhere that <<set>> does not satisfy the converse of
    this statement. *)
(******************************************************************************)
Section toset_fmap_injective_of_bind.

  Context
    F `{RightModule F T} `{Toset F}.

  Hypothesis
    (ret_inj : forall A (x y : A),
        ret T x = ret T y -> x = y).

  Theorem toset_fmap_injective_of_bind :
    (forall A B (t : F A), Proper (ext_rel t <++ eq_at t t) (bind F (B:=B))) ->
    (forall A B (t : F A), Proper (ext_rel t <++ eq_at t t) (fmap F (B:=B))).
  Proof.
    intros hyp A B t f g heq. specialize (hyp A B t (ret T ∘ f) (ret T ∘ g)).
    rewrite <- 2(fmap_to_bind F T) in hyp; unfold compose in hyp.
    unfold Proper, respectful, ext_rel, eq_at in *.
    auto using ret_inj.
  Qed.

End toset_fmap_injective_of_bind.
