(*|
This files defines typeclasses for monoids in the category of Coq types and functions

- [Monoid] for monoids_

- [Comonoid] for comonoids_

.. _monoids: https://ncatlab.org/nlab/show/monoid
.. _comonoids: https://ncatlab.org/nlab/show/comonoid

Just like in the category of sets, where

  Every set can be made into a comonoid in Set (with the cartesian product) in a unique way.

comonoids in Coq's category are not particularly varied: there is one comonoid on each type.
|*)

From Tealeaves Require Export
  Prelude.

#[local] Generalizable Variables x y z a A B.

(** * Monoids *)
(******************************************************************************)

(** ** Operational typeclasses *)
(******************************************************************************)
Class Monoid_op (A : Type) := monoid_op : A -> A -> A.

Class Monoid_unit (A : Type) := monoid_unit : A.

Arguments monoid_op {A}%type_scope {Monoid_op}.
Arguments monoid_unit A%type_scope {Monoid_unit}.

#[local] Notation "'Ƶ'" := (monoid_unit _) : tealeaves_scope. (* \Zbar *)
#[local] Infix "●" := monoid_op (at level 60) : tealeaves_scope. (* \CIRCLE *)

(** ** Monoid typeclass *)
(******************************************************************************)
Class Monoid (M : Type) {op : Monoid_op M} {unit : Monoid_unit M} :=
  { monoid_assoc : `((x ● y) ● z = x ● (y ● z));
    monoid_id_l : `(x ● Ƶ = x);
    monoid_id_r : `(Ƶ ● x = x); }.

(*|
=====================
Monoid homomorphisms
=====================

A homomorphism :math:`\phi : A \to B` is a function which satisfies

.. math::

  \phi (z_A) = z_B

.. math::

  \phi (a_1 \cdot_A a_2) = \phi(a_1) \cdot_B \phi(a_2)

.. coq::
|*)

(** ** Monoid homomorphsims *)
(******************************************************************************)
Class Monoid_Morphism
  (src tgt : Type)
  `{src_op : Monoid_op src}
  `{src_unit : Monoid_unit src}
  `{tgt_op : Monoid_op tgt}
  `{tgt_unit : Monoid_unit tgt}
  (ϕ : src -> tgt) :=
  { monmor_src : Monoid src;
    monmor_tgt : Monoid tgt;
    monmor_unit : ϕ Ƶ = Ƶ;
    monmor_op : `(ϕ (a1 ● a2) = ϕ a1 ● ϕ a2);
  }.

Section monoid_morphism_composition.

  Context
    (M1 M2 M3 : Type)
      `{Monoid M1}
      `{Monoid M2}
      `{Monoid M3}
      (ϕ1 : M1 -> M2)
      (ϕ2 : M2 -> M3)
      `{! Monoid_Morphism M1 M2 ϕ1 }
      `{! Monoid_Morphism M2 M3 ϕ2 }.

  #[export] Instance Monoid_Morphism_compose :
    Monoid_Morphism M1 M3 (ϕ2 ∘ ϕ1).
  Proof.
    constructor; try typeclasses eauto.
    all: unfold compose.
    - rewrite (monmor_unit (src := M1) (tgt := M2)).
      rewrite (monmor_unit (src := M2) (tgt := M3)).
      reflexivity.
    - intros.
      rewrite (monmor_op (src := M1) (tgt := M2)).
      rewrite (monmor_op (src := M2) (tgt := M3)).
      reflexivity.
  Qed.

End monoid_morphism_composition.

(** ** Some rudimentary automation *)
(******************************************************************************)
Ltac simpl_monoid :=
  repeat rewrite monoid_id_l;
  repeat rewrite monoid_id_r;
  repeat rewrite monoid_assoc.

Tactic Notation "simpl_monoid" "in" ident(H) :=
  repeat rewrite monoid_id_l in H;
  repeat rewrite monoid_id_r in H;
  repeat rewrite monoid_assoc in H.

Tactic Notation "simpl_monoid" "in" "*" :=
  repeat rewrite monoid_id_l in *;
  repeat rewrite monoid_id_r in *;
  repeat rewrite monoid_assoc in *.

(** * Cartesian product of monoids *)
(******************************************************************************)
Section product_monoid.

  Context `{Monoid A, Monoid B}.

  #[export] Instance Monoid_unit_product : Monoid_unit (A * B) :=
    (Ƶ, Ƶ).

  #[export] Instance Monoid_op_product : Monoid_op (A * B) :=
    fun '(a1, b1) '(a2, b2) => (a1 ● a2, b1 ● b2).
  #[export] Program Instance Monoid_product : Monoid (A * B).

  Solve Obligations with
    (intros; destruct_all_pairs; unfold transparent tcs;
     cbn beta iota; now simpl_monoid).

End product_monoid.

(** * Increment and pre-increment *)
(******************************************************************************)

(** ** The <<incr>> operation *)
(******************************************************************************)
Section incr.

  Context
    (W : Type)
    `{Monoid W}.

  (* It sometimes useful to have this curried operation, the
  composition of [strength] and [join]. *)
  Definition incr {A : Type} : W -> W * A -> W * A :=
    fun w2 '(w1, a) => (w2 ● w1, a).

  Lemma incr_zero {A : Type} :
    incr Ƶ = @id (W * A).
  Proof.
    ext [? ?]. cbn. now simpl_monoid.
  Qed.

  Lemma incr_incr {A : Type} : forall w1 w2,
    incr (A:=A) w2 ∘ incr w1 = incr (w2 ● w1).
  Proof.
    intros. ext [w a].
    cbn. now simpl_monoid.
  Qed.

End incr.

(** ** The <<preincr>> operation *)
(******************************************************************************)

Section preincr.

  Context
    (W : Type)
    `{Monoid W}.

  Definition preincr {A B : Type} (f : W * A -> B) (w : W) :=
    f ∘ incr W w.

  #[local] Infix "⦿" := preincr (at level 30) : tealeaves_scope.

  Lemma preincr_zero {A B : Type} : forall (f : W * A -> B),
      f ⦿ Ƶ = f.
  Proof.
    intros. unfold preincr.
    now rewrite incr_zero.
  Qed.

  Lemma preincr_preincr {A B : Type} : forall (f : W * A -> B) (w1 : W) (w2 : W),
       f ⦿ w1 ⦿ w2 = f ⦿ (w1 ● w2).
  Proof.
    intros. unfold preincr.
    reassociate ->.
    now rewrite (incr_incr W).
  Qed.

  Lemma preincr_assoc {A B C : Type} (g : B -> C) (f : W * A -> B) (w : W) :
    (g ∘ f) ⦿ w = g ∘ f ⦿ w.
  Proof.
    reflexivity.
  Qed.

End preincr.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "'Ƶ'" := (monoid_unit _) : tealeaves_scope. (* \Zbar *)
  Infix "●" := monoid_op (at level 60) : tealeaves_scope. (* \CIRCLE *)
  Infix "⦿" := (preincr _) (at level 30) : tealeaves_scope. (* \circledbullet *)

End Notations.
