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

From Tealeaves Require Import
  Util.Prelude.

#[local] Generalizable Variables x y z a A B.

(** * Monoids *)

(** ** Operational typeclasses *)
Class Monoid_op (A : Type) := monoid_op : A -> A -> A.

Class Monoid_unit (A : Type) := monoid_unit : A.

Arguments monoid_op {A}%type_scope {Monoid_op}.
Arguments monoid_unit A%type_scope {Monoid_unit}.

(** ** Notations *)
Module Notations.

  Notation "'Ƶ'" := (monoid_unit _) : tealeaves_scope. (* \Zbar *)

  Infix "●" := monoid_op (at level 60) : tealeaves_scope. (* \CIRCLE *)

End Notations.

Import Notations.

(** ** Monoid typeclass *)
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

Section monoid_morphism.

  Context
    {A B : Type}
      `{Monoid_op A}
      `{Monoid_unit A}
      `{Monoid_op B}
      `{Monoid_unit B}
      (ϕ : A -> B).

  Class Monoid_Morphism :=
    { monmor_a : Monoid A;
      monmor_b : Monoid B;
      monmor_unit : ϕ Ƶ = Ƶ;
      monmor_op : `(ϕ (a1 ● a2) = ϕ a1 ● ϕ a2); }.

End monoid_morphism.

(** ** Some rudimentary automation *)
Ltac simpl_monoid :=
  try rewrites monoid_id_l;
  try rewrites monoid_id_r;
  try rewrites monoid_assoc.

Tactic Notation "simpl_monoid" "in" ident(H) :=
  try rewrite monoid_id_l in H;
  try rewrite monoid_id_r in H;
  try rewrite monoid_assoc in H.

Tactic Notation "simpl_monoid" "in" "*" :=
  try rewrite monoid_id_l in *;
  try rewrite monoid_id_r in *;
  try rewrite monoid_assoc in *.

(** * Cartesian product of monoids *)
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
