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

#[local] Generalizable Variables x y z a A B W M R.

(** * Monoids *)
(**********************************************************************)

(** ** Operational typeclasses *)
(**********************************************************************)
Class Monoid_op (A: Type) := monoid_op: A -> A -> A.

Class Monoid_unit (A: Type) := monoid_unit: A.

#[global] Arguments monoid_op {A}%type_scope {Monoid_op}.
#[global] Arguments monoid_unit A%type_scope {Monoid_unit}.

#[local] Notation "'Ƶ'" := (monoid_unit _): tealeaves_scope.
#[local] Infix "●" := monoid_op (at level 60): tealeaves_scope.

(** ** Monoid typeclass *)
(**********************************************************************)
Class Monoid (M: Type) {op: Monoid_op M} {unit: Monoid_unit M} :=
  { monoid_assoc: `((x ● y) ● z = x ● (y ● z));
    monoid_id_l: `(x ● Ƶ = x);
    monoid_id_r: `(Ƶ ● x = x);
  }.

(*|
=====================
Monoid homomorphisms
=====================

A homomorphism :math:`\phi: A \to B` is a function which satisfies

.. math::

  \phi (z_A) = z_B

.. math::

  \phi (a_1 \cdot_A a_2) = \phi(a_1) \cdot_B \phi(a_2)

.. coq::
|*)

(** ** Monoid homomorphsims *)
(**********************************************************************)
Class Monoid_Morphism
  (src tgt: Type)
  `{src_op: Monoid_op src}
  `{src_unit: Monoid_unit src}
  `{tgt_op: Monoid_op tgt}
  `{tgt_unit: Monoid_unit tgt}
  (ϕ: src -> tgt) :=
  { monmor_src: Monoid src;
    monmor_tgt: Monoid tgt;
    monmor_unit: ϕ Ƶ = Ƶ;
    monmor_op: `(ϕ (a1 ● a2) = ϕ a1 ● ϕ a2);
  }.

Section monoid_morphism_composition.

  Context
    (M1 M2 M3: Type)
    `{Monoid M1}
    `{Monoid M2}
    `{Monoid M3}
    (ϕ1: M1 -> M2)
    (ϕ2: M2 -> M3)
    `{! Monoid_Morphism M1 M2 ϕ1 }
    `{! Monoid_Morphism M2 M3 ϕ2 }.

  #[export] Instance Monoid_Morphism_compose:
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

(** ** Some Rudimentary Automation *)
(**********************************************************************)
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

(** * Monoid Constructions *)
(**********************************************************************)

(** ** Cartesian Product of Monoids *)
(**********************************************************************)
Section product_monoid.

  Context `{Monoid A, Monoid B}.

  #[export] Instance Monoid_unit_product: Monoid_unit (A * B) :=
    (Ƶ, Ƶ).

  #[export] Instance Monoid_op_product: Monoid_op (A * B) :=
    fun '(a1, b1) '(a2, b2) => (a1 ● a2, b1 ● b2).
  #[export] Program Instance Monoid_product: Monoid (A * B).

  Solve Obligations with
    (intros; destruct_all_pairs; unfold transparent tcs;
     cbn beta iota; now simpl_monoid).

End product_monoid.

(** ** The Opposite Monoid *)
(**********************************************************************)
#[local] Instance Monoid_op_Opposite {M} (op: Monoid_op M):
  Monoid_op M := fun m1 m2 => m2 ● m1.

#[export] Instance Monoid_Opposite
  `{unit: Monoid_unit M}
  `{op: Monoid_op M}
  `{! Monoid M}:
  @Monoid M (Monoid_op_Opposite op) unit.
Proof.
  constructor; unfold_ops @Monoid_op_Opposite;
    intros.
  - now rewrite monoid_assoc.
  - now rewrite monoid_id_r.
  - now rewrite monoid_id_l.
Qed.

Lemma Monoid_op_Opposite_involutive `{op: Monoid_op M}:
  Monoid_op_Opposite (Monoid_op_Opposite op) = op.
Proof.
  reflexivity.
Qed.

(** * Increment and Pre-increment *)
(**********************************************************************)

(** ** The <<incr>> Operation *)
(**********************************************************************)
Section incr.

  Context
    `{Monoid W}.

  (* It sometimes useful to have this curried operation, the
  composition of [strength] and [join]. *)
  Definition incr {A: Type}: W -> W * A -> W * A :=
    fun w2 '(w1, a) => (w2 ● w1, a).

  Lemma incr_zero {A: Type}:
    incr Ƶ = @id (W * A).
  Proof.
    ext [? ?]. cbn. now simpl_monoid.
  Qed.

  Lemma incr_incr {A: Type}: forall w1 w2,
    incr (A:=A) w2 ∘ incr w1 = incr (w2 ● w1).
  Proof.
    intros. ext [w a].
    cbn. now simpl_monoid.
  Qed.

End incr.

(** ** The <<preincr>> Operation *)
(**********************************************************************)

Section preincr.

  Context
    `{Monoid W}.

  Definition preincr {A B: Type} (f: W * A -> B) (w: W) :=
    f ∘ incr w.

  #[local] Infix "⦿" := preincr (at level 30): tealeaves_scope.

  Lemma preincr_zero {A B: Type}: forall (f: W * A -> B),
      f ⦿ Ƶ = f.
  Proof.
    intros. unfold preincr.
    now rewrite incr_zero.
  Qed.

  Lemma preincr_preincr {A B: Type}:
    forall (f: W * A -> B) (w1: W) (w2: W),
       f ⦿ w1 ⦿ w2 = f ⦿ (w1 ● w2).
  Proof.
    intros. unfold preincr.
    reassociate ->.
    now rewrite incr_incr.
  Qed.

  Lemma preincr_assoc {A B C: Type}
    (g: B -> C) (f: W * A -> B) (w: W):
    (g ∘ f) ⦿ w = g ∘ f ⦿ w.
  Proof.
    reflexivity.
  Qed.

End preincr.

From Coq Require Export
  Relations
  Classes.RelationClasses.

(** * Preordered Monoids *)
(**********************************************************************)
Class PreOrderedMonoidLaws
  (M: Type)
  (R: relation M)
  (op: Monoid_op M)
  (unit: Monoid_unit M) :=
  { pom_mono_l: `(R x y -> R (z ● x) (z ● y));
    pom_mono_r: `(R x y -> R (x ● z) (y ● z));
  }.

Class PreOrderedMonoid (M: Type) (R: relation M)
  {op: Monoid_op M} {unit: Monoid_unit M} :=
  { pom_monoid :> Monoid M;
    pom_order :> PreOrder R;
    pom_laws :> PreOrderedMonoidLaws M R op unit;
  }.

Class PreOrderedMonoidPos (M: Type) (R: relation M)
  {op: Monoid_op M} {unit: Monoid_unit M} :=
  { pompos_pom :> PreOrderedMonoid M R;
    pompos_pos: forall m, R Ƶ m;
  }.

Section lemmas.

  Context
    `{PreOrderedMonoid M R}.

  Lemma pompos_both: forall m n m' n',
      R m m' -> R n n' ->
      R (m ● n) (m' ● n').
  Proof.
    intros.
    transitivity (m ● n').
    apply pom_mono_l; auto.
    apply pom_mono_r; auto.
  Qed.

  Context
    `{! PreOrderedMonoidPos M R}.

  Lemma pompos_incr_r: forall m n,
      R m (m ● n).
  Proof.
    intros.
    rewrite <- (monoid_id_l m) at 1.
    apply pom_mono_l.
    apply pompos_pos.
  Qed.

  Lemma pompos_incr_l: forall m n,
      R m (n ● m).
  Proof.
    intros.
    rewrite <- (monoid_id_r m) at 1.
    apply pom_mono_r.
    apply pompos_pos.
  Qed.

End lemmas.

(** * Commutative Monoids *)
(**********************************************************************)
Class CommutativeMonoidOp {M: Type}
  (op: Monoid_op M) :=
  { comm_mon_swap: forall (m1 m2: M),
      m1 ● m2 = m2 ● m1;
  }.

#[export] Instance CommutativeMonoidOp_Opposite
  `{op: Monoid_op M}
  `{comm: ! CommutativeMonoidOp op}:
  CommutativeMonoidOp (Monoid_op_Opposite op).
Proof.
  constructor.
  intros.
  unfold Monoid_op.
  unfold_ops @Monoid_op_Opposite.
  rewrite comm_mon_swap.
  reflexivity.
Qed.

(** * Notations *)
(**********************************************************************)
Module Notations.

  Notation "'Ƶ'" :=
    (monoid_unit _): tealeaves_scope. (* \Zbar *)
  Infix "●" :=
    monoid_op (at level 60): tealeaves_scope. (* \CIRCLE *)
  Infix "⦿" :=
    preincr (at level 30): tealeaves_scope. (* \circledbullet *)

End Notations.
