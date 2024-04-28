From Tealeaves Require Import
  Classes.Monoid.

(** * Natural numbers with addition *)
#[global] Instance Monoid_op_plus : Monoid_op nat := plus.

#[global] Instance Monoid_unit_zero : Monoid_unit nat := 0.

#[global, program] Instance Monoid_Nat : @Monoid nat Monoid_op_plus Monoid_unit_zero.

Solve Obligations with (intros; unfold transparent tcs; lia).

(** * Natural numbers with maximum *)
#[local] Instance Monoid_op_max : Monoid_op nat := max.

#[local] Instance Monoid_unit_max : Monoid_unit nat := 0.

#[local, program] Instance Monoid_Nat_max : @Monoid nat Monoid_op_max Monoid_unit_max.

Solve Obligations with (intros; unfold transparent tcs; lia).

#[global] Instance PreOrder_Nat_lt:
  @PreOrder nat le.
Proof.
  constructor; cbv; lia.
Qed.

#[global] Instance PreOrderedMonoidLaws_Nat_plus:
  @PreOrderedMonoidLaws nat le Monoid_op_plus Monoid_unit_zero.
Proof.
  constructor; unfold transparent tcs; lia.
Qed.

#[global] Instance PreOrderedMonoid_Nat_plus:
  @PreOrderedMonoid nat le Monoid_op_plus Monoid_unit_zero.
Proof.
  constructor; typeclasses eauto.
Qed.

#[global] Instance PreOrderedMonoidPos_Nat_plus:
  @PreOrderedMonoidPos nat le Monoid_op_plus Monoid_unit_zero.
Proof.
  constructor; try typeclasses eauto.
  cbv. lia.
Qed.

#[global] Instance PreOrderedMonoidLaws_Nat_max:
  @PreOrderedMonoidLaws nat le Monoid_op_max Monoid_unit_max.
Proof.
  constructor; unfold transparent tcs; lia.
Qed.

#[global] Instance PreOrderedMonoid_Nat_max:
  @PreOrderedMonoid nat le Monoid_op_max Monoid_unit_max.
Proof.
  constructor; typeclasses eauto.
Qed.

#[global] Instance PreOrderedMonoidPos_Nat_max:
  @PreOrderedMonoidPos nat le Monoid_op_max Monoid_unit_max.
Proof.
  constructor; try typeclasses eauto.
  cbv. lia.
Qed.
