From Tealeaves Require Import
  Util.Prelude
  Classes.Monoid.

(** * Natural numbers with addition *)
#[global] Instance Monoid_op_plus : Monoid_op nat := plus.

#[global] Instance Monoid_unit_zero : Monoid_unit nat := 0.

#[global, program] Instance Monoid_Nat : @Monoid nat Monoid_op_plus Monoid_unit_zero.

Solve Obligations with (intros; unfold transparent tcs; lia).
