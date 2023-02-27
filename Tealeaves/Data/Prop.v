From Tealeaves Require Import
  Classes.Monoid.

(** * Propositional monoids *)
#[export] Instance Monoid_op_or: Monoid_op Prop := or.

#[export] Instance Monoid_unit_false: Monoid_unit Prop := False.

#[program, export] Instance Monoid_disjunction: @Monoid Prop or False.

#[export] Instance Monoid_op_and: Monoid_op Prop := and.

#[export] Instance Monoid_unit_true: Monoid_unit Prop := True.

#[program, export] Instance Monoid_conjunction: @Monoid Prop and True.

Solve All Obligations with intros; propext; firstorder.

#[program, export] Instance Monmor_neg_disj_conj :
  @Monoid_Morphism Prop Prop or False and True not.

Solve Obligations with intros; propext; firstorder.
