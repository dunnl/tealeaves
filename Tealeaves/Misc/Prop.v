From Tealeaves Require Import
  Classes.Monoid.

Import Monoid.Notations.

(** * Propositional monoids *)
(**********************************************************************)

(** ** Disjunction *)
(**********************************************************************)
#[export] Instance Monoid_op_or: Monoid_op Prop := or.

#[export] Instance Monoid_unit_false: Monoid_unit Prop := False.

#[program, export] Instance Monoid_disjunction: @Monoid Prop or False.

(** ** Conjunction *)
(**********************************************************************)
#[export] Instance Monoid_op_and: Monoid_op Prop := and.

#[export] Instance Monoid_unit_true: Monoid_unit Prop := True.

#[program, export] Instance Monoid_conjunction: @Monoid Prop and True.

Solve All Obligations with intros; propext; firstorder.

#[program, export] Instance Monmor_neg_disj_conj:
  @Monoid_Morphism Prop Prop or False and True not.

Solve Obligations with intros; propext; firstorder.

(** * Boolean monoids *)

(** ** Disjunction *)
(**********************************************************************)
#[export] Instance Monoid_op_bool_or: Monoid_op bool := orb.

#[export] Instance Monoid_unit_bool_false: Monoid_unit bool := false.

#[program, export] Instance Monoid_disjunction_bool:
  @Monoid bool orb false.

Next Obligation.
  now destruct x, y, z.
Qed.

Next Obligation.
  now destruct x.
Qed.

(** ** Conjunction *)
(**********************************************************************)
#[export] Instance Monoid_op_bool_and: Monoid_op bool := andb.

#[export] Instance Monoid_unit_bool_true: Monoid_unit bool := true.

#[program, export] Instance Monoid_conjunction_bool:
  @Monoid bool andb true.

Next Obligation.
  now destruct x, y, z.
Qed.

Next Obligation.
  now destruct x.
Qed.
