From Tealeaves Require Import
  Classes.Monoid
  Tactics.Debug.

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

(** ** Simplification Support *)
(**********************************************************************)
Lemma monoid_conjunction_rw:
  forall (P1 P2: Prop),
    monoid_op (Monoid_op := Monoid_op_and) P1 P2 = (P1 /\ P2).
Proof.
  reflexivity.
Qed.

Lemma monoid_conjunction_unit_rw:
  monoid_unit Prop (Monoid_unit := Monoid_unit_true) = True.
Proof.
  reflexivity.
Qed.

Ltac simplify_monoid_conjunction :=
  ltac_trace "simplify_monoid_conjunction";
  match goal with
  | |- context[monoid_op (Monoid_op := Monoid_op_and) ?P1 ?P2] =>
      rewrite monoid_conjunction_rw
  | |- context[monoid_unit Prop (Monoid_unit := Monoid_unit_true)] =>
      rewrite monoid_conjunction_unit_rw
  end.

Ltac simplify_monoid_conjunction_in H :=
  rewrite monoid_conjunction_rw in H.

Lemma monoid_disjunction_rw:
  forall (P1 P2: Prop),
    monoid_op (Monoid_op := Monoid_op_or) P1 P2 = (P1 \/ P2).
Proof.
  reflexivity.
Qed.

Lemma monoid_disjunction_unit_rw:
  monoid_unit Prop (Monoid_unit := Monoid_unit_false) = False.
Proof.
  reflexivity.
Qed.

Ltac simplify_monoid_disjunction :=
  ltac_trace "simplify_monoid_disjunction";
  match goal with
  | |- context[monoid_op (Monoid_op := Monoid_op_or) ?P1 ?P2] =>
      rewrite monoid_disjunction_rw
  | |- context[monoid_unit Prop (Monoid_unit := Monoid_unit_false)] =>
      rewrite monoid_disjunction_unit_rw
  end.

(** * Boolean monoids *)
(**********************************************************************)

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
