Require Export Coq.Classes.EquivDec.
Require Export Coq.Structures.Equalities.

#[local] Set Implicit Arguments.

(** * Types with decidable equality *)
(******************************************************************************)
Class EqDec_eq (A : Type) :=
  eq_dec : forall (x y : A), {x = y} + {x <> y}.

#[export] Instance EqDec_eq_of_EqDec (A : Type) `(@EqDec A eq eq_equivalence) : EqDec_eq A.
Proof. trivial. Defined.

Declare Scope coqeqdec_scope.
Open Scope coqeqdec_scope.

Notation "x == y" := (eq_dec x y) (at level 70) : coqeqdec_scope.

Theorem eq_dec_refl {A : Type} `{EqDec_eq A} (x : A) : eq_dec x x = left eq_refl.
Proof.
  destruct (eq_dec x x); [|contradiction].
  f_equal; apply (Eqdep_dec.UIP_dec eq_dec).
Qed.

(** ** Support for decidable equalities *)
(******************************************************************************)
Ltac destruct_eq_args x y :=
  let DESTR_EQ := fresh "DESTR_EQ" in
  let DESTR_NEQ := fresh "DESTR_NEQ" in
  destruct (x == y) as [DESTR_EQ | DESTR_NEQ];
  let DESTR_EQs := fresh "DESTR_EQs" in
  let DESTR_NEQs := fresh "DESTR_NEQs" in
  destruct (y == x) as [DESTR_EQs | DESTR_NEQs];
  [ subst; try rewrite eq_dec_refl in *; try easy | subst; try easy ].

Tactic Notation "compare" "values" constr(x) "and" constr(y) :=
  destruct_eq_args x y.

Tactic Notation "compare" constr(x) "to" "both" "of " "{" constr(y) constr(z) "}" :=
  compare values x and y; try compare values x and z; try compare values y and z.
