Require Export Coq.Classes.EquivDec.
Require Export Coq.Structures.Equalities.

Set Implicit Arguments.

Class EqDec_eq (A : Type) :=
  eq_dec : forall (x y : A), {x = y} + {x <> y}.

Instance EqDec_eq_of_EqDec (A : Type) `(@EqDec A eq eq_equivalence) : EqDec_eq A.
Proof. trivial. Defined.

Declare Scope coqeqdec_scope.
Notation "x == y" := (eq_dec x y) (at level 70) : coqeqdec_scope.

Open Scope coqeqdec_scope.

Theorem eq_dec_refl {A : Type} `{EqDec_eq A} (x : A) : eq_dec x x = left eq_refl.
Proof.
  destruct (eq_dec x x); [|contradiction].
  f_equal; apply (Eqdep_dec.UIP_dec eq_dec).
Qed.
