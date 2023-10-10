(*|
#######################
Tealeaves.Axioms
#######################

============================
Axioms imported by Tealeaves
============================

These two exports bring in two axioms.

function extensionality
  .. math::
     \forall x, f x = g x \to f = g

and

propositional extensionality
  .. math::
     \forall \phi \psi, (\phi \iff \psi) \iff \phi = \psi
|*)
From Coq.Logic Require Export
     FunctionalExtensionality
     PropExtensionality.

(** ** Support for reasoning with extensionality *)
(******************************************************************************)
Ltac ext_destruct pat :=
  (let tmp := fresh "TMP" in extensionality tmp; destruct tmp as pat)
  + (extensionality pat) + (fail "ext failed, make sure your names are fresh").

Tactic Notation "ext" simple_intropattern(pat) := ext_destruct pat.
Tactic Notation "ext" simple_intropattern(x) simple_intropattern(y) := ext x; ext y.
Tactic Notation "ext" simple_intropattern(x) simple_intropattern(y) simple_intropattern(z) := ext x; ext y; ext z.
Tactic Notation "ext" simple_intropattern(x) simple_intropattern(y) simple_intropattern(z) simple_intropattern(w) := ext x; ext y; ext z.
Tactic Notation "ext" simple_intropattern(x) simple_intropattern(y) simple_intropattern(z) simple_intropattern(w) := ext x; ext y; ext z; ext w.
Tactic Notation "ext" simple_intropattern(x) simple_intropattern(y) simple_intropattern(z) simple_intropattern(w) simple_intropattern(w) := ext x; ext y; ext z; ext w; ext u.
Tactic Notation "ext" simple_intropattern(x) simple_intropattern(y) simple_intropattern(z) simple_intropattern(w) simple_intropattern(u) simple_intropattern(v) := ext x; ext y; ext z; ext w; ext u; ext v.

(** Reduce an equality between propositions to the two directions of
mutual implication using the propositional extensionality axiom. *)
Tactic Notation "propext" := apply propositional_extensionality; split.

(** Reduce an equality between propositions to the two directions of
mutual implication using the propositional extensionality axiom. *)
Tactic Notation "setext" :=
  intros; repeat (let x := fresh "x" in ext x); propext.

Tactic Notation "setext" simple_intropattern(pat) :=
  intros; ext pat; propext.
