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
