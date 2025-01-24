(*|
#######################
Tealeaves.Axioms
#######################

These two exports bring in two axioms.

Function extensionality:

  .. math::

     \forall x, f x = g x \to f = g

Propositional extensionality:

  .. math::

     \forall \phi \psi, (\phi \iff \psi) \iff \phi = \psi

These axioms are known to be consistent with Coq's theory. They are
not fundamental to Tealeaves in the sense that propositional equality
could be replaced everywhere with setoids, but these axioms make the
formalization much more convenient.
|*)

From Coq.Logic Require Export
  FunctionalExtensionality
  PropExtensionality.
