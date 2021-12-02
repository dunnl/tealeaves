From Tealeaves Require Import
     Util.Prelude
     Monoid
     Product
     Writer.

Require Import Tealeaves.Functors.
Require Import Tealeaves.FunctorsTheory.
Require Import Tealeaves.Decorated.
Require Import Tealeaves.DecoratedTheory.
Require Import Tealeaves.Listable.
Require Import Tealeaves.ListableTheory.
Require Import Tealeaves.Syntax.

Import Functors.Notations.
Import Sets.Notations.
Import Quantifiable.Notations.
Import List.Notations.
Local Open Scope list_scope.
Local Open Scope tealeaves_scope.
Import Functors.Notations.
Local Open Scope tealeaves_scope.
Import Monoid.Notations.


(*
Section syntax_functor_module_composition.

  Context
    `{SyntaxFunctor W F}
    `{SyntaxModule W G T}.

  Instance SyntaxModule_compose : SyntaxModule (W:=W) (F ∘ G) (T := T).
  Proof.
    constructor; typeclasses eauto.
  Qed.

End syntax_functor_module_composition.
*)
