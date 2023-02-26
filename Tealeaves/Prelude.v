From Tealeaves Require Export
  Axioms
  Basics.
From Tealeaves.Tactics Require Export
  Rewriting
  Unfolding
  LibTactics
  CompareNats.

(*|
Declare a scope for Tealeaves' notations.
|*)

Declare Scope tealeaves_scope.
Delimit Scope tealeaves_scope with tea.
#[global] Open Scope tealeaves_scope.

(*|
Open <<type_scope>> globally because (\*\) should mean [prod]
|*)

#[global] Open Scope type_scope.
