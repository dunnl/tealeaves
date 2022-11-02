(*|
#######################
Tealeaves.Util.Prelude
#######################

contains
  Various imports, definitions, and tactics that
  are generally useful for Tealeaves developlment.

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

(*|
Import helper tactics and decidable equality.
|*)

From Tealeaves.Util Require Export
  LibTactics
  EqDec_eq
  CompareNats
  Unfold.

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

(** * Generally useful operations *)

(** General-purpose functions used throughout Tealeaves. *)
(******************************************************************************)

#[local] Generalizable All Variables.

Polymorphic Definition compose {A B C} (g : B -> C) (f : A -> B) : A -> C := fun a => g (f a).

Notation "g ∘ f" := (compose g f) (at level 40, left associativity).

Notation "F ○ G" := (fun X => F (G X)) (at level 40, left associativity).

Lemma compose_assoc `{f : C -> D} `{g : B -> C} `{h : A -> B} :
  f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof.
  reflexivity.
Qed.

Definition const {A B : Type} (b : B) : A -> B := fun _ => b.

Definition evalAt `(a : A) `(f : A -> B) := f a.

Definition strength_arrow `(p : A * (B -> C)) : B -> A * C := fun b => (fst p, snd p b).

Definition costrength_arrow `(p : (A -> B) * C) : A -> B * C := fun a => (fst p a, snd p).

Definition pair_right {A B} : B -> A -> A * B := fun b a => (a, b).

(*|
We use this operation to reason about traversable functors.
|*)

Definition exfalso {A : Type} : False -> A :=
  fun bot => match bot with end.

(** * Some useful automation *)
(******************************************************************************)

(** ** Support for rewriting the left/right side of equations *)
(******************************************************************************)
Ltac get_lhs :=
  match goal with
  | |- ?R ?f ?g =>
    constr:(f)
  end.

Ltac get_rhs :=
  match goal with
  | |- ?R ?f ?g =>
    constr:(g)
  end.

Ltac change_left new :=
  match goal with
  | |- ?R ?f ?g =>
    change (R new g)
  end.

Ltac change_right new :=
  match goal with
  | |- ?R ?f ?g =>
    change (R f new)
  end.

Tactic Notation "change" "left" constr(new) := change_left new.
Tactic Notation "change" "right" constr(new) := change_right new.

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

(** ** Support for re-association of expressions *)
(******************************************************************************)
Tactic Notation "reassociate" "<-" := rewrite compose_assoc.
Tactic Notation "reassociate" "<-" "in" ident(h) := rewrite compose_assoc in h.
Tactic Notation "reassociate" "->" := rewrite <- compose_assoc.
Tactic Notation "reassociate" "->" "in" ident(h):= rewrite <- compose_assoc in h.

Ltac guard_left x :=
  let lhs := get_lhs in pose (x := lhs); change_left x.

Ltac guard_right x :=
  let rhs := get_rhs in pose (x := rhs); change_right x.

Ltac reassociate_left_on_right :=
  let x := fresh "guard" in
  guard_left x; reassociate <-; subst x.

Ltac reassociate_right_on_right :=
  let x := fresh "guard" in
  guard_left x; reassociate ->; subst x.

Ltac reassociate_left_on_left :=
  let x := fresh "guard" in
  guard_right x; reassociate <-; subst x.

Ltac reassociate_right_on_left :=
  let x := fresh "guard" in
  guard_right x; reassociate ->; subst x.

Tactic Notation "reassociate" "<-" "on" "left" := reassociate_left_on_left.
Tactic Notation "reassociate" "->" "on" "left" := reassociate_right_on_left.
Tactic Notation "reassociate" "<-" "on" "right" := reassociate_left_on_right.
Tactic Notation "reassociate" "->" "on" "right" := reassociate_right_on_right.

(** We wrap <<reassociate_xxx_near>> with <<progress>> to detect situations in
    which the <<change>> simply fails to match (and thus has no effect), which
    in practice indicates a user mistake. *)
Ltac reassociate_right_near f3 :=
  progress (change (?f1 ∘ ?f2 ∘ f3) with (f1 ∘ (f2 ∘ f3))).

Ltac reassociate_left_near f1 :=
  progress (change (f1 ∘ (?f2 ∘ ?f3)) with (f1 ∘ f2 ∘ f3)).

Tactic Notation "reassociate" "->" "near" uconstr(f3) := reassociate_right_near f3.
Tactic Notation "reassociate" "<-" "near" uconstr(f1) := reassociate_left_near f1.

(** ** Support for rewriting functions as compositions *)
(******************************************************************************)
Ltac compose_near arg :=
  progress (change (?f (?g arg)) with ((f ∘ g) arg)).

Ltac compose_near_on_left arg :=
  let x := fresh "guard" in
  guard_right x; compose_near arg; subst x.

Ltac compose_near_on_right arg :=
  let x := fresh "guard" in
  guard_left x; compose_near arg; subst x.

Tactic Notation "compose" "near" constr(arg) := compose_near arg.
Tactic Notation "compose" "near" constr(arg) "on" "left" := compose_near_on_left arg.
Tactic Notation "compose" "near" constr(arg) "on" "right" := compose_near_on_right arg.

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

(** ** Support for rewriting with setoids *)
(******************************************************************************)
Tactic Notation "rewrites" uconstr(r1) :=
  setoid_rewrite r1.

Tactic Notation "rewrites" uconstr(r1) "," uconstr(r2) :=
  rewrites r1; rewrites r2.

Tactic Notation "rewrites" uconstr(r1) "," uconstr(r2) "," uconstr(r3):=
  rewrites r1; rewrites r2, r3.

Tactic Notation "rewrites" uconstr(r1) "," uconstr(r2) "," uconstr(r3) "," uconstr(r4) :=
  rewrites r1; rewrites r2, r3, r4.

(** ** General logical reasoning suport *)
(******************************************************************************)
Ltac invert_pair_eq :=
  match goal with
  | H : (?x, ?y) = (?z, ?w) |- _ =>
    inverts H
  end.

Ltac injection_all :=
  repeat match goal with
         | H : ?f = ?g |- _ =>
           injection H; intros; clear H
         end.

Ltac destruct_all_existentials :=
  repeat match goal with
         | H : exists (x : ?A), ?P |- _ =>
           let x := fresh "x" in
           let H' := fresh "H" in
           destruct H as [x H']
         end.

Ltac destruct_all_pairs :=
  repeat match goal with
         | H : ?P1 /\ ?P2 |- _ =>
           destruct H
         | H : prod ?A ?B |- _ =>
           destruct H
         end.

Ltac preprocess :=
  repeat (destruct_all_pairs +
          destruct_all_existentials +
          injection_all + subst).

Tactic Notation "pp" tactic(tac) :=
  preprocess; tac.
