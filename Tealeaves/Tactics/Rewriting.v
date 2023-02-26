From Tealeaves Require Import
  Basics.

(*|
Import helper tactics and decidable equality.
|*)

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
    inversion H
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
