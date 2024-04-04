From Tealeaves Require Export
  Axioms
  Tactics.LibTactics
  Tactics.Debug.

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

(** * General operations *)

(** General-purpose functions used throughout Tealeaves. *)
(******************************************************************************)

(** We use <<exfalso>> to reason about traversable functors. *)
Definition exfalso {A : Type} : False -> A :=
  fun bot => match bot with end.

#[local] Generalizable All Variables.

Polymorphic Definition compose {A B C} (g : B -> C) (f : A -> B) : A -> C := fun a => g (f a).

Notation "g ∘ f" := (compose g f) (at level 40, left associativity).

(** Helpful to avoid inserting a hidden <<compose>> between two
    functors that would later need to be unfolded. TODO Get rid of this. *)
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

Definition precompose {A B C} := (fun (f : A -> B) (g : B -> C)  => g ○ f).

Theorem commute_hom_action1 :
  forall (A B C D : Type) (f1 : A -> B) (f2 : B -> C) (f3 : C -> D),
    compose f3 (precompose f1 f2) = precompose f1 (compose f3 f2).
Proof.
  reflexivity.
Qed.

Theorem commute_hom_action2 :
  forall (A B C D : Type) (f1 : A -> B) (f3 : C -> D),
    compose f3 ∘ precompose f1 = precompose f1 ∘ compose f3.
Proof.
  reflexivity.
Qed.

(** * Tactics *)
(******************************************************************************)

(** ** Tactics for rewriting *)
(******************************************************************************)

(** *** Rewriting the left or right side of an equation *)
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

(** *** Re-association of an expression *)
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

(** *** Expressing functions as compositions *)
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

(** *** Rewriting with setoids *)
(******************************************************************************)
Tactic Notation "rewrites" uconstr(r1) :=
  setoid_rewrite r1.

Tactic Notation "rewrites" uconstr(r1) "," uconstr(r2) :=
  rewrites r1; rewrites r2.

Tactic Notation "rewrites" uconstr(r1) "," uconstr(r2) "," uconstr(r3):=
  rewrites r1; rewrites r2, r3.

Tactic Notation "rewrites" uconstr(r1) "," uconstr(r2) "," uconstr(r3) "," uconstr(r4) :=
  rewrites r1; rewrites r2, r3, r4.

(** ** Unfolding operational typeclasses *)
(******************************************************************************)
Ltac head_of expr :=
  match expr with
  | ?f ?x => head_of f
  | ?head => head
  | _ => fail
  end.

Ltac head_of_matches expr head :=
  match expr with
  | ?f ?x =>
    head_of_matches f head
  | head => idtac
  | _ => fail
  end.

Goal False.
  Fail head_of_matches 0 S. (* Tactic failure. *)
  head_of_matches (S 0) S. (* Success *)
  head_of_matches 5 S. (* Success *)
Abort.

(** Unfold operational typeclasses in the goal. *)
Ltac unfold_operational_tc inst :=
  repeat (match goal with
          | |- context[?op ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op maybe_inst) with maybe_inst
          | |- context[?op ?F ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F maybe_inst) with maybe_inst
          | |- context[?op ?F ?G ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G inst) with maybe_inst
          | |- context[?op ?F ?G ?H ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G H inst) with maybe_inst
          | |- context[?op ?F ?G ?H ?I ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G H I inst) with maybe_inst
          | |- context[?op ?F ?G ?H ?I ?J ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G H I J inst) with maybe_inst
          | |- context[?op ?F ?G ?H ?I ?J ?K ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G H I J K inst) with maybe_inst
          end); unfold inst.

(** Unfold operational typeclasses in hypotheses. *)
Ltac unfold_operational_tc_hyp :=
  repeat (match goal with
          | H : context[?op ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op maybe_inst) with maybe_inst in H
          | H :context[?op ?F ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F maybe_inst) with maybe_inst
          | H :context[?op ?F ?G ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G inst) with maybe_inst
          | H :context[?op ?F ?G ?H ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G H inst) with maybe_inst
          | H :context[?op ?F ?G ?H ?I ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G H I inst) with maybe_inst
          | H :context[?op ?F ?G ?H ?I ?J ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G H I J inst) with maybe_inst
          | H :context[?op ?F ?G ?H ?I ?J ?K ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G H I J K inst) with maybe_inst
          end); unfold inst.

Tactic Notation "unfold_ops" constr(inst) :=
  unfold_operational_tc inst.

Tactic Notation "unfold_ops" constr(inst) constr(inst1) :=
  unfold_ops inst; unfold_ops inst1.

Tactic Notation "unfold_ops" constr(inst) constr(inst1) constr(inst2) :=
  unfold_ops inst; unfold_ops inst1 inst2.

Tactic Notation "unfold_ops" constr(inst) "in" "*" :=
  unfold_operational_tc inst;
    unfold_operational_tc_hyp inst.

Tactic Notation "unfold_ops" constr(inst) constr(inst1) "in" "*" :=
  unfold_ops inst in *; unfold_ops inst1 in *.

Tactic Notation "unfold_ops" constr(inst) constr(inst1) constr(inst2) "in" "*" :=
  unfold_ops inst in *; unfold_ops inst1 in *; unfold_ops inst2 in *.

(** Unfold all operational typeclasses. This will unfold anything that
    looks like an operational typeclass. *)
(******************************************************************************)
Ltac unfold_all_transparent_tcs :=
  repeat (match goal with
          | |- context[?op ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op inst) with x
          | |- context[?op ?F ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F inst) with x
          | |- context[?op ?F ?G ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G inst) with x
          | |- context[?op ?F ?G ?H ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H inst) with x
          | |- context[?op ?F ?G ?H ?I ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I inst) with x
          | |- context[?op ?F ?G ?H ?I ?J ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I J inst) with x
          | |- context[?op ?F ?G ?H ?I ?J ?K ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I J K inst) with x
          end); cbn beta zeta.

Ltac unfold_all_transparent_tcs_hyp :=
  repeat (match goal with
          | H :context[?op ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op inst) with x
          | H :context[?op ?F ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F inst) with x
          | H :context[?op ?F ?G ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G inst) with x
          | H :context[?op ?F ?G ?H ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H inst) with x
          | H :context[?op ?F ?G ?H ?I ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I inst) with x
          | H :context[?op ?F ?G ?H ?I ?J ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I J inst) with x
          | H :context[?op ?F ?G ?H ?I ?J ?K ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I J K inst) with x
          end); cbn beta zeta.

Tactic Notation "unfold" "transparent" "tcs" :=
  unfold_all_transparent_tcs.

Tactic Notation "unfold" "transparent" "tcs" "in" "*" :=
  unfold_all_transparent_tcs; unfold_all_transparent_tcs_hyp.

(** ** Support for comparing natural numbers *)
(******************************************************************************)
From Coq.Arith Require Import
     PeanoNat Compare_dec.

(** This gives access to the [lia] tactic *)
Require Export Psatz.

(** This lemma reduces a goal to three subgoals based on the possible ordering
    between two natural numbers. Each branch may invoke two hypothesis, one
    stipulating the ordering and the other stipulating an equation for
    [Nat.compare]. *)
Lemma comparison_naturals : forall (n m : nat) (p : Prop),
    (n ?= m = Lt -> n < m -> p) ->
    (n ?= m = Eq -> n = m -> p) ->
    (n ?= m = Gt -> n > m -> p) ->
    p.
Proof.
  intros n m ? ?lt ?eq ?gt.
  destruct (lt_eq_lt_dec n m) as [[? | ?] |];
    rewrite ?Nat.compare_eq_iff,
    ?Nat.compare_lt_iff, ?Nat.compare_gt_iff in *;
    auto.
Qed.

(** Compare natural numbers with [comparison_naturals], the try rewriting
    occurrences in [Nat.compare] and other basic tactics.*)
Ltac compare_nats_args n k :=
  apply (@comparison_naturals n k);
  (let ineq := fresh "ineq"
    with ineqp := fresh "ineqp"
    with ineqrw := fresh "ineqrw" in
    intros ineqrw ineqp;
    repeat rewrite ineqrw in *;
    (* In the n = k case, substitute the equality *)
    try match type of ineqp with
        | ?x = ?y => subst
        end; try lia; repeat f_equal; try lia; try reflexivity).

Tactic Notation "compare" "naturals" constr(n) "and" constr(m) :=
  compare_nats_args n m.

(** ** General tactics *)
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
