From Coq.Arith Require Import
     PeanoNat Compare_dec.

(** This gives access to the [lia] tactic *)
Require Export Psatz.


(** * Support for comparing natural numbers *)
(******************************************************************************)
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
