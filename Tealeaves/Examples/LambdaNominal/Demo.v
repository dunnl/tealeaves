
Require Import Coq.Arith.Wf_nat.

Definition nat_lt (x y : nat) := x < y.

Lemma nat_lt_wf : well_founded nat_lt.
Proof.
  unfold well_founded.
  intros n.
  induction n as [|n' IH].
  - (* Base case: 0 is accessible because there are no smaller numbers *)
    constructor. intros y Hy. inversion Hy.
  - (* Inductive step: every smaller number is accessible *)
    constructor. intros y Hy.
    apply IH.
    unfold nat_lt in *.
    admit.
Admitted.

Lemma lt_succ_diag_r : forall n, n < S n.
Proof.
  intros. auto.
Qed.


About Acc.
Print Acc.
Fixpoint fact (n : nat) (Hn : Acc nat_lt n) : nat :=
  match n as n' return (Acc nat_lt n' -> nat) with
  | 0 => fun _ => 1
  | S n' => fun Hn =>
      let Hn' := match Hn with Acc_intro _ Hacc => Hacc n' (lt_succ_diag_r n') end in
      (S n') * fact n' Hn'
  end Hn.
