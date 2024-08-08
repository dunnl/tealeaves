From Tealeaves Require Export
  Tactics.Debug.

Ltac assert_identical :=
    match goal with
    | |- ?x = ?x =>
        ltac_trace "Both sides identical:";
        print_goal
    | |- ?x <-> ?x =>
        ltac_trace "Both sides identical:";
        print_goal
    | |- _ =>
        ltac_trace "LHS and RHS not syntactically identical:";
        print_goal;
        fail
    end.

Ltac assert_different :=
  assert_fails (idtac; assert_identical).
(* idtac
 prevents Ltac from evaluating assert_identical right here *)

Ltac conclude := now assert_identical.
Ltac fixme := now assert_different. (* tests which ideally wouldn't fail *)
Ltac reject := now assert_different. (* tests which should fail *)
