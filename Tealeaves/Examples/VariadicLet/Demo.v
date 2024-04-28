From Tealeaves Require
  Examples.VariadicLet.Terms
  Examples.VariadicLet.Instances.Simple
  Examples.VariadicLet.Instances.LetIn
  Examples.VariadicLet.Instances.LetRec.

Import Terms.

Variables (x y z : atom).

Definition term1: term LN :=
  letin [tvar (Fr x)] (tvar (Bd 0)).
Definition term2: term LN :=
  letin [tvar (Bd 0)] (tvar (Bd 0)).
Definition term3: term LN :=
  letin [tvar (Fr x); tvar (Bd 1)] (tvar (Bd 1)).
Definition term4: term LN :=
  letin [tvar (Bd 0); tvar (Bd 1) ; tvar (Bd 2)] (tvar (Bd 2)).
Definition term5: term LN :=
  letin [tvar (Bd 1) ; tvar (Bd 2) ; tvar (Bd 3)] (tvar (Bd 2)).

Module demo1.

  Import Simple.

  Goal LCnb 0 term1 = true. reflexivity. Qed.

  Goal LCnb 0 term2 = false. reflexivity. Qed.
  Goal LCnb 1 term2 = true. reflexivity. Qed.

  Goal LCnb 0 term3 = false. reflexivity. Qed.
  Goal LCnb 1 term3 = false. reflexivity. Qed.

  Goal LCnb 0 term5 = false. reflexivity. Qed.
  Goal LCnb 1 term5 = false. reflexivity. Qed.
  Goal LCnb 2 term5 = false. reflexivity. Qed.

  Example ex1: level term1 = 0 := ltac:(trivial).
  Example ex2: level term2 = 1 := ltac:(trivial).
  Example ex3: level term3 = 2 := ltac:(trivial).
  Example ex4: level term4 = 3 := ltac:(trivial).
  Example ex5: level term5 = 4 := ltac:(trivial).

End demo1.

Module demo2.

  Import LetIn.

  Example ex1: level term1 = 0 := ltac:(trivial).
  Example ex2: level term2 = 1 := ltac:(trivial).
  Example ex3: level term3 = 1 := ltac:(trivial).
  Example ex4: level term4 = 1 := ltac:(trivial).
  Example ex5: level term5 = 2 := ltac:(trivial).

End demo2.

Module demo3.

  Import LetRec.

  Goal LCnb 0 term1 = true. reflexivity. Qed.

  Goal LCnb 0 term2 = true. reflexivity. Qed.

  Goal LCnb 0 term3 = true. reflexivity. Qed.


  Example ex1: level term1 = 0 := ltac:(trivial).
  Example ex2: level term2 = 0 := ltac:(trivial).
  Example ex3: level term3 = 0 := ltac:(trivial).
  Example ex4: level term4 = 0 := ltac:(trivial).
  Example ex5: level term5 = 1 := ltac:(trivial).
End demo3.
