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
  letin [tvar (Bd 0)] (tvar (Fr y)).
Definition term3: term LN :=
  letin [tvar (Fr x); tvar (Bd 0)] (tvar (Fr y)).
Definition term3a: term LN :=
    letin [tvar (Fr x); tvar (Bd 0); tvar (Bd 1)] (tvar (Fr y)).
Definition term4: term LN :=
  letin [tvar (Bd 1) ; tvar (Bd 0)] (tvar (Fr y)).

Module demo1.

  Import Simple.

  Notation "'LC'" :=
    (LCnb
       (Mapdt_U_inst:=Mapdt_term)) (at level 10).
  Notation "'GAP'" :=
    (local_closure_gap
       (Mapdt_U_inst:=Mapdt_term)) (at level 10).

  Goal LC 0 term1 = true. reflexivity. Qed.

  Goal LC 0 term2 = false. reflexivity. Qed.
  Goal LC 1 term2 = true. reflexivity. Qed.

  Goal LC 0 term3 = false. reflexivity. Qed.
  Goal LC 1 term3 = true. reflexivity. Qed.
  Goal LC 1 term3a = false. reflexivity. Qed.

  Goal LC 0 term4 = false. reflexivity. Qed.
  Goal LC 1 term4 = false. reflexivity. Qed.
  Goal LC 2 term4 = true. reflexivity. Qed.

  Example ex1: GAP term1 = 0 := ltac:(trivial).
  Example ex2: GAP term2 = 1 := ltac:(trivial).
  Example ex3: GAP term3 = 1 := ltac:(trivial).
  Example ex3a: GAP term3a = 2 := ltac:(trivial).
  Example ex4: GAP term4 = 2 := ltac:(trivial).

End demo1.

Module demo2.

  Import ex_binding_type2.

  Notation "'LC'" :=
    (locally_closed_gap_bool
       (Mapdt_U_inst:=Mapdt_term)) (at level 10).
  Notation "'GAP'" :=
    (local_closure_gap
       (Mapdt_U_inst:=Mapdt_term)) (at level 10).

  Goal LC 0 term1 = true. reflexivity. Qed.

  Goal LC 0 term2 = false. reflexivity. Qed.
  Goal LC 1 term2 = true. reflexivity. Qed.

  Goal LC 0 term3 = true. reflexivity. Qed.
  Goal LC 0 term3a = true. reflexivity. Qed.

  Goal LC 0 term4 = false. reflexivity. Qed.
  Goal LC 1 term4 = false. reflexivity. Qed.
  Goal LC 2 term4 = true. reflexivity. Qed.

  Example ex1: GAP term1 = 0 := ltac:(trivial).
  Example ex2: GAP term2 = 1 := ltac:(trivial).
  Example ex3: GAP term3 = 0 := ltac:(trivial).
  Example ex3a: GAP term3a = 0 := ltac:(trivial).
  Example ex4: GAP term4 = 2 := ltac:(trivial).

End demo2.

Module demo3.

  Import ex_binding_type3.
  Notation "'LC'" :=
    (locally_closed_gap_bool
       (Mapdt_U_inst:=Mapdt_term)) (at level 10).
  Notation "'GAP'" :=
    (local_closure_gap
       (Mapdt_U_inst:=Mapdt_term)) (at level 10).

  Goal LC 0 term1 = true. reflexivity. Qed.

  Goal LC 0 term2 = true. reflexivity. Qed.

  Goal LC 0 term3 = true. reflexivity. Qed.

  Goal LC 0 term4 = true. reflexivity. Qed.

  Example ex1: GAP term1 = 0 := ltac:(trivial).
  Example ex2: GAP term2 = 0 := ltac:(trivial).
  Example ex3: GAP term3 = 0 := ltac:(trivial).
  Example ex3a: GAP term3a = 0 := ltac:(trivial).
  Example ex4: GAP term4 = 0 := ltac:(trivial).

End demo3.
