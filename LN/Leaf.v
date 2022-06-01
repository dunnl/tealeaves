From Tealeaves Require Import
     Util.Prelude Util.EqDec_eq
     LN.Atom.

#[local] Open Scope tealeaves_scope.

(** * Locally nameless leaves *)
(******************************************************************************)
Inductive leaf :=
| Fr : atom -> leaf
| Bd : nat -> leaf.

Theorem eq_dec_leaf : forall l1 l2 : leaf, {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
  - compare values a and a0; auto.
  - compare values n and n0; auto.
Qed.

Instance EqDec_leaf : EquivDec.EqDec leaf eq := eq_dec_leaf.

(** [compare_to_atom] is an induction principle for leaves that splits
      the <<Fr x>> case into subcases <<x = y>> and <<x <> y>> for
      some user-specified atom <<y>>. *)
Lemma compare_to_atom : forall x l (P : leaf -> Prop),
    P (Fr x) ->
    (forall a : atom, a <> x -> P (Fr a)) ->
    (forall n : nat, P (Bd n)) ->
    P l.
Proof.
  introv case1 case2 case3. destruct l.
  - destruct_eq_args x a. auto.
  - auto.
Qed.

Tactic Notation "compare" constr(l) "to" "atom" constr(x) :=
  (induction l using (compare_to_atom x)).
