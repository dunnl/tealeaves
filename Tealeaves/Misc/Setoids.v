Require Import Tealeaves.Tactics.Prelude.
Require Export Coq.Classes.Morphisms.
Export Relation_Definitions.

#[local] Open Scope signature_scope.
#[local] Generalizable Variables A B C f g.

Class Eq A :=
  equal: Relation_Definitions.relation A.

Arguments equal A%type_scope {Eq}.

Infix "==" := (equal _) (at level 70, no associativity).

Class Equiv A {Ae: Eq A}: Prop :=
  equiv_equivalence :> Equivalence (@equal A Ae).

Section setoid_morphisms.

  Context
    {A B: Type}
    {Ae: Eq A}
    {Be: Eq B}.

  Class Setoid_Morphism (f: A -> B): Prop :=
    { sm_a :> Equiv A;
      sm_b :> Equiv B;
      sm_proper :> Proper (equal A ==> equal B) f }.

End setoid_morphisms.

(** Identity and composition of setoid morphisms. *)
#[local] Instance id_morphism `{Equiv A}:
  Setoid_Morphism (@id A) := ltac:(firstorder).

Section setoid_morphism_composition.

  Context
    `{Equiv A}
    `{Equiv B}
    `{Equiv C}
    `{! Setoid_Morphism (f: A -> B)}
    `{! Setoid_Morphism (g: B -> C)}.

  #[global] Instance setoid_morphism_composition : Setoid_Morphism (g ∘ f).
  Proof.
    constructor; auto. unfold compose. intros ? ? eq. now rewrite eq.
  Defined.

End setoid_morphism_composition.

(** This is the same thing as [Coq.Classes.Morphisms.respectful] but using [Eq] rather than [relation]. *)
Instance Eq_function {A B} `{Ea: Eq A} `{Eb: Eq B}: Eq (A -> B) :=
  equal A ==> equal B.
(* fun (f g : A -> B) => forall (a1 a2 : A), a1 == a2 -> f a1 == g a2.) *)

#[local] Instance Equiv_function {A B} `{Equiv A} `{Equiv B}:
  Coq.Classes.RelationClasses.PER Eq_function.
Proof.
  constructor.
  intros f1 f2 feq a1 a2 aeq. symmetry. apply feq. now symmetry.
  intros f g h hyp1 hyp2 a1 a2 aeq.
  transitivity (g a2). 2: apply hyp2; reflexivity.
  now apply hyp1.
Qed.

Instance: Eq Prop := iff.

Instance: Equiv Prop := iff_equivalence.

Instance Eq_product `{Eq A} `{Eq B} : Eq (A * B) :=
  fun '(a1, b1) '(a2, b2) => a1 == a2 /\ b1 == b2.

Instance Equiv_product `{Equiv A} `{Equiv B} : Equiv (A * B).
Proof.
  intros. constructor.
  - intros [a b]. now split.
  - intros [a b] [a' b'] e. cbn in e. now split.
  - intros [a1 b1] [a2 b2] [a3 b3] [ea eb] [ea' eb'].
    split. transitivity a2; auto. transitivity b2; auto.
Qed.

Instance Proper_product `{Eq A} `{Eq B} : Proper (equal A ==> equal B ==> equal (A * B)) pair
  := ltac:(cbv; auto).

Section coq_equality.

  Instance eq_coq_eq A : Eq A := @eq A.

  Instance equiv_coq_eq A : Equiv A := ltac:(cbv; typeclasses eauto).

End coq_equality.

Section basic.

  Context
    `{Equiv A} `{Equiv B}.

  Lemma respectful_reflexive : reflexive _ (equal A ==> equal B).
    (* This is not generally true! Obviously, since it claims all functions are respectful. *)
    intros f a1 a2 aeq.
  Abort.

  Lemma respectful_symmetric : symmetric _ (equal A ==> equal B).
  Proof.
    intros f1 f2 feq a1 a2 aeq. symmetry. apply feq. now symmetry.
  Qed.

  Lemma respectful_transitive : transitive _ (equal A ==> equal B).
  Proof.
    intros f g h hyp1 hyp2 a1 a2 aeq.
    transitivity (g a2). 2: apply hyp2; reflexivity.
    now apply hyp1.
  Qed.

  (** A fancier re-statement of the preceding *)
  #[global] Instance:
    Coq.Classes.RelationClasses.PER (equal A ==> equal B) := ltac:(firstorder).

  Lemma bisimilarity_self_similar :
    (equal A ==> equal B) == (equal A ==> equal B).
  Proof.
    intros f1 f2 feq g1 g2 geq. split.
    - intros. transitivity f1.
      now symmetry. now transitivity g1.
    - intros. transitivity g2.
      now transitivity f2. now symmetry.
  Defined.

  Instance hey2: Proper (equal (A -> B) ==> equal (A -> B) ==> equal Prop) (equal A ==> equal B).
  Proof. repeat intro; apply bisimilarity_self_similar; auto.
  Defined.

  Instance hey3: Proper (equal (A -> B) ==> equal ((A -> B) -> Prop)) (equal A ==> equal B).
  Proof. repeat intro; apply bisimilarity_self_similar; auto.
  Defined.

  Instance hey4: Proper ((equal A ==> equal B) ==> (equal A ==> equal B) ==> equal Prop) (equal A ==> equal B).
  Proof. repeat intro; apply bisimilarity_self_similar; auto.
  Defined.

End basic.


Lemma bisimilarity_self_similar2 `{Equiv A} `{Equiv B} :
  (equal A ==> equal B) == (equal A ==> equal B).
Proof.
  intros f1 f2 feq g1 g2 geq.
  rewrite geq.
  Fail rewrite feq.
Abort.

(*
Instance relational_respectful `{Eq A} : Eq (relation A) := ltac:(apply Eq_function).
*)

(** Can this be made to work? *)
(*
Instance Equiv_function {A B} `{Equiv A} `{Equiv B} : Equiv (A -> B).
Proof.
  constructor; try (cbv in *; firstorder).
Abort.
*)

Section Proper_is_Proper.

  Context
    `{Eq A}.

  Instance Proper_is_Proper'' : Proper (equal _) (Proper (A := A)).
  Proof.
    intros r1 r2 req. unfold equal, Eq_function in req.
    intros a1 a2 aeq. specialize (req _ _ aeq). cbv; split; intro.
    - specialize (req _ _ aeq). apply req. auto.
    - specialize (req _ _ aeq). apply req. auto.
  Qed.

  Instance Proper_is_Proper : Proper (equal (relation A) ==> equal A ==> equal Prop) (Proper (A := A))
    := Proper_is_Proper''.

  Instance Proper_is_Proper' : Proper (equal (relation A) ==> equal (A -> Prop)) (Proper (A := A))
    := Proper_is_Proper''.

End Proper_is_Proper.
