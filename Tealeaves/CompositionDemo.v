From Tealeaves Require Import Tactics.Prelude.

Open Scope tealeaves_scope.

Set Printing Notations.

Notation "(- ◻ g )" := (precompose g) (only parsing).
Notation "( f ◻ -)" := (compose f) (only parsing).


Context (A B C X Y Z Q R S: Type).
Context (f: A -> B) (g: B -> C).

Check g ∘ f.



Check @compose A B C: (B -> C) -> (A -> B) -> A -> C.
Check (@compose X (A -> B) (A -> C)) ∘ (@compose A B C): (B -> C) -> (X -> A -> B) -> X -> A -> C.
Check (@compose X (A -> B) (A -> C)) ∘ (@compose A B C): (B -> C) -> (X -> A -> B) -> X -> A -> C.

Check
  (@compose A B C g): (A -> B) -> A -> C.

Check
  (@compose X (B -> C) ((A -> B) -> A -> C))
    (@compose A B C): (X -> B -> C) -> X -> (A -> B) -> A -> C.

Check
  (@compose X (A -> B) (A -> C) (@compose A B C g)): (X -> A -> B) -> X -> A -> C.


Context
  (C1: A -> B)
  (C2: A -> A -> B)
  (C3: A -> A -> A -> B).

Unset Printing Implicit.
Unset Printing Notations.

Check C1: A -> B.
Check g ∘ C1: A -> C.

Check C2: A -> A -> B.
Check (@compose A B C g) ∘ C2: A -> A -> C.

Check C3: A -> A -> A -> B.
Check (@compose A (A -> B) (A -> C) (@compose A B C g) ∘ C3: A -> A -> A -> C).


Section experiments1.

  Context
    (A': Type)
      (f1: A' -> A)
      (f2: A' -> A)
      (f3: A' -> A).

  Set Printing Notations.

  Goal (fun a => C1 (f1 a)) = (precompose f1 C1).
    reflexivity.
  Qed.

  Goal (fun a b => C2 (f1 a) (f2 b)) =
         (((- ◻ f2) ◻ -) ◻ -) (- ◻ f1) C2.
    reflexivity.
  Qed.

  Goal (fun a b => C2 (f1 a) (f2 b)) =
         (((- ◻ f2) ◻ -) ∘ (- ◻ f1)) C2.
    reflexivity.
  Qed.

  Goal (fun a b => C2 (f1 a) (f2 b)) =
         (compose ((- ◻ f2) ◻ -) (- ◻ f1)) C2.
    reflexivity.
  Qed.

End experiments1.



Section experiments2.

  Context
    (A A' B': Type)
      (C: A -> B) (g: A' -> A) (f: B -> B').

  Goal (f ∘ C ∘ g) =
         (compose f ∘ precompose g) C.
    reflexivity.
  Qed.

  Goal (f ∘ C ∘ g) =
         ((f ◻ -) ∘ (- ◻ g)) C.
    reflexivity.
  Qed.

  Goal (f ∘ (fun x => C (g x))) =
         (compose f ∘ precompose g) C.
    reflexivity.
  Qed.

  Goal (fun a b => C2 (f1 a) (f2 b)) =
         (((- ◻ f2) ◻ -) ◻ -) (- ◻ f1) C2.
    reflexivity.
  Qed.

  Goal (fun a b => C2 (f1 a) (f2 b)) =
         (((- ◻ f2) ◻ -) ∘ (- ◻ f1)) C2.
    reflexivity.
  Qed.

  Goal (fun a b => C2 (f1 a) (f2 b)) =
         (compose ((- ◻ f2) ◻ -) (- ◻ f1)) C2.
    reflexivity.
  Qed.

End experiments1.
