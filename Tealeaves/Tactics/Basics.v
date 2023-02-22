(*|
We use this operation to reason about traversable functors.
|*)

Definition exfalso {A : Type} : False -> A :=
  fun bot => match bot with end.

(** * Generally useful operations *)

(** General-purpose functions used throughout Tealeaves. *)
(******************************************************************************)

#[local] Generalizable All Variables.

Polymorphic Definition compose {A B C} (g : B -> C) (f : A -> B) : A -> C := fun a => g (f a).

Notation "g ∘ f" := (compose g f) (at level 40, left associativity).

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
