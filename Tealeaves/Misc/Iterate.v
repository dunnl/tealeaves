From Tealeaves Require Import Tactics.Prelude.

(* Iterate an endofunction <<n>> times *)
Fixpoint iterate (n : nat) {A : Type} (f : A -> A) :=
  match n with
  | 0 => @id A
  | S n' => iterate n' f ∘ f
  end.

Lemma iterate_rw0 : forall {A : Type} (f : A -> A),
    iterate 0 f = id.
Proof.
  reflexivity.
Qed.

Lemma iterate_rw1 : forall (n : nat) {A : Type} (f : A -> A),
    iterate (S n) f = (iterate n f) ∘ f.
Proof.
  intros.
  cbn.
  reflexivity.
Qed.

Lemma iterate_rw2 : forall (n : nat) {A : Type} (f : A -> A),
    iterate (S n) f = f ∘ (iterate n f).
Proof.
  intros.
  cbn.
  induction n.
  + reflexivity.
  + rewrite iterate_rw1.
    reassociate <- on right.
    rewrite <- IHn.
    reflexivity.
Qed.

Lemma iterate_rw0A : forall {A : Type} (f : A -> A) a,
    iterate 0 f a = a.
Proof.
  reflexivity.
Qed.

Lemma iterate_rw1A : forall (n : nat) {A : Type} (f : A -> A) a,
    iterate (S n) f a = (iterate n f) (f a).
Proof.
  reflexivity.
Qed.


Lemma iterate_rw2A : forall (n : nat) {A : Type} (f : A -> A) a,
    iterate (S n) f a = f (iterate n f a).
Proof.
  intros.
  compose near a on right.
  rewrite iterate_rw2.
  reflexivity.
Qed.
