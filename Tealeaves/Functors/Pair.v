From Tealeaves Require Import
  Classes.Categorical.Applicative.

Import Applicative.Notations.

(** * Cartesian product bifunctor *)
(******************************************************************************)

(** ** Bi-map operation *)
(******************************************************************************)
Definition map_pair {A B C D: Type} (f : A -> B) (g: C -> D) : A * C -> B * D :=
  map_snd g ∘ map_fst f.

Lemma map_fst_to_pair {A1 A2 B}:
  forall (f: A1 -> A2),
    map_fst (Y := B) f = map_pair f id.
Proof.
  intros.
  ext [a b].
  reflexivity.
Qed.

Lemma map_snd_to_pair {A B1 B2}:
  forall (g: B1 -> B2),
    map_snd (X := A) g = map_pair id g.
Proof.
  intros.
  ext [a b].
  reflexivity.
Qed.


(** ** Bi-traverse operation *)
(******************************************************************************)
Definition traverse_both
  {A B C D: Type}
  {G: Type -> Type}
  `{Map G} `{Mult G} `{Pure G}
  (f : A -> G B) (g: C -> G D) : A * C -> G (B * D) :=
  fun '(a, c) => pure pair <⋆> f a <⋆> g c.
