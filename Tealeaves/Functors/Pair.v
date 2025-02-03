From Tealeaves Require Import
  Classes.Categorical.Applicative.

Import Applicative.Notations.

(** * Cartesian Product Bifunctor *)
(**********************************************************************)

(** ** Bi-map Operation *)
(**********************************************************************)
Section map_pair.

  Definition map_pair
    {A B C D: Type}
    (f: A -> B)
    (g: C -> D):
    A * C -> B * D :=
    map_snd g ∘ map_fst f.

  (** *** Rewriting Laws *)
  (**********************************************************************)
  Lemma map_pair_rw
    {A B C D: Type}
    {f: A -> B}
    {g: C -> D}:
    forall (a: A) (c: C),
      map_pair f g (a, c) = (f a, g c).
  Proof.
    reflexivity.
  Qed.

  (** *** Lifting <<map>> to <<map_pair>> *)
  (**********************************************************************)
  Lemma map_fst_to_pair
    {A B C: Type} {f: A -> B}:
    map_fst (Y := C) f = map_pair f id.
  Proof.
    intros.
    ext [a c].
    reflexivity.
  Qed.

  Lemma map_snd_to_pair
    {A C D: Type} {g: C -> D}:
    map_snd (X := A) g = map_pair id g.
  Proof.
    intros.
    ext [a c].
    reflexivity.
  Qed.

End map_pair.

(** ** Bi-traverse Operation *)
(**********************************************************************)
Section traverse_pair.

  Context
    {G: Type -> Type}
    `{Map G} `{Mult G} `{Pure G}.

  Context
    {A B C D: Type}

    (f: A -> G B) (g: C -> G D).

  Definition traverse_pair: A * C -> G (B * D) :=
    fun '(a, c) => pure pair <⋆> f a <⋆> g c.

  Lemma traverse_pair_rw:
    forall (a: A) (c: C),
      traverse_pair (a, c) =
        pure pair <⋆> f a <⋆> g c.
  Proof.
    reflexivity.
  Qed.

End traverse_pair.
