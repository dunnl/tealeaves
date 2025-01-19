From Tealeaves Require Import
  Classes.Categorical.Applicative.

Import Applicative.Notations.

(** * Cartesian product bifunctor *)
(******************************************************************************)

(** ** Bi-map operation *)
(******************************************************************************)
Definition map_pair {A B C D: Type} (f : A -> B) (g: C -> D) : A * C -> B * D :=
  map_snd g ∘ map_fst f.

(** ** Bi-traverse operation *)
(******************************************************************************)
Definition traverse_both
  {A B C D: Type}
  {G: Type -> Type}
  `{Map G} `{Mult G} `{Pure G}
  (f : A -> G B) (g: C -> G D) : A * C -> G (B * D) :=
  fun '(a, c) => pure pair <⋆> f a <⋆> g c.
