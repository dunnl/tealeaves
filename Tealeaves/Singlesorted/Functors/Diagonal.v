From Tealeaves Require Export
     Singlesorted.Classes.Applicative.

(** * Diagonal (duplication) applicative functor *)
(******************************************************************************)
Definition dup (A : Type) : Type := A * A.

Instance Fmap_dup : Fmap dup :=
  fun A B f => map_both f : A * A -> B * B.

Program Instance End_dup : Functor dup.

Solve All Obligations with
    (intros; now ext [?]).

Instance Pure_dup : Pure dup :=
  fun A a => (a, a).

Instance Mult_dup : Mult dup :=
  fun A B (x : dup A * dup B) => ((fst (fst x), fst (snd x)), (snd (fst x), snd (snd x))).

Program Instance Applicative_dup : Applicative dup.

Solve Obligations with
    (unfold dup; intros; now destruct_all_pairs).
