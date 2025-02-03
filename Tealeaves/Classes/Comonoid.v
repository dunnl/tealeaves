(*|
This files defines typeclasses for comonoids_ in the category of Coq types and functions

.. _comonoids: https://ncatlab.org/nlab/show/comonoid

Just like in the category of sets, where

  Every set can be made into a comonoid in Set (with the cartesian product) in a unique way.

comonoids in Coq's category are not particularly varied: there is one comonoid on each type.
|*)
From Tealeaves Require Import
  Prelude
  Misc.Product.

#[local] Generalizable Variables a.

(** * Comonoids *)
(**********************************************************************)

(** ** Operational Typeclasses *)
(**********************************************************************)

Class Comonoid_Counit A := comonoid_counit: A -> unit.

Class Comonoid_Comult A := comonoid_comult: A -> A * A.

Arguments comonoid_comult {A}%type_scope {Comonoid_Comult}.

Arguments comonoid_counit A%type_scope {Comonoid_Counit}.

(** ** Typeclass *)
(**********************************************************************)
Class Comonoid (A: Type)
  `{Comonoid_Comult A}
  `{Comonoid_Counit A} :=
  { comonoid_assoc:
    `(associator (map_fst comonoid_comult (comonoid_comult a)) =
        map_snd comonoid_comult (comonoid_comult a));
    comonoid_id_l:
    `(fst (comonoid_comult a) = a);
    comonoid_id_r:
    `(snd (comonoid_comult a) = a);
  }.

(** * The "Duplicate" Comonoid *)
(**********************************************************************)

(** Everything is a [Comonoid]. In fact, the copy comonoid is the only
    one, and the comonoid laws are proved by reflexivity. *)
Definition dup {A: Type} := fun a: A => (a, a).

#[export] Instance Comonoid_Counit_dup A:
  Comonoid_Counit A := fun _ => tt.

#[export] Instance Comonoid_Comult_dup A:
  Comonoid_Comult A := @dup A.

#[export, program] Instance Comonoid_dup {A}:
  @Comonoid A (Comonoid_Comult_dup A)
    (Comonoid_Counit_dup A).
