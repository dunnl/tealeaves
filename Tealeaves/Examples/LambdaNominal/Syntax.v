(*|
############################################################
Formalizing STLC with Named Variables
############################################################

============================
Imports and setup
============================
|*)
From Tealeaves Require Export
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Kleisli.DecoratedTraversableMonad
  Functors.List.

Import Monoid.Notations.
Import List.ListNotations.

#[local] Generalizable Variables G.
#[local] Set Implicit Arguments.

Import Applicative.Notations.

(** * Language definition *)
(******************************************************************************)
Inductive term (b v : Type) :=
| tvar : v -> term b v
| lam : b -> term b v -> term b v
| app : term b v -> term b v -> term b v.

(** ** Notations and automation *)
(******************************************************************************)
Module Notations.
  Notation "'λ'" := (lam) (at level 45).
End Notations.

Import Notations.

#[export] Instance: forall b, Return (term b) := tvar.

(*|
========================================
Definition of binddt
========================================
|*)
Program Fixpoint binddt_term {b1 b2} (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (ρ : list b1 * b1 -> G b2) (f : list b1 * v1 -> G (term b2 v2)) (t : term b1 v1) : G (term b2 v2) :=
  match t with
  | tvar _ v => f (nil, v)
  | lam v body => pure (@lam b2 v2)  <⋆> ρ (nil, v) <⋆> binddt_term (preincr ρ [v]) (preincr f [v]) body
  | app t1 t2 => pure (@app b2 v2)
                <⋆> binddt_term ρ f t1
                <⋆> binddt_term ρ f t2
  end.
