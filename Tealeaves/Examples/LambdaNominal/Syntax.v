(*|
############################################################
Formalizing STLC with Named Variables
############################################################

============================
Exports and setup
============================
|*)

From Tealeaves.Classes Require Export
  Functor2
  Categorical.ApplicativeCommutativeIdempotent
  Categorical.TraversableFunctor2
  Categorical.DecoratedFunctorPoly
  Categorical.DecoratedTraversableMonadPoly.
  (* Kleisli.DecoratedTraversableCommIdemFunctor
     Kleisli.DecoratedTraversableMonadPoly.
   *)

From Tealeaves.Functors Require Export
  List Z2 Pair.

From Tealeaves.Backends Require Export
  Common.Names.

Export Product.Notations.
Export Monoid.Notations.
Export List.ListNotations.
Export DecoratedTraversableCommIdemFunctor.Notations.

#[local] Generalizable Variables G ϕ.
#[local] Set Implicit Arguments.

Export Applicative.Notations.

(** * Language definition *)
(******************************************************************************)
Inductive term (B V: Type) :=
| tvar: V -> term B V
| lam: B -> term B V -> term B V
| tap: term B V -> term B V -> term B V.

#[global] Arguments tvar {B}%type_scope {V}%type_scope _.

#[export] Instance Return_lambda_term: forall B, Return (term B) :=
  @tvar.

(** ** Notations and automation *)
(******************************************************************************)
Module Notations.
  Notation "'λ'" := (lam) (at level 45).
End Notations.

Export Notations.

(*
Parameters (x y z: atom).

Example term1: term atom atom := lam x (tap (lam y (tvar z)) (tvar x)).
*)
