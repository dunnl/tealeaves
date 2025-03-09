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
  Notation "⟨ t ⟩ ( u )" := (tap t u) (at level 80, t at level 40, u at level 40).
End Notations.

Declare Scope lambda_scope.
Delimit Scope lambda_scope with lam.

(* Notation for variables *)
Notation "'`' x" := (@tvar atom atom x) (at level 1, format "'`' x") : lambda_scope.

(* Notation for lambda abstraction *)
Notation "'λ' x , t" := (@lam atom atom x t)
  (at level 100, right associativity, format "'λ' x ,  t") : lambda_scope.

(* Notation for application *)
Notation "t1 · t2" := (@tap atom atom t1 t2)
  (at level 50, left associativity, format "t1 · t2") : lambda_scope.

Open Scope lambda_scope.
