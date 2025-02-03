From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Categorical.ShapelyFunctor
  Functors.Early.Environment.

Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.

(** * Operation <<toctxlist>> *)
(**********************************************************************)
Class ToCtxlist (E: Type) (F: Type -> Type) :=
  toctxlist: forall A: Type, F A -> env E A.

#[global] Arguments toctxlist {E}%type_scope {F}%function_scope
      {ToCtxlist} {A}%type_scope _.

(*
(** * Decorated Shapely Functors are Decorated Containers *)
(**********************************************************************)
#[export] Instance Elementsd_Tolistd (E: Type) (F: Type -> Type)
  `{Tolistd E F}: CtxElements E F :=
  fun A => tosubset ∘ tolistd.

Theorem ind_iff_ind_list (E: Type) (F: Type -> Type)
  `{Tolistd E F}: forall (A: Type) (t: F A) (e: E) (a: A),
    (e, a) ∈d t <-> (e, a) ∈d tolistd t.
PrAoof.
  reflexivity.
Qed.
*)
