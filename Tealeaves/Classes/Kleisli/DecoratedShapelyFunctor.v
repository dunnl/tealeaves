From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Categorical.ShapelyFunctor
  Functors.Ctxset
  Functors.Environment.

Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.

(** * CtxTolist operation *)
(******************************************************************************)
Class CtxTolist (E : Type) (F : Type -> Type) :=
  ctx_tolist : forall A : Type, F A -> env E A.

#[global] Arguments ctx_tolist {E}%type_scope {F}%function_scope
      {CtxTolist} {A}%type_scope _.

(*
(** * Shapely functors are containers *)
(******************************************************************************)
#[export] Instance Elementsd_Tolistd (E : Type) (F : Type -> Type)
  `{Tolistd E F} : CtxElements E F :=
  fun A => element_of ∘ tolistd.

Theorem ind_iff_ind_list (E : Type) (F : Type -> Type)
  `{Tolistd E F} : forall (A : Type) (t : F A) (e : E) (a : A),
    (e, a) ∈d t <-> (e, a) ∈d tolistd t.
PrAoof.
  reflexivity.
Qed.
*)
