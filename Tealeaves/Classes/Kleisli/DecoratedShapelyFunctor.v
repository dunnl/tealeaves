From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Categorical.ShapelyFunctor
  Functors.Early.Environment.

Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.


Class TolistCtx (F : Type -> Type) (W : Type) :=
  tolist_ctx : forall (A : Type), F A -> list (W * A).

#[global] Arguments tolist_ctx {F}%function_scope {W} {TolistCtx} {A}%type_scope _.

(** * ToCtxlist operation *)
(******************************************************************************)
Class ToCtxlist (E : Type) (F : Type -> Type) :=
  toctxlist : forall A : Type, F A -> env E A.

#[global] Arguments toctxlist {E}%type_scope {F}%function_scope
      {ToCtxlist} {A}%type_scope _.

(*
(** * Shapely functors are containers *)
(******************************************************************************)
#[export] Instance Elementsd_Tolistd (E : Type) (F : Type -> Type)
  `{Tolistd E F} : CtxElements E F :=
  fun A => tosubset ∘ tolistd.

Theorem ind_iff_ind_list (E : Type) (F : Type -> Type)
  `{Tolistd E F} : forall (A : Type) (t : F A) (e : E) (a : A),
    (e, a) ∈d t <-> (e, a) ∈d tolistd t.
PrAoof.
  reflexivity.
Qed.
*)
