From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Functors.List_Telescoping_General
  Functors.Z2.

Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedTraversableMonad.Notations.

(** * Polymorphically decorated traversable functors *)
(******************************************************************************)

(** ** Mapdt Poly operation *)
(******************************************************************************)
Class MapdtPoly (T: Type -> Type -> Type) :=
    mapdtp:
      forall (A1 A2 B1 B2: Type)
        (G : Type -> Type)
        `{Gmap: Map G} `{Gpure: Pure G} `{Gmult: Mult G},
        (list B1 * B1 -> G B2) ->
        (list B1 * A1 -> G A2) ->
        T B1 A1 ->
        G (T B2 A2).

Arguments mapdtp {T}%function_scope {MapdtPoly} {A1 A2 B1 B2}%type_scope
  {G}%function_scope {Gmap Gpure Gmult} (_ _)%function_scope _.
