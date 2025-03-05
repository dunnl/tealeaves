From Tealeaves Require Import
  Classes.Categorical.Applicative.

(** ** Traverse Poly operation *)
(******************************************************************************)
Class TraversePoly (T: Type -> Type -> Type) :=
  traversep:
      forall (A1 A2 B1 B2: Type)
        (G : Type -> Type)
        `{Gmap: Map G} `{Gpure: Pure G} `{Gmult: Mult G},
        (B1 -> G B2) ->
        (A1 -> G A2) ->
        T B1 A1 ->
        G (T B2 A2).

Arguments traversep {T}%function_scope {TraversePoly} {A1 A2 B1 B2}%type_scope
  {G}%function_scope {Gmap Gpure Gmult} (_ _)%function_scope _.

(*
#[export] Instance TraversePoly_MapdtPoly {T} `{MapdtPoly T}: TraversePoly T :=
  fun A1 A2 B1 B2 G Gmap Gpure Gmult ρ σ =>
    mapdtp
      (ρ ∘ extract (W := prod (list B1)))
      (σ ∘ extract (W := prod (list B1))).
*)
