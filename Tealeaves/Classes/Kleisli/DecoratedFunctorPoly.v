From Tealeaves Require Export
  Functors.List_Telescoping_General
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Classes.Kleisli.DecoratedFunctorZ
  Functors.L
  Functors.List_Telescoping_General
  Functors.Writer.

Import Product.Notations.

(** * Polymorphically Decorated Functors *)
(******************************************************************************)

(** ** Operation <<mapdp>> *)
(******************************************************************************)
Class MapdPoly
  (T: Type -> Type -> Type) :=
  mapdp:
    forall (WA WB: Type) (A B: Type),
      (list WA * WA -> WB) ->
      (list WA * A -> B) ->
      T WA A -> T WB B.

#[global] Arguments mapdp {T}%function_scope {MapdPoly} {WA WB A B}%type_scope (_ _)%function_scope _.

(** ** Kleisli Composition *)
(**********************************************************************)
Definition kc_dfunp {T}
  `{MapdPoly T}
  {B1 A1 B2 A2 A3: Type}
  (σ2: list B2 * A2 -> A3) (* second op to rename variables *)
  (ρ1: list B1 * B1 -> B2) (* first op to rename binders *)
  (σ1: list B1 * A1 -> A2) (* first op to rename variables *)
  : list B1 * A1 -> A3 :=
  σ2 ∘ cobind_L ρ1 σ1.

(** ** Typeclass *)
(**********************************************************************)
Class DecoratedFunctorPoly
  (T: Type -> Type -> Type) `{MapdPoly T} :=
  { kdfunp_mapdp1:
    forall (B A: Type),
      mapdp
        (extract (W := (list B ×)))
        (extract (W := (list B ×)))
      = @id (T B A);
    kdfunp_mapdp2:
    forall {B1 B2 B3: Type}
      {A1 A2 A3: Type}
      (ρ1: list B1 * B1 -> B2)
      (ρ2: list B2 * B2 -> B3)
      (σ1: list B1 * A1 -> A2)
      (σ2: list B2 * A2 -> A3),
      (mapdp ρ2 σ2) ∘ mapdp (T := T) ρ1 σ1 =
        mapdp (T := T) (kc_dz ρ2 ρ1) (kc_dfunp σ2 ρ1 σ1);
  }.
