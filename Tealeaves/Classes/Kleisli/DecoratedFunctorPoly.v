From Tealeaves Require Export
  Functors.List_Telescoping_General
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Functors.Z2
  Functors.List_Telescoping_General
  Functors.Writer.

Import Product.Notations.


(** * Monomorphic Binder Instance *)
(******************************************************************************)

(** ** Operation <<mapdp>> *)
(******************************************************************************)
Class MapdZ
  (T: Type -> Type) :=
  mapdz:
    forall (A B: Type),
      (Z A -> B) ->
      T A -> T B.

(** ** Kleisli Composition *)
(**********************************************************************)
Definition kc_dz {B1 B2 B3: Type}
  (ρ2: list B2 * B2 -> B3) (* second op to rename binders *)
  (ρ1: list B1 * B1 -> B2) (* first op to rename binders *)
  : list B1 * B1 -> B3 :=
  ρ2 ∘ cobind (W := Z) ρ1.

#[global] Arguments mapdz {T}%function_scope {MapdZ} {A B}%type_scope _%function_scope _.

(** ** Typeclass *)
(**********************************************************************)
Class DecoratedFunctorZ
  (T: Type -> Type) `{MapdZ T} :=
  { kdz_mapdz1:
    forall (A: Type),
      mapdz
        (extract (W := Z))
      = @id (T A);
    kdz_mapdz2:
    forall {B1 B2 B3: Type}
      (ρ1: list B1 * B1 -> B2)
      (ρ2: list B2 * B2 -> B3),
      (mapdz ρ2) ∘ mapdz (T := T) ρ1 =
        mapdz (T := T) (kc_dz ρ2 ρ1)
  }.

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
  σ2 ∘ cobind_Z2 ρ1 σ1.

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
