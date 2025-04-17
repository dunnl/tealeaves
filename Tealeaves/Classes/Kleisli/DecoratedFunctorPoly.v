From Tealeaves Require Export
  Functors.List_Telescoping_General
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Functors.Z2
  Functors.List_Telescoping_General
  Functors.Writer.

Import Product.Notations.


(** * Functors Decorated by <<Z>> Comonad *)
(******************************************************************************)

(** ** Operation <<mapdz>> *)
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

(** ** Instance for List *)
(******************************************************************************)
#[export] Instance MapdZ_list: MapdZ list := @mapd_list_prefix.

#[export] Instance DecoratedFunctorZ_list: DecoratedFunctorZ list.
Proof.
  constructor; intros; unfold_ops @MapdZ_list.
  - rewrite kdfun_mapd1_list_prefix.
    reflexivity.
  - rewrite kdfun_mapd2_list_prefix.
    reflexivity.
Qed.

Import Functors.List.
(* TODO Relocate me *)
Lemma mapdz_map_list {A A' B: Type}: forall (f: Z A -> B) (g: A' -> A),
    mapdz (T := list) (f ∘ map (F := Z) g) =
      mapdz (T := list) f ∘ map (F := list) g.
Proof.
  intros. ext l.
  unfold compose.
  generalize dependent f.
  induction l.
  - reflexivity.
  - cbn. intros.
    rewrite <- IHl.
    fequal.
    fequal.
    ext [x y].
    cbn.
    unfold preincr, incr, compose.
    fequal.
Qed.


(** ** Instance for Z *)
(******************************************************************************)
#[export] Instance MapdZ_Z: MapdZ Z := @mapd_Z.

Lemma mapdz_rw_pair {A B: Type}: forall (f: Z A -> B) ctx a,
    mapdz (T := Z) f (ctx, a) =
      (mapdz (T := list) f ctx, f (ctx, a)).
Proof.
  reflexivity.
Qed.

#[export] Instance DecoratedFunctorZ_Z: DecoratedFunctorZ Z.
Proof.
  constructor; intros; ext [ctx a].
  - rewrite mapdz_rw_pair.
    rewrite kdz_mapdz1.
    reflexivity.
  - rewrite mapdz_rw_pair.
    unfold compose at 1.
    rewrite mapdz_rw_pair.
    rewrite mapdz_rw_pair.
    compose near ctx on left.
    rewrite (kdz_mapdz2 (T := list)).
    reflexivity.
Qed.

(*
#[export] Instance DecoratedContainerFunctor_list_prefix:
  DecoratedFunctorZ list.
*)

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
