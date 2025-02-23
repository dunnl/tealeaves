From Tealeaves Require Export
  Classes.Categorical.Comonad
  Functors.Reader
  Functors.List_Telescoping_General
  Classes.Functor2
  Classes.Monoid
  Functors.Z2.

Import Monoid.Notations.

(** * <<shift2>> *)
(**********************************************************************)
Definition shift2 {F: Type -> Type -> Type}
  `{Map2 F} {W} `{Monoid_op W} {A1 A2} :
  W * F (W * A1) (W * A2) -> F (W * A1) (W * A2) :=
  map2 (uncurry incr) (uncurry incr) ∘ strength2.

Lemma map2_shift2_preincr
  {F: Type -> Type -> Type}
  `{Map2 F}
  `{! Functor2 F}
  {W} `{Monoid_op W}
  {B1 V1 B2 V2} {g: W * B1 -> B2} {f: W * V1 -> V2} {w: W}:
  map2 g f ∘ shift2 ∘ pair w = map2 (g ⦿ w) (f ⦿ w).
Proof.
  intros.
  ext t.
  unfold shift2.
  unfold compose.
  unfold strength2.
  compose near t on left.
  rewrite (fun2_map_map).
  compose near t on left.
  rewrite (fun2_map_map).
  reflexivity.
Qed.

(** * Poly Decorated functors *)
(**********************************************************************)

(** ** Operations *)
(**********************************************************************)
Class DecoratePoly
  (F: Type -> Type -> Type) :=
  decp: forall (B V: Type), F B V -> F (Z B) (Z2 B V).

#[global] Arguments decp {F}%function_scope {DecoratePoly}
  {B V}%type_scope _.

#[local] Arguments decp {F}%function_scope {DecoratePoly}
  {B V}%type_scope _.

Definition PolyDecorateNatural F `{Map2 F} `{DecoratePoly F}: Prop :=
  forall (B V B' V': Type) (g: B -> B') (f: V -> V'),
    decp (B := B') (V := V') ∘ map2 g f =
      map2 (map (F := Z) g) (map2 (F := Z2) g f) ∘ decp (B := B) (V := V).


(** ** Typeclass *)
(**********************************************************************)
Class DecoratedFunctorPoly
  (F: Type -> Type -> Type)
  `{Map2 F}
  `{DecoratePoly F} :=
  { dfunp_functor :> Functor2 F;
    dfunp_natural: PolyDecorateNatural F;
    dfunp_dec_dec: forall (B V: Type),
      decp ∘ decp (B := B) (V := V) = map2 (cojoin (W := Z)) cojoin_Z2 ∘ decp;
    dfunp_dec_extract: forall (B V: Type),
      map2 (extract) (extract) ∘ decp (B := B) (V := V) = @id (F B V);
  }.
