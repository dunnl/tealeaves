From Tealeaves Require Import
  Classes.Functor2
  Classes.Categorical.Comonad
  Functors.Reader
  Functors.List
  Functors.List_Telescoping_General.

(** * <<Z>> Comonad of Two Arguments *)
(**********************************************************************)
Definition Z2: Type -> Type -> Type :=
  fun B A => list B * A.

Definition cojoin_Z2: forall (B A: Type),
    Z2 B A -> Z2 (Z2 B B) (Z2 B A) :=
  fun B A '(ctx, a) => (decorate_prefix_list ctx, (ctx, a)).

Definition extract_Z2: forall (B A: Type),
    Z2 B A -> A :=
  fun B A '(ctx, a) => a.

Definition map_Z2: forall (B1 A1 B2 A2: Type) (g: B1 -> B2) (f: A1 -> A2),
    Z2 B1 A1 -> Z2 B2 A2 :=
  fun _ _ _ _ g f '(ctx, a) => (map g ctx, f a).

#[global] Arguments extract_Z2 {B A}%type_scope _.
#[global] Arguments cojoin_Z2 {B A}%type_scope _.
#[global] Arguments map_Z2 {B1 A1 B2 A2}%type_scope g f.


#[export] Instance Extract_Z2: forall B, Extract (Z2 B) :=
  fun B V => extract (W := prod (list B)).

#[export] Instance Map2_Z2: Map2 Z2 := @map_Z2.

Instance Functor2_Z2: Functor2 Z2.
Proof.
  constructor; intros; ext t.
  - induction t; try auto.
    cbn. now rewrite fun_map_id.
  - induction t; try auto.
    cbn.
    compose near a on left.
    rewrite fun_map_map.
    reflexivity.
Qed.

(** * <<Dist>> instance on <<Z2>> *)
(**********************************************************************)
From Tealeaves Require Import
  Classes.Categorical.TraversableFunctor2.

Import Applicative.Notations.

Definition dist2_Z2
  {B V: Type} {G}
  `{Map G} `{Mult G} `{Pure G}:
  Z2 (G B) (G V) -> G (Z2 B V) :=
  fun '(x, y) => pure (@pair (list B) V) <⋆> dist list G x <⋆> y.

Instance Dist2_Z2: ApplicativeDist2 Z2.
Proof.
  intro G. intros.
  exact (dist2_Z2 X).
Defined.

