From Tealeaves Require Import
  Classes.Functor2
  Classes.Categorical.Comonad
  Functors.Reader
  Functors.List
  Functors.List_Telescoping_General.

(** * <<Z>> Comonad of Two Arguments *)
(**********************************************************************)
Definition L: Type -> Type -> Type :=
  fun B A => list B * A.

Definition cojoin_L {B A: Type}:
    L B A -> L (L B B) (L B A) :=
  fun '(ctx, a) => (decorate_prefix_list ctx, (ctx, a)).

Definition extract_L {B A: Type}:
    L B A -> A :=
  fun '(ctx, a) => a.

Definition map_L  {B1 A1 B2 A2: Type} (g: B1 -> B2) (f: A1 -> A2):
    L B1 A1 -> L B2 A2 :=
  fun '(ctx, a) => (map g ctx, f a).

Definition cobind_L {B1 B2 A1 A2: Type}
  (ρ: Z B1 -> B2)
  (σ: L B1 A1 -> A2):  L B1 A1 -> L B2 A2 :=
  map_L ρ σ ∘ cojoin_L.

#[global] Arguments extract_L {B A}%type_scope _.
#[global] Arguments cojoin_L {B A}%type_scope _.
#[global] Arguments map_L {B1 A1 B2 A2}%type_scope g f.

#[export] Instance Extract_L: forall B, Extract (L B) :=
  fun B V => extract (W := prod (list B)).

#[export] Instance Map2_L: Map2 L := @map_L.

#[export] Instance Functor2_L: Functor2 L.
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

(** * <<Dist>> instance on <<L>> *)
(**********************************************************************)
From Tealeaves Require Import
  Classes.Categorical.TraversableFunctor2.

Import Applicative.Notations.

Definition dist2_L
  {B V: Type} {G}
  `{Map G} `{Mult G} `{Pure G}:
  L (G B) (G V) -> G (L B V) :=
  fun '(x, y) => pure (@pair (list B) V) <⋆> dist list G x <⋆> y.

#[export] Instance Dist2_L: ApplicativeDist2 L.
Proof.
  intro G. intros.
  exact (dist2_L X).
Defined.

