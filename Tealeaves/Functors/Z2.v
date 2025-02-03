From Tealeaves Require Import
  Classes.Functor2
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
