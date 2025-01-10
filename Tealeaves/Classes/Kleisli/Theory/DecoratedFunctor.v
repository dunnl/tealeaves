From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.Theory.Comonad
  Classes.Monoid.

Import Monoid.Notations.
Import Product.Notations.
Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables E T.

(** * Derived map operation *)
(******************************************************************************)
#[export] Instance Map_Mapd `{Mapd_inst: Mapd E T}: Map T :=
  fun (A B: Type) (f: A -> B) => mapd (f ∘ extract).

Class Compat_Map_Mapd
  `{Map_inst: Map T}
  `{Mapd_inst: Mapd E T}: Prop :=
  compat_map_mapd:
    @map T Map_inst = @map T (@Map_Mapd E T Mapd_inst).

#[export] Instance Compat_Map_Mapd_Self
  `{Mapd E T}:
  Compat_Map_Mapd (Map_inst := Map_Mapd).
Proof.
  reflexivity.
Qed.

Corollary map_to_mapd
  `{Compat_Map_Mapd E T}: forall (A B: Type) (f: A -> B),
    map f = mapd (f ∘ extract).
Proof.
  rewrite compat_map_mapd.
  reflexivity.
Qed.

(** ** Full typeclasses *)
(******************************************************************************)
Class DecoratedFunctorFull (E: Type) (T: Type -> Type)
  `{Mapd_ET: Mapd E T} `{Map_T: Map T} :=
  { kdff_df :> DecoratedFunctor E T;
    kdff_map_compat :> Compat_Map_Mapd;
  }.

Definition DecoratedFunctorFull_DecoratedFunctor
  `{DecoratedFunctor E T}:
  `{DecoratedFunctorFull E T} :=
  {| kdff_df := _ |}.

(** * Derived instances *)
(******************************************************************************)
Section derived_instances.

  Context
    `{DecoratedFunctor E T}
    `{Map_T: Map T}
    `{! Compat_Map_Mapd}.

  (** ** Composition in special cases *)
  (******************************************************************************)
  Lemma map_mapd:
    forall (A B C: Type)
      (g: B -> C)
      (f: E * A -> B),
      map g ∘ mapd f = mapd (g ∘ f).
  Proof.
    intros.
    rewrite map_to_mapd.
    rewrite kdf_mapd2.
    rewrite kc4_04.
    reflexivity.
  Qed.

  Lemma mapd_map:
    forall (A B C: Type) (g: E * B -> C) (f: A -> B),
      mapd g ∘ map f = mapd (g ∘ map f).
  Proof.
    intros.
    rewrite map_to_mapd.
    rewrite kdf_mapd2.
    rewrite kc4_40.
    reflexivity.
  Qed.

  Lemma map_map: forall (A B C: Type) (f: A -> B) (g: B -> C),
      map g ∘ map f = map (F := T) (g ∘ f).
  Proof.
    intros.
    rewrite map_to_mapd.
    rewrite map_to_mapd.
    rewrite kdf_mapd2.
    rewrite kc4_00.
    rewrite map_to_mapd.
    reflexivity.
  Qed.

  Lemma map_id: forall (A: Type),
      map (@id A) = @id (T A).
  Proof.
    intros.
    rewrite map_to_mapd.
    change (id ∘ ?f) with f.
    rewrite kdf_mapd1.
    reflexivity.
  Qed.

  (** ** Typeclass instances *)
  (******************************************************************************)
  #[export] Instance Functor_DecoratedFunctor: Classes.Functor.Functor T :=
    {| fun_map_id := map_id;
       fun_map_map := map_map;
    |}.

End derived_instances.
