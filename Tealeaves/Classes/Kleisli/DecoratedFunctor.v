From Tealeaves Require Export
  Functors.Early.Reader.
From Tealeaves Require Import
  Classes.Kleisli.Comonad.

Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables E T.

(** * Decorated Functors *)
(******************************************************************************)

(** ** <<mapd>> Operation *)
(******************************************************************************)
Class Mapd (E: Type) (T: Type -> Type) :=
  mapd: forall (A B: Type), (E * A -> B) -> T A -> T B.

#[global] Arguments mapd {E}%type_scope {T}%function_scope
  {Mapd} {A B}%type_scope _%function_scope _.

(** ** Kleisli Composition *)
(** Kleisli composition is [kc1] *)
(******************************************************************************)

(** ** Typeclasses *)
(******************************************************************************)
Class DecoratedFunctor (E: Type) (T: Type -> Type) `{Mapd E T} :=
  { kdf_mapd1: forall (A: Type),
      mapd (extract (A := A)) = @id (T A);
    kdf_mapd2: forall (A B C: Type) (g: E * B -> C) (f: E * A -> B),
      mapd g ∘ mapd f = mapd (g ⋆1 f);
  }.

(** ** Homomorphisms between Decorated Functors *)
(******************************************************************************)
Class DecoratedHom
  (E: Type) (T1 T2: Type -> Type)
  (ϕ: forall A: Type, T1 A -> T2 A)
  `{Mapd E T1} `{Mapd E T2} :=
  { dhom_natural:
    forall (A B: Type) (f: E * A -> B), mapd f ∘ ϕ A = ϕ B ∘ mapd f;
  }.

(** * Derived Structures *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Map_Mapd
    (E: Type)
    (T: Type -> Type)
    `{Mapd_ET: Mapd E T}: Map T :=
  fun (A B: Type) (f: A -> B) => mapd (f ∘ extract).

End DerivedOperations.

Class Compat_Map_Mapd (E: Type) (T: Type -> Type)
  `{Map_T: Map T}
  `{Mapd_ET: Mapd E T}: Prop :=
  compat_map_mapd:
    Map_T = @DerivedOperations.Map_Mapd E T Mapd_ET.

#[export] Instance Compat_Map_Mapd_Self
  `{Mapd_ET: Mapd E T}:
  Compat_Map_Mapd E T (Map_T := DerivedOperations.Map_Mapd E T).
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

(** ** Derived Composition Laws *)
(******************************************************************************)
Section derived_instances.

  Context
    `{DecoratedFunctor E T}
    `{Map_T: Map T}
    `{! Compat_Map_Mapd E T}.

  Lemma map_mapd:
    forall (A B C: Type)
      (g: B -> C)
      (f: E * A -> B),
      map g ∘ mapd f = mapd (g ∘ f).
  Proof.
    intros.
    rewrite map_to_mapd.
    rewrite kdf_mapd2.
    rewrite kc1_01.
    reflexivity.
  Qed.

  Lemma mapd_map:
    forall (A B C: Type) (g: E * B -> C) (f: A -> B),
      mapd g ∘ map f = mapd (g ∘ map f).
  Proof.
    intros.
    rewrite map_to_mapd.
    rewrite kdf_mapd2.
    rewrite kc1_10.
    reflexivity.
  Qed.

  Lemma map_map: forall (A B C: Type) (f: A -> B) (g: B -> C),
      map g ∘ map f = map (F := T) (g ∘ f).
  Proof.
    intros.
    rewrite map_to_mapd.
    rewrite map_to_mapd.
    rewrite kdf_mapd2.
    rewrite kc1_00.
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

End derived_instances.

(** ** Derived Typeclass Instances *)
(******************************************************************************)
Module DerivedInstances.

  #[export] Instance Functor_DecoratedFunctor
    (E: Type) (T: Type -> Type)
    `{DecoratedFunctor_ET: DecoratedFunctor E T}
    `{Map_T: Map T}
    `{! Compat_Map_Mapd E T}:
  Classes.Functor.Functor T :=
    {| fun_map_id := map_id;
       fun_map_map := map_map;
    |}.

  Include DerivedOperations.

End DerivedInstances.

(** * Instance for Reader *)
(******************************************************************************)
Import Product.Notations.

Section decorated_functor_reader.

  Context {E: Type}.

  #[export] Instance Mapd_Reader: Mapd E (E ×) :=
    @cobind (E ×) (Cobind_reader E).

  #[export] Instance DecoratedFunctor_Reader:
    DecoratedFunctor E (E ×).
  Proof.
    constructor;
      unfold_ops @Mapd_Reader; intros.
    - apply kcom_cobind1.
    - apply kcom_cobind2.
  Qed.

End decorated_functor_reader.
