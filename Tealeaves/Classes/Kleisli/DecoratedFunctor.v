From Tealeaves Require Export
  Functors.Writer.

Import Monoid.Notations.
Import Product.Notations.
Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables E T.

(** * Decorated functors *)
(******************************************************************************)

(** ** Typeclasses *)
(******************************************************************************)
Class Mapd (E : Type) (T : Type -> Type) := mapd :
    forall (A B : Type), (E * A -> B) -> T A -> T B.

#[global] Arguments mapd {E}%type_scope {T}%function_scope {Mapd} {A B}%type_scope _%function_scope _.

Class DecoratedFunctor (E : Type) (T : Type -> Type) `{Mapd E T} :=
  { dfun_mapd1 : forall (A : Type),
      @mapd E T _ A A (extract) = @id (T A);
    dfun_mapd2 : forall (A B C : Type) (g : E * B -> C) (f : E * A -> B),
      @mapd E T _ B C g ∘ @mapd E T _ A B f = @mapd E T _ A C (g ⋆4 f);
  }.

(** ** Derived functor instance *)
(******************************************************************************)
Module DerivedInstances.

  Import Comonad.DerivedInstances.

  (** ** [map] as a special case of [mapd] *)
  (******************************************************************************)
  #[export] Instance Map_Mapd (E : Type) (T : Type -> Type) `{Mapd E T} : Map T :=
  fun (A B : Type) (f : A -> B) => @mapd E T _ A B (f ∘ extract).

  Lemma map_to_mapd (E : Type) (T : Type -> Type) `{Mapd E T} :
    forall (A B : Type) (f : A -> B),
      map f = mapd (f ∘ extract).
  Proof.
    reflexivity.
  Qed.

  Section with_instance.

    Context
      `{DecoratedFunctor E T}.

    (** ** Composition in special cases *)
    (******************************************************************************)
    Lemma map_mapd :
      forall (A B C : Type)
        (g : B -> C)
        (f : E * A -> B),
        map g ∘ mapd f = mapd (g ∘ f).
    Proof.
      intros.
      rewrite map_to_mapd.
      rewrite dfun_mapd2.
      rewrite kc4_04.
      reflexivity.
    Qed.

    Lemma mapd_map: forall (A B C : Type)
                      (g : E * B -> C)
                      (f : A -> B),
        mapd g ∘ map f = mapd (g ∘ map f).
    Proof.
      intros.
      rewrite map_to_mapd.
      rewrite dfun_mapd2.
      rewrite kc4_40.
      reflexivity.
    Qed.

    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map g ∘ map f = map (F := T) (g ∘ f).
    Proof.
      intros.
      do 2 rewrite map_to_mapd.
      rewrite dfun_mapd2.
      rewrite kc4_00.
      reflexivity.
    Qed.

    Lemma map_id : forall (A : Type),
        map (@id A) = @id (T A).
    Proof.
      intros.
      rewrite map_to_mapd.
      unfold id, compose.
      rewrite dfun_mapd1.
      reflexivity.
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

  End with_instance.

End DerivedInstances.
