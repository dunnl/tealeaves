From Tealeaves Require Export
  Functors.Writer.

Import Monoid.Notations.
Import Product.Notations.
Import Comonad.Notations.

(** * Decorated functors *)
(******************************************************************************)

(** ** Operation *)
(******************************************************************************)
Class Mapd (E : Type) (T : Type -> Type) := mapd :
    forall (A B : Type), (E * A -> B) -> T A -> T B.

#[global] Arguments mapd {E}%type_scope (T)%function_scope {Mapd} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Class DecoratedFunctor (E : Type) (T : Type -> Type) `{Mapd E T} :=
  { dfun_mapd1 : forall (A : Type),
      @mapd E T _ A A (extract (E ×) A) = @id (T A);
    dfun_mapd2 : forall (A B C : Type) (g : E * B -> C) (f : E * A -> B),
      @mapd E T _ B C g ∘ @mapd E T _ A B f = @mapd E T _ A C (g ⋆4 f);
  }.

(** ** Derived functor instance *)
(******************************************************************************)
Module DerivedInstances.


  (** ** [map] as a special case of [mapd] *)
  (******************************************************************************)
  #[export] Instance Map_Mapd (E : Type) (T : Type -> Type) `{Mapd E T} : Map T :=
  fun (A B : Type) (f : A -> B) => @mapd E T _ A B (f ∘ extract (E ×) A).

  Lemma map_to_mapd (E : Type) (T : Type -> Type) `{Mapd E T} : forall (A B : Type) (f : A -> B),
      map T f = mapd T (f ∘ extract (E ×) A).
  Proof.
    reflexivity.
  Qed.

  Section with_instance.

    Context
      (E : Type)
      (T : Type -> Type)
      `{DecoratedFunctor E T}.

    (** ** Composition in special cases *)
    (******************************************************************************)
    Lemma map_mapd :
      forall (A B C : Type)
        (g : B -> C)
        (f : E * A -> B),
        map T g ∘ mapd T f = mapd T (g ∘ f).
    Proof.
      intros.
      rewrite (map_to_mapd).
      rewrite (dfun_mapd2).
      rewrite (Comonad.DerivedInstances.kc4_04).
      reflexivity.
    Qed.

    Lemma mapd_map: forall (A B C : Type)
                      (g : E * B -> C)
                      (f : A -> B),
        mapd T g ∘ map T f = mapd T (g ∘ map (E ×) f).
    Proof.
      intros.
      rewrite (map_to_mapd).
      rewrite (dfun_mapd2).
      rewrite Comonad.DerivedInstances.kc4_40.
      reflexivity.
    Qed.

    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map T g ∘ map T f = map T (g ∘ f).
    Proof.
      intros.
      do 2 rewrite (map_to_mapd).
      rewrite (dfun_mapd2).
      rewrite (Comonad.DerivedInstances.kc4_00).
      reflexivity.
    Qed.

    Lemma map_id : forall (A : Type),
        map T (@id A) = @id (T A).
    Proof.
      intros. rewrite (map_to_mapd).
      unfold id, compose.
      now rewrite (dfun_mapd1).
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

  End with_instance.

End DerivedInstances.
