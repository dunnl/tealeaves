From Tealeaves Require Export
  Functors.Writer.

Import Monoid.Notations.
Import Product.Notations.
Import Comonad.Notations.

(** * Operational typeclasses for DTM hierarchy *)
(******************************************************************************)
Section operations.

  Context
    (M : Type)
    (T : Type -> Type)
    (U : Type -> Type).

  Class Mapd := mapd :
      forall (A B : Type),
        (M * A -> B) -> T A -> T B.

End operations.

Section class.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Mapd E T}.

  Class DecoratedFunctor :=
    { dfun_mapd1 : forall (A : Type),
        mapd E T A A (extract (E ×) A) = @id (T A);
      dfun_mapd2 : forall (A B C : Type) (g : E * B -> C) (f : E * A -> B),
        mapd E T B C g ∘ mapd E T A B f = mapd E T A C (g ⋆4 f);
    }.

End class.

(** ** Derived functor instance *)
(******************************************************************************)
Module DerivedInstances.

  Section op.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Mapd E T}.

    #[export] Instance Map_Mapd : Map T :=
      fun (A B : Type) (f : A -> B) => mapd E T A B (f ∘ extract (E ×) A).

    Lemma map_to_mapd : forall (A B : Type) (f : A -> B),
        map T f = mapd E T A B (f ∘ extract (E ×) A).
    Proof.
      reflexivity.
    Qed.

  End op.

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
        map T g ∘ mapd E T A B f = mapd E T A C (g ∘ f).
    Proof.
      intros.
      rewrite (map_to_mapd).
      rewrite (dfun_mapd2 E T).
      rewrite (Comonad.DerivedInstances.kc4_04 (E ×)).
      reflexivity.
    Qed.

    Lemma mapd_map: forall (A B C : Type)
                        (g : E * B -> C)
                        (f : A -> B),
        mapd E T B C g ∘ map T f = mapd E T A C (g ∘ map (E ×) f).
    Proof.
      intros.
      rewrite (map_to_mapd).
      rewrite (dfun_mapd2 E T).
      rewrite Comonad.DerivedInstances.kc4_40.
      reflexivity.
    Qed.

    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map T g ∘ map T f = map T (g ∘ f).
    Proof.
      intros.
      do 2 rewrite (map_to_mapd).
      rewrite (dfun_mapd2 E T).
      rewrite (Comonad.DerivedInstances.kc4_00 (E ×)).
      reflexivity.
    Qed.

    Lemma map_id : forall (A : Type),
        map T (@id A) = @id (T A).
    Proof.
      intros. rewrite (map_to_mapd).
      now rewrite (dfun_mapd1 E T).
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

  End with_instance.

End DerivedInstances.
