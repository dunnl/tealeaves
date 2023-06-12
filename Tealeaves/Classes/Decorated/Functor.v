From Tealeaves Require Export
  Functors.Writer.

Import Monoid.Notations.
Import Product.Notations.
Import Comonad.Notations.

#[export] Instance Return_writer {M : Type} `{Monoid_unit M} : Return (prod M) :=
  fun A (a : A) => (Ƶ, a).

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

  #[export] Instance Map_Mapd
   (E : Type)
    (T : Type -> Type)
    `{Mapd E T} : Map T :=
  fun (A B : Type) (f : A -> B) => mapd E T A B (f ∘ extract (E ×) A).

  Section with_instance.

    Context
      (E : Type)
      (T : Type -> Type)
      `{DecoratedFunctor E T}.

    Lemma map_id : forall (A : Type),
        map T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Map_Mapd.
      now rewrite (dfun_mapd1 E T).
    Qed.

    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map T g ∘ map T f = map T (g ∘ f).
    Proof.
      intros. unfold_ops @Map_Mapd.
      rewrite (dfun_mapd2 E T).
      fequal. reassociate ->.
      unfold kc4.
      reassociate ->.
      now rewrite (kcom_cobind0 (E ×)).
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

    Lemma map_mapd :
      forall (A B C : Type)
        (g : B -> C)
        (f : E * A -> B),
        map T g ∘ mapd E T A B f = mapd E T A C (g ∘ f).
    Proof.
      intros. unfold_ops @Map_Mapd.
      rewrite (dfun_mapd2 E T).
      unfold kc4.
      reassociate ->.
      now rewrite (kcom_cobind0 (E ×)).
    Qed.

    Lemma mapd_map: forall (A B C : Type)
                        (g : E * B -> C)
                        (f : A -> B),
        mapd E T B C g ∘ map T f = mapd E T A C (g ∘ map (E ×) f).
    Proof.
      intros. unfold_ops @Map_Mapd.
      rewrite (dfun_mapd2 E T).
      unfold kc4.
      now rewrite <- (map_to_cobind (E := E)).
    Qed.

  End with_instance.

End DerivedInstances.
