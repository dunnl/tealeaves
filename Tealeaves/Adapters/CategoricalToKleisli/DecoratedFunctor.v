From Tealeaves Require Import
  Classes.Categorical.DecoratedFunctor
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.Comonad (kc1, cobind)
  CategoricalToKleisli.Comonad.

#[local] Generalizable Variables E F.

Import Product.Notations.
Import Kleisli.Comonad.Notations.

(** * Categorical Decorated Functors to Kleisli Decorated Functors *)
(**********************************************************************)

(** ** Derived <<mapd>> Operation *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Mapd_Categorical
    (E: Type)
    (F: Type -> Type)
    `{Map_F: Map F}
    `{Decorate_EF: Decorate E F}: Mapd E F :=
  fun A B (f: E * A -> B) => map (F := F) f ∘ dec F.

End DerivedOperations.

Class Compat_Mapd_Categorical
    (E: Type)
    (F: Type -> Type)
    `{Map_F: Map F}
    `{Decorate_EF: Decorate E F}
    `{Mapd_F: Mapd E F} :=
  compat_mapd_categorical:
    Mapd_F = @DerivedOperations.Mapd_Categorical E F Map_F Decorate_EF.

Lemma mapd_to_categorical {E F}
    `{Map_F: Map F}
    `{Decorate_EF: Decorate E F}
    `{Mapd_F: Mapd E F}
    `{Compat: Compat_Mapd_Categorical E F}:
  forall (A B: Type) (f: E * A -> B) (t: F A),
    mapd f t = map f (dec F t).
Proof.
  now rewrite compat_mapd_categorical.
Qed.

Section decorate_after_mapd_reasoning.

  Context
    (E: Type)
    (T: Type -> Type)
    `{Map_F: Map F}
    `{Decorate_EF: Decorate E F}
    `{Mapd_F: Mapd E F}
    `{DecFun_EF: ! Categorical.DecoratedFunctor.DecoratedFunctor E F}
    `{Compat: ! Compat_Mapd_Categorical E F}.

  Context {A B: Type} {f: E * A -> B} (t: F A).

  Lemma dec_mapd:
    dec F (mapd f t) =
      (mapd (T := F) (map f) (dec F t)).
  Proof.
    intros.
    rewrite mapd_to_categorical.
    compose near (dec F t) on left.
    inversion DecFun_EF.
    rewrite <- (natural (ϕ := @dec E F _)).
    unfold compose.
    rewrite mapd_to_categorical.
    reflexivity.
  Qed.

  Lemma dec_mapd2:
    dec F (mapd f t) =
      (map (F := F) (cobind f) (dec F t)).
  Proof.
    intros.
    rewrite dec_mapd.
    rewrite mapd_to_categorical.
    compose near t on left.
    rewrite dfun_dec_dec.
    unfold compose.
    compose near (dec F t) on left.
    rewrite fun_map_map.
    fequal.
    now ext [e a].
  Qed.

End decorate_after_mapd_reasoning.

(** ** Derived co-Kleisli Laws *)
(**********************************************************************)
Module DerivedInstances.

  (* Alectryon doesn't like this
     Import CategoricalToKleisli.DecoratedFunctor.DerivedOperations.
   *)
  Import DerivedOperations.
  Import CategoricalToKleisli.Comonad.DerivedOperations.

  Section with_functor.

    Context
      (F: Type -> Type)
      `{Classes.Categorical.DecoratedFunctor.DecoratedFunctor E F}.

    Theorem mapd_id {A}:
      @mapd E F _ A A (extract (W := (E ×))) = @id (F A).
    Proof.
      introv.
      unfold mapd.
      unfold Mapd_Categorical.
      rewrite dfun_dec_extract.
      reflexivity.
    Qed.

    Theorem mapd_mapd (A B C: Type) (g: E * B -> C) (f: E * A -> B):
      @mapd E F _ B C g ∘ @mapd E F _ A B f = @mapd E F _ A C (kc1 g f).
    Proof.
      unfold_ops @Mapd_Categorical.
      reassociate <- on left.
      reassociate -> near (map f).
      rewrite <- (natural (G := F ○ prod E)).
      reassociate <- on left.
      unfold transparent tcs.
      rewrite (fun_map_map (F := F)).
      reassociate -> on left.
      rewrite (dfun_dec_dec).
      reassociate <- on left.
      rewrite (fun_map_map (F := F)).
      repeat fequal.
      ext [e a].
      reflexivity.
    Qed.

    (** ** Typeclass Instance *)
    (******************************************************************)
    #[export] Instance DecoratedFunctor:
      Kleisli.DecoratedFunctor.DecoratedFunctor E F :=
      {| kdf_mapd1 := @mapd_id;
         kdf_mapd2 := @mapd_mapd
      |}.

  End with_functor.

End DerivedInstances.

(** ** Miscellaneous Properties *)
(**********************************************************************)
Section DecoratedFunctor_misc.

  Context
    (T: Type -> Type)
    `{Categorical.DecoratedFunctor.DecoratedFunctor E T}.

  Theorem cobind_dec {A B}: forall (f: E * A -> B),
      map (F := T) (cobind (W := (E ×)) f) ∘ dec T =
        dec T ∘ map (F := T) f ∘ dec T.
  Proof.
    intros.
    unfold_ops @Cobind_reader.
    rewrite <- (natural (ϕ := @dec E T _)).
    unfold_ops @Map_compose.
    reassociate ->.
    rewrite  (dfun_dec_dec (E := E) (F := T)).
    reassociate <-.
    rewrite (fun_map_map (F := T)).
    fequal. fequal.
    now ext [e a].
  Qed.

End DecoratedFunctor_misc.
