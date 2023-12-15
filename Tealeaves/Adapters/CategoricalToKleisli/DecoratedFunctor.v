From Tealeaves Require Import
  Classes.Categorical.DecoratedFunctor
  Classes.Kleisli.DecoratedFunctor.

#[local] Generalizable Variables E F.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments dec {E}%type_scope F%function_scope {Decorate} {A}%type_scope _.
#[local] Arguments extract W%function_scope {Extract} {A}%type_scope _.

Import Product.Notations.

(** * Algebraic decorated functor to Kleisli decorated functor *)
(******************************************************************************)

(** ** Kleisli laws for <<fmapd>> *)
(******************************************************************************)
Module ToKleisli.

  Section operation.

    Context
      (E : Type)
      (F : Type -> Type)
      `{Map F} `{Decorate E F}.

    #[export] Instance Mapd_dec : Mapd E F :=
      fun A B (f : E * A -> B) => map F f ∘ dec F.

  End operation.

  Import Comonad.Notations.
  Import Comonad.ToKleisli.

  Section with_functor.

    Context
      (F : Type -> Type)
      `{Classes.Categorical.DecoratedFunctor.DecoratedFunctor E F}.

    Theorem mapd_id {A} : @mapd E F _ A A (extract (E ×)) = @id (F A).
    Proof.
      introv. unfold_ops @Mapd_dec.
      apply (dfun_dec_extract).
    Qed.

    Theorem mapd_mapd (A B C : Type) (g : E * B -> C) (f : E * A -> B) :
      @mapd E F _ B C g ∘ @mapd E F _ A B f = @mapd E F _ A C (kc4 g f).
    Proof.
      unfold_ops @Mapd_dec.
      reassociate <- on left.
      reassociate -> near (map F f).
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

    #[export] Instance DecoratedFunctor: Kleisli.DecoratedFunctor.DecoratedFunctor E F :=
      {| dfun_mapd1 := @mapd_id;
        dfun_mapd2 := @mapd_mapd
      |}.

  End with_functor.

End ToKleisli.

(** * Miscellaneous properties of decorated functors *)
(******************************************************************************)
Section DecoratedFunctor_misc.

  Context
    (T : Type -> Type)
    `{Categorical.DecoratedFunctor.DecoratedFunctor E T}.

  Theorem cobind_dec {A B} : forall (f : E * A -> B),
      map T (cobind (W := (E ×)) f) ∘ dec T = dec T ∘ map T f ∘ dec T.
  Proof.
    intros.
    unfold_ops @Cobind_env.
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
