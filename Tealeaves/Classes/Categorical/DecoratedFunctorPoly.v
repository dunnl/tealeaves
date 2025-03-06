From Tealeaves Require Export
  Classes.Categorical.Comonad
  Classes.Categorical.DecoratedFunctor
  Functors.Reader
  Functors.List_Telescoping_General
  Classes.Functor2
  Classes.Monoid
  Functors.List
  Functors.Z2.

Import Monoid.Notations.

(** * <<shift2>> *)
(**********************************************************************)
Definition shift2 {F: Type -> Type -> Type}
  `{Map2 F} {W} `{Monoid_op W} {A1 A2} :
  W * F (W * A1) (W * A2) -> F (W * A1) (W * A2) :=
  map2 (uncurry incr) (uncurry incr) ∘ strength2.

Lemma map2_shift2_preincr
  {F: Type -> Type -> Type}
  `{Map2 F}
  `{! Functor2 F}
  {W} `{Monoid_op W}
  {B1 V1 B2 V2} {g: W * B1 -> B2} {f: W * V1 -> V2} {w: W}:
  map2 g f ∘ shift2 ∘ pair w = map2 (g ⦿ w) (f ⦿ w).
Proof.
  intros.
  ext t.
  unfold shift2.
  unfold compose.
  unfold strength2.
  compose near t on left.
  rewrite (fun2_map_map).
  compose near t on left.
  rewrite (fun2_map_map).
  reflexivity.
Qed.

(** * Poly Decorated functors *)
(**********************************************************************)

(** ** Operations *)
(**********************************************************************)
Class DecoratePoly
  (F: Type -> Type -> Type) :=
  decp: forall (B V: Type), F B V -> F (Z B) (Z2 B V).

#[global] Arguments decp {F}%function_scope {DecoratePoly}
  {B V}%type_scope _.

#[local] Arguments decp {F}%function_scope {DecoratePoly}
  {B V}%type_scope _.

Class PolyDecorateNatural F `{Map2 F} `{DecoratePoly F}: Type :=
  polydecnat: forall (B V B' V': Type) (g: B -> B') (f: V -> V'),
    decp (B := B') (V := V') ∘ map2 g f =
      map2 (map (F := Z) g) (map2 (F := Z2) g f) ∘ decp (B := B) (V := V).

(** ** Typeclass *)
(**********************************************************************)
Class DecoratedFunctorPoly
  (F: Type -> Type -> Type)
  `{Map2 F}
  `{DecoratePoly F} :=
  { dfunp_functor :> Functor2 F;
    dfunp_natural :> PolyDecorateNatural F;
    dfunp_dec_dec: forall (B V: Type),
      decp ∘ decp (B := B) (V := V) = map2 (cojoin (W := Z)) cojoin_Z2 ∘ decp;
    dfunp_dec_extract: forall (B V: Type),
      map2 (extract) (extract) ∘ decp (B := B) (V := V) = @id (F B V);
  }.

Module ToMono.

  Section ctx.

    Context
      {F: Type -> Type -> Type}
      `{DecoratedFunctorPoly F}.

    #[export] Instance Decorate_PolyVar {B}:
      Decorate (list B) (F B) :=
      fun A => (map2 extract id ∘ decp).

    #[export] Instance DecoratedFunctor_PolyVar {B}:
      DecoratedFunctor (list B) (F B).
    Proof.
      constructor.
      - typeclasses eauto.
      - constructor; try typeclasses eauto.
        intros.
        unfold_ops @Map_compose.
        unfold_ops @Decorate_PolyVar.
        unfold_ops @Map2_1.
        reassociate <-.
        rewrite (fun2_map_map).
        reassociate -> on right.
        rewrite (polydecnat (F := F)).
        reassociate <- on right.
        rewrite fun2_map_map.
        rewrite fun_map_id.
        change (id ∘ ?f) with f.
        change (?f ∘ id) with f.
        unfold_ops @Map2_Z2.
        unfold map_Z2.
        rewrite fun_map_id.
        reflexivity.
      - intros.
        unfold_ops @Decorate_PolyVar.
        unfold_ops @Map2_1.
        repeat reassociate <-.
        rewrite (fun2_map_map).
        change (id ∘ ?f) with f.
        change (?f ∘ id) with f.
        change_left
          ( @map2 F H (Z B) (Z2 B (list B * A)) B (Z2 B (list B * A)) (@extract Z Extract_Z B) (@id (Z2 B (list B * A)))
              ∘ (@decp F H0 B (list B * A) ∘ @map2 F H (Z B) (Z2 B A) B (Z2 B A)
              (@extract Z Extract_Z B) (@id (Z2 B A))) ∘
              @decp F H0 B A).
        rewrite (polydecnat (F := F)).
        reassociate <- on left.
        rewrite fun2_map_map.
        change (id ∘ ?f) with f.
        change (?f ∘ id) with f.
        reassociate -> on left.
        rewrite dfunp_dec_dec.
        reassociate <- on left.
        rewrite fun2_map_map.
        fequal.
        fequal.
        { now ext [x y]. }
        { ext [x y].
          unfold compose.
          cbn.
          compose near x.
          now rewrite decorate_prefix_list_extract.
        }
      - intros.
        unfold_ops @Decorate_PolyVar.
        unfold_ops @Map2_1.
        reassociate <- on left.
        rewrite fun2_map_map.
        change (id ∘ ?f) with f.
        change (?f ∘ id) with f.
        rewrite dfunp_dec_extract.
        reflexivity.
    Qed.

  End ctx.

End ToMono.
