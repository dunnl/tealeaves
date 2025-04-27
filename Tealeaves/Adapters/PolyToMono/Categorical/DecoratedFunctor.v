From Tealeaves Require Export
  Classes.Categorical.Comonad
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.RightComodule
  Classes.Categorical.DecoratedFunctorPoly
  Functors.List.

(** * Parameterized Decorated Functor to Decorated in Variables *)
(**********************************************************************)
Module ToMono1.

  Section ctx.

    Context
      {F: Type -> Type -> Type}
      `{DecoratedFunctorPoly F}.

    #[export] Instance VDec {B}:
      Decorate (list B) (F B) :=
      fun A => (map2 extract id ∘ decp).

    Instance Natural_dec {B}: Natural (@dec (list B) (F B) VDec).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Map_compose.
        unfold_ops @VDec.
        unfold_ops @Map2_1.
        reassociate <-.
        rewrite (fun2_map_map).
        reassociate -> on right.
        rewrite (polydecnat (F := F)).
        reassociate <- on right.
        rewrite fun2_map_map.
        rewrite fun_map_id.

        change (?f ∘ id) with f.
        unfold_ops @Map2_L.
        unfold map_L.
        rewrite fun_map_id.
        reflexivity.
    Qed.

    Lemma dec_dec {B}:
      forall (A: Type),
        dec (F B) ∘ dec (F B) =
          map (F := F B) (cojoin (W := prod (list B))) ∘ dec (F B) (A := A).
    Proof.
      intros.
      unfold_ops @VDec.
      unfold_ops @Map2_1.
      repeat reassociate <-.
      rewrite (fun2_map_map).
      change (id ∘ ?f) with f.
      change (?f ∘ id) with f.
      change_left
        ( @map2 F H (Z B) (L B (list B * A)) B (L B (list B * A)) (@extract Z Extract_Z B) (@id (L B (list B * A)))
            ∘ (@decp F H0 B (list B * A) ∘ @map2 F H (Z B) (L B A) B (L B A)
                 (@extract Z Extract_Z B) (@id (L B A))) ∘
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
    Qed.

    #[export] Instance DecoratedFunctor_V {B}:
      DecoratedFunctor (list B) (F B).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - apply dec_dec.
      - intros.
        unfold_ops @VDec.
        unfold_ops @Map2_1.
        reassociate <- on left.
        rewrite fun2_map_map.
        change (id ∘ ?f) with f.
        change (?f ∘ id) with f.
        rewrite dfunp_dec_extract.
        reflexivity.
    Qed.

    #[export] Instance Bmap_Decorated_Hom:
      forall (B1 B2: Type) (f: B1 -> B2),
        DecoratePreservingTransformationHet
          (F B1) (F B2) (map (F := list) f) (fun V => @bmap F _ V B1 B2 f).
    Proof.
      intros.
      constructor.
      - intros.
        unfold bmap.
        rewrite (fun2_map22_map21).
        unfold dec.
        unfold VDec.
        reassociate <- on left.
        rewrite fun2_map_map.
        reassociate -> on right.
        unfold_ops @Map2_2.
        rewrite polydecnat.
        reassociate <- on right.
        rewrite fun2_map_map.
        fequal.
        fequal.
        rewrite <- (natural (ϕ := @extract _ _)).
        reflexivity.
      - typeclasses eauto.
    Qed.

  End ctx.

End ToMono1.

(** * Parameterized Decorated Functor to Decorated in Binders *)
(**********************************************************************)
Module ToMono2.

  Section ctx.

    Context
      {F: Type -> Type -> Type}
      `{DecoratedFunctorPoly F}.

    #[export] Instance BDec {V}:
      RightCoaction (fun B => F B V) Z :=
      fun A => (map2 id extract ∘ decp).

    #[export] Instance Natural_BDec {V}:
      Natural (@right_coaction (fun B: Type => F B V) Z BDec).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @BDec.
        unfold_ops @Map_compose.
        unfold_ops @Map2_2.
        reassociate <- on left.
        unfold_compose_in_compose.
        rewrite (fun2_map_map (F := F) (map2_F := H)).
        reassociate -> on right.
        rewrite polydecnat.
        reassociate <- on right.
        rewrite (fun2_map_map (F := F) (map2_F := H)).
        fequal.
        fequal.
        unfold compose; ext [l a].
        reflexivity.
    Qed.

    #[export] Instance DecoratedFunctor_B {V}:
      RightComodule (fun B => F B V) Z.
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @BDec.
        reassociate <- on left.
        rewrite fun2_map22_map2.
        change (?f ∘ id) with f.
        apply dfunp_dec_extract.
      - intros.
        unfold_ops @BDec.
        reassociate <- on right.
        rewrite fun2_map22_map2.
        change (?f ∘ id) with f.
        change_left (map2 id extract ∘ (decp ∘ map2 id extract) ∘ decp (B := A) (V := V)).
        rewrite polydecnat.
        reassociate <- on left.
        rewrite fun2_map_map.
        change (id ∘ ?f) with f.
        reassociate -> on left.
        rewrite dfunp_dec_dec.
        reassociate <- on left.
        rewrite fun2_map_map.
        rewrite fun_map_id.
        change (id ∘ ?f) with f.
        fequal.
        fequal.
        unfold compose; ext [l a].
        reflexivity.
    Qed.
  End ctx.

End ToMono2.
