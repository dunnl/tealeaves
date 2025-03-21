From Tealeaves Require Export
  Classes.Categorical.Comonad
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.RightComodule
  Classes.Categorical.DecoratedFunctorPoly
  Functors.List.

Module ToMono1.

  Section ctx.

    Context
      {F: Type -> Type -> Type}
      `{DecoratedFunctorPoly F}.

    #[export] Instance Decorate_PolyVar {B}:
      Decorate (list B) (F B) :=
      fun A => (map2 extract id ∘ decp).

    Instance Natural_dec {B}: Natural (@dec (list B) (F B) Decorate_PolyVar).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
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

        change (?f ∘ id) with f.
        unfold_ops @Map2_Z2.
        unfold map_Z2.
        rewrite fun_map_id.
        reflexivity.
    Qed.

    Lemma dec_dec {B}:
      forall A : Type, dec (F B) ∘ dec (F B) = map (F := F B) (cojoin (W := prod (list B))) ∘ dec (F B) (A := A).
    Proof.
      intros.
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
    Qed.

    #[export] Instance DecoratedFunctor_PolyVar {B}:
      DecoratedFunctor (list B) (F B).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - apply dec_dec.
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

End ToMono1.

Module ToMono2.

  Section ctx.

    Context
      {F: Type -> Type -> Type}
      `{DecoratedFunctorPoly F}.

    #[export] Instance Decorate_PolyVar2 {V}:
      RightCoaction (fun B => F B V) Z :=
      fun A => (map2 id extract ∘ decp).

    #[export] Instance Natural_Decorate_PolyVar2 {V}:
      Natural (@right_coaction (fun B : Type => F B V) Z Decorate_PolyVar2).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Decorate_PolyVar2.
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

    #[export] Instance DecoratedFunctor_PolyVar2 {V}:
      RightComodule (fun B => F B V) Z.
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Decorate_PolyVar2.
        reassociate <- on left.
        rewrite fun2_map22_map2.
        change (?f ∘ id) with f.
        apply dfunp_dec_extract.
      - intros.
        unfold_ops @Decorate_PolyVar2.
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
