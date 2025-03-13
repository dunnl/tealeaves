From Tealeaves Require Export
  Classes.Categorical.Comonad
  Classes.Categorical.DecoratedFunctor
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

End ToMono1.
