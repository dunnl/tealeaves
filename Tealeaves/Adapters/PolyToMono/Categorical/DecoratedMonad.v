From Tealeaves Require Export
  Classes.Categorical.DecoratedTraversableMonad
  Classes.Categorical.DecoratedTraversableMonadPoly
  Adapters.PolyToMono.Categorical.DecoratedFunctor.


Module ToMono1.
  Section ctx.

    Context
      {T: Type -> Type -> Type}
      `{DecoratedMonadPoly T}.

    Import DecoratedFunctor.ToMono1.

    #[export] Instance Bmap_Monad_Hom:
      forall (B1 B2: Type) (f: B1 -> B2),
        Monad_Hom (T B1) (T B2) (fun V => @bmap T _ V B1 B2 f).
    Proof.
      intros.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - unfold bmap.
        unfold_ops @Map2_2.
        typeclasses eauto.
      - intros.
        unfold bmap.
        unfold_ops @Map2_2.
        rewrite dmp_map_ret.
        reflexivity.
      - intros.
        unfold bmap.
        unfold_ops @Map2_2.
        rewrite dmp_map_join.
        reassociate -> on right.
        setoid_rewrite (fun2_map2_map21 (B1 := B1) (F := T)).
        reflexivity.
    Qed.

    #[export] Instance DecoratedMonad_PolyVar:
      forall (B: Type), DecoratedMonad (list B) (T B).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @VDec.
        reassociate -> on left.
        rewrite dmp_dec_ret.
        reassociate <- on left.
        rewrite dmp_map_ret.
        reflexivity.
      - intros.
        unfold_ops @VDec.
        reassociate -> on left.
        rewrite dmp_dec_join.
        reassociate <- on left.
        reassociate <- on left.
        rewrite dmp_map_join.
        reassociate -> near (map2 id (shift2 ∘ map_snd decp)).
        rewrite fun2_map_map.
        reassociate <- on right.
        repeat reassociate -> on right.
        repeat reassociate -> on left.
        fequal.
        repeat reassociate <- on right.
        setoid_rewrite (fun2_map21_map2 (F := T)).
        unfold shift.
        unfold strength.
        unfold_ops @Map2_1.
        reassociate -> on right.
        rewrite polydecnat.
        reassociate <- on right.
        setoid_rewrite (fun2_map_map (F := T)).
        rewrite fun_map_id.
        change (?x ∘ id) with x.
        fequal.
        fequal.
        unfold shift.
        unfold map.
        unfold strength.
        unfold compose.
        ext [l t].
        cbn.
        compose near (decp t) on right.
        rewrite fun2_map_map.
        compose near (decp t) on right.
        rewrite fun2_map_map.
        change (?x ∘ id) with x.
        repeat change (id ∘ ?x) with x.
        change (id ?x) with x.
        unfold shift2, strength2, compose.
        compose near (decp t) on left.
        rewrite fun2_map_map.
        compose near (decp t) on left.
        rewrite fun2_map_map.
        fequal.
        + now ext [l' b].
        + rewrite fun_map_id.
          reflexivity.
    Qed.

  End ctx.
End ToMono1.
