From Tealeaves Require Export
  Adapters.CategoricalToKleisli.DecoratedMonad
  Adapters.KleisliToCategorical.DecoratedMonad.

Import Product.Notations.
Import Monad.Notations.
Import Kleisli.Monad.Notations.

#[local] Generalizable Variable T W.

Import Kleisli.DecoratedMonad.DerivedInstances.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module Roundtrip1.

  Context
    `{mapT : Map T}
    `{decT : Decorate W T}
    `{joinT : Join T}
    `{retT : Return T}
    `{Monoid W}
    `{! Categorical.DecoratedMonad.DecoratedMonad W T}.

  #[local] Instance bindd' : Bindd W T T := ToKleisli.Bindd_dec W T.

  Definition map' : Map T := Map_Bindd (W := W) T.
  Definition dec' : Decorate W T := Decorate_Bindd W T.
  Definition join' : Join T := Join_Bindd W T.

  Goal mapT = map'.
  Proof.
    unfold map'. unfold_ops @Map_Bindd.
    unfold bindd, bindd'.
    unfold_ops @ToKleisli.Bindd_dec.
    ext A B f.
    rewrite <- (fun_map_map (F := T)).
    reassociate <-.
    reassociate ->.
    rewrite (dfun_dec_extract (E := W) (F := T)).
    rewrite <- (fun_map_map (F := T)).
    reassociate <-.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

  Goal decT = dec'.
  Proof.
    unfold dec'. unfold_ops @Decorate_Bindd.
    unfold bindd, bindd'.
    unfold_ops @ToKleisli.Bindd_dec.
    ext A.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

  Goal joinT = join'.
  Proof.
    unfold join'. unfold_ops @Join_Bindd.
    unfold bindd, bindd'.
    unfold_ops @ToKleisli.Bindd_dec.
    ext A.
    reassociate ->.
    rewrite (dfun_dec_extract (E := W) (F := T)).
    reflexivity.
  Qed.

End Roundtrip1.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Module Roundtrip2.

  Context
    `{binddT : Bindd W T T}
    `{retT : Return T}
    `{Monoid W}
    `{@Kleisli.DecoratedMonad.DecoratedMonad W T retT binddT _ _}.

  #[local] Instance map' : Map T := Map_Bindd (W := W) T.
  #[local] Instance dec' : Decorate W T := Decorate_Bindd W T.
  #[local] Instance join' : Join T := Join_Bindd W T.

  Definition bindd' : Bindd W T T := ToKleisli.Bindd_dec W T.

  Goal binddT = bindd'.
  Proof.
    unfold bindd'. unfold_ops @ToKleisli.Bindd_dec.
    unfold map, map', dec, dec', join, join'.
    unfold_ops @Map_Bindd.
    unfold_ops @Join_Bindd.
    unfold_ops @Decorate_Bindd.
    ext A B f.
    unfold_compose_in_compose.
    rewrite (kmond_bindd2 (T := T)).
    rewrite (kmond_bindd2 (T := T)).
    fequal.
    rewrite (kc5_50 T).
    change (ret T (W * A)) with (ret T ( W * A) ∘ id).
    rewrite (kc5_54 T).
    change (Map_Env ?x) with (Map_prod x) in *.
    (* TODO ^^ Fix this *)
    rewrite <- (natural (ϕ := @extract (W ×) _)).
    Search kc4 extract.
    rewrite (DerivedInstances.kc4_04).
    reflexivity.
  Qed.

End Roundtrip2.
