From Tealeaves Require Import
  Classes.Categorical.DecoratedMonad
  Classes.Kleisli.DecoratedMonad
  Adapters.CategoricalToKleisli.DecoratedMonad
  Adapters.KleisliToCategorical.DecoratedMonad.

Import Product.Notations.
Import Kleisli.Monad.Notations.
Import Kleisli.Comonad.Notations.
Import Kleisli.DecoratedMonad.Notations.

#[local] Generalizable Variable T W.

(** * Categorical ~> Kleisli ~> Categorical *)
(**********************************************************************)
Module decorated_monad_categorical_kleisli_categorical.

  Context
    `{mapT: Map T}
    `{decT: Decorate W T}
    `{joinT: Join T}
    `{retT: Return T}
    `{Monoid W}
    `{! Categorical.DecoratedMonad.DecoratedMonad W T}.

  Definition bindd': Bindd W T T :=
    DerivedOperations.Bindd_Categorical W T.

  Definition map2: Map T :=
    DerivedOperations.Map_Bindd W T T (Bindd_WTU := bindd').
  Definition dec2: Decorate W T :=
    DerivedOperations.Decorate_Bindd W T (Bindd_WTT := bindd').
  Definition join2: Join T :=
    DerivedOperations.Join_Bindd W T (Bindd_WTT := bindd').

  Goal mapT = map2.
  Proof.
    unfold map2.
    unfold_ops @DerivedOperations.Map_Bindd.
    unfold bindd.
    unfold bindd'.
    unfold_ops @DerivedOperations.Bindd_Categorical.
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

  Goal decT = dec2.
  Proof.
    unfold dec2.
    unfold_ops @DerivedOperations.Decorate_Bindd.
    unfold bindd.
    unfold bindd'.
    unfold_ops @DerivedOperations.Bindd_Categorical.
    ext A.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

  Goal joinT = join2.
  Proof.
    unfold join2.
    unfold_ops @DerivedOperations.Join_Bindd.
    unfold bindd.
    unfold bindd'.
    unfold_ops @DerivedOperations.Bindd_Categorical.
    ext A.
    reassociate ->.
    rewrite (dfun_dec_extract (E := W) (F := T)).
    reflexivity.
  Qed.

End decorated_monad_categorical_kleisli_categorical.

(** * Kleisli ~> Categorical ~> Kleisli *)
(**********************************************************************)
Module decorated_monad_kleisli_categorical_kleisli.

  Context
    `{binddT: Bindd W T T}
    `{retT: Return T}
    `{Monoid W}
    `{@Kleisli.DecoratedMonad.DecoratedMonad W T _ _ retT binddT}.

  Definition map': Map T :=
    DerivedOperations.Map_Bindd W T T.
  Definition dec': Decorate W T :=
    DerivedOperations.Decorate_Bindd W T.
  Definition join': Join T :=
    DerivedOperations.Join_Bindd W T.

  Definition bindd2: Bindd W T T :=
    DerivedOperations.Bindd_Categorical W T
      (Map_T := map') (Join_T := join') (Decorate_WT := dec').

  Goal binddT = bindd2.
  Proof.
    unfold bindd2.
    unfold_ops @DerivedOperations.Bindd_Categorical.
    unfold map, map', dec, dec', join, join'.
    unfold_ops @DerivedOperations.Map_Bindd.
    unfold_ops @DerivedOperations.Join_Bindd.
    unfold_ops @DerivedOperations.Decorate_Bindd.
    ext A B f.
    unfold_compose_in_compose.
    rewrite (kdm_bindd2 (T := T)).
    rewrite (kdm_bindd2 (T := T)).
    fequal.
    rewrite kc5_50.
    change (ret (T := T) (A := W * A)) with
      (ret (T:=T) (A := W * A) ∘ id).
    rewrite kc5_51.
    rewrite <- (natural (ϕ := @extract (W ×) _)).
    rewrite kc1_01.
    reflexivity.
  Qed.

End decorated_monad_kleisli_categorical_kleisli.
