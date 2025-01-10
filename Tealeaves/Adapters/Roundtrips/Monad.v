From Tealeaves Require Export
  Adapters.CategoricalToKleisli.Monad
  Adapters.KleisliToCategorical.Monad.

Import Product.Notations.
Import Functor.Notations.
Import Kleisli.Monad.Notations.

#[local] Generalizable Variable T.

(** * Categorical ~> Kleisli ~> Categorical *)
(******************************************************************************)
Module Roundtrip1.

  Context
    `{ret_T: Return T}
    `{map_T: Map T}
    `{join_T: Join T}
    `{! Categorical.Monad.Monad T}.

  #[local] Instance bind_derived: Bind T T :=
    CategoricalToKleisli.Monad.ToKleisli.Bind_Join T.

  Definition map2 :=  Map_Bind.
  About Map_Bind.
  Definition join2 := Join_Bind T.

  Goal map1 = map2.
  Proof.
    ext A B f.
    unfold map2, Map_Bind,
      bind, bind_derived, ToKleisli.Bind_Join.
    rewrite <- (fun_map_map (F := T)).
    reassociate <-.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

  Goal join1 = join2.
  Proof.
    ext A t.
    unfold join2, Join_Bind,
      bind, bind_derived, ToKleisli.Bind_Join.
    rewrite (fun_map_id (F := T)).
    reflexivity.
  Qed.

End Roundtrip1.

(** * Kleisli ~> Categorical ~> Kleisli *)
(******************************************************************************)
Section RoundTrip2.

  Context
    `{Return T}
    `{bind1 : Bind T T}
    `{! Kleisli.Monad.Monad T}.

  Definition map_derived := Map_Bind.
  Definition join_derived := Join_Bind.
  Definition bind2 : Bind T T := ToKleisli.Bind_Join T (H := Map_Bind).

  Goal bind1 = bind2.
  Proof.
    ext A B f.
    unfold bind2, ToKleisli.Bind_Join.
    unfold join, Join_Bind.
    unfold map, Map_Bind.
    unfold_compose_in_compose.
    rewrite (kmon_bind2 (T := T)).
    fequal. unfold kc1.
    reassociate <-.
    rewrite (kmon_bind0 (T := T)).
    reflexivity.
  Qed.

End RoundTrip2.
