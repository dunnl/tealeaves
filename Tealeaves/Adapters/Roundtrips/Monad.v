From Tealeaves Require Import
  Adapters.CategoricalToKleisli.Monad
  Adapters.KleisliToCategorical.Monad.

Import Product.Notations.
Import Functor.Notations.
Import Kleisli.Monad.Notations.

#[local] Generalizable Variable T.

(** * Categorical ~> Kleisli ~> Categorical *)
(**********************************************************************)
Section categorical_to_kleisli_to_categorical.

  Context
    `{Return_T: Return T}
    `{Map_T: Map T}
    `{Join_T: Join T}
    `{! Categorical.Monad.Monad T}.

  (* Derive the Kleisli operation *)
  Definition bind': Bind T T :=
    CategoricalToKleisli.Monad.DerivedOperations.Bind_Categorical T.

  (* Re-derive the categorical operations *)
  Definition map2: Map T :=
    Kleisli.Monad.DerivedOperations.Map_Bind T T
      (Bind_TU := bind').

  Definition join2: Join T :=
    Adapters.KleisliToCategorical.Monad.DerivedOperations.Join_Bind T
      (Bind_TT := bind').

  Lemma map_roundtrip: Map_T = map2.
  Proof.
    ext A B f.
    unfold map2.
    unfold DerivedOperations.Map_Bind.
    unfold bind.
    unfold bind'.
    unfold DerivedOperations.Bind_Categorical.
    rewrite <- (fun_map_map (F := T)).
    reassociate <- on right.
    rewrite (mon_join_map_ret (T := T)).
    reflexivity.
  Qed.

  Lemma join_roundtrip: Join_T = join2.
  Proof.
    ext A.
    unfold join2.
    unfold DerivedOperations.Join_Bind.
    unfold bind.
    unfold bind'.
    unfold DerivedOperations.Bind_Categorical.
    rewrite (fun_map_id (F := T)).
    reflexivity.
  Qed.

End categorical_to_kleisli_to_categorical.

(** * Kleisli ~> Categorical ~> Kleisli *)
(**********************************************************************)
Section kleisli_to_categorical_to_kleisli.

  Context
    `{Return_T: Return T}
    `{Bind_TT: Bind T T}
    `{! Kleisli.Monad.Monad T}.

  Definition map': Map T := DerivedOperations.Map_Bind T T.
  Definition join': Join T := DerivedOperations.Join_Bind T.

  Definition bind2: Bind T T :=
    DerivedOperations.Bind_Categorical T
      (map_T := map') (join_T := join').

  Goal Bind_TT = bind2.
  Proof.
    ext A B f.
    unfold bind2.
    unfold DerivedOperations.Bind_Categorical.
    unfold join.
    unfold join'.
    unfold DerivedOperations.Join_Bind.
    unfold map.
    unfold map'.
    unfold DerivedOperations.Map_Bind.
    unfold_compose_in_compose.
    rewrite (kmon_bind2 (T := T)).
    unfold kc.
    reassociate <- on right.
    rewrite (kmon_bind0 (T := T)).
    reflexivity.
  Qed.

End kleisli_to_categorical_to_kleisli.

