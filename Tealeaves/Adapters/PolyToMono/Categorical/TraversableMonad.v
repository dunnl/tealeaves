From Tealeaves Require Import
  Classes.Categorical.TraversableMonad2
  Classes.Categorical.TraversableMonad
  Adapters.PolyToMono.Categorical.TraversableFunctor.

#[local] Generalizable Variables T G A.

Import Functor2.Notations.
Import PolyToMono.Categorical.TraversableFunctor.ToMono.

(** ** Single-Argument Traversable Functor Instances *)
(**********************************************************************)
Module ToMono.

  Section mono.

    Context
      `{TraversableMonad2 T}.

    #[export] Instance TraversableMonad_Dist2_1 {B}:
      TraversableMonad (T B).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Dist2_1.
        reassociate -> on left.
        rewrite dmp_map_ret.
        reassociate <- on left.
        rewrite (xxx_dist2_ret (T := T) B A (G := G)).
        reflexivity.
      - intros.
        unfold_ops @Dist2_1.
        reassociate -> on left.
        rewrite dmp_map_join.
        reassociate <- on left.
        rewrite (xxx_dist2_join (T := T) B A (G := G)).
        reassociate -> on left.
        unfold_compose_in_compose.
        setoid_rewrite fun2_map_map.
        reassociate -> on right.
        reassociate -> on right.
        rewrite fun2_map2_map21.
        reflexivity.
    Qed.

  End mono.

End ToMono.
