From Tealeaves Require Export
  Classes.Algebraic.Traversable.Monad.

(** * The monad operations as <<traverse>>-respecting morphisms *)
(******************************************************************************)
Section traverable_monad_theory.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma dist_ret_spec :
    TraversableMorphism (T := (fun A => A)) (U := T) (@ret T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. now rewrite (trvmon_ret T).
  Qed.

  Lemma dist_join_spec :
      TraversableMorphism (T := T ∘ T) (U := T) (@join T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. now rewrite <- (trvmon_join T).
  Qed.

End traverable_monad_theory.
