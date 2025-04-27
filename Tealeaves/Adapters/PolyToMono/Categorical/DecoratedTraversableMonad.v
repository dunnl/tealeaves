From Tealeaves Require Export
  Classes.Categorical.DecoratedTraversableMonad
  Classes.Categorical.DecoratedTraversableMonadPoly
  Adapters.PolyToMono.Categorical.DecoratedFunctor
  Adapters.PolyToMono.Categorical.DecoratedMonad
  Adapters.PolyToMono.Categorical.TraversableMonad
  Adapters.PolyToMono.Categorical.TraversableFunctor.

Import PolyToMono.Categorical.DecoratedFunctor.ToMono1.
Import PolyToMono.Categorical.DecoratedMonad.ToMono1.
Import PolyToMono.Categorical.TraversableFunctor.ToMono.
Import PolyToMono.Categorical.TraversableMonad.ToMono.

#[local] Generalizable Variables T.

Module ToMono.
  Section toMono.

    Context `{DecoratedTraversableMonadPoly T}.

    #[export] Instance: forall B, DecoratedTraversableMonad (list B) (T B).
    Proof.
      intros. constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - typeclasses eauto.
    Qed.

  End toMono.
End ToMono.
