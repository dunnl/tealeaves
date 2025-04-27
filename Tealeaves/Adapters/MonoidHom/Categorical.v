From Tealeaves Require Export
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.DecoratedMonad
  Classes.Categorical.DecoratedTraversableFunctor
  Classes.Categorical.DecoratedTraversableMonad
  Classes.Monoid
  Functors.Writer.

Import Applicative.Notations.
Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

Section dtm_to_dtm.

  Context
    {T: Type -> Type}
    `{Dec_orig: Decorate W1 T}
    `{Monoid W1}
    `{Monoid W2}
    (ϕ: W1 -> W2)
    `{! Monoid_Morphism W1 W2 ϕ}.

  Context
    `{Map_T: Map T}
    `{Dist_T: ApplicativeDist T}
    `{Join_T: Join T}
    `{Return_T: Return T}.

  #[export] Instance Decorate_Monoid_Morphism: Decorate W2 T :=
    fun A t => map (F := T) (map_fst ϕ) (dec T t).

  #[export] Instance Natural_Decorate_Monoid_Morphism `{! DecoratedFunctor W1 T}:
    Natural (@dec W2 T Decorate_Monoid_Morphism).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Decorate_Monoid_Morphism.
      unfold_ops @Map_compose.
      ext t.
      unfold compose at 1.
      compose near (dec (Decorate := Dec_orig) T (A := A) t).
      rewrite (fun_map_map (F := T)).
      unfold compose at 2.
      compose near t on right.
      rewrite <- (natural (ϕ := @dec W1 T _)).
      unfold compose at 2.
      compose near (dec (Decorate := Dec_orig) T (A := A) t) on right.
      unfold_ops @Map_compose.
      rewrite (fun_map_map (F := T)).
      rewrite product_map_commute.
      reflexivity.
  Qed.

  #[export] Instance DecoratedFunctor_Monoid_Morphism `{! DecoratedFunctor W1 T}:
    DecoratedFunctor W2 T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - admit.
    - admit.
  Admitted.


  #[export] Instance DecoratedMonad_Monoid_Morphism `{! DecoratedMonad W1 T}:
    DecoratedMonad W2 T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold compose. admit.
    - admit.
  Admitted.


  #[export] Instance DecoratedTraversableFunctor_Monoid_Morphism
    `{! DecoratedTraversableFunctor W1 T}:
    DecoratedTraversableFunctor W2 T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      admit.
  Admitted.


  #[export] Instance DecoratedTraversableMonad_Monoid_Morphism
    `{! DecoratedTraversableMonad W1 T}:
    DecoratedTraversableMonad W2 T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

End dtm_to_dtm.
