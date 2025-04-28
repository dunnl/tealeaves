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

  Lemma fun_map_map_pw `{Functor F}:
    forall (A B C : Type) (f : A -> B) (g : B -> C) (t: F A),
      map g (map f t) = map (g ∘ f) t.
  Proof.
    intros. compose near t on left.
    now rewrite fun_map_map.
  Qed.

  #[export] Instance DecoratedFunctor_Monoid_Morphism `{! DecoratedFunctor W1 T}:
    DecoratedFunctor W2 T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      unfold_ops @Decorate_Monoid_Morphism.
      unfold compose.
      ext t.
      compose near (dec (Decorate := Dec_orig) T t).
      rewrite <- (natural (ϕ := @dec W1 T _)).
      unfold compose.
      unfold_ops @Map_compose.
      rewrite fun_map_map_pw.
      compose near t.
      rewrite dfun_dec_dec.
      unfold compose at 2.
      rewrite fun_map_map_pw.
      unfold compose at 4.
      rewrite fun_map_map_pw.
      fequal.
      ext [w a].
      unfold compose. cbn.
      reflexivity.
    - intros.
      unfold_ops @Decorate_Monoid_Morphism.
      unfold compose.
      ext t.
      rewrite fun_map_map_pw.
      assert (cut: extract ∘ map_fst ϕ = extract (A := A)).
      { now ext [w a]. }
      rewrite cut.
      compose near t on left.
      now rewrite dfun_dec_extract.
  Qed.

  #[export] Instance DecoratedMonad_Monoid_Morphism `{! DecoratedMonad W1 T}:
    DecoratedMonad W2 T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      unfold_ops @Decorate_Monoid_Morphism.
      unfold compose.
      ext a.
      compose near a.
      rewrite dmon_ret.
      unfold compose.
      compose near (Ƶ:W1, a) on left.
      rewrite (natural (ϕ := @ret T _)).
      unfold compose.
      cbn.
      now rewrite (monmor_unit (src := W1)).
    - intros.
      unfold_ops @Decorate_Monoid_Morphism.
      unfold compose.
      ext t.
      compose near t on left.
      rewrite dmon_join.
      unfold compose.
      compose near ((map (shift T)
                       (dec (Decorate := Dec_orig)
                          T (map (F := T) (dec (Decorate := Dec_orig) T) t)))).
      rewrite natural.
      unfold compose.
      unfold_ops @Map_compose.
      repeat rewrite fun_map_map_pw.
      change (?f ○ ?g) with (f ∘ g).
      rewrite <- (fun_map_map _ _ _ (dec T)).
      unfold compose at 3.
      compose near (map (dec (Decorate := Dec_orig) T) t).
      rewrite <- (natural (ϕ := @dec W1 T _)).
      unfold compose.
      unfold_ops @Map_compose.
      rewrite fun_map_map_pw.
      fequal.
      fequal.
      ext [w1 t'].
      unfold compose.
      unfold shift.
      unfold compose.
      cbn.
      rewrite fun_map_map_pw.
      rewrite fun_map_map_pw.
      rewrite fun_map_map_pw.
      unfold id.
      rewrite fun_map_map_pw.
      fequal.
      ext [w1' a].
      unfold compose. cbn.
      now rewrite (monmor_op (src := W1)).
  Qed.

  #[export] Instance DecoratedTraversableFunctor_Monoid_Morphism
    `{! DecoratedTraversableFunctor W1 T}:
    DecoratedTraversableFunctor W2 T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      unfold_ops @Decorate_Monoid_Morphism.
      unfold compose.
      ext t.
      rewrite fun_map_map_pw.
      change (?f ○ ?g) with (f ∘ g).
      rewrite <- (fun_map_map _ _ _ (dec T)).
      unfold compose.
      compose near t on right.
      rewrite <- dtfun_compat.
      unfold compose.
      compose near (map strength (dec (Decorate := Dec_orig) T t)).
      change (map (map (map_fst (Y := ?Y) ϕ))) with (map (F := G ∘ T) (map_fst (Y := Y) ϕ)).
      rewrite (natural (ϕ := @dist T _ G _ _ _)).
      unfold compose.
      unfold_ops @Map_compose.
      rewrite fun_map_map_pw.
      fequal.
      fequal.
      ext [w ga].
      unfold compose.
      cbn.
      rewrite fun_map_map_pw.
      fequal.
  Qed.

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
