From Tealeaves Require Export
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.Categorical.List
  Backends.LN.Atom
  Functors.List.

Import Product.Notations.
Import Monoid.Notations.
Import List.ListNotations.
Import DecoratedTraversableCommIdemFunctor.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables G ϕ.
#[local] Set Implicit Arguments.


Definition dist_pair
  {b1 v1: Type}
  `{Map G} `{Mult G} `{Pure G}:
  list (G b1) * G v1 -> G (list b1 * v1) :=
  fun '(x, y) => pure (@pair (list b1) v1) <⋆> dist list G x <⋆> y.

Definition dec_bag: forall (A: Type), list A -> list (list A * A) :=
  fun A l => map (pair l) l.

Section lfg.

  Context `{ApplicativeCommutativeIdempotent G} (A: Type).

  Lemma map_dist_pair_nil: forall (ctx: list (G A)) (l: list (G A)),
      l = nil ->
      dist list G (A := (list A) * A) (map dist_pair (map (F := list) (pair ctx) l))
      = pure (A := list (list A * A)) (@nil (list A * A)).
  Proof.
    intros. subst. reflexivity.
  Qed.

  Lemma map_dist_pair: forall (ctx: list (G A)) (l: list (G A)),
      l <> nil ->
      dist list G (A := (list A) * A) (map dist_pair (map (F := list) (pair ctx) l))
      =
        pure (F := G) (fun ctx => map (F := list) (pair ctx))
          <⋆> (dist list G ctx)
          <⋆> dist list G l.
  Proof.
    intros. destruct l.
    - contradiction.
    - clear H3.
      generalize dependent g.
      induction l; intro g.
      + cbn.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
      (* RHS *)
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        reflexivity.
      + rewrite map_list_cons.
        rewrite map_list_cons.
        rewrite dist_list_cons_1.
        rewrite IHl.
        cbn.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite (ap_ci2 (A := list A) (B := A) _ (dist list G ctx) g).
        rewrite app_pure_natural.
        rewrite ap_cidup.
        rewrite map_ap.
        rewrite app_pure_natural.
        rewrite (ap_ci2 (B := list A) (A := A) _ g (dist list G ctx)).
        rewrite app_pure_natural.
        (* RHS *)
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        reflexivity.
  Qed.

  Lemma informative_list_nilb: forall (l: list (G A)),
      {l = nil} + {l <> nil}.
  Proof.
    intros. destruct l.
    - now left.
    - now right.
  Defined.


  Lemma decorate_commute: forall (l: list (G A)),
      map (dec_bag (A := A)) (dist list G l) =
        dist list G (map dist_pair (dec_bag l)).
  Proof.
    intros. induction l.
    - cbn.
      rewrite app_pure_natural.
      reflexivity.
    - cbn.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      (* RHS *)
      rewrite <- ap4.
      rewrite ap2.
      rewrite <- ap4.
      rewrite ap2.
      rewrite ap2.
      rewrite <- ap4.
      rewrite ap2.
      rewrite <- ap4.
      rewrite ap2.
      rewrite ap2.
      destruct (informative_list_nilb l).
      + subst.
        cbn.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap_cidup.
        rewrite app_pure_natural.
        reflexivity.
      + rewrite map_dist_pair; auto.
        rewrite (ap_ci2 (A := A) (B := list A) (pure (compose (compose cons ∘ pair) ∘ cons))
                   a (dist list G l)).
        rewrite app_pure_natural.
        rewrite ap_cidup.
        rewrite map_ap.
        rewrite app_pure_natural.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite dist_list_cons_1.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap_cidup.
        rewrite map_ap.
        rewrite map_ap.
        rewrite map_ap.
        rewrite app_pure_natural.
        rewrite ap_cidup.
        rewrite map_ap.
        rewrite app_pure_natural.
        rewrite (ap_ci2 (A := list A) (B := A)
                   (pure
                      (double_input
                         ∘ (compose (compose double_input)
                              ∘ (compose (evalAt cons)
                                   ∘ (compose (compose ∘ compose)
                                        ∘ (compose (evalAt (map ○ pair)) ∘ compose (compose ∘ compose)
                                             ∘ (double_input ∘ flip (compose (compose cons ∘ pair) ∘ cons))))))))
                   (dist list G l) a).
        rewrite app_pure_natural.
        rewrite ap_cidup.
        rewrite map_ap.
        rewrite app_pure_natural.
        reflexivity.
  Qed.

End lfg.


Section mapci.

End mapci.
