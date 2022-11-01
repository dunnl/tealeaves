From Tealeaves Require Export
  Classes.Algebraic.DT.Monad
  Classes.Kleisli.DT.Monad
  Classes.Kleisli.Monad
  Classes.Kleisli.Decorated.Functor
  Classes.Kleisli.Decorated.Monad
  Classes.Kleisli.Traversable.Functor
  Classes.Kleisli.Traversable.Monad
  Classes.Kleisli.DT.Monad.

From Tealeaves Require
  Theory.Algebraic.Decorated.Functor.ToKleisli
  Theory.Algebraic.Decorated.Monad.ToKleisli
  Theory.Algebraic.Traversable.Functor.ToKleisli
  Theory.Algebraic.Traversable.Monad.ToKleisli
  Theory.Algebraic.DT.Functor.ToKleisli.

Import Strength.Notations.
Import Algebraic.Monad.Notations.
Import Product.Notations.
Import Monoid.Notations.
Import Algebraic.Traversable.Functor.Notations.
Import Kleisli.DT.Monad.Notations.

#[local] Generalizable Variables T F G W A B C.

(** * Kleisli presentation of D-T monads *)
(******************************************************************************)

(** ** Lifting operation <<binddt>> and Kleisli composition  *)
(******************************************************************************)
Module Operation.
  Section binddt.

    Context
      (T : Type -> Type)
        `{Fmap T} `{Decorate W T} `{Dist T} `{Join T}.

    #[export] Instance Binddt_alg : Binddt W T T :=
      fun G A B `{Fmap G} `{Pure G} `{Mult G}
        (f : W * A -> G (T B)) =>
        fmap G (join T) ∘ dist T G ∘ fmap T f ∘ dec T.

  End binddt.
End Operation.

#[local] Tactic Notation "bring" constr(x) "and" constr(y) "together" :=
  change (?f ∘ x ∘ y ∘ ?g) with (f ∘ (x ∘ y) ∘ g).

Section adapter.

  Import Operation.

  Context
    (T : Type -> Type)
    `{Algebraic.DT.Monad.DecoratedTraversableMonad W T}.

  Context
    (G1 : Type -> Type) `{Fmap G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
    (G2 : Type -> Type) `{Fmap G2} `{Pure G2} `{Mult G2} `{! Applicative G2}.


  Definition kcompose_dtm_alt :=
    fun `(g : W * B -> G2 (T C))
      `(f : W * A -> G1 (T B))
    => (fmap G1 ((fmap G2 (μ T))
                        ∘ δ T G2
                        ∘ fmap T (g ∘ μ (W ×))
                        ∘ σ T
                        ∘ fmap (W ×) (dec T)))
              ∘ σ G1
              ∘ cobind (W ×) f.

  Lemma equiv' :
    forall  `(g : W * B -> G2 (T C))
       `(f : W * A -> G1 (T B)),
    g ⋆dtm f =
      kcompose_dtm_alt g f.
  Proof.
    intros. unfold kcompose_dtm.
    unfold_ops @Binddt_alg.
    ext [w a].
    unfold kcompose_dtm_alt.
    unfold compose at 6. cbn.
    unfold compose at 6.
    cbn. compose near (f (w, a)) on right.
    rewrite (fun_fmap_fmap G1).
    repeat fequal.
    ext t.
    unfold compose. cbn.
    compose near (dec T t).
    rewrite (fun_fmap_fmap T).
    unfold compose.
    repeat fequal.
    now ext [w' b].
  Qed.

End adapter.

(** ** Functoriality of [binddt] *)
(******************************************************************************)
Module Instance.

  Import Operation.
  Import Algebraic.Monad.ToKleisli.Operation.
  Import Algebraic.Monad.ToKleisli.Instance.
  Import Algebraic.Decorated.Functor.ToKleisli.Operation.
  Import Algebraic.Decorated.Functor.ToKleisli.Instance.
  Import Algebraic.Decorated.Monad.ToKleisli.Operation.
  Import Algebraic.Decorated.Monad.ToKleisli.Instance.
  Import Algebraic.Traversable.Functor.ToKleisli.Operation.
  Import Algebraic.Traversable.Functor.ToKleisli.Instance.
  Import Algebraic.Traversable.Monad.ToKleisli.Operation.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Algebraic.DT.Monad.DecoratedTraversableMonad W T}.

    Theorem kdtm_binddt1_T {A} : binddt T (fun A => A) (ret T ∘ extract (prod W)) = @id (T A).
    Proof.
      introv. unfold_ops @Binddt_alg.
      change (fmap (fun A => A) ?f) with f.
      rewrite (dist_unit T).
      change_left (bindd T (η T ∘ extract (prod W) (A := A))).
      ext t. now rewrite (kmond_bindd1 T).
    Qed.

    Theorem kdtm_binddt0_T : forall
        (A B : Type)
        (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G} `{! Applicative G}
        (f : W * A -> G (T B)),
        binddt T G f ∘ η T = f ∘ η (prod W).
    Proof.
      intros.
      unfold_ops @Binddt_alg.
      reassociate -> on left.
      rewrite (dmon_ret W T).
      reassociate <- on left.
      reassociate -> near (η T).
      rewrite (natural (ϕ := @ret T _)).
      unfold_ops @Fmap_I.
      reassociate <- on left.
      reassociate -> near (η T).
      rewrite (trvmon_ret T).
      rewrite (fun_fmap_fmap G).
      rewrite (mon_join_ret T).
      rewrite (fun_fmap_id G).
      reflexivity.
    Qed.

    Section binddt_binddt.

      Context
        {A B C : Type}
        (G1 : Type -> Type) `{Fmap G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
        (G2 : Type -> Type) `{Fmap G2} `{Pure G2} `{Mult G2} `{! Applicative G2}
        (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)).

      Lemma binddt_binddt1 :
        (fmap G1 (dec T ∘ μ T) ∘ δ T G1 : T (G1 (T B)) -> G1 (T (W * B)))
        = fmap G1 (fmap T (μ (prod W)) ∘ μ T ∘ fmap T (σ T ∘ fmap (prod W) (dec T)))
            ∘ δ T G1 ∘ fmap T (σ G1) ∘ dec T.
      Proof.
        rewrite (dmon_join W T). unfold shift.
        change (?f ∘ δ T G1 ∘ fmap T (σ G1) ∘ dec T)
          with (f ∘ (δ T G1 ∘ fmap T (σ G1) ∘ dec T)).
        rewrite (dtfun_compat W T (G := G1)).
        reassociate <- on right. fequal.
        rewrite (fun_fmap_fmap G1).
        rewrite (natural (ϕ := @join T _)).
        fequal. rewrite <- (fun_fmap_fmap T _ _ _ _ (σ T)).
        repeat reassociate <- on right.
        change (fmap T (fmap (prod W) (dec T) (A := ?A)))
          with (fmap (T ∘ (W ×)) (dec T) (A := A)).
        reassociate -> near (dec T).
        #[local] Set Keyed Unification.
        rewrite (natural (ϕ := @dec W T _) (dec T)).
        do 2 reassociate <-.
        reassociate -> near (fmap T (σ T)).
        now rewrite (fun_fmap_fmap T).
        #[local] Unset Keyed Unification.
      Qed.

      (* Note that we *cannot* immediately cancel out the right-most two <<dec T>> sub-expressions *)
      Lemma binddt_binddt2 :
        fmap G1 (fmap T g ∘ dec T ∘ μ T) ∘ δ T G1 ∘ fmap T f ∘ dec T =
          fmap G1 (μ T ∘ fmap T (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))) ∘ δ T G1
            ∘ fmap T (σ G1 ∘ cobind (prod W) f) ∘ dec T.
      Proof.
        rewrite <- (fun_fmap_fmap T _ _ _ (cobind (W ×) f)).
        do 4 reassociate -> on right.
        rewrite (Properties.cobind_dec T f).
        do 5 reassociate <- on right. fequal. fequal.
        change (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))
          with (fmap T (g ∘ μ (prod W)) ∘ (σ T ∘ fmap (prod W) (dec T))).
        rewrite <- (fun_fmap_fmap T).
        change (fmap T (fmap T (g ∘ μ (prod W)))) with (fmap (T ∘ T) (g ∘ μ (W ×))).
        reassociate <- on right.
        rewrite <- (natural (ϕ := @join T _) (g ∘ μ (W ×))).
        change (fmap T g ∘ dec T ∘ μ T) with (fmap T g ∘ (dec T ∘ μ T)).
        rewrite <- (fun_fmap_fmap G1).
        rewrite <- (fun_fmap_fmap T).
        change ((fmap T g ∘ fmap T (μ (prod W)) ∘ μ T
                   ∘ fmap T (σ T ∘ fmap (prod W) (dec T))))
          with ((fmap T g ∘ (fmap T (μ (prod W)) ∘ μ T
                               ∘ fmap T (σ T ∘ fmap (prod W) (dec T))))).
        rewrite <- (fun_fmap_fmap G1 _ _ _ _ (fmap T g)).
        reassociate -> on left.
        do 4 reassociate -> on right.
        fequal. do 3 reassociate <- on right.
        apply binddt_binddt1.
      Qed.

      Theorem kdtm_binddt2_T :
        fmap G1 (binddt T G2 g) ∘ binddt T G1 f = binddt T (G1 ∘ G2) (g ⋆dtm f).
      Proof.
        unfold binddt at 1 2 3; unfold Binddt_alg at 1 2 3.
        repeat reassociate <-.
        rewrite (dist_linear T). reassociate <- on right.
        #[local] Set Keyed Unification.
        rewrite 2(fun_fmap_fmap G1).
        #[local] Unset Keyed Unification.
        rewrite (equiv' T G1 G2 g f).
        unfold kcompose_dtm_alt.
        reassociate -> near (cobind (W ×) f).
        rewrite <- (fun_fmap_fmap T).
        change (fmap T (fmap G1 ?f)) with (fmap (T ∘ G1) f).
        reassociate <- on right.
        change (fmap G1 (fmap G2 (μ T) ∘ δ T G2) ∘ ?dist ∘ ?op)
          with (fmap G1 (fmap G2 (μ T) ∘ δ T G2) ∘ (dist ∘ op)).
        unfold_compose_in_compose.
        rewrite <- (natural (ϕ := @dist T _ G1 _ _ _)).
        change (fmap (G1 ∘ T) ?f) with (fmap G1 (fmap T f)).
        reassociate <-.
        #[local] Set Keyed Unification.
        rewrite (fun_fmap_fmap G1).
        #[local] Unset Keyed Unification.
        change (fmap T (fmap G2 (μ T) ∘ δ T G2 ∘ fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T)))
          with (fmap T (fmap G2 (μ T) ∘ (δ T G2 ∘ fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T)))).
        rewrite <- (fun_fmap_fmap T).
        change (fmap T (fmap G2 ?f)) with (fmap (T ∘ G2) f).
        reassociate <- on right. reassociate -> near (fmap (T ∘ G2) (μ T)).
        unfold_compose_in_compose.
        rewrite <- (natural (ϕ := @dist T _ G2 _ _ _)).
        reassociate <- on right.
        #[local] Set Keyed Unification.
        rewrite (fun_fmap_fmap G2).
        rewrite <- (mon_join_join T).
        #[local] Unset Keyed Unification.
        rewrite <- (fun_fmap_fmap G2).
        reassociate -> near (δ T G2).
        change (δ T G2 ∘ fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))
          with (δ T G2 ∘ (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))).
        rewrite <- (fun_fmap_fmap T).
        do 2 reassociate <- on right.
        change (fmap G2 (μ T) ∘ fmap G2 (μ T) ∘ δ T G2 ∘ fmap T (δ T G2) (A := ?A))
          with (fmap G2 (μ T) ∘ (fmap G2 (μ T) ∘ δ T G2 ∘ fmap T (δ T G2) (A := A))).
        change (fmap G2 (μ T) ∘ δ T G2 ∘ fmap T (δ T G2) (A := T (G2 ?A)))
          with (fmap G2 (μ T) ∘ δ (T ∘ T) G2 (A := A)).
        rewrite <- (trvmon_join T).
        reassociate <- on right.
        change_left (fmap G1 (fmap G2 (μ T) ∘ δ T G2 ∘ (fmap T g ∘ dec T ∘ μ T)) ∘ δ T G1 ∘ fmap T f ∘ dec T).
        change_right (fmap G1 (fmap G2 (μ T) ∘ δ T G2 ∘
                                 (μ T ∘ fmap T (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))))
                        ∘ δ T G1
                        ∘ fmap T (σ G1 ∘ cobind (prod W) f) ∘ dec T).
        (* cancel out the common sub-expressions and apply a lemma to the remaining. *)
        rewrite <- (fun_fmap_fmap G1).
        rewrite <- (fun_fmap_fmap G1 _ _ _ _ (fmap G2 (μ T) ∘ δ T G2)).
        do 3 reassociate -> on left.
        do 3 reassociate -> on right.
        fequal. repeat reassociate <-.
        apply binddt_binddt2.
      Qed.

    End binddt_binddt.

    Lemma kdtm_morph_T :
      forall (G1 G2 : Type -> Type)
        `{Fmap G1} `{Pure G1} `{Mult G1}
        `{Fmap G2} `{Pure G2} `{Mult G2}
        (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : W * A -> G1 (T B)),
          ϕ (T B) ∘ binddt T G1 f = binddt T G2 (ϕ (T B) ∘ f).
    Proof.
      introv morph. intros.
      unfold_ops @Binddt_alg.
      do 3 reassociate <- on left.
      fequal.
      inversion morph.
      unfold compose. ext t.
      rewrite appmor_natural.
      fequal.
      compose near (fmap T f t).
      rewrite <- (dist_morph T).
      unfold compose. compose near t on left.
      now rewrite (fun_fmap_fmap T).
    Qed.

    #[export] Instance: Kleisli.DT.Monad.Monad W T :=
      {| kdtm_binddt0 := @kdtm_binddt0_T;
        kdtm_binddt1 := @kdtm_binddt1_T;
        kdtm_binddt2 := @kdtm_binddt2_T;
        kdtm_morph := @kdtm_morph_T;
      |}.

  End with_monad.

End Instance.
