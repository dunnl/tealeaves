From Tealeaves Require Export
  Classes.Algebraic.DT.Monad
  Classes.Kleisli.DT.Monad
  Classes.Kleisli.Monad
  Classes.Kleisli.Decorated.Functor
  Classes.Kleisli.Decorated.Monad
  Classes.Kleisli.Traversable.Functor
  Classes.Kleisli.Traversable.Monad
  Classes.Kleisli.DT.Functor.

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

Section kleisli_composition.

  Context
    `{DecoratedTraversableMonad W T}
    {A B C : Type} `{Applicative G1} `{Applicative G2}.

  Definition kcompose_dtm :
    (W * B -> G2 (T C)) ->
    (W * A -> G1 (T B)) ->
    (W * A -> G1 (G2 (T C))) :=
    fun g f => (fmap G1 ((fmap G2 (μ T))
                        ∘ δ T G2
                        ∘ fmap T (g ∘ μ (W ×))
                        ∘ σ T
                        ∘ fmap (W ×) (dec T)))
              ∘ σ G1
              ∘ cobind (W ×) f.

(* Compare the above definition to this candidate definition:
<<
  Definition kcomposedtm {A B C}
             `{Applicative G1}
             `{Applicative G2} :
    (W * B -> G2 (T C)) ->
    (W * A -> G1 (T B)) ->
    (W * A -> G1 (G2 (T C))) :=
    fun g f => (fmap G1 ((fmap G2 (join T))
                        ∘ dist T G2
                        ∘ fmap T (g ∘ join (prod W))
                        ∘ dec T))
              ∘ strength (G1 ∘ T)
              ∘ cobind (prod W) f.
>>
   This definition is wrong in the sense that it passes arguments to the monoid operation
   in an unexpected order (which is to say, not the same order as <<shift>>, which we understand as the
   operation used in the definition <<dec T>>. (Alternatively we could probably swap the order for both definitions.)
 *)

End kleisli_composition.

#[local] Notation "g ⋆dtm f" := (kcompose_dtm g f) (at level 40) : tealeaves_scope.

Tactic Notation "bring" constr(x) "and" constr(y) "together" :=
  change (?f ∘ x ∘ y ∘ ?g) with (f ∘ (x ∘ y) ∘ g).

(** ** Specifications for sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableMonad_suboperations.

  Import Operation.

  Context
    (T : Type -> Type)
    `{Algebraic.DT.Monad.DecoratedTraversableMonad W T}
    `{Applicative G1}
    `{Applicative G2}.

  Import Algebraic.Monad.ToKleisli.Operation.
  Import Algebraic.Decorated.Functor.ToKleisli.Operation.
  Import Algebraic.Decorated.Monad.ToKleisli.Operation.
  Import Algebraic.Traversable.Functor.ToKleisli.Operation.
  Import Algebraic.Traversable.Monad.ToKleisli.Operation.

  Import Algebraic.Decorated.Functor.ToKleisli.
  Import Algebraic.Decorated.Monad.ToKleisli.
  Import Algebraic.DT.Functor.ToKleisli.

  (** *** [bindd] as a special case of [binddt] *)
  Theorem bindd_to_binddt {A B} : forall (f : W * A -> T B),
      bindd T f = binddt T (fun A => A) f.
  Proof.
    intros. unfold_ops Binddt_alg.
    change (fmap (fun A => A) ?f) with f.
    now rewrite (dist_unit T).
  Qed.

  (** *** [bindt] as a special case of [binddt] *)
  Theorem bindt_to_binddt {A B} `{Applicative G} : forall (f : A -> G (T B)),
      bindt T G f = binddt T G (f ∘ extract (prod W)).
  Proof.
    intros. unfold_ops @Binddt_alg @Bindt_alg.
    now rewrite (fmap_to_fmapd T).
  Qed.

  (** *** [fmapdt] as a special case of [binddt] *)
  Theorem fmapdt_to_binddt {A B} `{Applicative G} :
    forall (f : W * A -> G B),
      fmapdt T G f = binddt T G (fmap G (ret T) ∘ f).
  Proof.
    introv. unfold_ops @Binddt_alg.
    (* Kill the join *)
    rewrite <- (fun_fmap_fmap T). reassociate <- on right.
    change (fmap T (fmap G ?f)) with (fmap (T ∘ G) f).
    bring (dist T G (A := T B)) and
      (fmap (T ∘ G) (ret T (A := B))) together.
    unfold compose at 1. unfold_compose_in_compose.
    rewrite <- (natural (ϕ := @dist T _ G _ _ _)). reassociate <-.
    unfold_ops @Fmap_compose.
    unfold_compose_in_compose; rewrite (fun_fmap_fmap G).
    rewrite (mon_join_fmap_ret T).
    now rewrite (fun_fmap_id G).
  Qed.

  (** *** [fmapd] as a special case of [binddt] *)
  Theorem fmapd_to_binddt {A B} : forall (f : W * A -> B),
      fmapd T f = binddt T (fun A => A) (ret T ∘ f).
  Proof.
    intros. rewrite (fmapd_to_fmapdt T).
    now rewrite (fmapdt_to_binddt).
  Qed.

  (** *** [traverse] as a special case of [binddt] *)
  Theorem fmapt_to_binddt {A B} `{Applicative G} : forall (f : A -> G B),
      traverse T G f = binddt T G (fmap G (ret T) ∘ f ∘ extract (prod W)).
  Proof.
    introv. rewrite (traverse_to_fmapdt T).
    now rewrite (fmapdt_to_binddt).
  Qed.

  (** *** [bind] as a special case of [binddt] *)
  Theorem bind_to_binddt {A B} : forall (f : A -> T B),
      bind T f = binddt T (fun A => A) (f ∘ extract (prod W)).
  Proof.
    intros.
    rewrite (bind_to_bindd T).
    now rewrite (bindd_to_binddt).
  Qed.

  (** *** [fmap] as a special case of [binddt] *)
  Theorem fmap_to_binddt {A B} : forall (f : A -> B),
      fmap T f = binddt T (fun A => A) (ret T ∘ f ∘ extract (prod W)).
  Proof.
    introv. rewrite (fmap_to_fmapdt T).
    now rewrite (fmapdt_to_binddt).
  Qed.

End DecoratedTraversableMonad_suboperations.

(** ** Functoriality of [binddt] *)
(******************************************************************************)
Section DecoratedTraversableMonad_binddt.

  Import Operation.

  Import Algebraic.Monad.ToKleisli.Operation.
  Import Algebraic.Decorated.Functor.ToKleisli.Operation.
  Import Algebraic.Decorated.Monad.ToKleisli.Operation.
  Import Algebraic.Traversable.Functor.ToKleisli.Operation.
  Import Algebraic.Traversable.Monad.ToKleisli.Operation.

  Import Algebraic.Decorated.Functor.ToKleisli.
  Import Algebraic.Decorated.Monad.ToKleisli.
  Import Algebraic.DT.Functor.ToKleisli.

  Context
    (T : Type -> Type)
    `{Algebraic.DT.Monad.DecoratedTraversableMonad W T}.

  Theorem binddt_id {A} : binddt T (fun A => A) (ret T ∘ extract (prod W)) = @id (T A).
  Proof.
    introv. unfold_ops @Binddt_alg.
    change (fmap (fun A => A) ?f) with f.
    rewrite (dist_unit T).
    change_left (bindd T (η T ∘ extract (prod W) (A := A))).
    ext t. now rewrite (bindd_id T).
  Qed.

  Section binddt_binddt.

    Context {A B C : Type} `{Applicative G1} `{Applicative G2}
            (f : W * A -> G1 (T B)) (g : W * B -> G2 (T C)).

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
      rewrite (cobind_dec T f).
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

    Theorem binddt_binddt :
      fmap G1 (binddt T G2 g) ∘ binddt T G1 f = binddt T (G1 ∘ G2) (g ⋆dtm f).
    Proof.
      unfold_ops @Binddt_alg. repeat reassociate <-.
      rewrite (dist_linear T). reassociate <- on right.
      #[local] Set Keyed Unification.
      rewrite 2(fun_fmap_fmap G1).
      #[local] Unset Keyed Unification.
      unfold kcompose_dtm.
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
      change_right (fmap G1 (fmap G2 (μ T) ∘ δ T G2 ∘ (μ T ∘ fmap T (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))))
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

End DecoratedTraversableMonad_binddt.

(** ** Kleisli composition laws  *)
(******************************************************************************)
Section DecoratedTraversableMonad_kleisli.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    `{! Monoid W}.

  (** *** Miscellaneous lemmas *)
  (******************************************************************************)

  (** If <<g>> is going to discard the decoration, we don't have to compute it. *)
  Lemma dtm_kleisli_lemma1 : forall A,
    (fmap T (extract (prod W) ∘ μ (prod W)) ∘ σ T
          ∘ fmap (W ×) (dec T) : W * T A -> T A) = extract (W ×).
  Proof.
    intros. ext [w t]. unfold compose; cbn. unfold id.
    compose near (dec T t). rewrite (fun_fmap_fmap T).
    replace (extract (W ×) ○ μ (W ×) ∘ pair w (B := W * A))
      with (extract (W ×) (A := A)).
    compose near t on left. now rewrite (dfun_dec_extract W T).
    now ext [? ?].
  Qed.

  (** If <<f>> has a trivial <<T>> output, we use its same <<W>> input. *)
  Lemma dtm_kleisli_lemma2 : forall A,
    (fmap T (μ (prod W)) ∘ σ T
          ∘ fmap (W ×) (dec T ∘ ret T) : W * A -> T (W * A)) = ret T (A := W * A).
  Proof.
    intros. ext [w t]. unfold compose; cbn. unfold id.
    compose near (t). rewrite (dmon_ret W T); unfold compose; cbn.
    compose near (Ƶ, t). rewrite (natural (ϕ := @ret T _)). unfold_ops @Fmap_I.
    unfold compose; cbn.
    compose near (w, (Ƶ, t)). rewrite (natural (ϕ := @ret T _)). unfold_ops @Fmap_I.
    unfold compose; cbn. now simpl_monoid.
  Qed.

  (** *** Left and right identity laws *)
  (******************************************************************************)
  Lemma dtm_kleisli_identity1 :  forall `(f : W * A -> G (T B)),
      kcompose_dtm (G2 := fun A => A) (ret T ∘ extract (W ×)) f = f.
  Proof.
    intros. unfold kcompose_dtm. unfold_ops @Fmap_I.
    rewrite (dist_unit T). reassociate -> near (μ (W ×)).
    rewrite <- (fun_fmap_fmap T). reassociate <-.
    change (?foo ∘ fmap T (extract (prod W) ∘ μ (prod W)) ∘ σ T
     ∘ fmap (prod W) (dec T)) with (foo ∘ (fmap T (extract (prod W) ∘ μ (prod W)) ∘ σ T
     ∘ fmap (prod W) (dec T))).
    rewrite dtm_kleisli_lemma1.
    change (?f ∘ id) with f.
    rewrite <- (fun_fmap_fmap G).
    reassociate -> near (σ G).
    rewrite (strength_extract W G).
    reassociate ->.
    rewrite (extract_cobind (W ×)).
    rewrite (mon_join_fmap_ret T).
    rewrite (fun_fmap_id G).
    easy.
  Qed.

  Lemma dtm_kleisli_identity2 :  forall `(g : W * A -> G (T B)),
      kcompose_dtm (G1 := fun A => A) g (ret T ∘ extract (W ×)) = g.
  Proof.
    intros. unfold kcompose_dtm. unfold_ops @Fmap_I.
    rewrite strength_I. change (?f ∘ id) with f.
    rewrite <- (fmap_to_cobind (W ×)).
    reassociate ->. rewrite (fun_fmap_fmap (W ×)).
    rewrite <- (fun_fmap_fmap T). reassociate <-.
    change (?foo ∘ fmap T (μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T ∘ η T))
      with (foo ∘ (fmap T (μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T ∘ η T))).
    rewrite dtm_kleisli_lemma2.
    reassociate -> on left. rewrite (natural (ϕ := @ret T _)).
    unfold_ops @Fmap_I. reassociate <-.
    reassociate -> near (η T). rewrite (trvmon_ret T).
    rewrite (fun_fmap_fmap G). rewrite (mon_join_ret T).
    now rewrite (fun_fmap_id G).
  Qed.

End DecoratedTraversableMonad_kleisli.
