From Tealeaves Require Export
  Classes.Algebraic.Decorated.Monad
  Classes.Kleisli.Decorated.Monad
  Theory.Algebraic.Decorated.Functor.Properties
  Theory.Algebraic.Decorated.Shift
  Theory.Algebraic.Monad.ToKleisli
  Theory.Algebraic.Decorated.Functor.ToKleisli.

Import Product.Notations.
Import Comonad.Notations.
Import Monoid.Notations.
Import Algebraic.Monad.Notations.
Import Kleisli.Decorated.Monad.Notations.

#[local] Generalizable Variables W A B C.

(** * Algebraic decorated monad to Kleisli decorated monad *)
(******************************************************************************)

(** ** Derived operation <<bindd>> *)
(******************************************************************************)
Module Operation.
  Section with_algebraic.
    Context
      (W : Type)
      (T : Type -> Type)
      `{Fmap T} `{Join T} `{Decorate W T}.

    #[export] Instance Bindd_alg : Bindd W T T :=
      fun A B f => join T ∘ fmap T f ∘ dec T.

    End with_algebraic.
End Operation.

(** ** Kleisli laws *)
(******************************************************************************)
Module Instance.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{DecoratedMonad W T}.

    Import Operation.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma bindd_id :
      `(bindd T (ret T ∘ extract (prod W)) = @id (T A)).
    Proof.
      intros. unfold_ops @Bindd_alg.
      rewrite <- (fun_fmap_fmap T).
      reassociate <-.
      rewrite (mon_join_fmap_ret T).
      reassociate ->.
      rewrite (dfun_dec_extract W T).
      reflexivity.
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma bindd_bindd : forall `(g : W * B -> T C) `(f : W * A -> T B),
        bindd T g ∘ bindd T f = bindd T (g ⋆dm f).
    Proof.
      intros. unfold bindd at 1 2, Bindd_alg.
      (* change (join T ∘ fmap T ?f) with (bind T f).*)
      do 2 reassociate <-.
      reassociate -> near (join T). rewrite (dmon_join W T).
      repeat reassociate <-.
      reassociate -> near (fmap T f).
      rewrite (fun_fmap_fmap T).
      change (?g ∘ dec T ∘ fmap T (dec T ∘ f) ∘ dec T)
        with (g ∘ (dec T ∘ fmap T (dec T ∘ f) ∘ dec T)).
      rewrite <- (cobind_dec T).
      reassociate <-.
      change (?g ∘ fmap T (shift T) ∘ fmap T (cobind (prod W) (dec T ∘ f)) ∘ ?h)
        with (g ∘ (fmap T (shift T) ∘ fmap T (cobind (prod W) (dec T ∘ f))) ∘ h).
      rewrite (fun_fmap_fmap T).
      unfold bindd.
      change (?h ∘ fmap T g ∘ join T ∘ fmap T (shift T ∘ cobind (prod W) (dec T ∘ f)) ∘ ?i)
        with (h ∘ (fmap T g ∘ join T ∘ fmap T (shift T ∘ cobind (prod W) (dec T ∘ f))) ∘ i).
      fequal.
      unfold kcompose_dm, bindd, prepromote.
      rewrite natural.
      reassociate ->. unfold_ops @Fmap_compose. unfold_compose_in_compose.
      rewrite (fun_fmap_fmap T).
      replace (fun '(w, a) => (join T ∘ fmap T (g ∘ incr w) ∘ dec T) (f (w, a)))
        with (join T ∘ (fun '(w, a) => (fmap T (g ∘ incr w) ∘ dec T) (f (w, a))))
        by (ext [? ?]; reflexivity).
      reassociate <-.
      #[local] Set Keyed Unification.
      rewrite (mon_join_join T).
      #[local] Unset Keyed Unification.
      reassociate ->.
      fequal. unfold_compose_in_compose.
      rewrite (fun_fmap_fmap T).
      fequal. fequal. ext [w a].
      unfold shift, compose; cbn.
      compose near (dec T (f (w, a))) on left.
      rewrite (fun_fmap_fmap T).
      compose near (dec T (f (w, a))) on left.
      rewrite (fun_fmap_fmap T).
      fequal. ext [w' b].
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma bindd_comp_ret `(f : W * A -> T B) :
      bindd T f ∘ ret T = f ∘ pair Ƶ.
    Proof.
      intros. unfold_ops Bindd_alg.
      reassociate -> on left.
      rewrite (dmon_ret W T).
      reassociate <- on left.
      reassociate -> near (ret T).
      rewrite (natural (G := T) (ϕ := @ret T _)).
      reassociate <-. rewrite (mon_join_ret T).
      reflexivity.
    Qed.

    #[export] Instance: Kleisli.Decorated.Monad.Monad T :=
      {| kmond_bindd0 := @bindd_comp_ret;
        kmond_bindd1 := @bindd_id;
        kmond_bindd2 := @bindd_bindd;
      |}.

  End with_monad.

End Instance.
