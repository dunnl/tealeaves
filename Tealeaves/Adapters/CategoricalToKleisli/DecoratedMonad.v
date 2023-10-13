From Tealeaves Require Import
  Classes.Categorical.DecoratedMonad
  Adapters.CategoricalToKleisli.DecoratedFunctor
  Categories.DecoratedFunctor.
From Tealeaves Require Import
  Classes.Kleisli.DecoratedMonad.

#[local] Generalizable Variables W T.

Import Monoid.Notations.
Import Product.Notations.
Import Classes.Kleisli.DecoratedMonad.Notations.

(** * Algebraic decorated monad to Kleisli decorated monad *)
(******************************************************************************)

(** ** Kleisli laws *)
(******************************************************************************)
Module ToKleisli.

  #[local] Generalizable Variables A B C.

  Section operation.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Map T} `{Join T} `{Decorate W T}.

    #[export] Instance Bindd_dec : Bindd W T T :=
      fun A B f => join T ∘ map T f ∘ dec T.

  End operation.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Categorical.DecoratedMonad.DecoratedMonad W T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma bindd_id :
      `(bindd T (ret T A ∘ extract (prod W) A) = @id (T A)).
    Proof.
      intros. unfold_ops @Bindd_dec.
      rewrite <- (fun_map_map (F := T)).
      reassociate <-.
      rewrite (mon_join_map_ret (T := T)).
      reassociate ->.
      rewrite (dfun_dec_extract (E := W) (F := T)).
      reflexivity.
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma bindd_bindd : forall (A B C : Type) (g : W * B -> T C) (f : W * A -> T B),
        bindd T g ∘ bindd T f = bindd T (g ⋆5 f).
    Proof.
      intros. unfold bindd at 1 2, Bindd_dec.
      (* change (join T ∘ map T ?f) with (bind T f).*)
      do 2 reassociate <-.
      reassociate -> near (join T).
      rewrite (dmon_join (W := W) (T := T)).
      repeat reassociate <-.
      reassociate -> near (map T f).
      rewrite (fun_map_map (F := T)).
      change (?g ∘ dec T ∘ map T (dec T ∘ f) ∘ dec T)
        with (g ∘ (dec T ∘ map T (dec T ∘ f) ∘ dec T)).
      rewrite <- (cobind_dec T).
      reassociate <-.
      change (?g ∘ map T (shift T) ∘ map T (cobind (prod W) (dec T ∘ f)) ∘ ?h)
        with (g ∘ (map T (shift T) ∘ map T (cobind (prod W) (dec T ∘ f))) ∘ h).
      rewrite (fun_map_map (F := T)).
      unfold bindd.
      change (?h ∘ map T g ∘ join T ∘ map T (shift T ∘ cobind (prod W) (dec T ∘ f)) ∘ ?i)
        with (h ∘ (map T g ∘ join T ∘ map T (shift T ∘ cobind (prod W) (dec T ∘ f))) ∘ i).
      fequal.
      unfold kc5, bindd, preincr.
      rewrite natural.
      reassociate ->. unfold_ops @Map_compose. unfold_compose_in_compose.
      rewrite (fun_map_map (F := T)).
      replace (fun '(w, a) => (join T ∘ map T (g ∘ incr W w) ∘ dec T) (f (w, a)))
        with (join T ∘ (fun '(w, a) => (map T (g ∘ incr W w) ∘ dec T) (f (w, a))))
        by (ext [? ?]; reflexivity).
      reassociate <-.
      #[local] Set Keyed Unification.
      rewrite (mon_join_join (T := T)).
      #[local] Unset Keyed Unification.
      reassociate ->.
      fequal. unfold_compose_in_compose.
      rewrite (fun_map_map (F := T)).
      fequal. fequal. ext [w a].
      unfold shift, compose; cbn.
      compose near (dec T (f (w, a))) on left.
      rewrite (fun_map_map (F := T)).
      compose near (dec T (f (w, a))) on left.
      rewrite (fun_map_map (F := T)).
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma bindd_comp_ret `(f : W * A -> T B) :
      bindd T f ∘ ret T A = f ∘ pair Ƶ.
    Proof.
      intros. unfold_ops Bindd_dec.
      reassociate -> on left.
      rewrite (dmon_ret (W := W) (T := T)).
      reassociate <- on left.
      reassociate -> near (ret T (W * A)).
      rewrite (natural (G := T) (ϕ := @ret T _)).
      reassociate <-. rewrite (mon_join_ret _).
      reflexivity.
    Qed.

    #[export] Instance: Kleisli.DecoratedMonad.DecoratedMonad T :=
      {| kmond_bindd0 := @bindd_comp_ret;
        kmond_bindd1 := @bindd_id;
        kmond_bindd2 := @bindd_bindd;
      |}.

  End with_monad.

End ToKleisli.
