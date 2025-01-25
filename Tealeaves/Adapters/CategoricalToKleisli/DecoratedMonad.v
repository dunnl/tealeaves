From Tealeaves Require Import
  Classes.Categorical.DecoratedMonad
  Classes.Kleisli.DecoratedMonad
  CategoricalToKleisli.DecoratedFunctor (cobind_dec).

#[local] Generalizable Variables W T.

Import Monoid.Notations.
Import Product.Notations.
Import Kleisli.DecoratedMonad.Notations.

(** * Categorical Decorated Monad to Kleisli Decorated Monad *)
(**********************************************************************)

(** ** Derived <<bindd>> Operation *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Bindd_Categorical
    (W: Type)
    (T: Type -> Type)
    `{Map_T: Map T}
    `{Join_T: Join T}
    `{Decorate_WT: Decorate W T}: Bindd W T T :=
  fun A B f => join (T := T) ∘ map (F := T) f ∘ dec T.

End DerivedOperations.

(** ** Derived Laws *)
(**********************************************************************)
Module DerivedInstances.

  (* Alectryon doesn't like this
     Import CategoricalToKleisli.DecoratedMonad.DerivedOperations.
   *)
  Import DerivedOperations.

  #[local] Generalizable Variables A B C.

  Section with_monad.

    Context
      (T: Type -> Type)
      `{Categorical.DecoratedMonad.DecoratedMonad W T}.

    (** *** Identity law *)
    (******************************************************************)
    Lemma bindd_id: forall (A: Type),
        bindd (ret (T := T) ∘ extract) = @id (T A).
    Proof.
      intros. unfold_ops @Bindd_Categorical.
      rewrite <- (fun_map_map (F := T)).
      reassociate <-.
      rewrite (mon_join_map_ret (T := T)).
      reassociate ->.
      rewrite (dfun_dec_extract (E := W) (F := T)).
      reflexivity.
    Qed.

    (** *** Composition law *)
    (******************************************************************)
    Lemma bindd_bindd:
      forall (A B C: Type) (g: W * B -> T C) (f: W * A -> T B),
        bindd g ∘ bindd f = bindd (g ⋆5 f).
    Proof.
      intros. unfold bindd at 1 2, Bindd_Categorical.
      (* change (join T ∘ map T ?f) with (bind T f).*)
      do 2 reassociate <-.
      reassociate -> near join.
      rewrite (dmon_join (W := W) (T := T)).
      repeat reassociate <-.
      reassociate -> near (map f).
      rewrite (fun_map_map (F := T)).
      change (?rest ∘ dec T ∘ map (F := T) (dec T ∘ f) ∘ dec T)
        with (rest ∘ (dec T ∘ map (F := T) (dec T ∘ f) ∘ dec T)).
      rewrite <- (cobind_dec T).
      reassociate <-.
      change (?g ∘ map (shift T) ∘ map (cobind (W := prod W) (dec T ∘ f)) ∘ ?h)
        with (g ∘ (map (shift T) ∘ map (cobind (W := prod W) (dec T ∘ f))) ∘ h).
      rewrite (fun_map_map (F := T)).
      unfold bindd.
      change (?h ∘ map g ∘ join ∘ map (shift T ∘ cobind (W := prod W) (dec T ∘ f)) ∘ ?i)
        with (h ∘ (map g ∘ join ∘ map (shift T ∘ cobind (W := prod W) (dec T ∘ f))) ∘ i).
      fequal.
      unfold kc5, bindd, preincr.
      rewrite natural.
      reassociate ->. unfold_ops @Map_compose. unfold_compose_in_compose.
      rewrite (fun_map_map (F := T)).
      replace (fun '(w, a) => (join (T := T) ∘ map (F := T) (g ∘ incr w) ∘ dec T) (f (w, a)))
        with (join (T := T) ∘ (fun '(w, a) => (map (F := T) (g ∘ incr w) ∘ dec T) (f (w, a))))
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
    (******************************************************************)
    Lemma bindd_comp_ret `(f: W * A -> T B):
      bindd f ∘ ret = f ∘ pair Ƶ.
    Proof.
      intros. unfold_ops Bindd_Categorical.
      reassociate -> on left.
      rewrite (dmon_ret (W := W) (T := T)).
      reassociate <- on left.
      reassociate -> near (ret (A := W * A)).
      rewrite (natural (G := T) (ϕ := @ret T _)).
      reassociate <-. rewrite (mon_join_ret _).
      reflexivity.
    Qed.

    (** ** Typeclass Instances *)
    (******************************************************************)
    #[export] Instance:
      Kleisli.DecoratedMonad.DecoratedRightPreModule W T T :=
      {| kdmod_bindd1 := @bindd_id;
         kdmod_bindd2 := @bindd_bindd;
      |}.

    #[export] Instance:
      Kleisli.DecoratedMonad.DecoratedMonad W T
      :=
      {| kdm_bindd0 := @bindd_comp_ret;
         kdm_monoid := dmon_monoid;
      |}.

  End with_monad.

End DerivedInstances.
