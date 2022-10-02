From Tealeaves Require Export
  Classes.Algebraic.Decorated.Monad
  Classes.Kleisli.Decorated.Monad
  Theory.Algebraic.Decorated.Functor.Properties
  Theory.Algebraic.Monad.ToKleisli
  Theory.Algebraic.Decorated.Functor.ToKleisli.

Import Comonad.Notations.
Import Monoid.Notations.
Import Kleisli.Decorated.Monad.Notations.

#[local] Generalizable Variables W A B C.

(** * Derived typeclass instance *)
(******************************************************************************)

(** * Derived <<Bindd>> operation *)
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

Import Operation.

(** ** Kleisli laws *)
(******************************************************************************)
Section laws.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  (** *** Identity law *)
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

  #[local] Instance: Kleisli.Decorated.Monad.Monad T :=
    {| kmond_bindd0 := @bindd_comp_ret;
      kmond_bindd1 := @bindd_id;
      kmond_bindd2 := @bindd_bindd;
    |}.

End laws.

(** ** Specification for sub-operations *)
(******************************************************************************)
Section decoratedmonad_suboperations.

  Context
    (T : Type -> Type)
      `{DecoratedMonad W T}.

  Import Algebraic.Monad.ToKleisli.Operation.
  Import Algebraic.Decorated.Functor.ToKleisli.Operation.
  Import Algebraic.Decorated.Monad.ToKleisli.Operation.

  Import Algebraic.Decorated.Functor.ToKleisli.

  Lemma fmapd_to_bindd : forall `(f : W * A -> B),
      fmapd T f = bindd T (ret T ∘ f).
  Proof.
    introv. unfold_ops @Fmapd_alg @Bindd_alg.
    change_right (bind T (ret T ∘ f) ∘ dec T).
    rewrite <- (bind_fmap T).
    now rewrite (mon_bind_id T).
  Qed.

  Lemma bind_to_bindd : forall `(f : A -> T B),
      bind T f = bindd T (f ∘ extract (prod W)).
  Proof.
    introv. unfold_ops @Bindd_alg.
    change_right (bind T (f ∘ extract (prod W)) ∘ dec T).
    rewrite <- (bind_fmap T).
    reassociate -> on right.
    now rewrite (dfun_dec_extract W T).
  Qed.

  Lemma fmap_to_bindd : forall `(f : A -> B),
      fmap T f = bindd T (ret T ∘ f ∘ extract (prod W)).
  Proof.
    introv. now rewrite (fmap_to_fmapd T), fmapd_to_bindd.
  Qed.

End decoratedmonad_suboperations.

(*
(** ** Interaction between [dec] and [bindd], [bind] *)
(******************************************************************************)
Section dec_bindd.

  #[local] Set Keyed Unification.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  Theorem dec_bindd : forall A B (f : W * A -> T B),
      dec T ∘ bindd T f =
      bindd T (shift T ∘ cobind (prod W) (dec T ∘ f)).
  Proof.
    intros A ? f. unfold bindd. unfold_ops @Bind_Join.
    do 2 reassociate <- on left.
    rewrite (dmon_join W T).
    reassociate -> near (fmap T f).
    rewrite (fun_fmap_fmap T).
    reassociate -> near (fmap T (dec T ∘ f)).
    rewrite <- (natural (G := T ∘ prod W) (F := T) (ϕ := @dec W T _)).
    reassociate <- on left.
    unfold_ops @Fmap_compose.
    change_left (join T ∘ (fmap T (shift T) ∘ fmap T (fmap (prod W) (dec T ∘ f))) ∘ dec T ∘ dec T).
    rewrite (fun_fmap_fmap T).
    reassociate -> on left.
    rewrite (dfun_dec_dec W T).
    reassociate <- on left.
    reassociate -> near (fmap T (cojoin (A:=A) (prod W))).
    now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary dec_bind : forall A B (f : W * A -> T B),
      dec T ∘ bind T f =
      bindd T (shift T ∘ fmap (prod W) (dec T ∘ f)).
  Proof.
    introv. rewrite (bind_to_bindd T).
    rewrite dec_bindd.
    fequal. now ext [w a].
  Qed.

End dec_bindd.

(* Original

(** ** Composition laws for sub-operations *)
(******************************************************************************)
Section decoratedmonad_suboperation_composition.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  Lemma bindd_fmapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      bindd T g ∘ fmapd T f = bindd T (g co⋆ f).
  Proof.
    introv. rewrite (fmapd_to_bindd T).
    rewrite <- (bindd_bindd T).
    now rewrite (dm_kleisli_star1).
  Qed.

  Corollary bind_bindd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      bind T g ∘ bindd T f = bindd T (g ⋆ f).
  Proof.
    intros. rewrite (bind_to_bindd T).
    rewrite <- (bindd_bindd T).
    now rewrite (dm_kleisli_star4).
  Qed.

  Corollary fmapd_bindd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      fmapd T g ∘ bindd T f = bindd T (fmap T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f)).
  Proof.
    intros. rewrite (fmapd_to_bindd T).
    rewrite <- (bindd_bindd T).
    unfold kcompose_dm.
    now rewrite <- (fmap_to_bind T).
  Qed.

  Corollary bindd_bind {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      bindd T g ∘ bind T f = bindd T (bind T g ∘ shift T ∘ fmap (prod W) (dec T ∘ f)).
  Proof.
    introv. rewrite (bind_to_bindd T).
    rewrite <- (bindd_bindd T).
    unfold kcompose_dm. reassociate <-. now rewrite <- (fmap_to_cobind (prod W)).
  Qed.

  Lemma bindd_fmap {A B C} : forall (g : W * B -> T C) (f : A -> B),
      bindd T g ∘ fmap T f = bindd T (g ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (fmap_to_bindd T).
    rewrite <- (bindd_bindd T).
    reassociate -> on left. rewrite (dm_kleisli_star1).
    unfold cokcompose. now rewrite (fmap_to_cobind (prod W)).
  Qed.

  Corollary fmap_bindd {A B C} : forall (g : B -> C) (f : W * A -> T B),
      fmap T g ∘ bindd T f = bindd T (fmap T g ∘ f).
  Proof.
    intros. rewrite (fmap_to_bindd T).
    rewrite <- (bindd_bindd T).
    rewrite <- (fmap_to_bindd T).
    rewrite (dm_kleisli_star4). unfold kcompose.
    now rewrite <- (fmap_to_bind T).
  Qed.

End decoratedmonad_suboperation_composition.
 *)
*)
