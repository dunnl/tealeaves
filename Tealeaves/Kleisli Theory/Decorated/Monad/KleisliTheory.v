From Tealeaves Require Export
  Theory.Algebraic.Decorated.Monad.ToKleisli
  Theory.Algebraic.Decorated.Functor.KleisliTheory.

Import Algebraic.Monad.Notations.
Import Comonad.Notations.
Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables W.

(** ** Properties *)
(******************************************************************************)

(** ** Kleisli composition *)
(******************************************************************************)
Section decorated_monad_kleisli_operations.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  Import
    Algebraic.Decorated.Monad.ToKleisli.Operation
    Algebraic.Monad.ToKleisli.Operation
    Algebraic.Monad.ToKleisli.Instance.

  Definition kcompose_dm {A B C} :
    (W * B -> T C) ->
    (W * A -> T B) ->
    (W * A -> T C) :=
    fun g f =>
      bind T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f).

  Definition prepromote {A B} (w : W) (f : W * A -> T B) :=
    fun '(w', a) => f (w ● w', a).

  Definition kcomposed_alt {A B C} :
    (W * B -> T C) ->
    (W * A -> T B) ->
    (W * A -> T C) := fun g f '(w, a) => bindd T (prepromote w g) (f (w, a)).

  Theorem kcomposed_equiv {A B C}
          (g : W * B -> T C) (f : W * A -> T B) :
    kcomposed_alt g f = kcompose_dm g f.
  Proof.
    unfold kcomposed_alt, kcompose_dm. ext [w a].
    unfold compose; cbn.
    unfold_ops @Bindd_alg @Bind_alg.
    unfold id, compose; cbn.
    unfold shift; cbn.
    fequal. unfold compose; cbn.
    compose near (f (w, a)) on left.
    compose near (dec T (f (w, a))) on right.
    rewrite (fun_fmap_fmap T).
    compose near (dec T (f (w, a))) on right.
    rewrite (fun_fmap_fmap T).
    compose near (f (w, a)) on right. fequal.
    fequal. ext [w' b]. easy.
  Qed.

End decorated_monad_kleisli_operations.

#[local] Notation "g ⋆dm f" := (kcompose_dm _ g f) (at level 40) : tealeaves_scope.

(** *** Kleisli category laws *)
(******************************************************************************)
Section decoratedmonad_kleisli_category.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  Existing Instance dmon_monoid.

  Import Algebraic.Monad.ToKleisli.Operation.
  Import Algebraic.Monad.ToKleisli.Instance.

  (** Composition when <<f>> has no substitution *)
  Theorem dm_kleisli_star1 {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      g ⋆dm (ret T ∘ f) = g co⋆ f.
  Proof.
    intros. unfold kcompose_dm, cokcompose.
    ext [w a]. unfold compose. cbn.
    unfold compose, id; cbn.
    compose near (f (w, a)) on left.
    rewrite (dmon_ret W T).
    unfold compose; cbn.
    rewrite shift_return.
    assert (Monoid W).
    { eapply @dmon_monoid; eauto. }
    rewrite (monoid_id_l).
    compose near (w, f (w, a)) on left.
    now rewrite (kmon_bind0 T).
  Qed.

  (** Composition when <<f>> is context-agnostic *)
  Theorem dm_kleisli_star2 {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      g ⋆dm (f ∘ extract (W ×)) =
      bind T g ∘ shift T ∘ fmap (W ×) (dec T ∘ f).
  Proof.
    intros. unfold kcompose_dm, cokcompose.
    reassociate <- on left.
    now rewrite <- (fmap_to_cobind (prod W)).
  Qed.

  (** Composition when <<g>> has no substitution *)
  Theorem dm_kleisli_star3 {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      (η T ∘ g) ⋆dm f = fmap T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f).
  Proof.
    intros. unfold kcompose_dm, kcompose.
    now rewrite (fmap_to_bind T).
  Qed.

  (** Composition when <<g>> is context-agnostic *)
  Theorem dm_kleisli_star4 {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      (g ∘ extract (prod W)) ⋆dm f = bind T g ∘ f.
  Proof.
    intros. unfold kcompose_dm, kcompose.
    rewrite <- (bind_fmap T).
    change (?f ∘ fmap T (extract (prod W)) ∘ shift T ∘ ?g) with
        (f ∘ (fmap T (extract (prod W)) ∘ shift T) ∘ g).
    rewrite (shift_extract T).
    repeat reassociate ->. rewrite (extract_cobind (prod W)).
    fequal. reassociate <- on left.
    now rewrite (dfun_dec_extract W T).
  Qed.

  Theorem dm_kleisli_id_r {B C} : forall (g : W * B -> T C),
      g ⋆dm (ret T ∘ extract (prod W)) = g.
  Proof.
    intros. rewrite dm_kleisli_star1.
    now rewrite (Comonad.cokleisli_id_r).
  Qed.

  Theorem dm_kleisli_id_l {A B} : forall (f : W * A -> T B),
      (ret T ∘ extract (prod W)) ⋆dm f = f.
  Proof.
    intros. rewrite dm_kleisli_star4.
    now rewrite (kmon_bind1 T).
  Qed.

  Theorem dm_kleisli_assoc {A B C D} : forall (h : W * C -> T D) (g : W * B -> T C) (f : W * A -> T B),
      h ⋆dm (g ⋆dm f) = (h ⋆dm g) ⋆dm f.
  Proof.
    intros. unfold kcompose_dm at 3.
  Abort.

End decoratedmonad_kleisli_category.

(** *** Specification for sub-operations *)
(******************************************************************************)
Section decoratedmonad_suboperations.

  #[local] Generalizable Variables A B C.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  Import Algebraic.Monad.ToKleisli.Operation.
  Import Algebraic.Monad.ToKleisli.Instance.
  Import Algebraic.Decorated.Monad.ToKleisli.Operation.
  Import Algebraic.Decorated.Functor.ToKleisli.Operation.

  Lemma fmapd_to_bindd : forall `(f : W * A -> B),
      fmapd T f = bindd T (ret T ∘ f).
  Proof.
    introv. unfold_ops @Fmapd_alg @Bindd_alg.
    change_right (bind T (ret T ∘ f) ∘ dec T).
    rewrite <- (bind_fmap T).
    now rewrite (kmon_bind1 T).
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
    introv.
    Search fmapd fmap.
    now rewrite (fmap_to_fmapd T), fmapd_to_bindd.
  Qed.

End decoratedmonad_suboperations.

(** ** Interaction between [dec] and [bindd], [bind] *)
(******************************************************************************)
Section dec_bindd.

  #[local] Set Keyed Unification.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  Import Operation.
  Import Instance.
  Import Algebraic.Monad.ToKleisli.Operation.
  Import Algebraic.Monad.ToKleisli.Instance.

  Theorem dec_bindd : forall A B (f : W * A -> T B),
      dec T ∘ bindd T f =
      bindd T (shift T ∘ cobind (prod W) (dec T ∘ f)).
  Proof.
    intros A ? f. unfold_ops @Bindd_alg.
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

(** ** Composition laws for sub-operations *)
(******************************************************************************)
Section decoratedmonad_suboperation_composition.

  Context
    (T : Type -> Type)
    `{Algebraic.Decorated.Monad.DecoratedMonad W T}.

  Import Instance.
  Import Operation.
  Import Algebraic.Monad.ToKleisli.Operation.
  Import Algebraic.Monad.ToKleisli.Instance.
  Import Algebraic.Decorated.Monad.ToKleisli.Operation.
  Import Algebraic.Decorated.Functor.ToKleisli.Operation.

  Lemma kcompose_equiv2  {A B C} : forall (g : W * B -> T C) (f : W * A -> T B),
      kcompose_dm T g f = Monad.kcompose_dm g f.
  Proof.
    intros. unfold Monad.kcompose_dm.
    rewrite <- (kcomposed_equiv T).
    unfold kcomposed_alt.
    ext [w a]. fequal. now ext [w' b].
  Qed.

  Lemma bindd_fmapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      bindd T g ∘ fmapd T f = bindd T (g co⋆ f).
  Proof.
    introv. rewrite (fmapd_to_bindd T).
    rewrite (kmond_bindd2 T).
    rewrite <- kcompose_equiv2.
    now rewrite (dm_kleisli_star1 T).
  Qed.

  Corollary bind_bindd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      bind T g ∘ bindd T f = bindd T (bind T g ∘ f).
  Proof.
    intros. rewrite (bind_to_bindd T).
    rewrite (bindd_bindd T).
    rewrite <- kcompose_equiv2.
    rewrite (dm_kleisli_star4 T).
    fequal. fequal. unfold_ops @Bind_alg @Bindd_alg.
    rewrite <- (fun_fmap_fmap T).
    do 2 reassociate -> on right.
    now rewrite (dfun_dec_extract W T).
  Qed.

  Corollary fmapd_bindd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      fmapd T g ∘ bindd T f = bindd T (fmap T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f)).
  Proof.
    intros. rewrite (fmapd_to_bindd T).
    rewrite (bindd_bindd T).
    rewrite <- kcompose_equiv2.
    fequal. unfold kcompose_dm.
    now rewrite (fmap_to_bind T).
  Qed.

  Corollary bindd_bind {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      bindd T g ∘ bind T f = bindd T (bind T g ∘ shift T ∘ fmap (prod W) (dec T ∘ f)).
  Proof.
    introv. rewrite (bind_to_bindd T).
    rewrite (bindd_bindd T).
    rewrite <- kcompose_equiv2.
    unfold kcompose_dm.
    reassociate <-. now rewrite <- (fmap_to_cobind (prod W)).
  Qed.

  Lemma bindd_fmap {A B C} : forall (g : W * B -> T C) (f : A -> B),
      bindd T g ∘ fmap T f = bindd T (g ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (fmap_to_bindd T).
    rewrite (bindd_bindd T).
    reassociate -> on left.
    rewrite <- kcompose_equiv2.
    rewrite (dm_kleisli_star1 T).
    unfold cokcompose. now rewrite (fmap_to_cobind (prod W)).
  Qed.

  Corollary fmap_bindd {A B C} : forall (g : B -> C) (f : W * A -> T B),
      fmap T g ∘ bindd T f = bindd T (fmap T g ∘ f).
  Proof.
    intros. rewrite (fmap_to_bindd T).
    rewrite (bindd_bindd T).
    rewrite <- kcompose_equiv2.
    rewrite <- (fmap_to_bindd T).
    rewrite (dm_kleisli_star4 T).
    now rewrite <- (fmap_to_bind T).
  Qed.

End decoratedmonad_suboperation_composition.
