(** This file implements "monads decorated by monoid <<W>>." *)

From Tealeaves Require Export
     Singlesorted.Classes.DecoratedFunctor.

Import Product.Notations.
Import Functor.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import Monoid.Notations.
#[local] Open Scope tealeaves_scope.

(** * Basic properties of [shift] on monads *)
(******************************************************************************)
Section shift_monad_lemmas.

  Context
    `{Monad T}
    `{Monoid W}.

  (** [shift] applied to a singleton simplifies to a singleton. *)
  Lemma shift_return `(a : A) (w1 w2 : W) :
    shift T (w2, ret T (w1, a)) = ret T (w2 ● w1, a).
  Proof.
    unfold shift, compose. rewrite strength_return.
    compose near (w2, (w1, a)) on left.
    now rewrite (natural (F := fun A => A)).
  Qed.

  Lemma shift_join `(t : T (T (W * A))) (w : W) :
    shift T (w, join T t) = join T (fmap T (fun t => shift T (w, t)) t).
  Proof.
    rewrite shift_spec. compose near t on left.
    rewrite natural. unfold compose; cbn.
    fequal. unfold_ops @Fmap_compose.
    fequal. ext x. now rewrite shift_spec.
  Qed.

  Lemma shift_bind `(t : T (W * A)) (w : W) `(f : W * A -> T (W * B)) :
    shift T (w, bind T f t) = bind T (fun p => shift T (w, f p)) t.
  Proof.
    unfold_ops @Bind_Join. unfold compose.
    rewrite shift_join. fequal.
    compose near t on left.
    now rewrite (fun_fmap_fmap T).
  Qed.

End shift_monad_lemmas.

(** * Decorated monads *)
(** A decorated monad is a decorated functor whose monad operations
    are compatible with decorated structure. *)
(******************************************************************************)
Section DecoratedMonad.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T}
    `{Monoid_op W} `{Monoid_unit W} .

  Class DecoratedMonad:=
    { dmon_functor :> DecoratedFunctor W T;
      dmon_monad :> Monad T;
      dmon_monoid : Monoid W;
      dmon_ret :
        `(dec T ∘ ret T = ret T ∘ pair Ƶ (B:=A));
      dmon_join :
        `(dec T ∘ join T (A:=A) =
          join T ∘ fmap T (shift T) ∘ dec T ∘ fmap T (dec T));
    }.

End DecoratedMonad.

(** * Kleisli presentation of decorated monads *)
(******************************************************************************)

(** ** Lifting operation <<bindd>> *)
(******************************************************************************)
Section decorated_monad_kleisli_operations.

  Context
    `{DecoratedMonad W T}.

  Definition kcomposed {A B C} :
    (W * B -> T C) ->
    (W * A -> T B) ->
    (W * A -> T C) :=
    fun g f =>
      bind T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f).

  Definition bindd (T : Type -> Type) `{Bind T} `{Decorate W T} {A B}
    : (W * A -> T B) -> T A -> T B := fun f => bind T f ∘ dec T.

  Definition prepromote {A B} (w : W) (f : W * A -> T B) :=
    fun '(w', a) => f (w ● w', a).

  Definition kcomposed_alt {A B C} :
    (W * B -> T C) ->
    (W * A -> T B) ->
    (W * A -> T C) := fun g f '(w, a) => bindd T (prepromote w g) (f (w, a)).

  Theorem kcomposed_equiv {A B C}
          (g : W * B -> T C) (f : W * A -> T B) :
    kcomposed_alt g f = kcomposed g f.
  Proof.
    unfold kcomposed_alt, kcomposed. ext [w a]. unfold compose; cbn.
    unfold bindd, id, compose; cbn. unfold_ops @Bind_Join; unfold compose.
    unfold shift; cbn. fequal. unfold compose; cbn.
    compose near (f (w, a)) on left.
    compose near (dec T (f (w, a))) on right.
    rewrite (fun_fmap_fmap T).
    compose near (dec T (f (w, a))) on right.
    rewrite (fun_fmap_fmap T).
    compose near (f (w, a)) on right. fequal.
    fequal. ext [w' b]. easy.
  Qed.

End decorated_monad_kleisli_operations.

#[local] Notation "g ⋆d f" := (kcomposed g f) (at level 40) : tealeaves_scope.

(** ** Specification for sub-operations *)
(******************************************************************************)
Section decoratedmonad_suboperations.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  Lemma fmapd_to_bindd : forall `(f : W * A -> B),
      fmapd T f = bindd T (ret T ∘ f).
  Proof.
    introv. unfold fmapd, bindd.
    unfold_compose_in_compose.
    rewrite <- (Monad.bind_fmap T).
    now rewrite (Monad.bind_id T).
  Qed.

  Lemma bind_to_bindd : forall `(f : A -> T B),
      bind T f = bindd T (f ∘ extract (prod W)).
  Proof.
    introv. unfold bindd.
    rewrite <- (Monad.bind_fmap T).
    reassociate -> on right.
    now rewrite (dfun_dec_extract W T).
  Qed.

  Lemma fmap_to_bindd : forall `(f : A -> B),
      fmap T f = bindd T (ret T ∘ f ∘ extract (prod W)).
  Proof.
    introv. now rewrite (fmap_to_fmapd T), fmapd_to_bindd.
  Qed.

End decoratedmonad_suboperations.

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

(** ** Functor laws for [bindd] *)
(******************************************************************************)
Section decoratedmonad_kleisli_laws.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  (** *** Identity law *)
  Lemma bindd_id :
    `(bindd T (ret T ∘ extract (prod W)) = @id (T A)).
  Proof.
    intros. unfold bindd.
    rewrite <- (Monad.bind_fmap T).
    reassociate -> on left.
    rewrite (dfun_dec_extract W T).
    now rewrite (Monad.bind_id T).
  Qed.

  (** *** Composition law *)
  Lemma bindd_bindd {A B C} : forall (g : W * B -> T C) (f : W * A -> T B),
      bindd T (g ⋆d f) = bindd T g ∘ bindd T f.
  Proof.
    intros. unfold bindd at 2.
    reassociate -> on right.
    rewrite (dec_bindd T).
    unfold bindd at 2.
    reassociate <- on right.
    now rewrite (Monad.bind_bind T).
  Qed.

  (** *** Unit law *)
  Lemma bindd_comp_ret `(f : W * A -> T B) :
    bindd T f ∘ ret T = f ∘ pair Ƶ.
  Proof.
    intros. unfold bindd.
    reassociate -> on left.
    rewrite (dmon_ret W T).
    reassociate <- on left.
    now rewrite (bind_comp_ret T).
  Qed.

End decoratedmonad_kleisli_laws.

(** ** Kleisli category laws *)
(******************************************************************************)
Section decoratedmonad_kleisli_category.

  Context
    `{DecoratedMonad W T}.

  Existing Instance dmon_monoid.

  (** Composition when <<f>> has no substitution *)
  Theorem dm_kleisli_star1 {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      g ⋆d (ret T ∘ f) = g co⋆ f.
  Proof.
    intros. unfold kcomposed, cokcompose.
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
    now rewrite (bind_comp_ret T).
  Qed.

  (** Composition when <<f>> is context-agnostic *)
  Theorem dm_kleisli_star2 {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      g ⋆d (f ∘ extract (W ×)) =
      bind T g ∘ shift T ∘ fmap (W ×) (dec T ∘ f).
  Proof.
    intros. unfold kcomposed, cokcompose.
    reassociate <- on left.
    now rewrite <- (fmap_to_cobind (prod W)).
  Qed.

  (** Composition when <<g>> has no substitution *)
  Theorem dm_kleisli_star3 {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      (η T ∘ g) ⋆d f = fmap T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f).
  Proof.
    intros. unfold kcomposed, kcompose.
    now rewrite (fmap_to_bind T).
  Qed.

  (** Composition when <<g>> is context-agnostic *)
  Theorem dm_kleisli_star4 {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      (g ∘ extract (prod W)) ⋆d f = g ⋆ f.
  Proof.
    intros. unfold kcomposed, kcompose.
    rewrite <- (Monad.bind_fmap T).
    change (?f ∘ fmap T (extract (prod W)) ∘ shift T ∘ ?g) with
        (f ∘ (fmap T (extract (prod W)) ∘ shift T) ∘ g).
    rewrite (shift_extract).
    repeat reassociate ->. rewrite (extract_cobind (prod W)).
    fequal. reassociate <- on left.
    now rewrite (dfun_dec_extract W T).
  Qed.

  Theorem dm_kleisli_id_r {B C} : forall (g : W * B -> T C),
      g ⋆d (ret T ∘ extract (prod W)) = g.
  Proof.
    intros. rewrite dm_kleisli_star1.
    now rewrite (Comonad.cokleisli_id_r).
  Qed.

  Theorem dm_kleisli_id_l {A B} : forall (f : W * A -> T B),
      (ret T ∘ extract (prod W)) ⋆d f = f.
  Proof.
    intros. rewrite dm_kleisli_star4.
    now rewrite (Monad.kleisli_id_l).
  Qed.

  Theorem dm_kleisli_assoc {A B C D} : forall (h : W * C -> T D) (g : W * B -> T C) (f : W * A -> T B),
      h ⋆d (g ⋆d f) = (h ⋆d g) ⋆d f.
  Proof.
    intros. unfold kcomposed at 3.
  Abort.

End decoratedmonad_kleisli_category.

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
    unfold kcomposed. rewrite <- (fmap_to_bind T).
    now rewrite <- (fmap_cobind (prod W)).
  Qed.

  Corollary bindd_bind {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      bindd T g ∘ bind T f = bindd T (bind T g ∘ shift T ∘ fmap (prod W) (dec T ∘ f)).
  Proof.
    introv. rewrite (bind_to_bindd T).
    rewrite <- (bindd_bindd T).
    unfold kcomposed. reassociate <-. now rewrite <- (fmap_to_cobind (prod W)).
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

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "g ⋆d f" := (kcomposed g f) (at level 40) : tealeaves_scope.
End Notations.
