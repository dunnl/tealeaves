From Tealeaves Require Export
     Singlesorted.Classes.DecoratedMonad
     Singlesorted.Classes.SetlikeFunctor
     Singlesorted.Classes.Monad.

Import Sets.Notations.
Import SetlikeFunctor.Notations.
Import Monoid.Notations.
#[local] Open Scope tealeaves_scope.

(** * Set-like monads *)
(******************************************************************************)
Section SetlikeMonad.

  Context
    (T : Type -> Type).

  (* "x" for "extensional" *)
  Class SetlikeMonad
        `{Fmap T} `{Return T} `{Join T} `{Toset T} : Prop :=
    { xmon_monad :> Monad T;
      xmon_functor :> SetlikeFunctor T;
      xmon_ret_injective :
        `(ret T (a : A) = ret T (b : A) -> a = b);
      xmon_ret :
        `(toset T ∘ ret T (A:=A) = ret set);
      xmon_join :
        `(toset (A:=A) T ∘ join T =
          join set ∘ toset T ∘ fmap T (toset T));
    }.

End SetlikeMonad.

(** ** Instance for [set] *)
(******************************************************************************)
Section SetlikeMonad_set_instance.

  Existing Instance toset_set.
  Existing Instance Natural_toset_set.
  Existing Instance SetlikeFunctor_set.

  Instance SetlikeMonad_set : SetlikeMonad set.
  Proof.
    constructor; try typeclasses eauto.
    - apply set_ret_injective.
    - reflexivity.
    - intros. unfold compose. ext S a.
      cbv. propext.
      + firstorder.
      + firstorder (subst; firstorder).
  Qed.

End SetlikeMonad_set_instance.

(** ** Basic properties of set-like monads *)
(******************************************************************************)
Section setlike_monad_properties.

  Context
    (T : Type -> Type)
    `{SetlikeMonad T}.

  (** [ret] always acts like a singleton *)
  Theorem in_ret_iff {A} : forall (a a' : A),
      a' ∈ ret T a <-> a = a'.
  Proof.
    intros a a'. compose near a on left.
    now rewrite (xmon_ret T).
  Qed.

  (** [join] acts like a union operation *)
  Corollary in_join_iff {A} : forall (t : T (T A)) (a : A),
      a ∈ join T t <-> (exists t', t' ∈ t /\ a ∈ t').
  Proof.
    introv. compose near t on left.
    rewrite (xmon_join T).
    reassociate -> on left.
    rewrite <- (natural (B:=set A) (G:=(->Prop))).
    unfold transparent tcs; unfold compose.
    intuition (preprocess; eauto).
  Qed.

  (** ** [bind] acts like a substitution *)
  Corollary in_bind_iff {A B} : forall t b (f : A -> T B),
      b ∈ bind T f t <->
      exists (a : A), a ∈ t /\ b ∈ f a.
  Proof.
    introv. unfold transparent tcs. unfold compose.
    rewrite (in_join_iff (fmap T f t)).
    setoid_rewrite (in_fmap_iff T).
    intuition (preprocess; eauto).
  Qed.

  (** ** Respectfulness conditions for [bind] *)
  Corollary bind_respectful : forall A B (t : T A) (f g : A -> T B),
      (forall a, a ∈ t -> f a = g a) -> bind T f t = bind T g t.
  Proof.
    introv hyp. unfold_ops @Bind_Join.
    unfold compose. fequal. now apply (fmap_respectful T).
  Qed.

  Corollary bind_respectful_id : forall A (t : T A) (f : A -> T A),
      (forall a, a ∈ t -> f a = ret T a) -> bind T f t = t.
  Proof.
    introv hyp. replace t with (bind T (ret T) t) at 2
      by now rewrite (Monad.bind_id T).
    now apply bind_respectful.
  Qed.

  Corollary bind_respectful_fmap {A} :
    forall (t : T A) (f : A -> T A) (g : A -> A),
      (forall a, a ∈ t -> f a = ret T (g a)) -> bind T f t = fmap T g t.
  Proof.
    intros. rewrite (Monad.fmap_to_bind T).
    now apply bind_respectful.
  Qed.

End setlike_monad_properties.

(** * Decorated set-like monads *)
(******************************************************************************)

(** ** Basic properties *)
(******************************************************************************)
Section decorated_setlike_properties.

  Context
    (T : Type -> Type)
    `{Monoid W}
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T} `{Toset T}
    `{! DecoratedMonad W T}
    `{! SetlikeMonad T}.

  Theorem ind_ret_iff {A} : forall w (a a' : A),
      (w, a') ∈d ret T a <-> w = Ƶ /\ a' = a.
  Proof.
    introv. unfold tosetd, compose.
    compose near a on left.
    rewrite (dmon_ret W T). unfold compose.
    rewrite (in_ret_iff T). now rewrite pair_equal_spec.
  Qed.

  Theorem ind_bindd_iff {A B} : forall t w b (f : W * A -> T B),
      (w, b) ∈d bindd T f t <->
      exists (a : A) (w1 w2 : W),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a) /\ w = w1 ● w2.
  Proof.
    introv. unfold tosetd.
    compose near t on left.
    reassociate -> on left.
    rewrite  (dec_bindd T).
    unfold bindd. unfold compose.
    rewrite (in_bind_iff T). split; intro hyp.
    - destruct hyp as [[w' a] [? ?]].
      cbn in H6; unfold id in H6.
      rewrite (in_shift_iff T) in H6.
      destruct H6 as [w2 [? ?]].
      exists a. exists w'. exists w2. split; auto.
    - destruct hyp as [a [w1 [w2 [? ?]]]].
      exists (w1, a). split; auto. cbn.
      rewrite (in_shift_iff T). exists w2. auto.
  Qed.

  (** *** Corollaries: [tosetd] and [bind] *)
  (******************************************************************************)
  Theorem ind_bind_iff {A B} : forall t w b (f : A -> T B),
      (w, b) ∈d bind T f t <->
      exists (a : A) (w1 w2 : W),
        (w1, a) ∈d t /\ (w2, b) ∈d f a /\ w = w1 ● w2.
  Proof.
    introv. rewrite (bind_to_bindd T).
    now rewrite ind_bindd_iff.
  Qed.

  (** *** Corollaries: [toset] and [bindd] *)
  (******************************************************************************)
  Theorem in_bindd_iff {A B} : forall t b (f : W * A -> T B),
      b ∈ bindd T f t <->
      exists (a : A) (w1 : W),
        (w1, a) ∈d t /\ b ∈ f (w1, a).
  Proof.
    introv. rewrite (ind_of_in T).
    setoid_rewrite ind_bindd_iff. split.
    - intros. preprocess. do 2 eexists.
      split; eauto. eapply (in_of_ind T); eauto.
    - intros [a [w [in1 in2]]]. rewrite (ind_of_in T) in in2.
      destruct in2 as [w2 ?]. exists (w ● w2) a w w2.
      auto.
  Qed.

End decorated_setlike_properties.

(** ** Respectfulness properties *)
(******************************************************************************)
Section decorated_setlike_respectfulness.

  Context
    (T : Type -> Type)
    `{Monoid W}
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T} `{Toset T}
    `{! DecoratedMonad W T}
    `{! SetlikeMonad T}.

    Theorem bindd_respectful {A B} : forall (t : T A) (f g : W * A -> T B),
        (forall w a, (w, a) ∈d t -> f (w, a) = g (w, a)) ->
        bindd T f t = bindd T g t.
    Proof.
      intros. unfold bindd, compose.
      eapply (SetlikeMonad.bind_respectful T); auto.
      intros [? ?]; eauto.
    Qed.

    Corollary bindd_respectful_id {A} : forall (t : T A) (f : W * A -> T A),
        (forall w a, (w, a) ∈d t -> f (w, a) = ret T a) ->
        bindd T f t = t.
    Proof.
      intros. replace t with (bindd T (ret T ∘ extract (prod W)) t) at 2
        by (now rewrite (bindd_id T)).
      now apply bindd_respectful.
    Qed.

    Corollary bindd_respectful_fmapd {A B} : forall (t : T A) (f : W * A -> T B) (g : W * A -> B),
        (forall w a, (w, a) ∈d t -> f (w, a) = ret T (g (w, a))) ->
        bindd T f t = fmapd T g t.
    Proof.
      introv. rewrite (fmapd_to_bindd T).
      intros ?. now apply bindd_respectful.
    Qed.

    Corollary bindd_respectful_bind {A B} : forall (t : T A) (f : W * A -> T B) (g : A -> T B),
        (forall w a, (w, a) ∈d t -> f (w, a) = g a) ->
        bindd T f t = bind T g t.
    Proof.
      introv. rewrite (bind_to_bindd T).
      intros ?. now apply bindd_respectful.
    Qed.

    Corollary bindd_respectful_fmap {A B} : forall (t : T A) (f : W * A -> T B) (g : A -> B),
        (forall w a, (w, a) ∈d t -> f (w, a) = ret T (g a)) ->
        bindd T f t = fmap T g t.
    Proof.
      introv. rewrite (fmap_to_bindd T).
      intros; now apply bindd_respectful.
    Qed.

End decorated_setlike_respectfulness.
