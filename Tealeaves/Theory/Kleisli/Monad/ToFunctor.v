From Tealeaves Require Export
  Classes.Kleisli.Monad.

Import Monad.Notations.

#[local] Generalizable Variables T A B C D.

(** * Kleisli monad to functor *)
(******************************************************************************)

(** ** <<fmap>> operation *)
(******************************************************************************)
Module Operation.
  Section with_bind.

    Context
      (T : Type -> Type)
      `{Return T}
      `{Bind T T}.

    #[export] Instance Fmap_Bind : Fmap T :=
      fun `(f : A -> B) => bind T (ret T ∘ f).

  End with_bind.
End Operation.

(** ** <<Functor>> instance *)
(******************************************************************************)
Module Instances.

  Import Operation.

  Section to_functor.

    Context
      (T : Type -> Type)
      `{Monad T}.

    #[export] Instance: Functor T.
    Proof.
      constructor.
      - intros. unfold transparent tcs.
        unfold compose. now rewrite (kmon_bind1 T).
      - intros. unfold transparent tcs.
        rewrite (kmon_bind2 T).
        unfold kcompose. reassociate <- near (bind T (ret T ∘ g)).
        now rewrite (kmon_bind0 T).
    Qed.

    (** *** Composition with [fmap] *)
    (******************************************************************************)
    Lemma bind_fmap : forall `(g : B -> T C) `(f : A -> B),
        bind T g ∘ fmap T f = bind T (g ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite (kmon_bind2 T).
      fequal. unfold kcompose.
      reassociate <-. rewrite (kmon_bind0 T).
      reflexivity.
    Qed.

    Corollary fmap_bind : forall `(g : B -> C) `(f : A -> T B),
        fmap T g ∘ bind T f = bind T (fmap T g ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite (kmon_bind2 T).
      reflexivity.
    Qed.

  (** *** Special cases for Kleisli composition *)
  (******************************************************************************)
  Lemma kcompose_ret : forall `(g : B -> C) `(f : A -> B),
      (ret T ∘ g) ⋆ (ret T ∘ f) = ret T ∘ (g ∘ f).
  Proof.
    intros. unfold kcompose.
    reassociate <-. now rewrite (kmon_bind0 T).
  Qed.

  Lemma kcompose10 : forall `(g : B -> T C) `(f : A -> B),
      g ⋆ (ret T ∘ f) = g ∘ f.
  Proof.
    intros. unfold kcompose.
    reassociate <-. now rewrite (kmon_bind0 T).
  Qed.

  Lemma kcompose01 : forall `(g : B -> C) `(f : A -> T B),
      (ret T ∘ g) ⋆ f = fmap T g ∘ f.
  Proof.
    intros. unfold kcompose.
    reflexivity.
  Qed.

  (** *** Other rules for Kleisli composition *)
  (******************************************************************************)
  Lemma kcompose_asc1 : forall `(g : B -> C) `(h : C -> T D) `(f : A -> T B),
      (h ∘ g) ⋆ f = h ⋆ (fmap T g ∘ f).
  Proof.
    intros. unfold kcompose.
    reassociate <-.
    rewrite (bind_fmap).
    reflexivity.
  Qed.

  Lemma kcompose_asc2 : forall `(f : A -> B) `(g : B -> T C) `(h : C -> T D),
      h ⋆ (g ∘ f) = (h ⋆ g) ∘ f.
  Proof.
    intros. unfold kcompose.
    reflexivity.
  Qed.

  End to_functor.

End Instances.
