From Tealeaves Require Export
  Functors.Writer
  Classes.Kleisli.Monad
  Theory.Kleisli.Monad.Properties
  Classes.Kleisli.Decorated.Functor
  Classes.Kleisli.Decorated.Monad
  Theory.Kleisli.Decorated.Prepromote.

Import Product.Notations.
Import Comonad.Notations.
Import Kleisli.Monad.Notations.
Import Decorated.Monad.Notations.

#[local] Generalizable Variables W T A B C.

(** * Lesser Kleisli operations *)
(******************************************************************************)
Module Operations.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Return T}
      `{Bindd W T T}.

    #[export] Instance Fmap_Bindd: Fmap T := fun A B f => bindd T (ret T ∘ f ∘ extract (W ×)).
    #[export] Instance Bind_Bindd: Bind T T := fun A B f => bindd T (f ∘ extract (W ×)).
    #[export] Instance Fmapd_Bindd: Fmapd W T := fun A B f => bindd T (ret T ∘ f).

  End with_kleisli.
End Operations.

Import Operations.

(** ** Lesser Kleisli composition laws *)
(******************************************************************************)
Section Kleisli_composition.

    Context
      `{Decorated.Monad.Monad W T}.

    (** *** Lifting context-agnostic substitutions *)
    Lemma kcompose_extract : forall `(g : B -> T C) `(f : A -> T B),
        (g ∘ extract (W ×)) ⋆dm (f ∘ extract (W ×)) = (g ⋆ f) ∘ extract (W ×).
    Proof.
      intros. unfold kcompose_dm.
      ext [w a]. rewrite prepromote_extract.
      reflexivity.
    Qed.

    (** *** Lifting context-sensitive maps *)
    Lemma kcompose_ret : forall `(g : W * B -> C) `(f : W * A -> B),
        (ret T ∘ g) ⋆dm (ret T ∘ f) = ret T ∘ (g co⋆ f).
    Proof.
      intros. unfold kcompose_dm.
      ext [w' a]. unfold compose at 2.
      compose near (f (w', a)).
      rewrite (kmond_bindd0 T).
      rewrite prepromote_ret.
      reflexivity.
    Qed.

  (** Composition when <<f>> has no substitution *)
  Theorem dm_kleisli_star1 {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      g ⋆dm (ret T ∘ f) = g co⋆ f.
  Proof.
    intros. unfold kcompose_dm, cokcompose.
    ext [w a]. unfold compose. cbn.
    unfold compose, id; cbn.
    compose near (f (w, a)) on left.
    rewrite (kmond_bindd0 T _).
    now rewrite (prepromote_ret).
  Qed.

  (** Composition when <<g>> is context-agnostic *)
  Theorem dm_kleisli_star2 {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      (g ∘ extract (W ×)) ⋆dm f = g ⋆ f.
  Proof.
    intros. unfold kcompose_dm.
    ext [w a]. rewrite prepromote_extract.
    reflexivity.
  Qed.

  (** Composition when <<f>> is context-agnostic *)
  Theorem dm_kleisli_star3 {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      g ⋆dm (f ∘ extract (W ×)) =
        ((fun '(w, t) => bindd T (prepromote w g) t) ∘ fmap (W ×) f).
  Proof.
    intros. unfold kcompose_dm.
    ext [w a]. reflexivity.
  Qed.

  (** Composition when <<g>> has no substitution *)
  Theorem dm_kleisli_star4 {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      (ret T ∘ g) ⋆dm f = fun '(w, t) => fmapd T (prepromote w g) (f (w, t)).
  Proof.
    reflexivity.
  Qed.

  (** Other laws *)
  (* Alternatively, this one could be proved using rewrite dm_kleisli_star1 *)
  Theorem dm_kleisli_star5 {A B C} : forall (g : B -> T C) (f : W * A -> B),
      (g ∘ extract (W ×)) ⋆dm (ret T ∘ f) = g ∘ f.
  Proof.
    intros. rewrite dm_kleisli_star2.
    rewrite ToFunctor.Instances.kcompose_asc2.
    unfold kcompose, bind, Bind_Bindd.
    rewrite (kmond_bindd0 T).
    reflexivity.
  Qed.

End Kleisli_composition.

(** ** Lessor Kleisli instances *)
(******************************************************************************)
Module Instances.

  Section with_monad.

    Context
      `{Decorated.Monad.Monad W T}.

    #[export] Instance: Kleisli.Monad.Monad T.
    Proof.
      constructor; unfold_ops @Bind_Bindd.
      - intros. now rewrite (kmond_bindd0 T).
      - intros. now rewrite (kmond_bindd1 T).
      - intros. rewrite (kmond_bindd2 T).
        rewrite kcompose_extract.
        reflexivity.
    Qed.

    #[export] Instance: Kleisli.Decorated.Functor.DecoratedFunctor W T.
    Proof.
      constructor; unfold_ops @Fmapd_Bindd.
      - intros. now rewrite (kmond_bindd1 T).
      - intros. rewrite (kmond_bindd2 T).
        rewrite kcompose_ret.
        reflexivity.
    Qed.

  End with_monad.

End Instances.

(** ** Lesser Kleisli composition laws *)
(******************************************************************************)
Section Kleisli_composition.

    Context
      `{Decorated.Monad.Monad W T}.

  (** *** Composition with <<bind>> *)
  (******************************************************************************)
  Corollary bind_bindd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      bind T g ∘ bindd T f = bindd T (g ⋆ f).
  Proof.
    intros. unfold_ops @Bind_Bindd.
    rewrite (kmond_bindd2 T).
    rewrite dm_kleisli_star2.
    reflexivity.
  Qed.


  Corollary bindd_bind {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      bindd T g ∘ bind T f = bindd T ((fun '(w, t) => bindd T (prepromote w g) t) ∘ fmap (W ×) f).
  Proof.
    introv. unfold_ops @Bind_Bindd.
    rewrite (kmond_bindd2 T).
    now rewrite dm_kleisli_star3.
  Qed.

  (** *** Composition with <<fmapd>> *)
  (******************************************************************************)
  Lemma bindd_fmapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      bindd T g ∘ fmapd T f = bindd T (g co⋆ f).
  Proof.
    introv. unfold_ops @Fmapd_Bindd.
    rewrite (kmond_bindd2 T).
    rewrite dm_kleisli_star1.
    reflexivity.
  Qed.

  Corollary fmapd_bindd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      fmapd T g ∘ bindd T f = bindd T (fun '(w, t) => fmapd T (prepromote w g) (f (w, t))).
  Proof.
    intros. unfold_ops @Fmapd_Bindd.
    rewrite (kmond_bindd2 T).
    rewrite dm_kleisli_star4.
    reflexivity.
  Qed.

  (** *** Composition with <<fmap>> *)
  (******************************************************************************)
  Lemma bindd_fmap {A B C} : forall (g : W * B -> T C) (f : A -> B),
      bindd T g ∘ fmap T f = bindd T (g ∘ fmap (prod W) f).
  Proof.
    intros. unfold_ops @Fmap_Bindd.
    rewrite (kmond_bindd2 T).
    reassociate ->.
    rewrite dm_kleisli_star1.
    rewrite (fmap_to_cobind (W ×)).
    reflexivity.
  Qed.

  Corollary fmap_bindd {A B C} : forall (g : B -> C) (f : W * A -> T B),
      fmap T g ∘ bindd T f = bindd T (fmap T g ∘ f).
  Proof.
    intros. unfold_ops @Fmap_Bindd.
    rewrite (kmond_bindd2 T).
    rewrite dm_kleisli_star2.
    reflexivity.
  Qed.

  (** *** Composition between <<fmapd>> and <<bind>> *)
  (******************************************************************************)

  (** *** Composition between <<fmapd>> and <<fmap>> *)
  (******************************************************************************)

  (** *** Composition between <<bind>> and <<fmap>> *)
  (******************************************************************************)

End Kleisli_composition.
