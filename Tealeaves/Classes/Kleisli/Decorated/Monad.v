From Tealeaves Require Export
  Functors.Writer.

Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W T A B C.

(** * The <<prepromote>> operation *)
(** A decorated monad is a decorated functor whose monad operations
    are compatible with the decorated structure. *)
(******************************************************************************)

Definition preincr `{Monoid_op W} (w : W) `(f : W * A -> B) :=
  f ∘ incr w.

Lemma preincr_zero `{Monoid W} : forall `(f : W * A -> B),
    preincr Ƶ f = f.
Proof.
  intros. unfold preincr.
  now rewrite incr_zero.
Qed.

Lemma preincr_incr1 `{Monoid W} : forall `(f : W * A -> B) (w1 : W) (w2 : W),
    preincr w2 (f ∘ incr w1) = f ∘ (incr (w1 ● w2)).
Proof.
  intros. unfold preincr.
  reassociate ->.
  now rewrite (incr_incr).
Qed.

Lemma preincr_preincr1 `{Monoid W} : forall `(f : W * A -> B) (w1 : W) (w2 : W),
    preincr w2 (preincr w1 f) = preincr (w1 ● w2) f.
Proof.
  intros. unfold preincr.
  reassociate ->.
  now rewrite (incr_incr).
Qed.

Lemma preincr_ret `{Monoid W} : forall `(f : W * A -> B) (w : W),
    preincr w f ∘ ret (W ×) = f ∘ pair w.
Proof.
  intros. ext a. cbv.
  change (op w unit0) with (w ● Ƶ).
  now simpl_monoid.
Qed.

Lemma preincr_extract `{Monoid W} : forall `(f : A -> B) (w : W),
    preincr w (f ∘ extract (W ×)) = f ∘ extract (W ×).
Proof.
  intros. now ext [w' a].
Qed.

Lemma preincr_extract2 `{Monoid W} : forall (A : Type) (w : W),
    preincr w (extract (W ×)) = extract (W ×) (A := A).
Proof.
  intros. now ext [w' a].
Qed.

(** * The <<Bindd>> operation *)
(** A decorated monad is a decorated functor whose monad operations
    are compatible with the decorated structure. *)
(******************************************************************************)
Section operations.

  Context
    (W : Type)
    (T : Type -> Type)
    (F : Type -> Type).

  Class Bindd :=
    bindd : forall (A B : Type), (W * A -> T B) -> F A -> F B.

End operations.

(** ** Kleisli composition *)
(** This definition is such that more recently seen binders (those
    deeper in the AST, closer to the variable occurrence) are seen on
    the _left_. So @f@ gets called on @([β0, β1, ... βn], v)@
    where @βn@ is the outermost binder. *)
(******************************************************************************)
Definition kcompose_dm {A B C} `{Bindd W T T} `{Monoid_op W} :
  (W * B -> T C) ->
  (W * A -> T B) ->
  (W * A -> T C) :=
  fun g f '(w, a) => bindd W T T B C (preincr w g) (f (w, a)).

#[local] Notation "g ⋆dm f" := (kcompose_dm g f) (at level 40) : tealeaves_scope.

(** ** Decorated Monad *)
(******************************************************************************)
Section class.

  Context
    {W : Type}
    (T : Type -> Type)
    `{Return T}
    `{Bindd W T T}
    `{Monoid_op W} `{Monoid_unit W}.

  Class Monad :=
    { kmond_monoid :> Monoid W;
      kmond_bindd0 : forall `(f : W * A -> T B),
        bindd W T T A B f  ∘ ret T (A := A) = f ∘ ret ((W ×));
      kmond_bindd1 : forall (A : Type),
        bindd W T T A A (ret T ∘ extract (W ×)) = @id (T A);
      kmond_bindd2 : forall `(g : W * B -> T C) `(f : W * A -> T B),
        bindd W T T B C g ∘ bindd W T T A B f = bindd W T T A C (g ⋆dm f);
    }.

End class.

Arguments bindd {W}%type_scope {T}%function_scope (F)%function_scope
  {Bindd} {A B}%type_scope _%function_scope _.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "g ⋆dm f" := (kcompose_dm g f) (at level 40) : tealeaves_scope.

End Notations.

(** * Kleisli composition *)
(******************************************************************************)
Section kleisli_composition.

  Context
    `{Decorated.Monad.Monad W T}.

  Lemma kcompose_incr : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      (g ∘ incr w) ⋆dm (f ∘ incr w) = (g ⋆dm f) ∘ incr w.
  Proof.
    intros. unfold kcompose_dm.
    ext [w' a]. rewrite preincr_incr1.
    reflexivity.
  Qed.

  Lemma preincr_kcompose : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      preincr w (g ⋆dm f) = (preincr w g) ⋆dm (preincr w f).
  Proof.
    intros. unfold preincr. now rewrite kcompose_incr.
  Qed.

  Theorem dm_kleisli_id_r {B C} : forall (g : W * B -> T C),
      g ⋆dm (ret T ∘ extract (W ×)) = g.
  Proof.
    intros. unfold kcompose_dm.
    ext [w a]. unfold compose. cbn.
    compose near a on left.
    rewrite (kmond_bindd0 T _).
    now rewrite preincr_ret.
  Qed.

  Theorem dm_kleisli_id_l {A B} : forall (f : W * A -> T B),
      (ret T ∘ extract (W ×)) ⋆dm f = f.
  Proof.
    intros. unfold kcompose_dm.
    ext [w a]. rewrite preincr_extract.
    now rewrite (kmond_bindd1 T _).
  Qed.

  Theorem dm_kleisli_assoc {A B C D} : forall (h : W * C -> T D) (g : W * B -> T C) (f : W * A -> T B),
      h ⋆dm (g ⋆dm f) = (h ⋆dm g) ⋆dm f.
  Proof.
    intros. unfold kcompose_dm at 3.
    ext [w a]. unfold preincr.
    rewrite <- kcompose_incr.
    rewrite <- (kmond_bindd2 T).
    reflexivity.
  Qed.

End kleisli_composition.


From Tealeaves Require Import
  Classes.Kleisli.Monad
  Classes.Kleisli.Decorated.Functor.

(** * Derived instances *)
(******************************************************************************)
Module Derived.

  Import
    Kleisli.Monad.Notations
    Comonad.Notations.

  Section operations.

    Context
      (T : Type -> Type)
      `{Return T}
      `{Bindd W T T}.

    #[export] Instance Fmap_Bindd: Fmap T := fun A B f => bindd T (ret T ∘ f ∘ extract (W ×)).
    #[export] Instance Bind_Bindd: Bind T T := fun A B f => bindd T (f ∘ extract (W ×)).
    #[export] Instance Fmapd_Bindd: Fmapd W T := fun A B f => bindd T (ret T ∘ f).

  End operations.

  (** ** Lesser Kleisli composition laws *)
  (******************************************************************************)
  Section Kleisli_composition.

    Context
      (T : Type -> Type)
      `{Decorated.Monad.Monad W T}.

    (** *** Lifting context-agnostic substitutions *)
    Lemma kcompose_extract : forall `(g : B -> T C) `(f : A -> T B),
        (g ∘ extract (W ×)) ⋆dm (f ∘ extract (W ×)) = (g ⋆ f) ∘ extract (W ×).
    Proof.
      intros. unfold kcompose_dm.
      ext [w a]. rewrite preincr_extract.
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
      rewrite preincr_ret.
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
      now rewrite (preincr_ret).
    Qed.

    (** Composition when <<g>> is context-agnostic *)
    Theorem dm_kleisli_star2 {A B C} : forall (g : B -> T C) (f : W * A -> T B),
        (g ∘ extract (W ×)) ⋆dm f = g ⋆ f.
    Proof.
      intros. unfold kcompose_dm.
      ext [w a]. rewrite preincr_extract.
      reflexivity.
    Qed.

    (** Composition when <<f>> is context-agnostic *)
    Theorem dm_kleisli_star3 {A B C} : forall (g : W * B -> T C) (f : A -> T B),
        g ⋆dm (f ∘ extract (W ×)) =
          ((fun '(w, t) => bindd T (preincr w g) t) ∘ fmap (W ×) f).
    Proof.
      intros. unfold kcompose_dm.
      ext [w a]. reflexivity.
    Qed.

    (** Composition when <<g>> has no substitution *)
    Theorem dm_kleisli_star4 {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
        (ret T ∘ g) ⋆dm f = fun '(w, t) => fmapd T (preincr w g) (f (w, t)).
    Proof.
      reflexivity.
    Qed.

    (** Other laws *)
    (* Alternatively, this one could be proved using rewrite dm_kleisli_star1 *)
    Theorem dm_kleisli_star5 {A B C} : forall (g : B -> T C) (f : W * A -> B),
        (g ∘ extract (W ×)) ⋆dm (ret T ∘ f) = g ∘ f.
    Proof.
      intros. rewrite dm_kleisli_star2.
      rewrite ToFunctor.kcompose_asc2.
      unfold kcompose, bind, Bind_Bindd.
      rewrite (kmond_bindd0 T).
      reflexivity.
    Qed.

  End Kleisli_composition.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Decorated.Monad.Monad W T}.

    #[export] Instance: Kleisli.Monad.Monad T.
    Proof.
      constructor; unfold_ops @Bind_Bindd.
      - intros. now rewrite (kmond_bindd0 T).
      - intros. now rewrite (kmond_bindd1 T).
      - intros. rewrite (kmond_bindd2 T).
        rewrite (kcompose_extract T).
        reflexivity.
    Qed.

    #[export] Instance: Kleisli.Decorated.Functor.DecoratedFunctor W T.
    Proof.
      constructor; unfold_ops @Fmapd_Bindd.
      - intros. now rewrite (kmond_bindd1 T).
      - intros. rewrite (kmond_bindd2 T).
        rewrite (kcompose_ret T).
        reflexivity.
    Qed.

  End with_monad.

  Section laws.

    Context
      (T : Type -> Type)
      `{Decorated.Monad.Monad W T}.

    (** *** Composition with <<bind>> *)
    (******************************************************************************)
    Corollary bind_bindd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
        bind T g ∘ bindd T f = bindd T (g ⋆ f).
    Proof.
      intros. unfold_ops @Bind_Bindd.
      rewrite (kmond_bindd2 T).
      rewrite (dm_kleisli_star2 T).
      reflexivity.
    Qed.


    Corollary bindd_bind {A B C} : forall (g : W * B -> T C) (f : A -> T B),
        bindd T g ∘ bind T f = bindd T ((fun '(w, t) => bindd T (preincr w g) t) ∘ fmap (W ×) f).
    Proof.
      introv. unfold_ops @Bind_Bindd.
      rewrite (kmond_bindd2 T).
      now rewrite (dm_kleisli_star3 T).
    Qed.

    (** *** Composition with <<fmapd>> *)
    (******************************************************************************)
    Lemma bindd_fmapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
        bindd T g ∘ fmapd T f = bindd T (g co⋆ f).
    Proof.
      introv. unfold_ops @Fmapd_Bindd.
      rewrite (kmond_bindd2 T).
      rewrite (dm_kleisli_star1 T).
      reflexivity.
    Qed.

    Corollary fmapd_bindd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
        fmapd T g ∘ bindd T f = bindd T (fun '(w, t) => fmapd T (preincr w g) (f (w, t))).
    Proof.
      intros. unfold_ops @Fmapd_Bindd.
      rewrite (kmond_bindd2 T).
      rewrite (dm_kleisli_star4 T).
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
      rewrite (dm_kleisli_star1 T).
      rewrite (fmap_to_cobind (W ×)).
      reflexivity.
    Qed.

    Corollary fmap_bindd {A B C} : forall (g : B -> C) (f : W * A -> T B),
        fmap T g ∘ bindd T f = bindd T (fmap T g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Bindd.
      rewrite (kmond_bindd2 T).
      rewrite (dm_kleisli_star2 T).
      reflexivity.
    Qed.

    (** *** Composition between <<fmapd>> and <<bind>> *)
    (******************************************************************************)

    (** *** Composition between <<fmapd>> and <<fmap>> *)
    (******************************************************************************)

    (** *** Composition between <<bind>> and <<fmap>> *)
    (******************************************************************************)

  End laws.

End Derived.
