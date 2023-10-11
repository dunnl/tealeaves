From Tealeaves Require Export
  Functors.Writer
  Classes.Kleisli.DecoratedFunctor.

Import Classes.Kleisli.Monad.Notations.
Import Classes.Kleisli.Comonad.Notations.
Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W T A B C.

(** * Decorated Monads *)
(******************************************************************************)

(** ** The [bindd] operation *)
(******************************************************************************)
Class Bindd (M : Type) (U T : Type -> Type):=
  bindd : forall (A B : Type), (M * A -> U B) -> T A -> T B.

Definition kc5 (W : Type) (T : Type -> Type)
  `{Bindd W T T} `{Monoid_op W}
  {A B C : Type} :
  (W * B -> T C) ->
  (W * A -> T B) ->
  (W * A -> T C) :=
  fun g f '(w, a) => @bindd W T T _ B C (g ⦿ w) (f (w, a)).

#[local] Infix "⋆5" := (kc5 _ _) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedMonad
  {W : Type}
  (T : Type -> Type)
  `{Return T}
  `{Bindd W T T}
  `{Monoid_op W} `{Monoid_unit W}
  :=
  { kmond_monoid :> Monoid W;
    kmond_bindd0 : forall (A B : Type) (f : W * A -> T B),
      @bindd W T T _ A B f  ∘ ret T A = f ∘ ret (W ×) A;
    kmond_bindd1 : forall (A : Type),
      @bindd W T T _ A A (ret T A ∘ extract (W ×) A) = @id (T A);
    kmond_bindd2 : forall (A B C : Type) (g : W * B -> T C) (f : W * A -> T B),
      @bindd W T T _ B C g ∘ @bindd W T T _ A B f = @bindd W T T _ A C (g ⋆5 f);
  }.

#[local] Arguments bindd {M}%type_scope {U}%function_scope (T)%function_scope {Bindd} {A B}%type_scope _%function_scope _.

(** * Kleisli category *)
(******************************************************************************)
Section DecoratedMonad_kleisli_category.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  (** ** Interaction with [incr], [preincr] *)
  (******************************************************************************)
  Lemma kc5_incr : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      (g ∘ incr W w) ⋆5 (f ∘ incr W w) = (g ⋆5 f) ∘ incr W w.
  Proof.
    intros.
    unfold kc5.
    ext [w' a].
    unfold preincr.
    reassociate ->.
    rewrite (incr_incr W).
    reflexivity.
  Qed.

  Lemma kc5_preincr : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      (g ⋆5 f) ⦿ w = g ⦿ w ⋆5 f ⦿ w.
  Proof.
    intros. unfold preincr.
    now rewrite kc5_incr.
  Qed.

  (** ** Right identity law *)
  (******************************************************************************)
  Theorem kc5_id_r {B C} : forall (g : W * B -> T C),
      g ⋆5 (ret T B ∘ extract (W ×) B) = g.
  Proof.
    intros.
    unfold kc5.
    ext [w a].
    unfold compose; cbn.
    compose near a on left.
    rewrite (kmond_bindd0).
    rewrite (preincr_ret W).
    reflexivity.
  Qed.

  (** ** Left identity law *)
  (******************************************************************************)
  Theorem kc5_id_l {A B} : forall (f : W * A -> T B),
      (ret T B ∘ extract (W ×) B) ⋆5 f = f.
  Proof.
    intros.
    unfold kc5.
    ext [w a].
    rewrite (preincr_assoc).
    rewrite (extract_preincr).
    now rewrite (kmond_bindd1).
  Qed.

  (** ** Associativity law *)
  (******************************************************************************)
  Theorem kc5_assoc {A B C D} : forall (h : W * C -> T D) (g : W * B -> T C) (f : W * A -> T B),
      h ⋆5 (g ⋆5 f) = (h ⋆5 g) ⋆5 f.
  Proof.
    intros. unfold kc5.
    ext [w a].
    compose near (f (w, a)) on left.
    rewrite (kmond_bindd2).
    rewrite <- (kc5_preincr).
    reflexivity.
  Qed.

End DecoratedMonad_kleisli_category.

(** * Derived instances *)
(******************************************************************************)
Module DerivedInstances.

  Section operations.

    Context
      (T : Type -> Type)
      `{Return T}
      `{Bindd W T T}.

    #[export] Instance Map_Bindd: Map T := fun A B f => bindd T (ret T B ∘ f ∘ extract (W ×) A).
    #[export] Instance Bind_Bindd: Bind T T := fun A B f => bindd T (f ∘ extract (W ×) A).
    #[export] Instance Mapd_Bindd: Mapd W T := fun A B f => bindd T (ret T B ∘ f).

    (** ** Rewriting rules for special cases of <<binddt>> *)
    (******************************************************************************)
    Lemma bind_to_bindd `(f : A -> T B) :
      @bind T T _ A B f = bindd T (f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    Lemma mapd_to_bindd `(f : W * A -> B):
      @mapd W T _ A B f = bindd T (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindd `(f : A -> B):
      @map T _ A B f = bindd T (ret T B ∘ f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

  End operations.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Section kc_special_cases.

    Context
      (T : Type -> Type)
      `{DecoratedMonad W T}.

    (** *** Homogeneous cases *)
    (******************************************************************************)
    Lemma kc5_44 : forall `(g : W * B -> C) `(f : W * A -> B),
        (ret T C ∘ g) ⋆5 (ret T B ∘ f) = ret T C ∘ (g ⋆4 f).
    Proof.
      intros. unfold kc5. ext [w' a].
      unfold compose at 2.
      compose near (f (w', a)).
      rewrite (kmond_bindd0).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

    Lemma kc5_11 : forall `(g : B -> T C) `(f : A -> T B),
        (g ∘ extract (W ×) B) ⋆5 (f ∘ extract (W ×) A) = (g ⋆1 f) ∘ extract (W ×) A.
    Proof.
      intros. unfold kc5. ext [w a].
      rewrite (extract_preincr2).
      reflexivity.
    Qed.

    Lemma kc5_00 : forall `(g : B -> C) `(f : A -> B),
        (ret T C ∘ g ∘ extract (W ×) B) ⋆5 (ret T B ∘ f ∘ extract (W ×) A) =
          ret T C ∘ (g ∘ f) ∘ extract (W ×) A.
    Proof.
      intros. unfold kc5. ext [w a].
      unfold compose at 3 4.
      cbn.
      compose near (f a) on left.
      rewrite (kmond_bindd0).
      rewrite (extract_preincr2).
      reflexivity.
    Qed.

    (** *** Heterogeneous cases *)
    (******************************************************************************)
    Lemma kc5_54 {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
        g ⋆5 (ret T B ∘ f) = g ⋆4 f.
    Proof.
      intros. unfold kc5, kc4.
      ext [w a]. unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite (kmond_bindd0).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

    Lemma kc5_51 {A B C} : forall (g : W * B -> T C) (f : A -> T B),
        g ⋆5 (f ∘ extract (W ×) A) =
          ((fun '(w, t) => bindd T (g ⦿ w) t) ∘ map (W ×) f).
    Proof.
      intros. ext [w a]. reflexivity.
    Qed.

    Lemma kc5_50 {A B C} : forall (g : W * B -> T C) (f : A -> B),
        g ⋆5 (ret T B ∘ f ∘ extract (W ×) A) =
          g ∘ map (W ×) f.
    Proof.
      intros. ext [w a]. unfold kc5.
      unfold compose; cbn.
      compose near (f a).
      rewrite (kmond_bindd0).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

    Lemma kc5_45 {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
        (ret T C ∘ g) ⋆5 f = fun '(w, t) => @mapd W T _ B C (g ⦿ w) (f (w, t)).
    Proof.
      reflexivity.
    Qed.

    Lemma kc5_15 {A B C} : forall (g : B -> T C) (f : W * A -> T B),
        (g ∘ extract (W ×) B) ⋆5 f = g ⋆1 f.
    Proof.
      intros. unfold kc5, kc1.
      ext [w a].
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    Lemma kc5_05 {A B C} : forall (g : B -> C) (f : W * A -> T B),
        (ret T C ∘ g ∘ extract (W ×) B) ⋆5 f =
          map T g ∘ f.
    Proof.
      intros. ext [w a]. unfold kc5.
      rewrite (extract_preincr2).
      reflexivity.
    Qed.

    Lemma kc5_14 {A B C} : forall (g : B -> T C) (f : W * A -> B),
        (g ∘ extract (W ×) B) ⋆5 (ret T B ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc5. ext [w a].
      unfold compose at 2; cbn.
      compose near (f (w, a)) on left.
      rewrite (kmond_bindd0).
      rewrite (extract_preincr2).
      reflexivity.
    Qed.

    Lemma kc5_41 {A B C} : forall (g : W * B -> C) (f : A -> T B),
        (ret T C ∘ g) ⋆5 (f ∘ extract (W ×) A) = (fun '(w, a) => @mapd W T _ B C (g ⦿ w) (f a)).
    Proof.
      reflexivity.
    Qed.

    Lemma kc5_04 {A B C} : forall (g : B -> C) (f : W * A -> B),
        (ret T C ∘ g ∘ extract (W ×) B) ⋆5 (ret T B ∘ f) = ret T C ∘ g ∘ f.
    Proof.
      intros. unfold kc5. ext [w a].
      unfold compose at 3; cbn.
      compose near (f (w, a)) on left.
      rewrite (kmond_bindd0).
      reflexivity.
    Qed.

    Lemma kc5_40 {A B C} : forall (g : W * B -> C) (f : A -> B),
        (ret T C ∘ g) ⋆5 (ret T B ∘ f ∘ extract (W ×) A) = ret T C ∘ (g ∘ map (W ×) f).
    Proof.
      intros. unfold kc5. ext [w a].
      unfold compose; cbn.
      compose near (f a).
      rewrite (kmond_bindd0).
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

  End kc_special_cases.

  (** ** Special cases for composition laws *)
  (******************************************************************************)
  Section laws.

    Context
      (T : Type -> Type)
      `{DecoratedMonad W T}.

    (** *** Composition with <<bind>> *)
    (******************************************************************************)
    Corollary bind_bindd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
        @bind T T _ B C g ∘ bindd T f = bindd T (g ⋆1 f).
    Proof.
      intros.
      rewrite (bind_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_15 T).
      reflexivity.
    Qed.

    Corollary bindd_bind {A B C} : forall (g : W * B -> T C) (f : A -> T B),
        bindd T g ∘ @bind T T _ A B f = bindd T ((fun '(w, t) => bindd T (g ⦿ w) t) ∘ map (W ×) f).
    Proof.
      intros.
      rewrite (bind_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_51).
      reflexivity.
    Qed.

    (** *** Composition with <<mapd>> *)
    (******************************************************************************)
    Lemma bindd_mapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
        bindd T g ∘ @mapd W T _ A B f = bindd T (g ⋆4 f).
    Proof.
      intros.
      rewrite (mapd_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_54 T).
      reflexivity.
    Qed.

    Corollary mapd_bindd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
        @mapd W T _ B C g ∘ bindd T f = bindd T (fun '(w, t) => @mapd W T _ B C (g ⦿ w) (f (w, t))).
    Proof.
      intros.
      rewrite (mapd_to_bindd).
      rewrite (kmond_bindd2 ).
      rewrite (kc5_45 T).
      reflexivity.
    Qed.

    (** *** Composition with <<map>> *)
    (******************************************************************************)
    Lemma bindd_map {A B C} : forall (g : W * B -> T C) (f : A -> B),
        bindd T g ∘ map T f = bindd T (g ∘ map (prod W) f).
    Proof.
      intros.
      rewrite (map_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_50 T).
      reflexivity.
    Qed.

    Corollary map_bindd {A B C} : forall (g : B -> C) (f : W * A -> T B),
        map T g ∘ bindd T f = bindd T (map T g ∘ f).
    Proof.
      intros.
      rewrite (map_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_05).
      reflexivity.
    Qed.

    (** *** Composition between <<mapd>> and <<mapd>> *)
    (******************************************************************************)
    Lemma mapd_mapd : forall (A B C : Type) (g : W * B -> C) (f : W * A -> B),
        @mapd W T _ B C g ∘ @mapd W T _ A B f = @mapd W T _ A C (g ⋆4 f).
    Proof.
      intros.
      do 2 rewrite (mapd_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_44 T).
      reflexivity.
    Qed.

    (** *** Composition between <<bind>> and <<bind>> *)
    (******************************************************************************)
    Lemma bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        @bind T T _ B C g ∘ @bind T T _ A B f = @bind T T _ A C (g ⋆1 f).
    Proof.
      intros.
      do 2 rewrite (bind_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_11 T).
      reflexivity.
    Qed.

    (** *** Composition between <<mapd>> and <<bind>> *)
    (******************************************************************************)
    Lemma mapd_bind : forall (A B C : Type) (g : W * B -> C) (f : A -> T B),
        @mapd W T _ B C g ∘ @bind T T _ A B f =
          bindd T (fun '(w, a) => @mapd W T _ B C (g ⦿ w) (f a)).
    Proof.
      intros.
      rewrite (mapd_to_bindd).
      rewrite (bind_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_41 T).
      reflexivity.
    Qed.

    Lemma bind_mapd : forall (A B C : Type) (g : B -> T C) (f : W * A -> B),
        @bind T T _ B C g ∘ @mapd W T _ A B f =
          bindd T (g ∘ f).
    Proof.
      intros.
      rewrite (mapd_to_bindd).
      rewrite (bind_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_14 T).
      reflexivity.
    Qed.

    (** *** Composition between <<mapd>> and <<map>> *)
    (******************************************************************************)
    Lemma mapd_map : forall (A B C : Type) (g : W * B -> C) (f : A -> B),
        @mapd W T _ B C g ∘ map T f =
          @mapd W T _ A C (g ∘ map (W ×) f).
    Proof.
      intros.
      rewrite (mapd_to_bindd).
      rewrite (map_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_40 T).
      reflexivity.
    Qed.

    Lemma map_mapd : forall (A B C : Type) (g : W * B -> C) (f : A -> B),
        @mapd W T _ B C g ∘ map T f =
          @mapd W T _ A C (g ∘ map (W ×) f).
    Proof.
      intros.
      rewrite (mapd_to_bindd).
      rewrite (map_to_bindd).
      rewrite (kmond_bindd2).
      rewrite (kc5_40 T).
      reflexivity.
    Qed.

    (** *** Composition between <<bind>> and <<map>> *)
    (******************************************************************************)

  End laws.

  (** ** Derived typeclass instances *)
  (******************************************************************************)
  Section instances.

    Context
      (T : Type -> Type)
      `{DecoratedMonad W T}.

    #[export] Instance: Monad T.
    Proof.
      constructor.
      - intros. unfold_ops @Bind_Bindd; now rewrite (kmond_bindd0).
      - intros. unfold_ops @Bind_Bindd; now rewrite (kmond_bindd1).
      - intros. apply (bind_bind T).
    Qed.

    #[export] Instance: DecoratedFunctor W T.
    Proof.
      constructor; unfold_ops @Mapd_Bindd.
      - intros. now rewrite (kmond_bindd1).
      - apply (mapd_mapd T).
    Qed.

  End instances.

End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆5" := (kc5 _ _) (at level 60) : tealeaves_scope.
End Notations.
