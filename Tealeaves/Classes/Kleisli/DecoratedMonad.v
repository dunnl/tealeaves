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
Class Bindd (W : Type) (U T : Type -> Type):=
  bindd : forall (A B : Type), (W * A -> U B) -> T A -> T B.

#[global] Arguments bindd {W}%type_scope {U T}%function_scope {Bindd} {A B}%type_scope.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc5 {W : Type} {T : Type -> Type}
  `{Bindd W T T} `{Monoid_op W}
  {A B C : Type} :
  (W * B -> T C) ->
  (W * A -> T B) ->
  (W * A -> T C) :=
  fun g f '(w, a) => @bindd W T T _ B C (g ⦿ w) (f (w, a)).

#[local] Infix "⋆5" := (kc5) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedMonad
  (W : Type)
  (T : Type -> Type)
  `{Return T}
  `{Bindd W T T}
  `{Monoid_op W} `{Monoid_unit W}
  :=
  { kmond_monoid :> Monoid W;
    kmond_bindd0 : forall (A B : Type) (f : W * A -> T B),
      @bindd W T T _ A B f  ∘ ret = f ∘ ret;
    kmond_bindd1 : forall (A : Type),
      @bindd W T T _ A A (ret ∘ extract) = @id (T A);
    kmond_bindd2 : forall (A B C : Type) (g : W * B -> T C) (f : W * A -> T B),
      @bindd W T T _ B C g ∘ @bindd W T T _ A B f = @bindd W T T _ A C (g ⋆5 f);
  }.

Class DecoratedMonadFull
  (W : Type)
  (T : Type -> Type)
  `{ret_inst : Return T}
  `{bindd_inst : Bindd W T T}
  `{mapd_inst : Mapd W T}
  `{bind_inst : Bind T T}
  `{map_inst : Map T}
  `{op : Monoid_op W} `{unit : Monoid_unit W}
  :=
  { kmondf_kmond :> DecoratedMonad W T;
    kmondf_map_compat : forall (A B : Type) (f : A -> B),
      map f = bindd (ret ∘ f ∘ extract);
    kmondf_mapd_compat : forall (A B : Type) (f : W * A -> B),
      mapd f = bindd (ret ∘ f);
    kmondf_bind_compat : forall (A B : Type) (f : A -> T B),
      bind f = bindd (f ∘ extract);
  }.

(** * Kleisli category *)
(******************************************************************************)
Section DecoratedMonad_kleisli_category.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  (** ** Interaction with [incr], [preincr] *)
  (******************************************************************************)
  Lemma kc5_incr : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      (g ∘ incr w) ⋆5 (f ∘ incr w) = (g ⋆5 f) ∘ incr w.
  Proof.
    intros.
    unfold kc5.
    ext [w' a].
    unfold preincr.
    reassociate ->.
    rewrite incr_incr.
    reflexivity.
  Qed.

  Lemma kc5_preincr : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      (g ⋆5 f) ⦿ w = g ⦿ w ⋆5 f ⦿ w.
  Proof.
    intros.
    unfold preincr.
    rewrite kc5_incr.
    reflexivity.
  Qed.

  (** ** Right identity law *)
  (******************************************************************************)
  Theorem kc5_id_r {B C} : forall (g : W * B -> T C),
      g ⋆5 (ret ∘ extract) = g.
  Proof.
    intros.
    unfold kc5.
    ext [w a].
    unfold compose; cbn.
    compose near a on left.
    rewrite kmond_bindd0.
    rewrite preincr_ret.
    reflexivity.
  Qed.

  (** ** Left identity law *)
  (******************************************************************************)
  Theorem kc5_id_l {A B} : forall (f : W * A -> T B),
      (ret ∘ extract) ⋆5 f = f.
  Proof.
    intros.
    unfold kc5.
    ext [w a].
    rewrite preincr_assoc.
    rewrite extract_preincr.
    rewrite kmond_bindd1.
    reflexivity.
  Qed.

  (** ** Associativity law *)
  (******************************************************************************)
  Theorem kc5_assoc {A B C D} : forall (h : W * C -> T D) (g : W * B -> T C) (f : W * A -> T B),
      h ⋆5 (g ⋆5 f) = (h ⋆5 g) ⋆5 f.
  Proof.
    intros. unfold kc5.
    ext [w a].
    compose near (f (w, a)) on left.
    rewrite kmond_bindd2.
    rewrite <- kc5_preincr.
    reflexivity.
  Qed.

End DecoratedMonad_kleisli_category.

(** * Derived instances *)
(******************************************************************************)
Module DerivedInstances.

  (** ** Derived operations *)
  (******************************************************************************)
  Section operations.

    Context
      `{Return T}
      `{Bindd W T T}.

    #[export] Instance Map_Bindd: Map T := fun A B f => bindd (ret ∘ f ∘ extract).
    #[export] Instance Bind_Bindd: Bind T T := fun A B f => bindd (f ∘ extract).
    #[export] Instance Mapd_Bindd: Mapd W T := fun A B f => bindd (ret ∘ f).

    Lemma bind_to_bindd `(f : A -> T B) :
      bind f = bindd (f ∘ extract).
    Proof.
      reflexivity.
    Qed.

    Lemma mapd_to_bindd `(f : W * A -> B):
      mapd f = bindd (ret ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindd `(f : A -> B):
      map f = bindd (ret ∘ f ∘ extract).
    Proof.
      reflexivity.
    Qed.

  End operations.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Section kc_special_cases.

    Context
      `{DecoratedMonad W T}.

    (** *** Homogeneous cases *)
    (******************************************************************************)
    Lemma kc5_44 : forall `(g : W * B -> C) `(f : W * A -> B),
        (ret ∘ g) ⋆5 (ret ∘ f) = ret ∘ (g ⋆4 f).
    Proof.
      intros. unfold kc5. ext [w' a].
      unfold compose at 2.
      compose near (f (w', a)).
      rewrite kmond_bindd0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc5_11 : forall `(g : B -> T C) `(f : A -> T B),
        g ∘ extract ⋆5 f ∘ extract = (g ⋆1 f) ∘ extract.
    Proof.
      intros. unfold kc5. ext [w a].
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    Lemma kc5_00 : forall `(g : B -> C) `(f : A -> B),
        (ret ∘ g ∘ extract) ⋆5 (ret ∘ f ∘ extract) =
          ret ∘ g ∘ f ∘ extract.
    Proof.
      intros. unfold kc5. ext [w a].
      unfold compose at 3 4.
      cbn.
      compose near (f a) on left.
      rewrite kmond_bindd0.
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    (** *** Heterogeneous cases *)
    (******************************************************************************)
    Lemma kc5_54 {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
        g ⋆5 (ret ∘ f) = g ⋆4 f.
    Proof.
      intros. unfold kc5, kc4.
      ext [w a]. unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite kmond_bindd0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc5_51 {A B C} : forall (g : W * B -> T C) (f : A -> T B),
        g ⋆5 (f ∘ extract) = (fun '(w, t) => bindd (g ⦿ w) t) ∘ map f.
    Proof.
      intros. ext [w a]. reflexivity.
    Qed.

    Lemma kc5_50 {A B C} : forall (g : W * B -> T C) (f : A -> B),
        g ⋆5 (ret ∘ f ∘ extract) = g ∘ map f.
    Proof.
      intros. ext [w a]. unfold kc5.
      unfold compose; cbn.
      compose near (f a).
      rewrite kmond_bindd0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc5_45 {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
        (ret ∘ g) ⋆5 f = fun '(w, t) => mapd (g ⦿ w) (f (w, t)).
    Proof.
      reflexivity.
    Qed.

    Lemma kc5_15 {A B C} : forall (g : B -> T C) (f : W * A -> T B),
        (g ∘ extract) ⋆5 f = g ⋆1 f.
    Proof.
      intros. unfold kc5, kc1.
      ext [w a].
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    Lemma kc5_05 {A B C} : forall (g : B -> C) (f : W * A -> T B),
        (ret ∘ g ∘ extract) ⋆5 f = map g ∘ f.
    Proof.
      intros. ext [w a]. unfold kc5.
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    Lemma kc5_14 {A B C} : forall (g : B -> T C) (f : W * A -> B),
        (g ∘ extract) ⋆5 (ret ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc5. ext [w a].
      unfold compose at 2; cbn.
      compose near (f (w, a)) on left.
      rewrite kmond_bindd0.
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    Lemma kc5_41 {A B C} : forall (g : W * B -> C) (f : A -> T B),
        (ret ∘ g) ⋆5 (f ∘ extract) = fun '(w, a) => mapd (g ⦿ w) (f a).
    Proof.
      reflexivity.
    Qed.

    Lemma kc5_04 {A B C} : forall (g : B -> C) (f : W * A -> B),
        (ret ∘ g ∘ extract) ⋆5 (ret ∘ f) = ret ∘ g ∘ f.
    Proof.
      intros. unfold kc5. ext [w a].
      unfold compose at 3; cbn.
      compose near (f (w, a)) on left.
      rewrite kmond_bindd0.
      reflexivity.
    Qed.

    Lemma kc5_40 {A B C} : forall (g : W * B -> C) (f : A -> B),
        (ret ∘ g) ⋆5 (ret ∘ f ∘ extract) = ret ∘ g ∘ map f.
    Proof.
      intros. unfold kc5. ext [w a].
      unfold compose; cbn.
      compose near (f a).
      rewrite kmond_bindd0.
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite preincr_ret.
      reflexivity.
    Qed.

  End kc_special_cases.

  (** ** Special cases for composition laws *)
  (******************************************************************************)
  Section laws.

    Context
      `{DecoratedMonad W T}.

    (** *** Composition with <<bind>> *)
    (******************************************************************************)
    Corollary bind_bindd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
        bind g ∘ bindd f = bindd (g ⋆1 f).
    Proof.
      intros.
      rewrite bind_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_15.
      reflexivity.
    Qed.

    Corollary bindd_bind {A B C} : forall (g : W * B -> T C) (f : A -> T B),
        bindd g ∘ bind f = bindd ((fun '(w, t) => bindd (g ⦿ w) t) ∘ map f).
    Proof.
      intros.
      rewrite bind_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_51.
      reflexivity.
    Qed.

    (** *** Composition with <<mapd>> *)
    (******************************************************************************)
    Lemma bindd_mapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
        bindd g ∘ mapd f = bindd (g ⋆4 f).
    Proof.
      intros.
      rewrite mapd_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_54.
      reflexivity.
    Qed.

    Corollary mapd_bindd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
        mapd g ∘ bindd f = bindd (fun '(w, t) => mapd (g ⦿ w) (f (w, t))).
    Proof.
      intros.
      rewrite mapd_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_45.
      reflexivity.
    Qed.

    (** *** Composition with <<map>> *)
    (******************************************************************************)
    Lemma bindd_map {A B C} : forall (g : W * B -> T C) (f : A -> B),
        bindd g ∘ map f = bindd (g ∘ map f).
    Proof.
      intros.
      rewrite map_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_50.
      reflexivity.
    Qed.

    Corollary map_bindd {A B C} : forall (g : B -> C) (f : W * A -> T B),
        map g ∘ bindd f = bindd (map g ∘ f).
    Proof.
      intros.
      rewrite map_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_05.
      reflexivity.
    Qed.

    (** *** Composition between <<mapd>> and <<mapd>> *)
    (******************************************************************************)
    Lemma mapd_mapd : forall (A B C : Type) (g : W * B -> C) (f : W * A -> B),
        mapd g ∘ mapd f = mapd (g ⋆4 f).
    Proof.
      intros.
      do 2 rewrite mapd_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_44.
      reflexivity.
    Qed.

    (** *** Composition between <<bind>> and <<bind>> *)
    (******************************************************************************)
    Lemma bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind g ∘ bind f = bind (g ⋆1 f).
    Proof.
      intros.
      do 2 rewrite bind_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_11.
      reflexivity.
    Qed.

    (** *** Composition between <<mapd>> and <<bind>> *)
    (******************************************************************************)
    Lemma mapd_bind : forall (A B C : Type) (g : W * B -> C) (f : A -> T B),
        mapd g ∘ bind f = bindd (fun '(w, a) => mapd (g ⦿ w) (f a)).
    Proof.
      intros.
      rewrite mapd_to_bindd.
      rewrite bind_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_41.
      reflexivity.
    Qed.

    Lemma bind_mapd : forall (A B C : Type) (g : B -> T C) (f : W * A -> B),
        bind g ∘ mapd f = bindd (g ∘ f).
    Proof.
      intros.
      rewrite mapd_to_bindd.
      rewrite bind_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_14.
      reflexivity.
    Qed.

    (** *** Composition between <<mapd>> and <<map>> *)
    (******************************************************************************)
    Lemma mapd_map : forall (A B C : Type) (g : W * B -> C) (f : A -> B),
        mapd g ∘ map f = mapd (g ∘ map f).
    Proof.
      intros.
      rewrite mapd_to_bindd.
      rewrite map_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_40.
      reflexivity.
    Qed.

    Lemma map_mapd : forall (A B C : Type) (g : W * B -> C) (f : A -> B),
        mapd g ∘ map f = mapd (g ∘ map f).
    Proof.
      intros.
      rewrite mapd_to_bindd.
      rewrite map_to_bindd.
      rewrite kmond_bindd2.
      rewrite kc5_40.
      reflexivity.
    Qed.

    (** *** Composition between <<bind>> and <<map>> *)
    (******************************************************************************)

  End laws.

  (** ** Derived typeclass instances *)
  (******************************************************************************)
  Section instances.

    Context
      `{DecoratedMonad W T}.

    #[export] Instance Monad_DecoratedMonad : Monad T.
    Proof.
      constructor.
      - intros. unfold_ops @Bind_Bindd; now rewrite kmond_bindd0.
      - intros. unfold_ops @Bind_Bindd; now rewrite kmond_bindd1.
      - intros. apply bind_bind.
    Qed.

    #[export] Instance DecoratedFunctor_DecoratedMonad : DecoratedFunctor W T.
    Proof.
      constructor; unfold_ops @Mapd_Bindd.
      - intros. now rewrite kmond_bindd1.
      - apply mapd_mapd.
    Qed.

  End instances.

End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆5" := (kc5) (at level 60) : tealeaves_scope.
End Notations.
