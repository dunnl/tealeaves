From Tealeaves Require Export
  Classes.Applicative
  Classes.Comonad
  Functors.Environment.

Import Product.Notations.

#[local] Generalizable Variables W ϕ G A B C M.

(** * Kleisli presentation *)
(******************************************************************************)

(** ** Operation <<fmapdt>> *)
(******************************************************************************)
Section dt_operations.

  Context
    (W : Type)
    (F : Type -> Type).

  Class Fmapdt := fmapdt :
      forall `{Fmap G} `{Pure G} `{Mult G}
        {A B : Type} (f : W * A -> G B), F A -> G (F B).

End dt_operations.

#[local] Arguments fmapdt {W}%type_scope F%function_scope {Fmapdt}
  G%function_scope {H H0 H1} (A B)%type_scope f%function_scope _.

Definition kcompose_dt {A B C W : Type}
  `{Applicative G1}
  `{Applicative G2} :
  (W * B -> G2 C) ->
  (W * A -> G1 B) ->
  (W * A -> G1 (G2 C)) :=
  fun g f => fmap G1 g ∘ strength G1 ∘ cobind (prod W) f.

#[local] Notation "g ⋆dt f" := (kcompose_dt g f) (at level 40) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Section decorated_class.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Fmapdt E T}.

  Class DecoratedTraversableFunctor :=
    { kdtfun_fmapdt1 : forall (A : Type),
        fmapdt T (fun A => A) A A (extract (E ×)) = @id (T A);
      kdtfun_fmapdt2 : forall
        `{Applicative G1} `{Applicative G2}
        `(g : E * B -> G2 C) `(f : E * A -> G1 B),
        fmap G1 (fmapdt T G2 B C g) ∘ fmapdt T G1 A B f = fmapdt T (G1 ∘ G2) A C (g ⋆dt f);
      kdtfun_morph : forall `{ApplicativeMorphism G1 G2 ϕ} `(f : E * A -> G1 B),
        fmapdt T G2 A B (ϕ B ∘ f) = ϕ (T B) ∘ fmapdt T G1 A B f;
    }.

End decorated_class.

#[global] Arguments fmapdt {W}%type_scope F%function_scope {Fmapdt}
  G%function_scope {H H0 H1} {A B}%type_scope f%function_scope _.

From Tealeaves Require Import
  Classes.Kleisli.Decorated.Functor
  Classes.Kleisli.Traversable.Functor.

Import Strength.Notations Comonad.Notations.

(** * Derived instances *)
(******************************************************************************)
Module Derived.
  
  Section operations.

    Context
      (T : Type -> Type)
      `{Fmapdt W T}.

    #[export] Instance Fmap_Fmapdt: Fmap T := fun A B f => fmapdt T (fun A => A) (f ∘ extract (W ×)).
    #[export] Instance Fmapd_Fmapdt: Fmapd W T := fun A B f => fmapdt T (fun A => A) f.
    #[export] Instance Traverse_Fmapdt: Traverse T := fun G _ _ _ A B f => fmapdt T G (f ∘ extract (W ×)).

  End operations.

  Section kcompose_dt_lemmas.

    Context
      (T : Type -> Type)
      `{DecoratedTraversableFunctor W T}
      (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      (A B C : Type).
 
    Lemma kcompose_dt_00 :
      forall (A B C : Type) (f : A -> B) (g : B -> C),
        kcompose_dt (G1 := fun A => A) (G2 := fun A => A)
          (g ∘ extract (prod W)) (f ∘ extract (prod W)) = g ∘ f ∘ extract (prod W).
    Proof.
      intros. unfold kcompose_dt. unfold strength.
      unfold_ops @Fmap_I. rewrite <- (fmap_to_cobind (W ×)).
      now ext [w a].
    Qed.

    Lemma kcompose_dt_22 :
      forall (g : B -> G2 C) (f : A -> G1 B),
        (g ∘ extract (prod W)) ⋆dt (f ∘ extract (prod W)) = fmap G1 g ∘ f ∘ extract (prod W).
    Proof.
      intros. unfold kcompose_dt.
      rewrite <- (fmap_to_cobind (W ×)).
      ext [w a].
      unfold compose; cbn.
      compose near (f a) on left.
      now rewrite (fun_fmap_fmap G1).
    Qed.

    Lemma kcompose_dt_23 :
      forall (g : B -> G2 C) (f : W * A -> G1 B),
        (g ∘ extract (prod W)) ⋆dt f = fmap G1 g ∘ f.
    Proof.
      intros. unfold kcompose_dt.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      now rewrite (fun_fmap_fmap G1).
    Qed.

    Lemma kcompose_dt_03 :
      forall (g : B -> C) (f : W * A -> G1 B),
        kcompose_dt (G2 := fun A => A) (g ∘ extract (W ×)) f = fmap G1 g ∘ f.
    Proof.
      intros. unfold kcompose_dt.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      now rewrite (fun_fmap_fmap G1).
    Qed.

    Lemma kcompose_dt_32 :
      forall (g : W * B -> G2 C) (f : A -> G1 B),
        g ⋆dt (f ∘ extract (prod W)) = fmap G1 g ∘ σ G1 ∘ fmap (prod W) f.
    Proof.
      intros. unfold kcompose_dt.
      ext [w a].
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite (fun_fmap_fmap G1).
      compose near (f a) on right.
      rewrite (fun_fmap_fmap G1).
      reflexivity.
    Qed.

    Lemma kcompose_dt_31 :
      forall (g : W * B -> G2 C)
        (f : W * A -> B),
        g ⋆dt f = g co⋆ f.
    Proof.
      intros. unfold kcompose_dt.
      unfold strength; unfold_ops @Fmap_I.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kcompose_dt_30 :
      forall (g : W * B -> G2 C) (f : A -> B),
        g ⋆dt (f ∘ extract (prod W)) = g ∘ fmap (prod W) f.
    Proof.
      intros. unfold kcompose_dt.
      unfold strength; unfold_ops @Fmap_I.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kcompose_dt_01 :
      forall (g : B -> C) (f : W * A -> B),
        kcompose_dt (G2 := fun A => A) (g ∘ extract (prod W)) f = g ∘ f.
    Proof.
      intros. unfold kcompose_dt.
      unfold strength; unfold_ops @Fmap_I.
      ext [w a].
      reflexivity.
    Qed.

  End kcompose_dt_lemmas.

  (** ** Composition with lesser Kleisli operations *)
  (******************************************************************************)
  Section composition.

    Context
      (T : Type -> Type)
      `{DecoratedTraversableFunctor W T}
      (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}.

    (** *** <<fmapdt>> on the right *)
    (******************************************************************************)
    Corollary traverse_fmapdt {A B C} : forall (g : B -> G2 C) (f : W * A -> G1 B),
        fmap G1 (traverse T G2 g) ∘ fmapdt T G1 f = fmapdt T (G1 ∘ G2) (fmap G1 g ∘ f).
    Proof.
      intros. unfold_ops @Traverse_Fmapdt.
      rewrite (kdtfun_fmapdt2 W T).
      fequal. now rewrite kcompose_dt_23.
    Qed.

    Corollary fmapd_fmapdt {A B C} : forall (g : W * B -> C) (f : W * A -> G1 B),
        fmap G1 (fmapd T g) ∘ fmapdt T G1 f = fmapdt T G1 (fmap G1 g ∘ σ G1 ∘ cobind (W ×) f).
    Proof.
      intros. unfold_ops @Fmapd_Fmapdt.
      rewrite (kdtfun_fmapdt2 W T (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    Corollary fmap_fmapdt {A B C} : forall (g : B -> C) (f : W * A -> G1 B),
        fmap G1 (fmap T g) ∘ fmapdt T G1 f = fmapdt T G1 (fmap G1 g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Fmapdt.
      rewrite (kdtfun_fmapdt2 W T (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
      now rewrite kcompose_dt_03.
    Qed.

    (** *** <<fmapdt>> on the right *)
    (******************************************************************************)
    Corollary fmapdt_traverse {A B C} : forall (g : W * B -> G2 C) (f : A -> G1 B),
        fmap G1 (fmapdt T G2 g) ∘ traverse T G1 f = fmapdt T (G1 ∘ G2) (fmap G1 g ∘ σ G1 ∘ fmap (W ×) f).
    Proof.
      introv. unfold_ops @Traverse_Fmapdt.
      rewrite (kdtfun_fmapdt2 W T).
      rewrite kcompose_dt_32.
      reflexivity.
    Qed.

    Lemma fmapdt_fmapd {A B C} : forall (g : W * B -> G2 C) (f : W * A -> B),
        fmapdt T G2 g ∘ fmapd T f = fmapdt T G2 (g co⋆ f).
    Proof.
      introv. unfold_ops @Fmapd_Fmapdt.
      change (fmapdt T G2 g) with (fmap (fun A => A) (fmapdt T G2 g)).
      rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      now rewrite kcompose_dt_31.
    Qed.

    Lemma fmapdt_fmap {A B C} : forall (g : W * B -> G2 C) (f : A -> B),
        fmapdt T G2 g ∘ fmap T f = fmapdt T G2 (g ∘ fmap (prod W) f).
    Proof.
      intros. unfold_ops @Fmap_Fmapdt.
      change (fmapdt T G2 g) with (fmap (fun A => A) (fmapdt T G2 g)).
      rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      now rewrite kcompose_dt_30.
    Qed.

    (** *** Mixes *)
    (******************************************************************************)
    Corollary fmap_fmapd {A B C} : forall (g : B -> C) (f : W * A -> B),
        fmap T g ∘ fmapd T f = fmapd T (g ∘ f).
    Proof.
      intros.
      change_left (fmap (fun A => A) (fmap T g) ∘ fmapd T f).
      unfold fmap at 2. unfold Fmap_Fmapdt. unfold_ops @Fmapd_Fmapdt.
      rewrite (kdtfun_fmapdt2 W T (G2 := fun A => A) (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      now rewrite (kcompose_dt_03).
    Qed.

  End composition.

  Section instances.
    
    Context
      (T : Type -> Type)
      `{DecoratedTraversableFunctor W T}.

    Lemma fmap_id_T :
      forall A : Type, fmap T (@id A) = @id (T A).
    Proof.
      unfold_ops @Fmap_Fmapdt.
      intros. now rewrite (kdtfun_fmapdt1 W T).
    Qed.

    Lemma fmap_fmap_T :
      forall (A B C : Type) (f : A -> B) (g : B -> C), fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      unfold_ops @Fmap_Fmapdt.
      intros.
      change_left (fmap (fun A => A) (fmapdt T (fun A0 : Type => A0) (g ∘ extract (prod W))) ∘
                     fmapdt T (fun A0 : Type => A0) (f ∘ extract (prod W))).
      rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
      now rewrite kcompose_dt_00.
    Qed.

    #[export] Instance: Functor T :=
      {| fun_fmap_id := fmap_id_T;
        fun_fmap_fmap := fmap_fmap_T;
      |}.

    #[export] Instance: Kleisli.Decorated.Functor.DecoratedFunctor W T.
    Proof.
      constructor; unfold_ops @Fmapd_Fmapdt.
      - intros. now rewrite (kdtfun_fmapdt1 W T).
      - intros.
        change_left ((fmap (fun A => A) (fmapdt T (fun A0 : Type => A0) g) ∘
                        fmapdt T (fun A0 : Type => A0) f)).
        rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A) (G2 := fun A => A) g f).
        fequal. now rewrite Mult_compose_identity1.
        unfold kcompose_dt. now ext [w a].
    Qed.

    #[export] Instance: Kleisli.Traversable.Functor.TraversableFunctor T.
    Proof.
      constructor; unfold_ops @Traverse_Fmapdt.
      - intros. now rewrite (kdtfun_fmapdt1 W T).
      - intros. rewrite (kdtfun_fmapdt2 W T _ _ (G1 := G1) (G2 := G2)).
        fequal. now rewrite kcompose_dt_22.
      - intros. rewrite <- (kdtfun_morph W T).
        reflexivity.
    Qed.

  End instances.
  
End Derived.

(** * Batch *)
(******************************************************************************)
Section with_functor.

  Import Derived.
  
  Context
    (T : Type -> Type)
    `{DT.Functor.DecoratedTraversableFunctor W T}.

  Definition toBatchd {A : Type} (B : Type) : T A -> @Batch (W * A) B (T B) :=
    fmapdt T (Batch (W * A) B) (batch B).

  (** ** Expressing operations with <<runBatch>> *)
  (******************************************************************************)

  (** *** <<fmapdt>> *)
  (******************************************************************************)
  Theorem fmapdt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G B) (t : T A),
      fmapdt T G f t = runBatch f (toBatchd B t).
  Proof.
    intros. unfold toBatchd.
    compose near t on right.
    rewrite <- (kdtfun_morph W T).
    now rewrite runBatch_batch.
  Qed.

  (** *** <<fmapd>> *)
  (******************************************************************************)
  Theorem fmapd_to_runBatch :
    forall (A B : Type) (f : W * A -> B) (t : T A),
      fmapd T f t = runBatch f (toBatchd B t).
  Proof.
    intros. unfold toBatchd.
    compose near t on right.
    rewrite <- (kdtfun_morph W T (G1 := Batch (prod W A) B) (G2 := fun A => A)).
    reflexivity.
  Qed.

  (** *** <<fmapt>> *)
  (******************************************************************************)
  Theorem fmap_to_runBatch :
    forall (A B : Type) (f : A -> B),
      fmap T f = runBatch f ∘ toBatch T B.
  Proof.
    intros.
    Set Printing All.
    change (@Fmap_Fmapdt T W H) with (@ToFunctor.Fmap_Traverse T _).
    apply (fmap_to_runBatch T).
  Qed.

End with_functor.

(** * <<foldMapd>> *)
(******************************************************************************)
Section foldMapd.

  Context
    (T : Type -> Type)
    `{Monoid_op M} `{Monoid_unit M}
    `{Fmapdt W T}.

  Definition foldMapd : forall {A : Type}, (W * A -> M) -> T A -> M :=
    fun A f => fmapdt (B := False) T (const M) f.

End foldMapd.

(** ** Basic properties *)
(******************************************************************************)
Section with_functor.

  Context
    (T : Type -> Type)
    `{DT.Functor.DecoratedTraversableFunctor W T}.

  Import Derived.
  
  (** *** Lemmas for <<fmapdt>> with constant applicative functors *)
  (******************************************************************************)
  Section constant_applicatives.

    Context
      `{Monoid M}
      `{f : W * A -> M}.

    Lemma fmapdt_constant_applicative1: forall (B : Type),
        fmapdt (B := B) T (const M) f = fmapdt (B := False) T (const M) f.
    Proof.
      intros.
      change_right (fmap (B := T B) (const M) (fmap T exfalso)
                      ∘ fmapdt (B := False) T (const M) (f : W * A -> const M False)).
      rewrite (fmap_fmapdt T (const M)).
      reflexivity.
    Qed.

    Lemma fmapdt_constant_applicative2 : forall (fake1 fake2 : Type),
        fmapdt (B := fake1) T (const M) f = fmapdt (B := fake2) T (const M) f.
    Proof.
      intros. rewrite (fmapdt_constant_applicative1 fake1).
      rewrite (fmapdt_constant_applicative1 fake2).
      reflexivity.
    Qed.

  End constant_applicatives.

  (** *** Expressing <<foldMapd>> in terms of <<runBatch>> *)
  (******************************************************************************)
  Theorem foldMapd_to_runBatch :
    forall `{Monoid M} (A : Type) (f : W * A -> M) (t : T A),
      foldMapd T f t = runBatch f (toBatchd T False t).
  Proof.
    intros. unfold foldMapd.
    rewrite (fmapdt_to_runBatch); auto.
    typeclasses eauto.
  Qed.

  (** *** Rewriting the "tag" parameter *)
  (******************************************************************************)
  Lemma foldMapd_equiv1 `{Monoid M} : forall (fake : Type) `(f : W * A -> M),
      foldMapd T f = fmapdt (B := fake) T (const M) f.
  Proof.
    intros. unfold foldMapd.
    now rewrite (fmapdt_constant_applicative2 fake False).
  Qed.

  (** *** Homomorphism law *)
  (******************************************************************************)
  Lemma foldMapd_morphism `{Monoid_Morphism M1 M2 ϕ} : forall `(f : W * A -> M1),
      ϕ ∘ foldMapd T f = foldMapd T (ϕ ∘ f).
  Proof.
    intros.
    unfold foldMapd. inversion H5.
    change ϕ with (const (ϕ) (T False)).
    rewrite (fmapdt_constant_applicative2 (f := const ϕ (T False) ∘ f) False (T False)).
    rewrite (kdtfun_morph W T f (G1 := const M1) (G2 := const M2) (ϕ := const ϕ) (B := T False) (A := A)).
    rewrite (fmapdt_constant_applicative2 (T False) False).
    reflexivity.
  Qed.

  (** *** Composition with <<fmapdt>> *)
  (******************************************************************************)
  Lemma foldMapd_fmapdt : forall `{Monoid M} `{Applicative G} `(g : W * B -> M) `(f : W * A -> G B),
      fmap G (foldMapd T g) ∘ fmapdt T G f =
        foldMapd T (M := G M) (fmap G g ∘ σ G ∘ cobind (W ×) f).
  Proof.
    intros. unfold foldMapd.
    rewrite (kdtfun_fmapdt2 W T _ _ (G1 := G) (G2 := const M)).
    fequal.
    - ext A' B' f' t. unfold Fmap_compose, Fmap_const.
      change t with (id t) at 2. rewrite (fun_fmap_id G).
      reflexivity.
    - ext A' B' [a b]. reflexivity.
  Qed.

  (** *** Composition with <<fmapd>>, <<traverse>>, <<fmap>> *)
  (******************************************************************************)
  Lemma foldMapd_fmapd : forall `{Monoid M} `(g : W * B -> M) `(f : W * A -> B),
      foldMapd T g ∘ fmapd T f =
        foldMapd T (M := M) (g ∘ cobind (W ×) f).
  Proof.
    intros. unfold foldMapd. unfold_ops @Fmapd_Fmapdt.
    change (fmapdt (B := ?B) T (const M) g) with (fmap (fun A => A) (fmapdt (B := B) T (const M) g)).
    rewrite (kdtfun_fmapdt2 W T _ _ (G1 := fun A => A) (G2 := const M)).
    fequal.
    - ext A' B' [a b]. reflexivity.
    - ext [w a]. reflexivity.
  Qed.

  Lemma foldMapd_traverse : forall `{Monoid M} `{Applicative G} `(g : W * B -> M) `(f : A -> G B),
      fmap G (foldMapd T g) ∘ traverse T G f =
        foldMapd T (M := G M) (fmap G g ∘ σ G ∘ fmap (W ×) f).
  Proof.
    intros. unfold_ops @Traverse_Fmapdt.
    rewrite (foldMapd_fmapdt g (f ∘ extract (W ×))).
    fequal. ext [w a]. reflexivity.
  Qed.

  Lemma foldMap_fmap : forall `{Monoid M} `(g : W * B -> M) `(f : A -> B),
      foldMapd T g ∘ fmap T f =
        foldMapd T (M := M) (g ∘ fmap (W ×) f).
  Proof.
    intros. unfold_ops @Fmap_Fmapdt.
    change (fmapdt T (fun A => A) ?f) with (fmapd T f).
    rewrite foldMapd_fmapd.
    fequal. now ext [w a].
  Qed.

End with_functor.

Import Sets.Notations.

(** * <<tolistd>> and <<tosetd>> *)
(******************************************************************************)
Section tolistd.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}.

  Definition tolistd {A} : T A -> list (W * A) :=
    foldMapd T (ret list).

  Definition tosetd {A} : T A -> set (W * A) :=
    foldMapd T (ret set).

  #[local] Notation "x ∈d t" :=
    (tosetd t x) (at level 50) : tealeaves_scope.

  Import Derived.

  (** ** Relating <<tosetd>> and <<tolistd>> *)
  (******************************************************************************)
  Lemma tosetd_to_tolistd : forall (A : Type),
      @tosetd A = toset list ∘ tolistd.
  Proof.
    intros. unfold tosetd, tolistd.
    rewrite (foldMapd_morphism T).
    fequal. ext [w a]. unfold compose.
    solve_basic_set.
  Qed.

  (** ** Characterizing <<∈d>> *)
  (******************************************************************************)
  Theorem ind_fmapd_iff :
    forall `(f : W * A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d fmapd T f t <-> exists (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros. unfold tosetd.
    compose near t on left. rewrite (foldMapd_fmapd);
      try typeclasses eauto.
    rewrite foldMapd_to_runBatch;
      try typeclasses eauto.
    rewrite foldMapd_to_runBatch;
      try typeclasses eauto.
    induction (toBatchd T False t).
    - splits.
      + introv hyp. inverts hyp.
      + introv [a' hyp]. inverts hyp.
        solve_basic_set.
    - splits.
      + intros [hyp | hyp].
        { rewrite IHb0 in hyp. preprocess.
          eexists. split; [| reflexivity]. now left. }
        { destruct x as [w' a]. inverts hyp.
          eexists. split; [| reflexivity]. now right. }
      + introv [a [rest1 rest2]]. subst.
        inverts rest1.
        { left. rewrite IHb0.
          exists a. split; auto. }
        { right. destruct x.
          unfold compose; cbn.
          inverts H1. easy. }
  Qed.

  Corollary ind_fmap_iff :
    forall `(f : A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d fmap T f t <-> exists (a : A), (w, a) ∈d t /\ f a = b.
  Proof.
    intros. change_left ((w, b) ∈d fmapd T (f ∘ extract (prod W)) t).
    rewrite ind_fmapd_iff.
    unfold compose. cbn. splits; eauto.
  Qed.

End tolistd.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.
  Notation "g ⋆dt f" := (kcompose_dt g f) (at level 40) : tealeaves_scope.

End Notations.

Import Notations.

Import Setlike.Functor.Notations.

(** * Relating <<foldMapd>> and <<foldMap>> *)
(******************************************************************************)
Section new.

  Context
    (T : Type -> Type)
    `{DT.Functor.DecoratedTraversableFunctor W T}.

  Import Derived.

  (** ** Expressing <<foldMap>> with <<foldMapd>> *)
  (******************************************************************************)
  Lemma foldMap_to_foldMapd : forall `{Monoid M} `(f : A -> M),
      foldMap T f = foldMapd T (f ∘ extract (W ×)).
  Proof.
    intros. unfold foldMapd, foldMap.
    unfold_ops @Traverse_Fmapdt.
    reflexivity.
  Qed.


  (** ** Relating <<tolist>> to <<tolistd>>*)
  (******************************************************************************)
  Lemma tolist_to_tolistd : forall (A : Type),
      @tolist T _ A = fmap list (extract (W ×)) ∘ tolistd T.
  Proof.
    intros. unfold_ops Tolist_Traverse.
    rewrite (foldMap_to_foldMapd).
    unfold tolistd.
    rewrite (foldMapd_morphism T).
    rewrite (natural (ϕ := @ret list _)).
    reflexivity.
  Qed.

  (** ** Relating <<toset>> to <<tosetd>>*)
  (******************************************************************************)
  Lemma toset_to_tosetd : forall (A : Type),
      @toset T _ A = fmap set (extract (W ×)) ∘ tosetd T.
  Proof.
    intros. unfold_ops @Toset_Traverse @Tolist_Traverse.
    unfold tosetd.
    rewrite (foldMap_to_foldMapd).
    rewrite (foldMapd_morphism T).
    rewrite (natural (ϕ := @ret set _)).
    reflexivity.
  Qed.

  (** ** Relating <<∈>> to <<∈d>> *)
  (******************************************************************************)
  Existing Instance Toset_set.
  Existing Instance SetlikeFunctor_set.
  Lemma ind_iff_in : forall (A : Type) (a : A) (t : T A),
      a ∈ t <-> exists w, (w, a) ∈d t.
  Proof.
    intros. unfold_ops @Toset_Traverse.
    rewrite (foldMap_to_foldMapd).
    change (extract (prod W)) with (fmap (fun A => A) (@extract (prod W) _ A)).
    rewrite <- (natural (ϕ := @ret set _)).
    rewrite <- (foldMapd_morphism T).
    unfold tosetd.
    unfold compose.
    unfold_ops @Fmap_set. split.
    - intros [[w a'] [rest1 rest2]]. exists w.
      unfold toset in rest1. unfold Toset_set in rest1.
      now inverts rest2.
    - intros [w rest]. exists (w, a). auto.
  Qed.

  Corollary ind_implies_in : forall (A : Type) (a : A) (w : W) (t : T A),
      (w, a) ∈d t -> a ∈ t.
  Proof.
    intros. rewrite ind_iff_in. eauto.
  Qed.

  (** ** Characterizing <<∈>> to with <<fmapdt>> *)
  (******************************************************************************)
  Theorem in_fmapd_iff :
    forall `(f : W * A -> B) (t : T A) (b : B),
      b ∈ fmapd T f t <-> exists (w : W) (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros. rewrite ind_iff_in.
    setoid_rewrite (ind_fmapd_iff T).
    reflexivity.
  Qed.

End new.

(** * Respectfulness *)
(******************************************************************************)
Section decorated_setlike_respectfulness.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Kleisli.DT.Functor.DecoratedTraversableFunctor W T}.

  Import Derived.

  Lemma fmapd_respectful {A B} : forall (t : T A) (f g : W * A -> B),
      (forall w a, (w, a) ∈d t -> f (w, a) = g (w, a)) ->
      fmapd T f t = fmapd T g t.
  Proof.
    unfold tosetd. introv hyp.
    unfold foldMapd in hyp.
    rewrite (fmapdt_constant_applicative2 T False B) in hyp.
    rewrite (fmapdt_to_runBatch T) in hyp.
    unfold_ops @Fmapd_Fmapdt.
    do 2 rewrite (fmapdt_to_runBatch T).
    induction (toBatchd T B t).
    - reflexivity.
    - destruct x as [w a]. cbn. rewrite IHb. fequal.
      apply hyp. now right.
      intros. apply hyp. now left.
  Qed.

  Corollary fmapd_respectful_id {A} : forall (t : T A) (f : W * A -> A),
      (forall w a, (w, a) ∈d t -> f (w, a) = a) ->
      fmapd T f t = t.
  Proof.
    intros. replace t with (fmapd T (extract (prod W)) t) at 2
      by (now rewrite (dfun_fmapd1 W T)).
    now apply fmapd_respectful.
  Qed.

End decorated_setlike_respectfulness.
