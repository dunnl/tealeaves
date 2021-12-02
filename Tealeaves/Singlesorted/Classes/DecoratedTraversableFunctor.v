From Tealeaves Require Export
     Singlesorted.Classes.Monoid
     Singlesorted.Classes.DecoratedFunctor
     Singlesorted.Classes.TraversableFunctor.

Import Monoid.Notations.
Import TraversableFunctor.Notations.
Import SetlikeFunctor.Notations.
#[local] Open Scope tealeaves_scope.

(** * Decorated-traversable functors *)
(******************************************************************************)
Section DecoratedTraversableFunctor.

  Context
    (W : Type)
    (F : Type -> Type)
    `{Fmap F} `{Decorate W F} `{Dist F}
    `{op : Monoid_op W} `{unit : Monoid_unit W}.

  Class DecoratedTraversableFunctor :=
    { dtfun_decorated :> DecoratedFunctor W F;
      dtfun_traversable :> TraversableFunctor F;
      dtfun_compat : forall (A : Type) `{Applicative G},
             dist F G ∘ fmap F (strength G) ∘ dec F (A := G A) =
             fmap G (dec F) ∘ dist F G;
    }.

End DecoratedTraversableFunctor.

Section test_typeclasses.

  Context
    `{DecoratedTraversableFunctor W T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal DecoratedFunctor W T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
  Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal SetlikeFunctor T. typeclasses eauto. Qed.
  Goal ListableFunctor T. typeclasses eauto. Qed.

End test_typeclasses.

(** * Monoid structure of D-T functors *)
(******************************************************************************)
Section DecoratedTraversableFunctor_monoid.

  Context
    `{@Monoid W op zero}.

  (** ** The identity functor is D-T *)
  (******************************************************************************)
  #[program] Instance DecoratedTraversable_I : DecoratedTraversableFunctor W (fun A => A).

  (** ** D-T functors are closed under composition *)
  (******************************************************************************)
  Section compose.

    Context
      (U T : Type -> Type)
      `{DecoratedTraversableFunctor W (op := op) (unit := zero) T}
      `{DecoratedTraversableFunctor W (op := op) (unit := zero) U}.

    #[local] Set Keyed Unification.
    Theorem dtfun_compat_compose :
      forall (A : Type) `{Applicative G},
        dist (U ∘ T) G ∘ fmap (U ∘ T) (strength G) ∘ dec (U ∘ T) (A := G A) =
        fmap G (dec (U ∘ T)) ∘ dist (U ∘ T) G.
    Proof.
      intros.
      reassociate -> on left. unfold dec at 1, Decorate_compose.
      (* bring <<strength G >> and <<shift T>> together*)
      do 3 reassociate <- on left;
        reassociate -> near (fmap U (shift T));
        rewrite (fun_fmap_fmap U).
      unfold shift.
      reassociate <- on left;
        rewrite (fun_fmap_fmap T).
      rewrite <- (fun_fmap_fmap U).
      reassociate <- on left.
      rewrite (strength_join_l).
      change (fmap U (fmap T ?f)) with (fmap (U ∘ T) f).
      do 2 rewrite <- (fun_fmap_fmap (U ∘ T)).
      change (fmap (U ∘ T) (fmap G ?f)) with (fmap (U ∘ T ∘ G) f).
      do 2 reassociate <-.
      rewrite <- (dist_natural (U ∘ T)).
      reassociate -> near (fmap (U ∘ T) (fmap (prod W) (strength G))).
      rewrite (fun_fmap_fmap (U ∘ T)).
      unfold dist at 1, Dist_compose.
      reassociate -> near (fmap (U ∘ T) (strength G ∘ fmap (prod W) (strength G))).
      reassociate -> near (fmap (U ∘ T) (strength G ∘ fmap (prod W) (strength G))).
      rewrite (fun_fmap_fmap U).
    Admitted.
    #[local] Unset Keyed Unification.

    #[global] Instance DecoratedTraversableFunctor_compose :
      DecoratedTraversableFunctor W (U ∘ T) :=
      {| dtfun_compat := dtfun_compat_compose; |}.

  End compose.

End DecoratedTraversableFunctor_monoid.

(** ** Zero-decorated traversable functors are decorated-traversable *)
(******************************************************************************)
Section TraversableFunctor_zero_DT.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Monoid W}.

  Existing Instance Decorate_zero.
  Existing Instance DecoratedFunctor_zero.

  Theorem dtfun_compat_zero : forall (A : Type) `{Applicative G},
      dist T G ∘ fmap T (strength G) ∘ dec T =
      fmap G (dec T) ∘ dist T G (A := A).
  Proof.
    intros. unfold_ops @Decorate_zero.
    reassociate -> on left. rewrite (fun_fmap_fmap T).
    change_right (fmap (G ∘ T) (pair Ƶ) ∘ δ T G (A := A)).
    rewrite (dist_natural T).
    now unfold_ops @Fmap_compose.
  Qed.

  Instance DecoratedTraversableFunctor_zero :
    DecoratedTraversableFunctor W T :=
    {| dtfun_compat := dtfun_compat_zero |}.

End TraversableFunctor_zero_DT.

(** * Kleisli presentation *)
(******************************************************************************)

(** ** Lifting operation <<fmapdt>> *)
(******************************************************************************)
Definition fmapdt F `{Fmap F} `{Decorate W F} `{Dist F}
           `{Fmap G} `{Pure G} `{Mult G}
           {A B : Type} (f : W * A -> G B) : F A -> G (F B) :=
  dist F G ∘ fmap F f ∘ dec F.

Section kleisli_composition.

  Context
    `{DecoratedTraversableFunctor W F}.

  Definition kcomposedt {A B C}
             `{Applicative G1}
             `{Applicative G2} :
    (W * B -> G2 C) ->
    (W * A -> G1 B) ->
    (W * A -> G1 (G2 C)) :=
    fun g f => fmap G1 g ∘ strength G1 ∘ cobind (prod W) f.

End kleisli_composition.

#[local] Notation "g ⋆dt f" := (kcomposedt g f) (at level 40) : tealeaves_scope.

(** ** Specifications for sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableFunctor_suboperations.

  Context
    (F : Type -> Type)
    `{DecoratedTraversableFunctor W F}.

  (** *** [fmap] as a special case of [fmapdt] *)
  Theorem fmap_to_fmapdt {A B} : forall (f : A -> B),
      fmap F f = fmapdt F (G := (fun A => A)) (f ∘ extract (prod W)).
  Proof.
    introv. unfold fmapdt.
    rewrite <- (fun_fmap_fmap F).
    do 2 reassociate -> on right.
    rewrite (dfun_dec_extract W F).
    now rewrite (dist_unit F).
  Qed.

  (** *** [traverse] as a special case of [fmapdt] *)
  Theorem traverse_to_fmapdt {A B} `{Applicative G} : forall (f : A -> G B),
      traverse F G f = fmapdt F (f ∘ extract (prod W)).
  Proof.
    introv. unfold fmapdt.
    rewrite <- (fun_fmap_fmap F).
    do 2 reassociate -> on right.
    now rewrite (dfun_dec_extract W F).
  Qed.

  (** *** [fmapd] as a special case of [fmapdt] *)
  Theorem fmapd_to_fmapdt {A B} : forall (f : W * A -> B),
      fmapd F f = fmapdt F (G := (fun A => A)) f.
  Proof.
    introv. unfold fmapdt.
    now rewrite (dist_unit F).
  Qed.

End DecoratedTraversableFunctor_suboperations.

(** ** Functoriality of <<fmapdt>> *)
(******************************************************************************)
Section DecoratedTraversableFunctor_fmapdt.

  Context
    (F : Type -> Type)
    `{DecoratedTraversableFunctor W F}.

  Theorem fmapdt_id {A} : fmapdt F (extract _) = @id (F A).
  Proof.
    introv. unfold fmapdt. reassociate -> on left.
    rewrite (dfun_dec_extract W F). now rewrite (dist_unit F).
  Qed.

  Theorem fmapdt_fmapdt {A B C} `{Applicative G1} `{Applicative G2}
          (f : W * A -> G1 B) (g : W * B -> G2 C) :
    fmap G1 (fmapdt F g) ∘ fmapdt F f = fmapdt (G := G1 ∘ G2) F (g ⋆dt f).
  Proof.
    intros. unfold fmapdt, kcomposedt.
    rewrite <- (fun_fmap_fmap G1).
    repeat reassociate <- on left.
    change (?f ∘ fmap G1 (dec F) ∘ dist F G1 ∘ ?g) with
        (f ∘ (fmap G1 (dec F) ∘ dist F G1) ∘ g).
    rewrite <- (dtfun_compat W F B).
    rewrite <- (fun_fmap_fmap G1).
    repeat reassociate <- on left.
    change (?f ∘ fmap G1 (fmap F g) ∘ dist F G1 ∘ ?h) with
        (f ∘ (fmap G1 (fmap F g) ∘ dist F G1) ∘ h).
    change (fmap G1 (fmap F g)) with (fmap (G1 ∘ F) g).
    rewrite (dist_natural F (G := G1) g).
    rewrite (dist_linear F).
    repeat reassociate <- on left.
    rewrite <- (fun_fmap_fmap F).
    unfold_ops @Fmap_compose.
    change (?f ∘ fmap F (fmap G1 g) ∘ ?x ∘ ?h) with
        (f ∘ (fmap F (fmap G1 g) ∘ x) ∘ h).
    rewrite (fun_fmap_fmap F). reassociate -> near (fmap F f).
    rewrite (dec_fmap F).
    repeat reassociate ->.
    repeat fequal. rewrite (dfun_dec_dec W F).
    reassociate <-. now rewrite (fun_fmap_fmap F).
  Qed.

End DecoratedTraversableFunctor_fmapdt.

(** ** Purity laws for <<fmapdt>> *)
(******************************************************************************)
Section DecoratedTraversableFunctor_purity.

  Context
    (F : Type -> Type)
    `{DecoratedTraversableFunctor W F}.

  Theorem fmapdt_purity1 `{Applicative G1} `{Applicative G2} {A B} : forall (f : W * A -> G1 B),
    fmapdt F (G := G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ fmapdt F f.
  Proof.
    intros. unfold fmapdt. rewrite <- (fun_fmap_fmap F).
    reassociate <-. rewrite (dist_linear F).
    reassociate -> near (fmap F (pure G2)).
    rewrite (fmap_purity_1 F). repeat reassociate <-.
    fequal. fequal. ext t. unfold compose.
    now rewrite <- (app_pure_natural G2).
  Qed.

  Theorem fmapdt_purity `{Applicative G} {A} :
    fmapdt F (pure G ∘ extract (prod W)) = pure G (A := F A).
  Proof.
    unfold fmapdt. rewrite <- (fun_fmap_fmap F).
    reassociate <-. rewrite (fmap_purity_1 F).
    reassociate ->. now rewrite (dfun_dec_extract W F).
  Qed.

End DecoratedTraversableFunctor_purity.

(** ** Composition with sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableFunctor_composition.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}
    `{Applicative F}
    `{Applicative F1}
    `{Applicative F2}.

  Corollary fmapd_fmapdt {A B C} : forall (g : W * B -> C) (f : W * A -> F B),
    fmap F (fmapd T g) ∘ fmapdt T f = fmapdt T (fmap F g ∘ strength F ∘ cobind (prod W) f).
  Proof.
    intros. rewrite (fmapd_to_fmapdt T).
    rewrite (fmapdt_fmapdt (G2 := (fun A => A)) T).
    unfold kcomposedt. fequal. unfold Mult_compose.
    ext A' B' [fa fb]. cbn. unfold_ops @Mult_I.
    now rewrite (fun_fmap_id F).
  Qed.

  Corollary fmapdt_fmapd {A B C} : forall (g : W * B -> F C) (f : W * A -> B),
    fmapdt T g ∘ fmapd T f = fmapdt T (g ∘ cobind (prod W) f).
  Proof.
    intros. rewrite (fmapd_to_fmapdt T).
    change (fmapdt T g) with (fmap (fun A => A) (fmapdt T g)).
    rewrite (fmapdt_fmapdt (G1 := (fun A => A)) T).
    unfold kcomposedt. fequal.
    + unfold Mult_compose.
      ext A' B' [fa fb]. cbn. unfold_ops @Mult_I.
      reflexivity.
    + now ext [? ?].
  Qed.

  Corollary fmapt_fmapdt {A B C} : forall (g : B -> F2 C) (f : W * A -> F1 B),
    fmap F1 (traverse T F2 g) ∘ fmapdt T f = fmapdt (G := F1 ∘ F2) T (fmap F1 g ∘ f).
  Proof.
    intros. rewrite (traverse_to_fmapdt T).
    rewrite (fmapdt_fmapdt T).
    unfold kcomposedt. fequal.
    rewrite <- (fun_fmap_fmap F1).
    unfold strength.
    ext [w a]; unfold compose; cbn.
    compose near (f (w, a)) on left. rewrite (fun_fmap_fmap F1).
    replace (extract (prod W) ∘ pair (id w)) with (@id B).
    compose near (f (w, a)) on left.
    now rewrite (fun_fmap_id F1).
    now ext x.
  Qed.

  Corollary fmapdt_fmapt {A B C} : forall (g : W * B -> F2 C) (f : A -> F1 B),
    fmap F1 (fmapdt T g) ∘ traverse T F1 f = fmapdt (G := F1 ∘ F2) T (fmap F1 g ∘ strength F1 ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (traverse_to_fmapdt T).
    rewrite (fmapdt_fmapdt T).
    unfold kcomposedt. fequal.
    now rewrite (fmap_to_cobind (prod W)).
  Qed.

  Corollary fmapd_fmapt {A B C} : forall (g : W * B -> C) (f : A -> F B),
      fmap F (fmapd T g) ∘ traverse T F f = fmapdt T (fmap F g ∘ strength F ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (traverse_to_fmapdt T), (fmapd_to_fmapdt T).
    rewrite (fmapdt_fmapdt (G2 := fun A => A) T).
    fequal.
    + unfold Mult_compose.
      ext A' B' [fa fb]. cbn. unfold_ops @Mult_I.
      now rewrite (fun_fmap_id F).
    + unfold kcomposedt. now rewrite (fmap_to_cobind (prod W)).
  Qed.

  Corollary fmapt_fmapd {A B C} : forall (g : B -> F C) (f : W * A -> B),
      traverse T F g ∘ fmapd T f = fmapdt T (g ∘ f).
  Proof.
    intros. change (traverse T F g) with (fmap (fun A => A) (traverse T F g)).
    rewrite (traverse_to_fmapdt T), (fmapd_to_fmapdt T).
    rewrite (fmapdt_fmapdt (G1 := fun A => A) T).
    fequal.
    + unfold Mult_compose.
      ext A' B' [fa fb]. cbn. unfold_ops @Mult_I.
      reflexivity.
    + unfold kcomposedt. change (fmap (fun A => A) ?f) with f.
      now ext [w a].
  Qed.

  Corollary fmapd_fmapdt_alt {A B C} : forall (g : W * B -> C) (f : W * A -> F B),
    fmap F (fmapd T g) ∘ fmapdt T f = fmapdt T (fmap F g ∘ strength F ∘ cobind (prod W) f).
  Proof.
    intros. unfold fmapdt, fmapd. repeat reassociate <- on left.
    rewrite <- (fun_fmap_fmap F).
    (* Scoot distribution left over decoration *)
    reassociate -> near (dist T F).
    rewrite <- (dtfun_compat W T B).
    (* Scoot distribution left over <<g>> *)
    repeat reassociate <-.
    change (fmap F (fmap T g)) with (fmap (F ∘ T) g).
    rewrite (dist_natural (G := F) T g). unfold_ops @Fmap_compose.
    reassociate -> near (fmap T (strength F)). rewrite (fun_fmap_fmap T).
    (* Replace repeated decorations with a <<cobind>> *)
    reassociate -> near (dec T). change (fmap T f ∘ dec T) with (fmapd T f).
    reassociate -> near (fmapd T f). rewrite (dec_fmapd T f).
    (* Fuse <<fmap>> together *)
    unfold fmapd. reassociate <- on left.
    reassociate -> near (fmap T (cobind (prod W) f)).
    now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary fmapdt_fmap {A B C} : forall (g : B -> C) (f : W * A -> F B),
    fmap F (fmap T g) ∘ fmapdt T f = fmapdt T (fmap F g ∘ f).
  Proof.
    intros. unfold fmapdt. repeat reassociate <- on left.
    change (fmap F (fmap T g)) with (fmap (F ∘ T) g).
    rewrite (dist_natural (G := F) T g). unfold_ops @Fmap_compose.
    reassociate -> near (fmap T f). now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary fmap_fmapdt {A B C} : forall (g : B -> C) (f : W * A -> F B),
    fmap F (fmap T g) ∘ fmapdt T f = fmapdt T (fmap F g ∘ f).
  Proof.
    intros. unfold fmapdt. repeat reassociate <- on left.
    change (fmap F (fmap T g)) with (fmap (F ∘ T) g).
    rewrite (dist_natural (G := F) T g). unfold_ops @Fmap_compose.
    reassociate -> near (fmap T f). now rewrite (fun_fmap_fmap T).
  Qed.

  (** ** Re-statement of inherited composition properties  *)
  Corollary fmapd_fmap {A B C} : forall (g : W * B -> C) (f : A -> B),
      fmapd T g ∘ fmap T f = fmapd T (g ∘ map_snd f).
  Proof.
    intros; apply (DecoratedFunctor.fmapd_fmap T).
  Qed.

  Corollary fmap_fmapd {A B C} : forall (g : B -> C) (f : W * A -> B),
    fmap T g ∘ fmapd T f = fmapd T (g ∘ f).
  Proof.
    intros; apply (DecoratedFunctor.fmap_fmapd T).
  Qed.

  Corollary fmap_traverse : forall `(g : B -> C) `(f : A -> F B),
      fmap F (fmap T g) ∘ traverse T F f = traverse T F (fmap F g ∘ f).
  Proof.
    intros; apply (TraversableFunctor.fmap_traverse T).
  Qed.

  Corollary traverse_fmap : forall `(g : B -> F C) `(f : A -> B),
      traverse T F g ∘ fmap T f = traverse T F (g ∘ f).
  Proof.
    intros; apply (TraversableFunctor.traverse_fmap T).
  Qed.

End DecoratedTraversableFunctor_composition.

(** ** Respectfulness properties *)
(******************************************************************************)
Section DecoratedTraversableFunctor_respectfulness.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}
    `{Applicative G}.

  Lemma fmapdt_respectful {A B} : forall t (f g : W * A -> G B),
      (forall w a, (w, a) ∈d t -> f (w, a) = g (w, a)) -> fmapdt T f t = fmapdt T g t.
  Proof.
    intros. unfold fmapdt, compose. fequal.
    apply (fmap_respectful T). intros [? ?]. auto.
  Qed.

  Lemma fmapdt_respectful_traverse {A B} : forall t (f : W * A -> G B) (g : A -> G B),
      (forall w a, (w, a) ∈d t -> f (w, a) = g a) -> fmapdt T f t = traverse T G g t.
  Proof.
    intros. rewrite (traverse_to_fmapdt T).
    apply fmapdt_respectful. auto.
  Qed.

  Lemma fmapdt_respectful_fmapd {A B} : forall t (f : W * A -> G B) (g : W * A -> B),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G (g (w, a))) -> fmapdt T f t = pure G (fmapd T g t).
  Proof.
    intros. rewrite (fmapd_to_fmapdt T).
    compose near t on right.
    rewrite <- (fmapdt_purity1 T (G2 := G) (G1 := fun A => A)).
    erewrite (fmapdt_respectful t). fequal.
    ext A' B' [? ?]. unfold Mult_compose. unfold_ops @Mult_I.
    cbn. now rewrite (fun_fmap_id G).
    auto.
  Qed.

  Lemma fmapdt_respectful_fmap {A B} : forall t (f : W * A -> G B) (g : A -> B),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G (g a)) -> fmapdt T f t = pure G (fmap T g t).
  Proof.
    intros. rewrite (fmap_to_fmapd T).
    apply fmapdt_respectful_fmapd. auto.
  Qed.

  Corollary fmapdt_respectful_id {A} : forall t (f : W * A -> G A),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G a) -> fmapdt T f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity T).
    rewrite (traverse_to_fmapdt T).
    now apply fmapdt_respectful.
  Qed.

End DecoratedTraversableFunctor_respectfulness.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Include Functor.Notations.
  Include Monoid.Notations.
  Include SetlikeFunctor.Notations.
  Include Applicative.Notations.
  Include TraversableFunctor.Notations.
  Notation "g ⋆dt f" := (kcomposedt g f) (at level 40) : tealeaves_scope.
End Notations.
