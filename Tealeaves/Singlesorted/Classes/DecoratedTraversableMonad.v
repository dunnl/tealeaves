From Tealeaves Require Export
     Singlesorted.Classes.DecoratedMonad
     Singlesorted.Classes.TraversableMonad
     Singlesorted.Classes.DecoratedTraversableFunctor.

Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedTraversableFunctor.Notations.
#[local] Open Scope tealeaves_scope.

(** * Decorated-traversable monads *)
(******************************************************************************)
Section DecoratedTraverableMonad.

  Context
  (W : Type)
  (T : Type -> Type)
  `{op : Monoid_op W}
  `{unit : Monoid_unit W}
  `{Fmap T} `{Return T} `{Join T}
  `{Decorate W T} `{Dist T}.

  Class DecoratedTraversableMonad :=
    { dtmon_decorated :> DecoratedMonad W T;
      dtmon_traversable :> TraversableMonad T;
      dtmon_functor :> DecoratedTraversableFunctor W T;
    }.

End DecoratedTraverableMonad.

Section test_typeclasses.

  Context
    `{DecoratedTraversableMonad W T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal DecoratedFunctor W T. typeclasses eauto. Qed.
  Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
  Goal SetlikeFunctor T. typeclasses eauto. Qed.
  Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal DecoratedTraversableFunctor W T. typeclasses eauto. Qed.

  Goal Monad T. typeclasses eauto. Qed.
  Goal DecoratedMonad W T. typeclasses eauto. Qed.
  Goal ListableMonad T. typeclasses eauto. Qed.
  Goal TraversableMonad T. typeclasses eauto. Qed.
  Goal SetlikeMonad T. typeclasses eauto. Qed.
  Goal ListableMonad T. typeclasses eauto. Qed.

End test_typeclasses.

(** * Kleisli presentation of D-T monads *)
(******************************************************************************)

(** ** Lifting operation <<binddt>> and Kleisli composition  *)
(******************************************************************************)
Definition binddt T `{Fmap T} `{Decorate W T} `{Dist T} `{Join T}
           `{Fmap G} `{Pure G} `{Mult G}
           {A B : Type} (f : W * A -> G (T B)) : T A -> G (T B) :=
  fmap G (join T) ∘ dist T G ∘ fmap T f ∘ dec T.

Section kleisli_composition.

  Context
    `{DecoratedTraversableMonad W T}.

  Definition kcomposedtm {A B C}
             `{Applicative G1}
             `{Applicative G2} :
    (W * B -> G2 (T C)) ->
    (W * A -> G1 (T B)) ->
    (W * A -> G1 (G2 (T C))) :=
    fun g f => (fmap G1 (fmap G2 (join T) ∘ dist T G2))
              ∘ fmap G1 (fmap T (g ∘ join (prod W)) ∘ dec T)
              ∘ strength (G1 ∘ T)
              ∘ cobind (prod W) f.

End kleisli_composition.

#[local] Notation "g ⋆dtm f" := (kcomposedtm g f) (at level 40) : tealeaves_scope.

Tactic Notation "bring" constr(x) "and" constr(y) "together" :=
  change (?f ∘ x ∘ y ∘ ?g) with (f ∘ (x ∘ y) ∘ g).

(** ** Specifications for sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableMonad_suboperations.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}
    `{Applicative G1}
    `{Applicative G2}.

  (** *** [bindd] as a special case of [binddt] *)
  Theorem bindd_to_binddt {A B} : forall (f : W * A -> T B),
      bindd T f = binddt T (G := fun A => A) f.
  Proof.
    intros. unfold binddt.
    change (fmap (fun A => A) ?f) with f.
    now rewrite (dist_unit T).
  Qed.

  (** *** [bindt] as a special case of [binddt] *)
  Theorem bindt_to_binddt {A B} `{Applicative G} : forall (f : A -> G (T B)),
      bindt T f = binddt T (f ∘ extract (prod W)).
  Proof.
    intros. unfold binddt, bindt.
    now rewrite (fmap_to_fmapd T).
  Qed.

  (** *** [fmapdt] as a special case of [binddt] *)
  Theorem fmapdt_to_binddt {A B} `{Applicative G} :
    forall (f : W * A -> G B),
      fmapdt T f = binddt T (fmap G (ret T) ∘ f).
  Proof.
    introv. unfold binddt.
    (* Kill the join *)
    rewrite <- (fun_fmap_fmap T). reassociate <- on right.
    change (fmap T (fmap G ?f)) with (fmap (T ∘ G) f).
    bring (dist T G (A := T B)) and
          (fmap (T ∘ G) (ret T (A := B))) together.
    rewrite <- (dist_natural T). reassociate <-.
    unfold_ops @Fmap_compose.
    unfold_compose_in_compose; rewrite (fun_fmap_fmap G).
    rewrite (mon_join_fmap_ret T).
    now rewrite (fun_fmap_id G).
  Qed.

  (** *** [fmapd] as a special case of [binddt] *)
  Theorem fmapd_to_binddt {A B} : forall (f : W * A -> B),
      fmapd T f = binddt T (G := (fun A => A)) (ret T ∘ f).
  Proof.
    intros. rewrite (DecoratedTraversableFunctor.fmapd_to_fmapdt T).
    now rewrite (fmapdt_to_binddt).
  Qed.

  (** *** [traverse] as a special case of [binddt] *)
  Theorem fmapt_to_binddt {A B} `{Applicative G} : forall (f : A -> G B),
      traverse T G f = binddt T (fmap G (ret T) ∘ f ∘ extract (prod W)).
  Proof.
    introv. rewrite (DecoratedTraversableFunctor.traverse_to_fmapdt T).
    now rewrite (fmapdt_to_binddt).
  Qed.

  (** *** [bind] as a special case of [binddt] *)
  Theorem bind_to_binddt {A B} : forall (f : A -> T B),
      bind T f = binddt T (G := (fun A => A)) (f ∘ extract (prod W)).
  Proof.
    intros. rewrite (bind_to_bindd T).
    now rewrite (bindd_to_binddt).
  Qed.

  (** *** [fmap] as a special case of [binddt] *)
  Theorem fmap_to_binddt {A B} : forall (f : A -> B),
      fmap T f = binddt T (G := (fun A => A)) (ret T ∘ f ∘ extract (prod W)).
  Proof.
    introv. rewrite (DecoratedTraversableFunctor.fmap_to_fmapdt T).
    now rewrite (fmapdt_to_binddt).
  Qed.

End DecoratedTraversableMonad_suboperations.

(** ** Functoriality of [binddt] *)
(******************************************************************************)
Section DecoratedTraversableMonad_binddt.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}.

  Theorem binddt_id {A} : binddt (G := fun A => A) T (ret T ∘ extract (prod W)) = @id (T A).
  Proof.
    introv. rewrite <- (bindd_to_binddt T).
    apply (bindd_id T).
  Qed.

  Theorem binddt_binddt {A B C} `{Applicative G1} `{Applicative G2}
          (f : W * A -> G1 (T B)) (g : W * B -> G2 (T C)) :
    fmap G1 (binddt T g) ∘ binddt T f = binddt (G := G1 ∘ G2) T (g ⋆dtm f).
  Proof.
  Admitted.

End DecoratedTraversableMonad_binddt.

(** ** Composition with sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableMonad_composition.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    `{! Monoid W}.

  (** *** Compositions like <<binddt_xxx>> *)
  (******************************************************************************)
  Corollary binddt_bindd {A B C} : forall (g : W * B -> G (T C)) (f : W * A -> T B),
      binddt T g ∘ bindd T f =
      binddt T ((fmap G (join T))
                  ∘ dist T G
                  ∘ fmap T (g ∘ join (prod W))
                  ∘ dec T
                  ∘ strength T
                  ∘ cobind (prod W) f).
  Proof.
    intros. rewrite (bindd_to_binddt T).
    change (binddt T g) with (fmap (fun A => A) (binddt T g)).
    rewrite (binddt_binddt T (G1 := fun A => A)).
    fequal. apply Mult_compose_identity2.
  Qed.

  Corollary binddt_bindt {A B C} : forall (g : W * B -> G2 (T C)) (f : A -> G1 (T B)),
      fmap G1 (binddt T g) ∘ bindt T f =
      binddt (G := G1 ∘ G2) T ((fmap G1 (fmap G2 (join T) ∘ dist T G2))
                  ∘ fmap G1 (fmap T (g ∘ join (prod W)) ∘ dec T)
                  ∘ strength (G1 ∘ T)
                  ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (bindt_to_binddt T). rewrite (binddt_binddt T).
    fequal. unfold kcomposedtm. now rewrite <- (fmap_to_cobind (prod W)).
  Qed.

  Corollary binddt_fmapdt {A B C} : forall (g : W * B -> G2 (T C)) (f : W * A -> G1 B),
      fmap G1 (binddt T g) ∘ fmapdt T f =
      binddt (G := G1 ∘ G2) T
             ((fmap G1 g)
                ∘ strength G1
                ∘ cobind (prod W) f).
  Proof.
    intros.
    rewrite (fmapdt_to_binddt T).
    rewrite (binddt_binddt T).
    fequal. unfold kcomposedtm.
    rewrite <- (fmap_cobind (prod W)).
    reassociate <-. fequal.
    rewrite (fun_fmap_fmap G1). ext [w t].
    unfold compose; cbn.
    compose near t;
      rewrite (fun_fmap_fmap G1).
    Set Keyed Unification.
    rewrite (fun_fmap_fmap G1).
    Unset Keyed Unification.
    compose near t on left.
    rewrite (fun_fmap_fmap G1).
    fequal. ext b; unfold compose; cbn.
    compose near b on left.
    rewrite (natural (ϕ := @ret T _)).
    unfold_ops @Fmap_I. unfold compose.
    unfold id. compose near (w, b) on left.
    rewrite (dmon_ret W T). unfold compose.
    compose near (Ƶ, (w, b)) on left.
    rewrite (natural (ϕ := @ret T _)).
    unfold_ops @Fmap_I. unfold compose.
    unfold_ops @Join_writer. cbn.
    rewrite monoid_id_r. unfold id.
    compose near (g (w, b)) on left.
    rewrite (trvmon_ret T).
    compose near (g (w, b)) on left.
    rewrite (fun_fmap_fmap G2).
    rewrite (mon_join_ret T).
    now rewrite (fun_fmap_id G2).
  Qed.

  Corollary binddt_bind {A B C} : forall (g : W * B -> G (T C)) (f : A -> T B),
      binddt T g ∘ bind T f =
      binddt T ((fmap G (join T))
                  ∘ dist T G
                  ∘ fmap T (g ∘ join (prod W))
                  ∘ dec T
                  ∘ strength T
                  ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (bind_to_bindd T). rewrite (binddt_bindd).
    now rewrite (fmap_to_cobind (prod W)).
  Qed.

  Corollary binddt_fmapt {A B C} : forall (g : W * B -> G2 (T C)) (f : A -> G1 B),
      fmap G1 (binddt T g) ∘ traverse T G1 f =
      binddt (G := G1 ∘ G2) T
             (fmap G1 g
                  ∘ strength G1
                  ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (traverse_to_bindt T). rewrite (binddt_bindt).
  Admitted.

  Corollary binddt_fmapd {A B C} : forall (g : W * B -> G2 (T C)) (f : W * A -> B),
      binddt T g ∘ fmapd T f =
      binddt T (g ∘ cobind (prod W) f).
  Proof.
  Admitted.

  Corollary binddt_fmap {A B C} : forall (g : W * B -> G2 (T C)) (f : A -> B),
      binddt T g ∘ fmap T f =
      binddt T (g ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (fmap_to_cobind (prod W)).
    rewrite <- binddt_fmapd. now rewrite (fmap_to_fmapd T).
  Qed.

  (** *** Compositions like <<xxx_binddt>> *)
  Corollary bindd_binddt {A B C} : forall (g : W * B -> T C) (f : W * A -> G (T B)),
      fmap G (bindd T g) ∘ binddt T f =
      binddt T ((fmap G (join T))
                  ∘ fmap G (fmap T (g ∘ join (prod W)) ∘ dec T)
                  ∘ strength (G ∘ T)
                  ∘ cobind (prod W) f).
  Proof.
    intros. rewrite (bindd_to_binddt T).
    rewrite (binddt_binddt T (G2 := fun A => A)).
    unfold kcomposedtm. rewrite (dist_unit T).
    change (fmap (fun A => A) ?f) with f.
    change (?f ∘ id) with f. fequal.
    + ext X Y x. change (G ∘ (fun A => A)) with G in x.
      destruct x. unfold Mult_compose.
      unfold_ops @Mult_I. rewrite (fun_fmap_id G).
      reflexivity.
  Qed.

  Corollary bindt_binddt {A B C} : forall (g : B -> G2 (T C)) (f : W * A -> G1 (T B)),
      fmap G1 (bindt T g) ∘ binddt T f =
      binddt T (G := G1 ∘ G2)
             ((fmap G1 ((fmap G2 (join T))
                          ∘ dist T G2
                          ∘ fmap T g))
                ∘ f).
  Proof.
    intros. rewrite (bindt_to_binddt T). rewrite (binddt_binddt T).
    fequal.
  Admitted.

  Corollary fmapdt_binddt {A B C} : forall (g : W * B -> G2 C) (f : W * A -> G1 (T B)),
      fmap G1 (fmapdt T g) ∘ binddt T f =
      binddt T (G := G1 ∘ G2)
             ((fmap G1 (dist T G2))
                ∘ fmap G1 (fmap T (g ∘ join (prod W)) ∘ dec T)
                ∘ strength (G1 ∘ T)
                ∘ cobind (prod W) f).
  Proof.
  Admitted.


  Corollary bind_binddt {A B C} : forall (g : B -> T C) (f : W * A -> G1 (T B)),
      fmap G1 (bind T g) ∘ binddt T f =
      binddt T ((fmap G1 (join T))
                  ∘ fmap G1 (fmap T g)
                  ∘ f).
  Proof.
    intros. rewrite (bind_to_bindt T).
  Admitted.

  Corollary fmapt_binddt {A B C} : forall (g : B -> G2 C) (f : W * A -> G1 (T B)),
      fmap G1 (traverse T G2 g) ∘ binddt T f =
      binddt T (G := G1 ∘ G2) ((fmap G1 (dist T G2 ∘ fmap T g)) ∘ f).
  Proof.
  Admitted.

  Corollary fmapd_binddt {A B C} : forall (g : W * B -> C) (f : W * A -> G1 (T B)),
      fmap G1 (fmapd T g) ∘ binddt T f =
      binddt T (fmap G1 (fmap T (g ∘ join (prod W)) ∘ dec T)
                  ∘ strength (G1 ∘ T)
                  ∘ cobind (prod W) f).
  Proof.
  Admitted.

  Corollary fmap_binddt {A B C} : forall (g : B -> C) (f : W * A -> G1 (T B)),
      fmap G1 (fmap T g) ∘ binddt T f =
      binddt T (fmap (G1 ∘ T) g ∘ f).
  Proof.
  Admitted.

  (** ** Re-statement of inherited composition properties for [bindd] *)
  Corollary bindd_fmapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      bindd T g ∘ fmapd T f = bindd T (g co⋆ f).
  Proof.
    intros. apply (DecoratedMonad.bindd_fmapd T).
  Qed.

  Corollary bind_bindd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      bind T g ∘ bindd T f = bindd T (g ⋆ f).
  Proof.
    intros. apply (DecoratedMonad.bind_bindd T).
  Qed.

  Corollary fmapd_bindd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      fmapd T g ∘ bindd T f = bindd T (fmap T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f)).
  Proof.
    intros. apply (DecoratedMonad.fmapd_bindd T).
  Qed.

  Corollary bindd_bind {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      bindd T g ∘ bind T f = bindd T (bind T g ∘ shift T ∘ fmap (prod W) (dec T ∘ f)).
  Proof.
    intros. apply (DecoratedMonad.bindd_bind T).
  Qed.

  Corollary bindd_fmap {A B C} : forall (g : W * B -> T C) (f : A -> B),
      bindd T g ∘ fmap T f = bindd T (g ∘ fmap (prod W) f).
  Proof.
    intros. apply (DecoratedMonad.bindd_fmap T).
  Qed.

  Corollary fmap_bindd {A B C} : forall (g : B -> C) (f : W * A -> T B),
      fmap T g ∘ bindd T f = bindd T (fmap T g ∘ f).
  Proof.
    intros. apply (DecoratedMonad.fmap_bindd T).
  Qed.

  (** ** Re-statement of inherited composition properties for [bindt] *)
  Corollary bindt_fmapt {A B C} : forall (g : B -> G2 (T C)) (f : A -> G1 B),
      fmap G1 (bindt T g) ∘ traverse T G1 f = bindt T (G := G1 ∘ G2) (fmap G1 g ∘ f).
  Proof.
    intros. apply (TraversableMonad.bindt_fmapt T).
  Qed.

  Corollary bind_bindt {A B C} : forall (g : B -> T C) (f : A -> G (T B)),
      fmap G (bind T g) ∘ bindt T f = bindt T (fmap G (bind T g) ∘ f).
  Proof.
    intros. apply (TraversableMonad.bind_bindt T).
  Qed.

  Corollary fmapt_bindt {A B C} : forall (g : B -> G2 C) (f : A -> G1 (T B)),
      fmap G1 (traverse T G2 g) ∘ bindt T f = bindt (G := G1 ∘ G2) T (fmap G1 (traverse T G2 g) ∘ f).
  Proof.
    intros. apply (TraversableMonad.fmapt_bindt T).
  Qed.

  Corollary bindt_bind {A B C} : forall (g : B -> G (T C)) (f : A -> T B),
      bindt T g ∘ bind T f = bindt T (bindt T g ∘ f).
  Proof.
    intros. apply (TraversableMonad.bindt_bind T).
  Qed.

  Corollary bindt_fmap {A B C} : forall (g : B -> G (T C)) (f : A -> B),
      bindt T g ∘ fmap T f = bindt T (g ∘ f).
  Proof.
    intros. apply (TraversableMonad.bindt_fmap T).
  Qed.

  Corollary fmap_bindt {A B C} : forall (g : B -> C) (f : A -> G (T B)),
      fmap G (fmap T g) ∘ bindt T f = bindt T (fmap (G ∘ T) g ∘ f).
  Proof.
    intros. apply (TraversableMonad.fmap_bindt T).
  Qed.

End DecoratedTraversableMonad_composition.

(** ** Purity laws for [binddt] *)
(******************************************************************************)
Section DecoratedTraversableFunctor_purity.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}.

  #[local] Set Keyed Unification.

  Theorem binddt_purity1 `{Applicative G1} `{Applicative G2} {A B} : forall (f : W * A -> G1 (T B)),
      binddt T (G := G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ binddt T f.
  Proof.
    intros. unfold binddt.
    rewrite <- (fun_fmap_fmap T).
    rewrite (dist_linear T (G1 := G2) (G2 := G1) (H6 := H5) (H2 := H9)).
    do 5 reassociate <-. fequal. fequal.
    unfold_ops @Fmap_compose. rewrite (fun_fmap_fmap G2).
    reassociate -> on left.
    rewrite (fmap_purity_1 T (G := G2)).
    ext t. unfold compose. now rewrite (app_pure_natural G2).
  Qed.

  Theorem binddt_purity2 `{Applicative G} {A B} : forall (f : W * A -> T B),
      binddt T (pure G ∘ f) = pure G ∘ bindd T f.
  Proof.
    intros. rewrite (bindd_to_binddt T).
    rewrite <- (binddt_purity1 (G1 := fun A => A)).
    fequal. ext A' B' [? ?]. unfold Mult_compose.
    unfold_ops @Mult_I. rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

  Theorem binddt_purity `{Applicative G} {A} :
    binddt T (pure G ∘ ret T ∘ extract (prod W)) = pure G (A := T A).
  Proof.
    reassociate ->.
    pose (binddt_purity1 (G2 := G) (G1 := fun A => A) (A := A) (B := A)).
    specialize (e (ret T ∘ extract (prod W))).
  Admitted.

  #[local] Unset Keyed Unification.

End DecoratedTraversableFunctor_purity.

(** ** Respectfulness properties *)
(******************************************************************************)
Section DecoratedTraversableMonad_respectfulness.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}
    `{Applicative G}.

  Lemma binddt_respectful {A B} : forall t (f g : W * A -> G (T B)),
      (forall w a, (w, a) ∈d t -> f (w, a) = g (w, a)) -> binddt T f t = binddt T g t.
  Proof.
    intros. unfold binddt, compose. fequal. fequal.
    apply (fmap_respectful T). intros [? ?]. auto.
  Qed.

  Lemma binddt_respectful_bindt {A B} : forall t (f : W * A -> G (T B)) (g : A -> G (T B)),
      (forall w a, (w, a) ∈d t -> f (w, a) = g a) -> binddt T f t = bindt T g t.
  Proof.
    intros. rewrite (bindt_to_binddt T).
    apply binddt_respectful. auto.
  Qed.

  Lemma binddt_respectful_bindd {A B} : forall t (f : W * A -> G (T B)) (g : W * A -> T B),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G (g (w, a))) -> binddt T f t = pure G (bindd T g t).
  Proof.
    intros. compose near t on right.
    rewrite <- (binddt_purity2 T).
    apply binddt_respectful. auto.
  Qed.

  Lemma binddt_respectful_fmapdt {A B} : forall t (f : W * A -> G (T B)) (g : W * A -> G B),
      (forall w a, (w, a) ∈d t -> f (w, a) = fmap G (ret T) (g (w, a))) -> binddt T f t = fmapdt T g t.
  Proof.
    intros. rewrite (fmapdt_to_binddt T).
    apply binddt_respectful. auto.
  Qed.

  Lemma binddt_respectful_traverse {A B} : forall t (f : W * A -> G (T B)) (g : A -> G B),
      (forall w a, (w, a) ∈d t -> f (w, a) = fmap G (ret T) (g a)) -> binddt T f t = traverse T G g t.
  Proof.
    intros. rewrite (fmapt_to_binddt T).
    apply binddt_respectful. auto.
  Qed.

  Lemma binddt_respectful_fmapd {A B} : forall t (f : W * A -> G (T B)) (g : W * A -> B),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G (ret T (g (w, a)))) -> binddt T f t = pure G (fmapd T g t).
  Proof.
    intros. rewrite (fmapd_to_binddt T).
    compose near t on right.
    rewrite <- (binddt_purity1 T (G2 := G) (G1 := fun A => A)).
    erewrite (binddt_respectful t). fequal.
    ext A' B' [? ?]. unfold Mult_compose. unfold_ops @Mult_I.
    cbn. now rewrite (fun_fmap_id G).
    auto.
  Qed.

  Lemma binddt_respectful_bind {A B} : forall t (f : W * A -> G (T B)) (g : A -> G B),
      (forall w a, (w, a) ∈d t -> f (w, a) = fmap G (ret T) (g a)) -> binddt T f t = traverse T G g t.
  Proof.
    intros. rewrite (fmapt_to_binddt T).
    apply binddt_respectful. auto.
  Qed.

  Lemma binddt_respectful_fmap {A B} : forall t (f : W * A -> G (T B)) (g : A -> B),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G (ret T (g a))) -> binddt T f t = pure G (fmap T g t).
  Proof.
    intros. rewrite (fmap_to_fmapd T).
    apply binddt_respectful_fmapd. auto.
  Qed.

  Corollary binddt_respectful_id {A} : forall t (f : W * A -> G (T A)),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G (ret T a)) -> binddt T f t = pure G t.
  Proof.
    intros. replace t with (fmap T id t) at 2
      by (now rewrite (fun_fmap_id T)).
    apply binddt_respectful_fmap. auto.
  Qed.

End DecoratedTraversableMonad_respectfulness.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Include DecoratedTraversableFunctor.Notations.
  Include Monad.Notations.
  Include Comonad.Notations.
  Include DecoratedMonad.Notations.
  Include TraversableMonad.Notations.
  Notation "g ⋆dtm f" := (kcomposedtm g f) (at level 40) : tealeaves_scope.
End Notations.
