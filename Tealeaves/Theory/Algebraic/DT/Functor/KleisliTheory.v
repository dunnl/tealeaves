
Import Decorated.Functor.ToKleisli.Operation.
Import Traversable.Functor.ToKleisli.Operation.

(** ** Specifications for sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableFunctor_suboperations.

  Context
    (F : Type -> Type)
    `{DecoratedTraversableFunctor E F}.

  (** *** [fmap] as a special case of [fmapdt] *)
  Theorem fmap_to_fmapdt {A B} : forall (f : A -> B),
      fmap F f = fmapdt F (fun A => A) (f ∘ extract (prod E)).
  Proof.
    introv. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap F).
    do 2 reassociate -> on right.
    rewrite (dfun_dec_extract E F).
    now rewrite (dist_unit F).
  Qed.

  (** *** [traverse] as a special case of [fmapdt] *)
  Theorem traverse_to_fmapdt {A B} `{Applicative G} : forall (f : A -> G B),
      traverse F G f = fmapdt F G (f ∘ extract (prod E)).
  Proof.
    introv. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap F).
    do 2 reassociate -> on right.
    now rewrite (dfun_dec_extract E F).
  Qed.

  (** *** [fmapd] as a special case of [fmapdt] *)
  Theorem fmapd_to_fmapdt {A B} : forall (f : E * A -> B),
      fmapd F f = fmapdt F (fun A => A) f.
  Proof.
    introv. unfold transparent tcs.
    now rewrite (dist_unit F).
  Qed.

End DecoratedTraversableFunctor_suboperations.

(** ** Purity laws for <<fmapdt>> *)
(******************************************************************************)
Section DecoratedTraversableFunctor_purity.

  Context
    (F : Type -> Type)
    `{DecoratedTraversableFunctor E F}.

  Theorem fmapdt_purity1 `{Applicative G1} `{Applicative G2} {A B} : forall (f : E * A -> G1 B),
    fmapdt F (G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ fmapdt F G1 f.
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap F).
    reassociate <-. rewrite (dist_linear F).
    reassociate -> near (fmap F (pure G2)).
    rewrite (fmap_purity_1 F). repeat reassociate <-.
    fequal. fequal. ext t. unfold compose.
    now rewrite <- (app_pure_natural G2).
  Qed.

  Theorem fmapdt_purity `{Applicative G} {A} :
    fmapdt F G (pure G ∘ extract (prod E)) = pure G (A := F A).
  Proof.
    unfold transparent tcs. rewrite <- (fun_fmap_fmap F).
    reassociate <-. rewrite (fmap_purity_1 F).
    reassociate ->. now rewrite (dfun_dec_extract E F).
  Qed.

End DecoratedTraversableFunctor_purity.

(** ** Composition with sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableFunctor_composition.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableFunctor E T}
    `{Applicative F}
    `{Applicative F1}
    `{Applicative F2}.

  Corollary fmapd_fmapdt {A B C} : forall (g : E * B -> C) (f : E * A -> F B),
    fmap F (fmapd T g) ∘ fmapdt T F f = fmapdt T F (fmap F g ∘ strength F ∘ cobind (prod E) f).
  Proof.
    intros. rewrite (fmapd_to_fmapdt T).
    rewrite (fmapdt_fmapdt (G2 := (fun A => A)) T).
    unfold kcompose_dt. fequal. unfold Mult_compose.
    ext A' B' [fa fb]. cbn. unfold_ops @Mult_I.
    now rewrite (fun_fmap_id F).
  Qed.

  Corollary fmapdt_fmapd {A B C} : forall (g : E * B -> F C) (f : E * A -> B),
    fmapdt T F g ∘ fmapd T f = fmapdt T F (g ∘ cobind (prod E) f).
  Proof.
    intros. rewrite (fmapd_to_fmapdt T).
    change (fmapdt T F g) with (fmap (fun A => A) (fmapdt T F g)).
    rewrite (fmapdt_fmapdt (G1 := (fun A => A)) T).
    unfold kcompose_dt. fequal.
    + unfold Mult_compose.
      ext A' B' [fa fb]. cbn. unfold_ops @Mult_I.
      reflexivity.
    + now ext [? ?].
  Qed.

  Corollary fmapt_fmapdt {A B C} : forall (g : B -> F2 C) (f : E * A -> F1 B),
    fmap F1 (traverse T F2 g) ∘ fmapdt T F1 f = fmapdt T (F1 ∘ F2) (fmap F1 g ∘ f).
  Proof.
    intros. rewrite (traverse_to_fmapdt T).
    rewrite (fmapdt_fmapdt T).
    unfold kcompose_dt. fequal.
    rewrite <- (fun_fmap_fmap F1).
    unfold strength.
    ext [w a]; unfold compose; cbn.
    compose near (f (w, a)) on left. rewrite (fun_fmap_fmap F1).
    replace (extract (prod E) ∘ pair (id w)) with (@id B).
    compose near (f (w, a)) on left.
    now rewrite (fun_fmap_id F1).
    now ext x.
  Qed.

  Corollary fmapdt_fmapt {A B C} : forall (g : E * B -> F2 C) (f : A -> F1 B),
    fmap F1 (fmapdt T F2 g) ∘ traverse T F1 f = fmapdt T (F1 ∘ F2) (fmap F1 g ∘ strength F1 ∘ fmap (prod E) f).
  Proof.
    intros. rewrite (traverse_to_fmapdt T).
    rewrite (fmapdt_fmapdt T).
    unfold kcompose_dt. fequal.
    now rewrite (fmap_to_cobind (prod E)).
  Qed.

  Corollary fmapd_fmapt {A B C} : forall (g : E * B -> C) (f : A -> F B),
      fmap F (fmapd T g) ∘ traverse T F f = fmapdt T F (fmap F g ∘ strength F ∘ fmap (prod E) f).
  Proof.
    intros. rewrite (traverse_to_fmapdt T), (fmapd_to_fmapdt T).
    rewrite (fmapdt_fmapdt (G2 := fun A => A) T).
    fequal.
    + unfold Mult_compose.
      ext A' B' [fa fb]. cbn. unfold_ops @Mult_I.
      now rewrite (fun_fmap_id F).
    + unfold kcompose_dt. now rewrite (fmap_to_cobind (prod E)).
  Qed.

  Corollary fmapt_fmapd {A B C} : forall (g : B -> F C) (f : E * A -> B),
      traverse T F g ∘ fmapd T f = fmapdt T F (g ∘ f).
  Proof.
    intros. change (traverse T F g) with (fmap (fun A => A) (traverse T F g)).
    rewrite (traverse_to_fmapdt T), (fmapd_to_fmapdt T).
    rewrite (fmapdt_fmapdt (G1 := fun A => A) T).
    fequal.
    + unfold Mult_compose.
      ext A' B' [fa fb]. cbn. unfold_ops @Mult_I.
      reflexivity.
    + unfold kcompose_dt. change (fmap (fun A => A) ?f) with f.
      now ext [w a].
  Qed.

  Corollary fmapd_fmapdt_alt {A B C} : forall (g : E * B -> C) (f : E * A -> F B),
    fmap F (fmapd T g) ∘ fmapdt T F f = fmapdt T F (fmap F g ∘ strength F ∘ cobind (prod E) f).
  Proof.
    intros. unfold transparent tcs.
    unfold fmapd. repeat reassociate <- on left.
    rewrite <- (fun_fmap_fmap F).
    (* Scoot distribution left over decoration *)
    reassociate -> near (dist T F).
    rewrite <- (dtfun_compat E T B).
    (* Scoot distribution left over <<g>> *)
    repeat reassociate <-.
    change (fmap F (fmap T g)) with (fmap (F ∘ T) g).
    rewrite (natural (ϕ := @dist T _ F _ _ _) g).
    unfold_ops @Fmap_compose.
    reassociate -> near (fmap T (strength F)). rewrite (fun_fmap_fmap T).
    (* Replace repeated decorations with a <<cobind>> *)
    reassociate -> near (dec T). change (fmap T f ∘ dec T) with (fmapd T f).
    reassociate -> near (fmapd T f).
    rewrite (dec_fmapd T f).
    (* Fuse <<fmap>> together *)
    unfold_ops @Fmapd_alg.
    reassociate <- on left.
    reassociate -> near (fmap T (cobind (prod E) f)).
    now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary fmapdt_fmap {A B C} : forall (g : B -> C) (f : E * A -> F B),
    fmap F (fmap T g) ∘ fmapdt T F f = fmapdt T F (fmap F g ∘ f).
  Proof.
    intros. unfold transparent tcs. repeat reassociate <- on left.
    change (fmap F (fmap T g)) with (fmap (F ∘ T) g).
    rewrite (natural (ϕ := @dist T _ F _ _ _) g).
    unfold_ops @Fmap_compose.
    reassociate -> near (fmap T f). now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary fmap_fmapdt {A B C} : forall (g : B -> C) (f : E * A -> F B),
    fmap F (fmap T g) ∘ fmapdt T F f = fmapdt T F (fmap F g ∘ f).
  Proof.
    intros. unfold transparent tcs. repeat reassociate <- on left.
    change (fmap F (fmap T g)) with (fmap (F ∘ T) g).
    rewrite (natural (ϕ := @dist T _ F _ _ _) g).
    unfold_ops @Fmap_compose.
    reassociate -> near (fmap T f). now rewrite (fun_fmap_fmap T).
  Qed.

  (** ** Re-statement of inherited composition properties  *)
  Corollary fmapd_fmap {A B C} : forall (g : E * B -> C) (f : A -> B),
      fmapd T g ∘ fmap T f = fmapd T (g ∘ map_snd f).
  Proof.
    intros; apply (fmapd_fmap T).
  Qed.

  Corollary fmap_fmapd {A B C} : forall (g : B -> C) (f : E * A -> B),
    fmap T g ∘ fmapd T f = fmapd T (g ∘ f).
  Proof.
    intros; apply (fmap_fmapd T).
  Qed.

  Corollary fmap_traverse : forall `(g : B -> C) `(f : A -> F B),
      fmap F (fmap T g) ∘ traverse T F f = traverse T F (fmap F g ∘ f).
  Proof.
    intros; apply (fmap_traverse T F); auto.
  Qed.

  Corollary traverse_fmap : forall `(g : B -> F C) `(f : A -> B),
      traverse T F g ∘ fmap T f = traverse T F (g ∘ f).
  Proof.
    intros; apply (traverse_fmap T); auto.
  Qed.

End DecoratedTraversableFunctor_composition.

(*
(** ** Respectfulness properties *)
(******************************************************************************)
Section DecoratedTraversableFunctor_respectfulness.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableFunctor E T}
    `{Applicative G}.

  Lemma fmapdt_respectful {A B} : forall t (f g : E * A -> G B),
      (forall w a, (w, a) ∈d t -> f (w, a) = g (w, a)) -> fmapdt T G f t = fmapdt T G g t.
  Proof.
    intros. unfold transparent tcs. unfold compose. fequal.
    apply (fmap_respectful T). intros [? ?]. auto.
  Qed.

  Lemma fmapdt_respectful_traverse {A B} : forall t (f : E * A -> G B) (g : A -> G B),
      (forall w a, (w, a) ∈d t -> f (w, a) = g a) -> fmapdt T f t = traverse T G g t.
  Proof.
    intros. rewrite (traverse_to_fmapdt T).
    apply fmapdt_respectful. auto.
  Qed.

  Lemma fmapdt_respectful_fmapd {A B} : forall t (f : E * A -> G B) (g : E * A -> B),
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

  Lemma fmapdt_respectful_fmap {A B} : forall t (f : E * A -> G B) (g : A -> B),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G (g a)) -> fmapdt T f t = pure G (fmap T g t).
  Proof.
    intros. rewrite (fmap_to_fmapd T).
    apply fmapdt_respectful_fmapd. auto.
  Qed.

  Corollary fmapdt_respectful_id {A} : forall t (f : E * A -> G A),
      (forall w a, (w, a) ∈d t -> f (w, a) = pure G a) -> fmapdt T f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity T).
    rewrite (traverse_to_fmapdt T).
    now apply fmapdt_respectful.
  Qed.

End DecoratedTraversableFunctor_respectfulness.
*)
