From Tealeaves Require Export
     Classes.DecoratedMonad
     Classes.TraversableMonad
     Classes.DecoratedTraversableFunctor.

Import Product.Notations.
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

(** Now we verify that the sub-classes can be inferred as well. *)
(******************************************************************************)
Section test_typeclasses.

  Context
    `{DecoratedTraversableMonad W T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal DecoratedFunctor W T. typeclasses eauto. Qed.
  Goal SetlikeFunctor T. typeclasses eauto. Qed.
  Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
  Goal DecoratedTraversableFunctor W T. typeclasses eauto. Qed.

  Goal Monad T. typeclasses eauto. Qed.
  Goal DecoratedMonad W T. typeclasses eauto. Qed.
  Goal SetlikeMonad T. typeclasses eauto. Qed.
  Goal ListableMonad T. typeclasses eauto. Qed.
  Goal TraversableMonad T. typeclasses eauto. Qed.

End test_typeclasses.

(** * Kleisli presentation of D-T monads *)
(******************************************************************************)

(** ** Lifting operation <<binddt>> and Kleisli composition  *)
(******************************************************************************)
Definition binddt (T : Type -> Type)
           `{Fmap T} `{Decorate W T} `{Dist T} `{Join T}
           `{Fmap G} `{Pure G} `{Mult G}
           {A B : Type} (f : W * A -> G (T B)) : T A -> G (T B) :=
  fmap G (join T) ∘ dist T G ∘ fmap T f ∘ dec T.

Section kleisli_composition.

  Context
    `{DecoratedTraversableMonad W T}
    {A B C : Type} `{Applicative G1} `{Applicative G2}.

  Definition kcomposedtm :
    (W * B -> G2 (T C)) ->
    (W * A -> G1 (T B)) ->
    (W * A -> G1 (G2 (T C))) :=
    fun g f => (fmap G1 ((fmap G2 (μ T))
                        ∘ δ T G2
                        ∘ fmap T (g ∘ μ (W ×))
                        ∘ σ T
                        ∘ fmap (W ×) (dec T)))
              ∘ σ G1
              ∘ cobind (W ×) f.

(* Compare the above definition to this candidate definition:
<<
  Definition kcomposedtm {A B C}
             `{Applicative G1}
             `{Applicative G2} :
    (W * B -> G2 (T C)) ->
    (W * A -> G1 (T B)) ->
    (W * A -> G1 (G2 (T C))) :=
    fun g f => (fmap G1 ((fmap G2 (join T))
                        ∘ dist T G2
                        ∘ fmap T (g ∘ join (prod W))
                        ∘ dec T))
              ∘ strength (G1 ∘ T)
              ∘ cobind (prod W) f.
>>
   This definition is wrong in the sense that it passes arguments to the monoid operation
   in an unexpected order (which is to say, not the same order as <<shift>>, which we understand as the
   operation used in the definition <<dec T>>. (Alternatively we could probably swap the order for both definitions.)
 *)

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

  Section binddt_binddt.

    Context {A B C : Type} `{Applicative G1} `{Applicative G2}
            (f : W * A -> G1 (T B)) (g : W * B -> G2 (T C)).

    Lemma binddt_binddt1 :
      (fmap G1 (dec T ∘ μ T) ∘ δ T G1 : T (G1 (T B)) -> G1 (T (W * B)))
      = fmap G1 (fmap T (μ (prod W)) ∘ μ T ∘ fmap T (σ T ∘ fmap (prod W) (dec T)))
             ∘ δ T G1 ∘ fmap T (σ G1) ∘ dec T.
    Proof.
      rewrite (dmon_join W T). unfold shift.
      change (?f ∘ δ T G1 ∘ fmap T (σ G1) ∘ dec T)
        with (f ∘ (δ T G1 ∘ fmap T (σ G1) ∘ dec T)).
      rewrite (dtfun_compat W T (G := G1)).
      reassociate <- on right. fequal.
      rewrite (fun_fmap_fmap G1).
      rewrite (natural (ϕ := @join T _)).
      fequal. rewrite <- (fun_fmap_fmap T (g := σ T)).
      repeat reassociate <- on right.
      change (fmap T (fmap (prod W) (dec T) (A := ?A)))
        with (fmap (T ∘ (W ×)) (dec T) (A := A)).
      reassociate -> near (dec T).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dec W T _) (dec T)).
      do 2 reassociate <-.
      reassociate -> near (fmap T (σ T)).
      now rewrite (fun_fmap_fmap T).
      #[local] Unset Keyed Unification.
    Qed.

    (* Note that we *cannot* immediately cancel out the right-most two <<dec T>> sub-expressions *)
    Lemma binddt_binddt2 :
      fmap G1 (fmap T g ∘ dec T ∘ μ T) ∘ δ T G1 ∘ fmap T f ∘ dec T =
        fmap G1 (μ T ∘ fmap T (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))) ∘ δ T G1
             ∘ fmap T (σ G1 ∘ cobind (prod W) f) ∘ dec T.
    Proof.
      rewrite <- (fun_fmap_fmap T (f := cobind (W ×) f)).
      do 4 reassociate -> on right.
      rewrite (cobind_dec T f).
      do 5 reassociate <- on right. fequal. fequal.
      change (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))
        with (fmap T (g ∘ μ (prod W)) ∘ (σ T ∘ fmap (prod W) (dec T))).
      rewrite <- (fun_fmap_fmap T).
      change (fmap T (fmap T (g ∘ μ (prod W)))) with (fmap (T ∘ T) (g ∘ μ (W ×))).
      reassociate <- on right.
      rewrite <- (natural (ϕ := @join T _) (g ∘ μ (W ×))).
      change (fmap T g ∘ dec T ∘ μ T) with (fmap T g ∘ (dec T ∘ μ T)).
      rewrite <- (fun_fmap_fmap G1).
      rewrite <- (fun_fmap_fmap T).
      change ((fmap T g ∘ fmap T (μ (prod W)) ∘ μ T
                    ∘ fmap T (σ T ∘ fmap (prod W) (dec T))))
        with ((fmap T g ∘ (fmap T (μ (prod W)) ∘ μ T
                                ∘ fmap T (σ T ∘ fmap (prod W) (dec T))))).
      rewrite <- (fun_fmap_fmap G1 (g := fmap T g)).
      reassociate -> on left.
      do 4 reassociate -> on right.
      fequal. do 3 reassociate <- on right.
      apply binddt_binddt1.
    Qed.

    Theorem binddt_binddt :
      fmap G1 (binddt T g) ∘ binddt T f = binddt (G := G1 ∘ G2) T (g ⋆dtm f).
    Proof.
      unfold binddt. repeat reassociate <-.
      rewrite (dist_linear T). reassociate <- on right.
      #[local] Set Keyed Unification.
      rewrite 2(fun_fmap_fmap G1).
      #[local] Unset Keyed Unification.
      unfold kcomposedtm.
      reassociate -> near (cobind (W ×) f).
      rewrite <- (fun_fmap_fmap T).
      change (fmap T (fmap G1 ?f)) with (fmap (T ∘ G1) f).
      reassociate <- on right.
      change (fmap G1 (fmap G2 (μ T) ∘ δ T G2) ∘ ?dist ∘ ?op)
        with (fmap G1 (fmap G2 (μ T) ∘ δ T G2) ∘ (dist ∘ op)).
      rewrite <- (dist_natural T (G := G1)).
      change (fmap (G1 ∘ T) ?f) with (fmap G1 (fmap T f)).
      reassociate <-.
      #[local] Set Keyed Unification.
      rewrite (fun_fmap_fmap G1).
      #[local] Unset Keyed Unification.
      change (fmap T (fmap G2 (μ T) ∘ δ T G2 ∘ fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T)))
        with (fmap T (fmap G2 (μ T) ∘ (δ T G2 ∘ fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T)))).
      rewrite <- (fun_fmap_fmap T).
      change (fmap T (fmap G2 ?f)) with (fmap (T ∘ G2) f).
      reassociate <- on right. reassociate -> near (fmap (T ∘ G2) (μ T)).
      rewrite <- (dist_natural T). reassociate <- on right.
      #[local] Set Keyed Unification.
      rewrite (fun_fmap_fmap G2).
      #[local] Unset Keyed Unification.
      rewrite <- (mon_join_join T).
      rewrite <- (fun_fmap_fmap G2).
      reassociate -> near (δ T G2).
      change (δ T G2 ∘ fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))
        with (δ T G2 ∘ (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))).
      rewrite <- (fun_fmap_fmap T).
      do 2 reassociate <- on right.
      change (fmap G2 (μ T) ∘ fmap G2 (μ T) ∘ δ T G2 ∘ fmap T (δ T G2) (A := ?A))
        with (fmap G2 (μ T) ∘ (fmap G2 (μ T) ∘ δ T G2 ∘ fmap T (δ T G2) (A := A))).
      change (fmap G2 (μ T) ∘ δ T G2 ∘ fmap T (δ T G2) (A := T (G2 ?A)))
        with (fmap G2 (μ T) ∘ δ (T ∘ T) G2 (A := A)).
      rewrite <- (trvmon_join T).
      reassociate <- on right.
      change_left (fmap G1 (fmap G2 (μ T) ∘ δ T G2 ∘ (fmap T g ∘ dec T ∘ μ T)) ∘ δ T G1 ∘ fmap T f ∘ dec T).
      change_right (fmap G1 (fmap G2 (μ T) ∘ δ T G2 ∘ (μ T ∘ fmap T (fmap T (g ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))))
                         ∘ δ T G1
                         ∘ fmap T (σ G1 ∘ cobind (prod W) f) ∘ dec T).
      (* cancel out the common sub-expressions and apply a lemma to the remaining. *)
      rewrite <- (fun_fmap_fmap G1).
      rewrite <- (fun_fmap_fmap G1 (g := fmap G2 (μ T) ∘ δ T G2)).
      do 3 reassociate -> on left.
      do 3 reassociate -> on right.
      fequal. repeat reassociate <-.
      apply binddt_binddt2.
    Qed.

  End binddt_binddt.

End DecoratedTraversableMonad_binddt.

(** ** Kleisli composition laws  *)
(******************************************************************************)
Section DecoratedTraversableMonad_kleisli.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    `{! Monoid W}.

  (** *** Miscellaneous lemmas *)
  (******************************************************************************)

  (** If <<g>> is going to discard the decoration, we don't have to compute it. *)
  Lemma dtm_kleisli_lemma1 : forall A,
    (fmap T (extract (prod W) ∘ μ (prod W)) ∘ σ T
          ∘ fmap (W ×) (dec T) : W * T A -> T A) = extract (W ×).
  Proof.
    intros. ext [w t]. unfold compose; cbn. unfold id.
    compose near (dec T t). rewrite (fun_fmap_fmap T).
    replace (extract (W ×) ○ μ (W ×) ∘ pair w (B := W * A))
      with (extract (W ×) (A := A)).
    compose near t on left. now rewrite (dfun_dec_extract W T).
    now ext [? ?].
  Qed.

  (** If <<f>> has a trivial <<T>> output, we use its same <<W>> input. *)
  Lemma dtm_kleisli_lemma2 : forall A,
    (fmap T (μ (prod W)) ∘ σ T
          ∘ fmap (W ×) (dec T ∘ ret T) : W * A -> T (W * A)) = ret T (A := W * A).
  Proof.
    intros. ext [w t]. unfold compose; cbn. unfold id.
    compose near (t). rewrite (dmon_ret W T); unfold compose; cbn.
    compose near (Ƶ, t). rewrite (natural (ϕ := @ret T _)). unfold_ops @Fmap_I.
    unfold compose; cbn.
    compose near (w, (Ƶ, t)). rewrite (natural (ϕ := @ret T _)). unfold_ops @Fmap_I.
    unfold compose; cbn. now simpl_monoid.
  Qed.

  (** *** Left and right identity laws *)
  (******************************************************************************)
  Lemma dtm_kleisli_identity1 :  forall `(f : W * A -> G (T B)),
      kcomposedtm (G2 := fun A => A) (ret T ∘ extract (W ×)) f = f.
  Proof.
    intros. unfold kcomposedtm. unfold_ops @Fmap_I.
    rewrite (dist_unit T). reassociate -> near (μ (W ×)).
    rewrite <- (fun_fmap_fmap T). reassociate <-.
    change (?foo ∘ fmap T (extract (prod W) ∘ μ (prod W)) ∘ σ T
     ∘ fmap (prod W) (dec T)) with (foo ∘ (fmap T (extract (prod W) ∘ μ (prod W)) ∘ σ T
     ∘ fmap (prod W) (dec T))).
    rewrite dtm_kleisli_lemma1.
    change (?f ∘ id) with f.
    rewrite <- (fun_fmap_fmap G).
    reassociate -> near (σ G).
    rewrite (strength_extract).
    reassociate ->.
    rewrite (extract_cobind (W ×)).
    rewrite (mon_join_fmap_ret T).
    rewrite (fun_fmap_id G).
    easy.
  Qed.

  Lemma dtm_kleisli_identity2 :  forall `(g : W * A -> G (T B)),
      kcomposedtm (G1 := fun A => A) g (ret T ∘ extract (W ×)) = g.
  Proof.
    intros. unfold kcomposedtm. unfold_ops @Fmap_I.
    rewrite strength_I. change (?f ∘ id) with f.
    rewrite <- (fmap_to_cobind (W ×)).
    reassociate ->. rewrite (fun_fmap_fmap (W ×)).
    rewrite <- (fun_fmap_fmap T). reassociate <-.
    change (?foo ∘ fmap T (μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T ∘ η T))
      with (foo ∘ (fmap T (μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T ∘ η T))).
    rewrite dtm_kleisli_lemma2.
    reassociate -> on left. rewrite (natural (ϕ := @ret T _)).
    unfold_ops @Fmap_I. reassociate <-.
    reassociate -> near (η T). rewrite (trvmon_ret T).
    rewrite (fun_fmap_fmap G). rewrite (mon_join_ret T).
    now rewrite (fun_fmap_id G).
  Qed.

  (** *** Kleisli composition with special cases in <<f>>  *)
  (******************************************************************************)

  (** Kleisli composition when <<f>> has no applicative effect. *)
  Lemma dtm_kleisli_star1 :  forall `(g : W * B -> G (T C)) `(f : W * A -> T B),
      (kcomposedtm (G1 := fun A => A) g f) = (fmap G (μ T))
                   ∘ δ T G
                   ∘ fmap T (g ∘ μ (W ×))
                   ∘ σ T
                   ∘ fmap (W ×) (dec T)
                   ∘ cobind (W ×) f.
  Proof.
    intros. unfold kcomposedtm.
    now rewrite strength_I.
  Qed.

  (** Kleisli composition when <<f>> has no substitution. *)
  Lemma dtm_kleisli_star2 {A B C} : forall (g : W * B -> G2 (T C)) (f : W * A -> G1 B),
      g ⋆dtm (fmap G1 (ret T) ∘ f) = fmap G1 g ∘ σ G1 ∘ cobind (W ×) f.
  Proof.
    intros. fequal. unfold kcomposedtm.
    rewrite <- (fmap_cobind (prod W)).
    reassociate <-. fequal. ext [w t].
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
    unfold id.
    rewrite (dmon_ret W T). unfold compose.
    compose near (Ƶ, b).
    rewrite (natural (ϕ := @ret T _)).
    unfold_ops @Fmap_I. unfold compose.
    compose near (w, (Ƶ, b)) on left.
    rewrite (natural (ϕ := @ret T _)).
    unfold_ops @Fmap_I.
    unfold compose. cbn. rewrite monoid_id_l.
    unfold id.
    compose near (g (w, b)) on left.
    rewrite (trvmon_ret T).
    compose near (g (w, b)) on left.
    rewrite (fun_fmap_fmap G2).
    rewrite (mon_join_ret T).
    now rewrite (fun_fmap_id G2).
  Qed.

  (** Kleisli composition when <<f>> discards the decoration. *)
  Lemma dtm_kleisli_star3 {A B C} : forall (g : W * B -> G2 (T C)) (f : A -> G1 (T B)),
      g ⋆dtm (f ∘ extract (W ×)) = fmap G1 ((fmap G2 (μ T))
                                              ∘ δ T G2
                                              ∘ fmap T (g ∘ μ (prod W))
                                              ∘ σ T
                                              ∘ fmap (W ×) (dec T))
                                        ∘ σ G1
                                        ∘ fmap (W ×) f.
  Proof.
    intros. fequal. unfold kcomposedtm. now rewrite <- (fmap_to_cobind (prod W)).
  Qed.

  (** Kleisli composition when <<f>> discards the decoration and has no applicative effect. *)
  Lemma dtm_kleisli_star4 {A B C} : forall (g : W * B -> G (T C)) (f : A -> T B),
      (kcomposedtm (G1 := fun A => A) g (f ∘ extract (W ×)) =
         (fmap G (μ T))
           ∘ dist T G
           ∘ fmap T (g ∘ μ (prod W))
           ∘ σ T
           ∘ fmap (W ×) (dec T ∘ f)).
  Proof.
    intros. unfold kcomposedtm. rewrite strength_I. unfold_ops @Fmap_I.
    rewrite <- (fmap_to_cobind (W ×)).
    change (?f ∘ id) with f.
    reassociate -> on left. now rewrite (fun_fmap_fmap (W ×)).
  Qed.

  (** Kleisli composition when <<f>> has no effects. *)
  Lemma dtm_kleisli_star5 {A B C} : forall (g : W * B -> G (T C)) (f : A -> B),
      kcomposedtm (G1 := fun A => A) g (η T ∘ f ∘ extract (W ×)) = (g ∘ fmap (W ×) f).
  Proof.
    intros. unfold kcomposedtm. rewrite strength_I. unfold_ops @Fmap_I.
    change (?f ∘ id) with f.
    change (η T ∘ f ∘ extract (prod W)) with (η T ∘ (f ∘ extract (prod W))).
    rewrite <- (fmap_cobind (W ×)).
    rewrite <- (fmap_to_cobind (W ×)).
    reassociate <- on left.
    reassociate -> near (fmap (W ×) (η T)).
    rewrite (fun_fmap_fmap (W ×)).
    change (?g ∘ σ T ∘ fmap (prod W) (dec T ∘ η T) ∘ fmap (prod W) f)
      with (g ∘ (σ T ∘ fmap (prod W) (dec T ∘ η T)) ∘ fmap (prod W) f).
    rewrite (dmon_ret W T).
    replace (σ T ∘ fmap (W ×) (η T ∘ pair (Ƶ : W)) (A := B))
      with (fmap T (fmap (W ×) (pair (Ƶ : W))) ∘ η T (A := W * B)).
    2:{ ext [w a]. unfold compose. cbn.
        compose near (w, a). compose near (Ƶ, a).
        rewrite (natural (ϕ := @ret T _)).
        rewrite (natural (ϕ := @ret T _)).
        reflexivity. }
    reassociate <- on left.
    reassociate -> near (fmap T (fmap (prod W) (pair Ƶ))).
    rewrite (fun_fmap_fmap T).
    reassociate -> near (fmap (prod W) (pair Ƶ)).
    change (fmap (prod W) (pair Ƶ (B := ?A))) with (fmap (prod W) (η (W ×) (A := A))).
    rewrite (mon_join_fmap_ret (W ×)).
    reassociate -> near (η T).
    rewrite (natural (ϕ := @ret T _)).
    unfold_ops @Fmap_I. reassociate <- on left.
    reassociate -> near (η T). rewrite (trvmon_ret T).
    rewrite (fun_fmap_fmap G). rewrite (mon_join_ret T).
    now rewrite (fun_fmap_id G).
  Qed.

  (** *** Kleisli composition with special cases in <<g>>  *)
  (******************************************************************************)

  (** Composition with <<g>> discards the decoration. *)
  Lemma dtm_kleisli_star6  {A B C} : forall (g : B -> G2 (T C)) (f : W * A -> G1 (T B)),
      (g ∘ extract (prod W)) ⋆dtm f = fmap G1 (fmap G2 (μ T) ∘ δ T G2 ∘ fmap T g) ∘ f.
  Proof.
    intros. unfold kcomposedtm.
    reassociate -> near (μ (prod W)).
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on left.
    change (?foo ∘ fmap T (extract (prod W) ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))
      with (foo ∘ (fmap T (extract (prod W) ∘ μ (prod W)) ∘ σ T ∘ fmap (prod W) (dec T))).
    rewrite dtm_kleisli_lemma1.
    rewrite <- (fun_fmap_fmap G1).
    change (?foo ∘ fmap G1 (extract (prod W)) ∘ σ G1 ∘ cobind (prod W) f)
      with (foo ∘ (fmap G1 (extract (prod W)) ∘ σ G1 ∘ cobind (prod W) f)).
    rewrite strength_extract.
    now rewrite (extract_cobind (W ×)).
  Qed.

End DecoratedTraversableMonad_kleisli.

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

  (** *** Composition laws when <<f>> is trivial in a certain effect. *)
  (******************************************************************************)

  (** Composition when <<f>> has no applicative effect. *)
  Corollary binddt_bindd {A B C} : forall (g : W * B -> G (T C)) (f : W * A -> T B),
      binddt T g ∘ bindd T f =
        binddt T ((fmap G (μ T))
                    ∘ δ T G
                    ∘ fmap T (g ∘ μ (W ×))
                    ∘ σ T
                    ∘ fmap (W ×) (dec T)
                    ∘ cobind (W ×) f).
  Proof.
    intros. rewrite (bindd_to_binddt T).
    change (binddt T g) with (fmap (fun A => A) (binddt T g)).
    rewrite (binddt_binddt T (G1 := fun A => A)).
    rewrite dtm_kleisli_star1.
    fequal. apply Mult_compose_identity2.
  Qed.

  (** Composition when <<f>> does not use the decoration structure. *)
  Corollary binddt_bindt {A B C} : forall (g : W * B -> G2 (T C)) (f : A -> G1 (T B)),
      fmap G1 (binddt T g) ∘ bindt T f =
        binddt (G := G1 ∘ G2) T
               ((fmap G1 ((fmap G2 (μ T))
                        ∘ δ T G2
                        ∘ fmap T (g ∘ μ (W ×))
                        ∘ σ T
                        ∘ fmap (W ×) (dec T)))
              ∘ σ G1
              ∘ fmap (W ×) f).
  Proof.
    intros. rewrite (bindt_to_binddt T). rewrite (binddt_binddt T).
    now rewrite dtm_kleisli_star3.
  Qed.

  (** Composition when <<f>> has no substitution. *)
  Corollary binddt_fmapdt {A B C} : forall (g : W * B -> G2 (T C)) (f : W * A -> G1 B),
      fmap G1 (binddt T g) ∘ fmapdt T f =
        binddt (G := G1 ∘ G2) T ((fmap G1 g)
                                   ∘ σ G1
                                   ∘ cobind (prod W) f).
  Proof.
    intros.
    rewrite (fmapdt_to_binddt T).
    rewrite (binddt_binddt T).
    now rewrite (dtm_kleisli_star2 T).
  Qed.

  (** Composition when <<f>> has no decoration or applicative effect. *)
  Corollary binddt_bind {A B C} : forall (g : W * B -> G (T C)) (f : A -> T B),
      binddt T g ∘ bind T f =
        binddt T ((fmap G (μ T))
                    ∘ dist T G
                    ∘ fmap T (g ∘ μ (prod W))
                    ∘ σ T
                    ∘ fmap (W ×) (dec T ∘ f)).
  Proof.
    intros. rewrite (bind_to_binddt T).
    change (binddt T g) with (fmap (fun A => A) (binddt T g)).
    rewrite (binddt_binddt T (G1 := fun A => A)).
    rewrite (dtm_kleisli_star4).
    fequal; apply Mult_compose_identity2.
  Qed.

  (** Composition when <<f>> has no decoration or substitution effect. *)
  Corollary binddt_fmapt {A B C} : forall (g : W * B -> G2 (T C)) (f : A -> G1 B),
      fmap G1 (binddt T g) ∘ traverse T G1 f =
        binddt (G := G1 ∘ G2) T
               (fmap G1 g
                     ∘ σ G1
                     ∘ fmap (W ×) f).
  Proof.
    intros. rewrite (traverse_to_bindt T). unfold binddt, bindt.
    repeat reassociate <-. rewrite (fun_fmap_fmap G1).
    rewrite (dist_linear T). reassociate <-.
    unfold_ops @Fmap_compose.
    #[local] Set Keyed Unification.
    rewrite (fun_fmap_fmap G1).
    #[local] Unset Keyed Unification.
    repeat reassociate <-.
    change (fmap G1 g ∘ σ G1 ∘ fmap (prod W) f)
      with (fmap G1 g ∘ (σ G1 ∘ fmap (prod W) f)).
    rewrite <- (fun_fmap_fmap T (g  := fmap G1 g)).
    reassociate <-.
    change (fmap T (fmap G1 g)) with (fmap (T ∘ G1) g).
    reassociate -> near (fmap (T ∘ G1) g).
    rewrite <- (dist_natural T).
    repeat reassociate <-.
    #[local] Set Keyed Unification.
    rewrite (fun_fmap_fmap G1).
    #[local] Unset Keyed Unification.
    rewrite <- (fun_fmap_fmap T (g := σ G1)).
    reassociate <-.
    change (fmap T (fmap (W ×) f)) with (fmap (T ∘ (W ×)) f).
    reassociate -> on right.
    rewrite (natural (ϕ := @dec W T _)).
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on left.
    change (fmap T (fmap G1 ?eta)) with (fmap (T ∘ G1) eta).
    reassociate -> near (fmap (T ∘ G1) (η T)).
    rewrite <- (dist_natural T).
    #[local] Set Keyed Unification.
    reassociate <-. rewrite (fun_fmap_fmap G1).
    #[local] Unset Keyed Unification.
    reassociate -> near (fmap T (η T)).
    rewrite (mon_join_fmap_ret T).
    reassociate <-.
    change (?g ∘ δ T G1 ∘ fmap T (σ G1) ∘ dec T ∘ fmap T f)
      with (g ∘ (δ T G1 ∘ fmap T (σ G1) ∘ dec T) ∘ fmap T f).
    rewrite (dtfun_compat W T).
    reassociate <- on right.
    now rewrite (fun_fmap_fmap G1).
  Qed.

  (** Composition when <<f>> has no substitution or applicative effect. *)
  Corollary binddt_fmapd {A B C} : forall (g : W * B -> G2 (T C)) (f : W * A -> B),
      binddt T g ∘ fmapd T f =
      binddt T (g ∘ cobind (prod W) f).
  Proof.
    intros. unfold binddt.
    reassociate ->. rewrite (dec_fmapd T).
    reassociate ->. rewrite (fmap_fmapd T).
    reflexivity.
  Qed.

  (** Composition when <<f>> has no special effect. *)
  Corollary binddt_fmap {A B C} : forall (g : W * B -> G2 (T C)) (f : A -> B),
      binddt T g ∘ fmap T f =
      binddt T (g ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (fmap_to_binddt T).
    change (binddt T g) with (fmap (fun A => A) (binddt T g)).
    rewrite (binddt_binddt T (G1 := fun A => A)).
    rewrite (dtm_kleisli_star5 T g f).
    now rewrite Mult_compose_identity2. (* tricky *)
  Qed.

  (** *** Composition laws when <<g>> is trivial in a certain effect. *)
  (******************************************************************************)

  (** Composition with g has no applicative effect. *)
  Corollary bindd_binddt {A B C} : forall (g : W * B -> T C) (f : W * A -> G (T B)),
      fmap G (bindd T g) ∘ binddt T f =
        binddt T ((fmap G (μ T
                             ∘ fmap T (g ∘ μ (prod W))
                             ∘ σ T
                             ∘ fmap (W ×) (dec T)))
                    ∘ σ G
                    ∘ cobind (prod W) f).
  Proof.
    intros. rewrite (bindd_to_binddt T).
    rewrite (binddt_binddt T (G2 := fun A => A)).
    unfold kcomposedtm. rewrite (dist_unit T).
    change (fmap (fun A => A) ?f) with f.
    change (?f ∘ id) with f. fequal.
    + ext X Y x. change (G ∘ (fun A => A)) with G in x.
      destruct x. unfold Mult_compose.
      unfold_ops @Mult_I. now rewrite (fun_fmap_id G).
  Qed.

  (** Composition with g discards the decoration. *)
  Corollary bindt_binddt {A B C} : forall (g : B -> G2 (T C)) (f : W * A -> G1 (T B)),
      fmap G1 (bindt T g) ∘ binddt T f =
        binddt T (G := G1 ∘ G2)
               ((fmap G1 ((fmap G2 (μ T))
                            ∘ δ T G2
                            ∘ fmap T g))
                  ∘ f).
  Proof.
    intros. rewrite (bindt_to_binddt T). rewrite (binddt_binddt T).
    fequal. now rewrite (dtm_kleisli_star6 T).
  Qed.

  (** Composition with g has no substitution. *)
  Corollary fmapdt_binddt {A B C} : forall (g : W * B -> G2 C) (f : W * A -> G1 (T B)),
      fmap G1 (fmapdt T g) ∘ binddt T f =
      binddt T (G := G1 ∘ G2)
             (fmap G1 (δ T G2
                         ∘ fmap T (g ∘ μ (W ×))
                         ∘ σ T
                         ∘ fmap (W ×) (dec T))
             ∘ σ G1
             ∘ cobind (W ×) f).
  Proof.
    intros. rewrite (fmapdt_to_binddt T).
    rewrite (binddt_binddt T). fequal. unfold kcomposedtm.
    change (fmap G2 (η T) ∘ g ∘ μ (prod W)) with
        (fmap G2 (η T) ∘ (g ∘ μ (prod W))).
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on left. reassociate -> near (fmap T (fmap G2 (η T))).
    change (fmap T (fmap G2 (η T (A := ?A)))) with (fmap (T ∘ G2) (η T (A := A))).
    Set Keyed Unification.
    rewrite <- (dist_natural T (G := G2) (η T)).
    reassociate <-. rewrite (fun_fmap_fmap G2).
    rewrite (mon_join_fmap_ret T).
    now rewrite (fun_fmap_id G2).
    Unset Keyed Unification.
  Qed.

  (** Composition with g has no decoration or applicative effect. *)
  Corollary bind_binddt {A B C} : forall (g : B -> T C) (f : W * A -> G1 (T B)),
      fmap G1 (bind T g) ∘ binddt T f =
        binddt T ((fmap G1 (join T))
                    ∘ fmap G1 (fmap T g)
                    ∘ f).
  Proof.
    intros. rewrite (bind_to_binddt T).
    rewrite (binddt_binddt (G2 := fun A => A) T).
    fequal.
    - apply Mult_compose_identity1.
    - Set Keyed Unification.
      rewrite (dtm_kleisli_star6 T).
      unfold_ops @Fmap_I. rewrite (dist_unit T).
      now rewrite (fun_fmap_fmap G1).
      Unset Keyed Unification.
  Qed.

  (** Composition with g has no decoration effect or substitution. *)
  Corollary fmapt_binddt {A B C} : forall (g : B -> G2 C) (f : W * A -> G1 (T B)),
      fmap G1 (traverse T G2 g) ∘ binddt T f =
        binddt T (G := G1 ∘ G2) ((fmap G1 (dist T G2 ∘ fmap T g)) ∘ f).
  Proof.
    intros. rewrite (fmapt_to_binddt T). rewrite (binddt_binddt T).
    fequal.
    Set Keyed Unification.
    rewrite (dtm_kleisli_star6 T).
    rewrite <- (fun_fmap_fmap T).
    reassociate <-. change (fmap T (fmap G2 (?f))) with (fmap (T ∘ G2) f).
    reassociate -> near (fmap (T ∘ G2) (η T)).
    rewrite <- (dist_natural T).
    reassociate <-. rewrite (fun_fmap_fmap G2).
    rewrite (mon_join_fmap_ret T).
    now rewrite (fun_fmap_id G2).
    Unset Keyed Unification.
  Qed.

  (** Composition with g has no substitution or applicative effect. *)
  Corollary fmapd_binddt {A B C} : forall (g : W * B -> C) (f : W * A -> G1 (T B)),
      fmap G1 (fmapd T g) ∘ binddt T f =
        binddt T (fmap G1 (fmap T (g ∘ μ (W ×))
                                ∘ σ T
                                ∘ fmap (W ×) (dec T))
                       ∘ σ G1
                       ∘ cobind (W ×) f).
  Proof.
    intros. rewrite (fmapd_to_binddt T).
    rewrite (binddt_binddt T (G2 := (fun A => A))).
    fequal.
    - apply Mult_compose_identity1.
    - unfold kcomposedtm. unfold_ops @Fmap_I.
      rewrite (dist_unit T). change (?f ∘ id) with f.
      reassociate -> near (μ (W ×)). rewrite <- (fun_fmap_fmap T).
      reassociate <-. rewrite (mon_join_fmap_ret T).
      now change (id ∘ ?f) with f.
  Qed.

  (** Composition with g has no special effects. *)
  Corollary fmap_binddt {A B C} : forall (g : B -> C) (f : W * A -> G1 (T B)),
      fmap G1 (fmap T g) ∘ binddt T f =
        binddt T (fmap (G1 ∘ T) g ∘ f).
  Proof.
    intros. unfold binddt.
    repeat reassociate <-. rewrite (fun_fmap_fmap G1).
    rewrite (natural (ϕ := @join T _)).
    unfold_ops @Fmap_compose.
    rewrite <- (fun_fmap_fmap G1).
    change (fmap G1 (fmap T ?g)) with (fmap (G1 ∘ T) g) at 1.
    reassociate -> near (δ T G1).
    rewrite (dist_natural T).
    unfold_ops @Fmap_compose.
    reassociate <-. reassociate -> near (fmap T f).
    now rewrite (fun_fmap_fmap T).
  Qed.

  (** ** Re-statement of inherited composition properties for [bindd] *)
  (******************************************************************************)
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
  (******************************************************************************)
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
    rewrite Mult_compose_identity1 in e.
    rewrite e.
    now rewrite (binddt_id T).
  Qed.

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
