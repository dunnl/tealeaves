From Tealeaves Require Export
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Adapters.KleisliToCoalgebraic.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedContainerFunctor
  Theory.DecoratedTraversableFunctor
  Theory.TraversableMonad.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.
Import DecoratedTraversableMonad.Notations.

#[local] Generalizable Variables M W T G A B C.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.

(** * Theory of DTMs *)
(******************************************************************************)
Section lemmas.

  Context
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}.

  Lemma toBatch6_to_toBatch7 : forall A A' t,
      toBatch6 (A := A) (B := A') t =
        mapsnd_Batch A' (T A') (ret (T := T) (A := A')) (toBatch7 (A := A) (B := A') t).
  Proof.
    intros.
    unfold_ops @ToBatch6_Mapdt.
    unfold_ops @ToBatch7_Binddt.
    rewrite kdtmf_mapdt_compat.
    compose near t on right.
    rewrite (kdtm_morph (A := A) (T := T)
               (Batch _ (T A'))
               (Batch _ A')
               (ϕ := fun C => mapsnd_Batch A' (T A') ret)
               (batch (W * A) (T A'))).
    reflexivity.
  Qed.

  (** ** Composition in the applicative functor *)
  (******************************************************************************)
  Lemma binddt_app_const_r :
    forall {G : Type -> Type} `{Monoid M} {A B : Type} `{Applicative G} (f : W * A -> G M),
      @binddt W T T _ (G ∘ const M)
        (Map_compose G (const M))
        (Pure_compose G (const M))
        (Mult_compose G (const M)) A B f =
        binddt (T := T) (G := const (G M)) (B := B) f.
  Proof.
    intros. fequal.
    - ext X Y h x.
      unfold_ops @Map_compose @Map_const.
      now rewrite fun_map_id.
    - ext X Y [x y].
      unfold_ops @Mult_compose @Mult_const.
      unfold_ops @Monoid_op_applicative.
      reflexivity.
  Qed.

  (** ** Lemmas for particular applicative functors *)
  (******************************************************************************)

  (** *** <<binddt>> with constant applicative functors *)
  (******************************************************************************)
  Section constant_applicative.

    Context `{Monoid M}.

    Lemma binddt_constant_applicative1 {A B : Type}
      `(f : W * A -> const M (T B)) :
      binddt (U := T) f = binddt (U := T) (B := False) f.
    Proof.
      change_right (map (F := const M) (A := T False) (B := T B)
                      (map (F := T) (A := False) (B := B) exfalso)
                      ∘ binddt (U := T) (B := False) f).
      rewrite (map_binddt (G1 := const M)).
      reflexivity.
    Qed.

    Lemma binddt_constant_applicative2 (fake1 fake2 : Type)
      `(f : W * A -> const M (T B)) :
      binddt (U := T) (B := fake1) f = binddt (U := T) (B := fake2) f.
    Proof.
      intros.
      rewrite (binddt_constant_applicative1 (B := fake1)).
      rewrite (binddt_constant_applicative1 (B := fake2)).
      reflexivity.
    Qed.

  End constant_applicative.

  (** ** Expressing <<binddt>> with <<runBatch>> *)
  (******************************************************************************)
  Theorem binddt_through_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G (T B)),
      binddt f = runBatch f ∘ toBatch7.
  Proof.
    intros.
    unfold_ops @ToBatch7_Binddt.
    rewrite (kdtm_morph (Batch (W * A) (T B)) G).
    rewrite (runBatch_batch G). (* TODO get rid of G argument *)
    reflexivity.
  Qed.

  Theorem bindd_through_runBatch :
    forall (A B : Type) (f : W * A -> T B),
      bindd f = runBatch (F := fun A => A) f ∘ toBatch7.
  Proof.
    intros.
    rewrite kdtmf_bindd_compat.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  (** ** Properties of <<foldMapd>> *)
  (******************************************************************************)

  (** *** Composition with monad operattions *)
  (******************************************************************************)
  Theorem foldMapd_ret `{Monoid M} : forall `(f : W * A -> M),
      foldMapd (T := T) f ∘ ret = f ∘ ret.
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1. (* todo get rid of this arg *)
    rewrite kdtmf_mapdt_compat.
    rewrite (kdtm_binddt0 (G := const M) A False).
    reflexivity.
  Qed.

  Theorem foldMapd_binddt `{Applicative G} `{Monoid M} :
    forall `(g : W * B -> M) `(f : W * A -> G (T B)),
      map (foldMapd g) ∘ binddt f =
        foldMapd (fun '(w, a) => map (foldMapd (g ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite kdtmf_mapdt_compat.
    rewrite (kdtm_binddt2 (G2 := const M) (G1 := G) A B False). (* TODO args *)
    rewrite foldMapd_to_mapdt1.
    rewrite kdtmf_mapdt_compat.
    rewrite binddt_app_const_r.
    unfold foldMapd.
    rewrite kdtmf_mapdt_compat'.
    reflexivity.
  Qed.

  Corollary foldMap_binddt `{Applicative G} `{Monoid M} :
    forall `(g : B -> M) `(f : W * A -> G (T B)),
      map (foldMap g) ∘ binddt f =
        foldMapd (fun '(w, a) => map (foldMap g) (f (w, a))).
  Proof.
    intros.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_binddt.
    fequal; ext [w a].
    rewrite extract_preincr2.
    reflexivity.
  Qed.

  Corollary foldMapd_binddt_I `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd g ∘ binddt (T := T) (G := fun A => A) f =
        foldMapd (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
  Proof.
    intros.
    change (foldMapd g) with (map (F := fun A => A) (foldMapd (T := T) g)).
    rewrite (foldMapd_binddt (G := fun A => A)).
    reflexivity.
  Qed.

  Corollary foldMapd_bindd `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd g ∘ bindd f =
        foldMapd (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
  Proof.
    intros.
    rewrite kdtmf_bindd_compat.
    rewrite foldMapd_binddt_I.
    reflexivity.
  Qed.

  Corollary foldMap_bindd `{Monoid M} : forall `(g : B -> M) `(f : W * A -> T B),
      foldMap g ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap g (f (w, a))).
  Proof.
    intros.
    rewrite kdtmf_bindd_compat.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_binddt_I.
    fequal; ext [w a].
    rewrite extract_preincr2.
    reflexivity.
  Qed.

  (** ** <<tolistd>> *)
  (******************************************************************************)

  (** *** Relating <<tolistd>> and <<binddt>> / <<ret>> *)
  (******************************************************************************)
  Lemma ctx_tolist_ret : forall (A : Type) (a : A),
      ctx_tolist (ret (T := T) a) = [ (Ƶ, a) ].
  Proof.
    intros.
    rewrite ctx_tolist_to_foldMapd.
    compose near a on left.
    rewrite foldMapd_ret.
    reflexivity.
  Qed.

  Lemma ctx_tolist_binddt : forall `{Applicative G} `(f : W * A -> G (T B)),
      map (F := G) ctx_tolist ∘ binddt (G := G) f =
        foldMapd (T := T) (fun '(w, a) => map (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite ctx_tolist_to_foldMapd.
    rewrite foldMapd_binddt.
    reflexivity.
  Qed.

  (** *** Relating <<ctx_tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma ctx_tolist_bindd : forall `(f : W * A -> T B),
      ctx_tolist ∘ bindd f =
        foldMapd (T := T) (fun '(w, a) => (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite ctx_tolist_to_foldMapd.
    rewrite foldMapd_bindd.
    reflexivity.
  Qed.

  (** *** Corollaries for the rest *)
  (******************************************************************************)
  Corollary ctx_element_ret : forall (A : Type) (a : A),
      element_ctx_of (ret (T := T) a) = {{ (Ƶ, a) }}.
  Proof.
    intros.
    rewrite ctx_elements_to_foldMapd.
    compose near a on left.
    rewrite foldMapd_ret.
    reflexivity.
  Qed.

  Corollary tolist_binddt : forall `{Applicative G} `(f : W * A -> G (T B)),
      map tolist ∘ binddt f = foldMapd (T := T) (map tolist ∘ f).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_binddt.
    (* todo why isn't reflexivity enough... b.c. destructing the pair? *)
    fequal. ext [w a].
    reflexivity.
  Qed.

  (** *** Relating <<tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma tolist_bindd : forall `(f : W * A -> T B),
      tolist ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap (ret (T := list)) (f (w, a))).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_bindd.
    reflexivity.
  Qed.

  Lemma element_bindd : forall `(f : W * A -> T B),
      element_of ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap (ret (T := subset)) (f (w, a))).
  Proof.
    intros.
    rewrite element_to_foldMap1.
    rewrite foldMap_bindd.
    reflexivity.
  Qed.

  (** ** Characterizing <<∈d>> *)
  (******************************************************************************)
  Lemma ind_ret_iff : forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret (T := T) a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros.
    rewrite ctx_element_ret.
    unfold subset_one.
    split.
    - now inversion 1.
    - intros [x y]. now subst.
  Qed.

  Lemma ind_bindd_iff_core :
    forall `(f : W * A -> T B),
      element_ctx_of (F := T) ∘ bindd (T := T) f =
        bindd (T := ctxset W) (element_ctx_of (F := T) ∘ f) ∘ element_ctx_of (F := T).
  Proof.
    intros.
    rewrite ctx_elements_to_foldMapd.
    rewrite (foldMapd_bindd).
    rewrite ctx_elements_to_foldMapd.
    rewrite foldMapd_morphism.
    fequal.
    ext [w a].
    change_right (bindd (T := ctxset W) (foldMapd (ret (T := subset)) ∘ f) {{(w, a)}}).
    rewrite bindd_ctxset_one.
    unfold compose.
    rewrite (DecoratedFunctor.shift_spec subset (W := W) (op := op) (A := B)).
    compose near (f (w, a)) on right.
    rewrite foldMapd_morphism.
    rewrite (natural (ϕ := @ret subset _)).
    reflexivity.
  Qed.

  Theorem ind_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd f t <->
        exists (w1 w2 : W) (a : A),
          (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
          /\ wtotal = w1 ● w2.
  Proof.
    intros.
    change_left ((evalAt (wtotal, b) ∘ (element_ctx_of (F := T) ∘ bindd (T := T) f)) t).
    rewrite ind_bindd_iff_core.
    unfold evalAt, compose.
    unfold_ops @Bindd_ctxset.
    split.
    - intros [w1 [a [Ht [w2 [Hf Heq]]]]].
      exists w1 w2 a. eauto.
    - intros [w1 [w2 [a [Ht [Hf Heq]]]]].
      exists w1 a. eauto.
  Qed.

  Corollary in_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (b : B),
      b ∈ bindd f t <->
        exists (w1 : W) (a : A),
          (w1, a) ∈d t /\ b ∈ f (w1, a).
  Proof.
    intros.
    rewrite ind_iff_in.
    setoid_rewrite ind_bindd_iff.
    setoid_rewrite ind_iff_in.
    split; intros; preprocess; repeat eexists; eauto.
  Qed.

  (** ** Respectfulness for <<bindd>> *)
  (******************************************************************************)
  Lemma bindd_respectful_core :
    forall A B (t : T A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a)) =
        Forall_ctx (fun '(w, a) => f (w, a) = g (w, a)) t.
    intros.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.

  Theorem bindd_respectful :
    forall A B (t : T A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd f t = bindd g t.
  Proof.
    introv.
    rewrite (bindd_respectful_core A B t f g).
    unfold Forall_ctx.
    rewrite (foldMapd_through_runBatch2 A B).
    do 2 rewrite bindd_through_runBatch.
    unfold compose.
    rewrite toBatch6_to_toBatch7.
    rewrite <- runBatch_mapsnd.
    induction (toBatch7 t).
    - cbn. reflexivity.
    - destruct a as [w a].
      cbn.
      intros [hyp1 hyp2].
      rewrite hyp2.
      rewrite IHb; auto.
  Qed.

  (** *** For equalities with special cases *)
  (** Corollaries with conclusions of the form <<bindd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary bindd_respectful_bind :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> bindd f t = bind g t.
  Proof.
    introv hyp.
    rewrite kmondf_bind_compat.
    apply bindd_respectful.
    introv Hin.
    eauto.
  Qed.

  Corollary bindd_respectful_mapd :
    forall A B (t : T A) (f : W * A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret (g (w, a)))
      -> bindd f t = mapd g t.
  Proof.
    introv hyp.
    rewrite kmondf_mapd_compat.
    apply bindd_respectful.
    introv Hin.
    eauto.
  Qed.

  Corollary bindd_respectful_map :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret (g a))
      -> bindd f t = map g t.
  Proof.
    introv hyp.
    rewrite kmondf_map_compat.
    apply bindd_respectful.
    introv Hin.
    eauto.
  Qed.

  Corollary bindd_respectful_id :
    forall A (t : T A) (f : W * A -> T A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret a)
      -> bindd f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- kmond_bindd1.
    eapply bindd_respectful.
    eauto.
  Qed.

End lemmas.
