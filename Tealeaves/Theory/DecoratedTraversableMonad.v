From Tealeaves Require Export
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Adapters.KleisliToCoalgebraic.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedContainerMonad
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

#[local] Generalizable Variables M U W T G A B C.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.

(** * Theory of DTMs *)
(******************************************************************************)
Section lemmas.

  Context
    `{op : Monoid_op W}
    `{unit : Monoid_unit W}
    `{ret_inst : Return T}
    `{Map_T_inst : Map T}
    `{Mapd_T_inst : Mapd W T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Mapdt_T_inst : Mapdt W T}
    `{Bindd_T_inst : Bindd W T T}
    `{Bindt_T_inst : Bindt T T}
    `{Binddt_T_inst : Binddt W T T}
    `{! Compat_Map_Binddt W T T}
    `{! Compat_Mapd_Binddt W T T}
    `{! Compat_Traverse_Binddt W T T}
    `{! Compat_Bind_Binddt W T T}
    `{! Compat_Mapdt_Binddt W T T}
    `{! Compat_Bindd_Binddt W T T}
    `{! Compat_Bindt_Binddt W T T}
    `{Monad_inst : ! DecoratedTraversableMonad W T}
    `{Map_U_inst : Map U}
    `{Mapd_U_inst : Mapd W U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Mapdt_U_inst : Mapdt W U}
    `{Bindd_U_inst : Bindd W T U}
    `{Bindt_U_inst : Bindt T U}
    `{Binddt_U_inst : Binddt W T U}
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Mapd_Binddt W T U}
    `{! Compat_Traverse_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    `{! Compat_Mapdt_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    `{! Compat_Bindt_Binddt W T U}
    `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  Lemma toBatch6_to_toBatch7 : forall A A' t,
      toBatch6 (A := A) (B := A') t =
        mapsnd_Batch A' (T A') (ret (T := T) (A := A')) (toBatch7 (A := A) (B := A') t).
  Proof.
    intros.
    unfold_ops @ToBatch6_Mapdt.
    unfold_ops @ToBatch7_Binddt.
    rewrite mapdt_to_binddt.
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
      @binddt W T U _ (G ∘ const M)
        (Map_compose G (const M))
        (Pure_compose G (const M))
        (Mult_compose G (const M)) A B f =
        binddt (U := U) (G := const (G M)) (B := B) f.
  Proof.
    intros. fequal.
    - ext X Y h x.
      unfold_ops @Map_compose @Map_const.
      now rewrite (fun_map_id (Functor := app_functor)).
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
      binddt (T := T) (U := U) f =
        binddt (T := T) (U := U) (B := False) f.
    Proof.
      change_right (map (F := const M) (A := U False) (B := U B)
                      (map (F := U) (A := False) (B := B) exfalso)
                      ∘ binddt (T := T) (U := U) (B := False) f).
      rewrite (map_binddt (G1 := const M)).
      reflexivity.
    Qed.

    Lemma binddt_constant_applicative2 (fake1 fake2 : Type)
      `(f : W * A -> const M (T B)) :
      binddt (T := T) (U := U) (B := fake1) f =
        binddt (T := T) (U := U) (B := fake2) f.
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
      binddt (U := U) f = runBatch f ∘ toBatch7.
  Proof.
    intros.
    unfold_ops @ToBatch7_Binddt.
    rewrite (kdtm_morph (Batch (W * A) (T B)) G).
    rewrite (runBatch_batch G). (* TODO get rid of G argument *)
    reflexivity.
  Qed.

  Theorem bindd_through_runBatch :
    forall (A B : Type) (f : W * A -> T B),
      bindd (U := U) f = runBatch (F := fun A => A) f ∘ toBatch7.
  Proof.
    intros.
    rewrite bindd_to_binddt.
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
    rewrite mapdt_to_binddt.
    rewrite (kdtm_binddt0 (G := const M) (A := A) (B := False)).
    reflexivity.
  Qed.

  Theorem foldMapd_binddt `{Applicative G} `{Monoid M} :
    forall `(g : W * B -> M) `(f : W * A -> G (T B)),
      map (foldMapd g) ∘ binddt f =
        foldMapd (fun '(w, a) => map (foldMapd (g ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    rewrite (kdtm_binddt2 (G2 := const M) (G1 := G)). (* TODO args *)
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    rewrite binddt_app_const_r.
    unfold foldMapd.
    (* TODO Make mapdt_to_binddt work immediately here *)
    fequal. ext [w a].
    unfold compose. cbn.
    rewrite mapdt_to_binddt.
    reflexivity.
  Qed.

  Corollary foldMap_binddt `{Applicative G} `{Monoid M} :
    forall `(g : B -> M) `(f : W * A -> G (T B)),
      map (foldMap g) ∘ binddt f =
        foldMapd (fun '(w, a) => map (foldMap g) (f (w, a))).
  Proof.
    intros.
    rewrite foldMap_to_foldMapd.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_binddt.
    fequal; ext [w a].
    rewrite extract_preincr2.
    reflexivity.
  Qed.

  Corollary foldMapd_binddt_I `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd g ∘ binddt (U := U) (G := fun A => A) f =
        foldMapd (T := U) (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
  Proof.
    intros.
    change (foldMapd g) with (map (F := fun A => A) (foldMapd (T := U) g)).
    rewrite (foldMapd_binddt (G := fun A => A)).
    reflexivity.
  Qed.

  Corollary foldMapd_bindd `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd g ∘ bindd f =
        foldMapd (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite foldMapd_binddt_I.
    reflexivity.
  Qed.

  Corollary foldMap_bindd `{Monoid M} : forall `(g : B -> M) `(f : W * A -> T B),
      foldMap g ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap g (f (w, a))).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_binddt_I.
    fequal; ext [w a].
    rewrite extract_preincr2.
    rewrite foldMap_to_foldMapd.
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
        foldMapd (T := U)
          (fun '(w, a) => map (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
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
        foldMapd (T := U) (fun '(w, a) => (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
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
      map tolist ∘ binddt f = foldMapd (T := U) (map tolist ∘ f).
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
    rewrite element_of_to_foldMap.
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
      element_ctx_of ∘ bindd (T := T) (U := U) f =
        bindd (U := ctxset W) (element_ctx_of (F := T) ∘ f) ∘ element_ctx_of (F := U).
  Proof.
    intros.
    rewrite ctx_elements_to_foldMapd.
    rewrite (foldMapd_bindd).
    rewrite ctx_elements_to_foldMapd.
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

  (** ** Respectfulness for <<binddt>> *)
  (******************************************************************************)
  Lemma binddt_respectful_core :
    forall A B (t : U A) G `{Mult G} `{Map G} `{Pure G} (f g : W * A -> G (T B)),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a)) =
        Forall_ctx (fun '(w, a) => f (w, a) = g (w, a)) t.
  Proof.
    intros.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.

  Theorem binddt_respectful :
    forall A B (t : U A) G `{Mult G} `{Map G} `{Pure G} `{! Applicative G}
      (f g : W * A -> G (T B)),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> binddt f t = binddt (U := U) g t.
  Proof.
    introv App_inst.
    intros f g.
    rewrite (binddt_respectful_core A B t G f g).
    unfold Forall_ctx.
    rewrite (foldMapd_through_runBatch2 A B).
    do 2 rewrite binddt_through_runBatch.
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

  Theorem binddt_respectful_pure :
    forall A (t : U A) {G} `{Mult G} `{Map G} `{Pure G} `{! Applicative G}
      (f : W * A -> G (T A)),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = pure (F := G) (ret (T := T) a))
      -> binddt f t = pure t.
  Proof.
    intros.
    rewrite <- (binddt_pure A).
    apply binddt_respectful;
    assumption.
  Qed.

  (** ** Respectfulness for <<bindd>> *)
  (******************************************************************************)
  Lemma bindd_respectful_core :
    forall A B (t : U A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a)) =
        Forall_ctx (fun '(w, a) => f (w, a) = g (w, a)) t.
    intros.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.

  Theorem bindd_respectful :
    forall A B (t : U A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd f t = bindd (U := U) g t.
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

  #[export] Instance: DecoratedContainerRightModule W T U.
  Proof.
    constructor.
    - typeclasses eauto.
    - constructor.
      intros.
      apply ind_bindd_iff_core.
    - intros.
      apply bindd_respectful.
      assumption.
  Qed.

End lemmas.
