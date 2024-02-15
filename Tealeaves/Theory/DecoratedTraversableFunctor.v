From Tealeaves Require Export
  Functors.Batch
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.DecoratedShapelyFunctor
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Functors.Environment
  Theory.TraversableFunctor.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variables M E T G A B C ϕ.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.

(** * Theory of decorated traversable functors *)
(******************************************************************************)
Section decorated_traversable_functor_theory.

  Context
    {E: Type} {T: Type -> Type}
      `{Map_inst: Map T}
      `{Mapd_inst: Mapd E T}
      `{Traverse_inst: Traverse T}
      `{Mapdt_inst: Mapdt E T}
      `{! Compat_Map_Mapdt}
      `{! Compat_Mapd_Mapdt}
      `{! Compat_Traverse_Mapdt}
      `{! DecoratedTraversableFunctor E T}.

  (** ** <<mapdt>> with constant applicative functors *)
  (******************************************************************************)
  Section constant_applicatives.

    Context
      `{Monoid M}.

    Lemma mapdt_constant_applicative1 {A B : Type}
      `(f : E * A -> const M B) :
      mapdt (G := const M) (A := A) (B := B) f=
        mapdt (G := const M) (B := False) f.
    Proof.
      change_right
        (map (F := const M) (A := T False) (B := T B)
           (map (F := T) (@exfalso B))
           ∘ (mapdt (G := const M) (B := False) f)).
      rewrite map_mapdt.
      reflexivity.
    Qed.

    Lemma mapdt_constant_applicative2 (B fake1 fake2 : Type)
      `(f : E * A -> const M B) :
      mapdt (G := const M) (B := fake1) f =
        mapdt (G := const M) (B := fake2) f.
    Proof.
      intros.
      rewrite (mapdt_constant_applicative1 (B := fake1)).
      rewrite (mapdt_constant_applicative1 (B := fake2)).
      easy.
    Qed.

  End constant_applicatives.

  (** ** Factoring <<mapdt>> through <<runBatch>> *)
  (******************************************************************************)
  Theorem mapdt_through_runBatch `{Applicative G} `(f : E * A -> G B) :
      mapdt f = runBatch f ∘ toBatch6.
  Proof.
    intros. unfold_ops @ToBatch6_Mapdt.
    rewrite <- kdtfun_morph.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse f = runBatch (f ∘ extract (W := (E ×))) ∘ toBatch6.
  Proof.
    rewrite traverse_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapd_through_runBatch `(f : E * A -> B) :
      mapd f = runBatch (F := fun A => A) f ∘ toBatch6.
  Proof.
    intros.
    rewrite mapd_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
      map f = runBatch (F := fun A => A) (f ∘ extract) ∘ toBatch6.
  Proof.
    intros.
    rewrite map_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  (** ** The <<foldmapd>> operation *)
  (******************************************************************************)
  Definition foldMapd {T : Type -> Type} `{Mapdt E T}
    `{op : Monoid_op M} `{unit : Monoid_unit M}
    {A : Type} (f : E * A -> M) : T A -> M :=
    mapdt (G := const M) (B := False) f.

  (** *** Rewriting the "tag" type parameter *)
  (******************************************************************************)
  Lemma foldMapd_to_mapdt1 `{Monoid M} `(f : E * A -> M) :
      foldMapd (T := T) (M := M) (A := A) f =
        mapdt (G := const M) (B := False) f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_to_mapdt2 `{Monoid M} `(f : E * A -> M) : forall (fake : Type),
      foldMapd (T := T) (M := M) (A := A) f =
        mapdt (G := const M) (B := fake) f.
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_constant_applicative1 (B := fake)).
    reflexivity.
  Qed.

  (** *** <<foldMapd>> a special case of <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMapd_through_runBatch1 {A} `{Monoid M} : forall `(f : E * A -> M),
      foldMapd f = runBatch (F := const M) f (C := T False) ∘ toBatch6 (B := False).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_through_runBatch (G := const M)).
    reflexivity.
  Qed.

  Lemma foldMapd_through_runBatch2 `{Monoid M} : forall (A fake : Type) `(f : E * A -> M),
      foldMapd f = runBatch (F := const M) f (C := T fake) ∘ toBatch6 (B := fake).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_constant_applicative2 False False fake).
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  (** *** <<foldMapd>> composition with <<mapd>> and <<map>> *)
  (******************************************************************************)
  Lemma foldMapd_mapd `{Monoid M} {B : Type} :
    forall `(g : E * B -> M) `(f : E * A -> B),
      foldMapd g ∘ mapd f = foldMapd (g ∘ cobind f).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_mapd g f).
    reflexivity.
  Qed.

  Corollary foldMapd_map `{Monoid M} : forall `(g : E * B -> M) `(f : A -> B),
      foldMapd g ∘ map f = foldMapd (g ∘ map (F := prod E) f).
  Proof.
    intros.
    rewrite map_to_mapdt.
    replace (mapdt (G := fun A => A) (f ∘ extract)) with (mapd (f ∘ extract)).
    - rewrite foldMapd_mapd.
      reflexivity.
    - rewrite mapd_to_mapdt.
      reflexivity.
  Qed.

  (** *** <<foldMapd>> composition with monoid homomorphisms *)
  (******************************************************************************)
  Lemma foldMapd_morphism
    `{morphism : Monoid_Morphism M1 M2 ϕ} : forall `(f : E * A -> M1),
      ϕ ∘ foldMapd f = foldMapd (ϕ ∘ f).
  Proof.
    intros.
    inversion morphism.
    rewrite foldMapd_to_mapdt1.
    change ϕ with (const ϕ (T False)).
    rewrite <- (kdtfun_morph (G1 := const M1) (G2 := const M2)).
    reflexivity.
  Qed.

  (** *** <<foldMapd>> as a generalization of <<foldMap>> *)
  (******************************************************************************)
  Lemma foldMap_to_foldMapd : forall `{Monoid M} `(f : A -> M),
      foldMap (T := T) f = foldMapd (T := T) (f ∘ extract).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_to_mapdt.
    reflexivity.
  Qed.

  (** ** The <<ctx_tolist>> operation *)
  (******************************************************************************)
  Section ctx_tolist.

    #[export] Instance CtxTolist_Mapdt : CtxTolist E T :=
    fun A => foldMapd (ret (T := list)).

    (** *** <<ctx_tolist>> as a special case of <<foldMapd>>/<<mapdt>>*)
    (******************************************************************************)
    Lemma ctx_tolist_to_foldMapd : forall (A : Type),
        ctx_tolist (F := T) = foldMapd (ret (T := list) (A := E * A)).
    Proof.
      reflexivity.
    Qed.

    Corollary ctx_tolist_to_mapdt1 : forall (A : Type),
        ctx_tolist = mapdt (G := const (list (E * A))) (B := False) (ret (T := list)).
    Proof.
      reflexivity.
    Qed.

    Corollary ctx_tolist_to_mapdt2 : forall (A fake : Type),
        ctx_tolist = mapdt (G := const (list (E * A))) (B := fake) (ret (T := list)).
    Proof.
      intros.
      rewrite ctx_tolist_to_mapdt1.
      rewrite (mapdt_constant_applicative1 (B := fake)).
      reflexivity.
    Qed.

    (** *** Factoring through <<runBatch>> *)
    (******************************************************************************)
    Corollary ctx_tolist_to_runBatch6 {A : Type} (tag : Type) :
      ctx_tolist = runBatch (B := tag) (F := const (list (E * A))) (ret (T := list))
                  ∘ toBatch6.
    Proof.
      rewrite (ctx_tolist_to_mapdt2 A tag).
      now rewrite mapdt_to_runBatch.
    Qed.

    (** *** <<ctx_tolist>> is a natural transformation *)
    (******************************************************************************)
    #[export] Instance Natural_CtxTolist_Mapdt : Natural (@ctx_tolist E T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        (* LHS *)
        change (list ○ prod E) with (env E). (* hidden *)
        rewrite ctx_tolist_to_foldMapd.
        assert (Monoid_Morphism (list (E * A)) (list (E * B)) (map f)).
        { rewrite env_map_spec.
          apply Monmor_list_map. }
        rewrite (foldMapd_morphism (M1 := list (E * A)) (M2 := list (E * B))).
        rewrite env_map_spec.
        rewrite (natural (ϕ := @ret list _)); unfold_ops @Map_I.
        (* RHS *)
        rewrite ctx_tolist_to_foldMapd.
        rewrite foldMapd_map.
        reflexivity.
    Qed.

    (** *** Composing <<ctx_tolist>> with <<mapd>> *)
    (******************************************************************************)
    Lemma ctx_tolist_mapd : forall `(f : E * A -> B),
        ctx_tolist (F := T) ∘ mapd f = foldMapd (ret (T := list) ∘ cobind f).
    Proof.
      intros.
      rewrite ctx_tolist_to_foldMapd.
      rewrite foldMapd_mapd.
      reflexivity.
    Qed.

    Lemma ctx_tolist_map : forall `(f : A -> B),
        ctx_tolist (F := T) ∘ map f = foldMapd (ret (T := list) ∘ map (F := (E ×)) f).
    Proof.
      intros.
      rewrite ctx_tolist_to_foldMapd.
      rewrite foldMapd_map.
      reflexivity.
    Qed.

    Lemma tolist_mapd : forall `(f : E * A -> B),
        tolist ∘ mapd f = foldMapd (ret (T := list) ∘ f).
    Proof.
      intros.
      rewrite tolist_to_foldMap.
      rewrite foldMap_to_foldMapd.
      rewrite foldMapd_mapd.
      reassociate -> on left.
      rewrite kcom_cobind0.
      reflexivity.
    Qed.

    (** *** Decorated naturality for <<ctx_tolist>> *)
    (******************************************************************************)
    Lemma mapd_ctx_tolist : forall `(f : E * A -> B),
        mapd f ∘ ctx_tolist (F := T) = ctx_tolist ∘ mapd f.
    Proof.
      intros.
      rewrite ctx_tolist_mapd.
      rewrite ctx_tolist_to_foldMapd.
      assert (Monoid_Morphism (env E A) (env E B) (mapd f)).
      { unfold env. rewrite env_mapd_spec.
        typeclasses eauto. }
      rewrite (foldMapd_morphism).
      fequal. now ext [e a].
      (* TODO ^ generalize this part *)
    Qed.

    Lemma map_ctx_tolist : forall `(f : A -> B),
        map f ∘ ctx_tolist (F := T) =
          ctx_tolist (F := T) ∘ map f.
    Proof.
      intros.
      rewrite ctx_tolist_to_foldMapd.
      rewrite ctx_tolist_to_foldMapd.
      rewrite foldMapd_map.
      assert (Monoid_Morphism (env E A) (env E B) (map f)).
      { unfold env at 1 2. rewrite env_map_spec.
        typeclasses eauto. }
      rewrite (foldMapd_morphism).
      fequal.
      rewrite env_map_spec.
      now rewrite (natural (ϕ := @ret list _) (A := E * A) (B := E * B)).
    Qed.

    (** *** Factoring <<foldMapd>> through <<ctx_tolist>> *)
    (******************************************************************************)
    Section foldMapd_through_ctx_tolist.

      Corollary foldMapd_through_ctx_tolist `{Monoid M} : forall (A : Type) (f : E * A -> M),
          foldMapd f = foldMap (T := list) f ∘ ctx_tolist.
      Proof.
        intros.
        unfold_ops @CtxTolist_Mapdt.
        rewrite foldMap_list_eq.
        rewrite (foldMapd_morphism (M1 := list (E * A)) (M2 := M)).
        fequal. ext a. cbn. rewrite monoid_id_l.
        reflexivity.
      Qed.

      Lemma foldMapd_through_List_foldMap `{Monoid M} : forall (A : Type) (f : E * A -> M),
          foldMapd f = List.foldMap f ∘ ctx_tolist.
      Proof.
        intros.
        rewrite foldMapd_through_ctx_tolist.
        rewrite foldMap_list_eq.
        reflexivity.
      Qed.

    End foldMapd_through_ctx_tolist.

    (** *** Relating <<tolist>> and <<ctx_tolist>> *)
    (******************************************************************************)
    Lemma tolist_to_ctx_tolist : forall (A : Type),
        tolist (F := T) (A := A) = map (F := list) extract ∘ ctx_tolist.
    Proof.
      intros.
      rewrite tolist_to_foldMap.
      rewrite foldMap_to_foldMapd.
      rewrite ctx_tolist_to_foldMapd.
      rewrite (foldMapd_morphism).
      rewrite (natural (ϕ := @ret list _)).
      reflexivity.
    Qed.

  End ctx_tolist.

  (** ** The <<∈d>> operation *)
  (******************************************************************************)
  Section tosetd.

    #[export] Instance ElementsCtx_CtxTolist `{CtxTolist E T} : ElementsCtx E T :=
      fun A => element_ctx_of ∘ ctx_tolist.

    (** *** Factoring through <<ctx_tolist>>/<<foldMapd>> *)
    (******************************************************************************)
    Lemma ctx_elements_through_ctx_tolist : forall (A : Type),
        element_ctx_of (F := T) (A := A) =
          element_of (F := list) ∘ ctx_tolist (F := T).
    Proof.
      reflexivity.
    Qed.

    Lemma ctx_elements_through_ctx_tolist2 : forall (A : Type),
        element_ctx_of (F := T) (A := A) =
          element_ctx_of (F := env E) ∘ ctx_tolist (F := T).
    Proof.
      reflexivity.
    Qed.

    Lemma ctx_elements_through_foldMapd : forall (A : Type),
        element_ctx_of (F := T) (A := A) =
          element_of ∘ foldMapd (ret (T := list)).
    Proof.
      reflexivity.
    Qed.

    (** *** As a special case of <<foldMapd>>/<<mapdt>> *)
    (******************************************************************************)
    Lemma ctx_elements_to_foldMapd : forall (A : Type),
        element_ctx_of (F := T) (A := A) = foldMapd (ret (T := subset)).
    Proof.
      intros.
      rewrite ctx_elements_through_foldMapd.
      rewrite (foldMapd_morphism (ϕ := element_of)).
      rewrite element_of_list_hom1.
      reflexivity.
    Qed.

    Lemma element_to_foldMapd2 : forall (A : Type) (e : E) (a : A) (t : T A),
        element_ctx_of t (e, a) = foldMapd (op := or) (unit := False) (eq (e, a)) t.
    Proof.
      intros.
      rewrite ctx_elements_to_foldMapd.
      change_left ((evalAt (e, a) ∘ foldMapd (ret (T := subset))) t).
      rewrite foldMapd_morphism.
      now (fequal; ext [e' a']; propext; intuition).
    Qed.

    Corollary ctx_elements_to_mapdt1 : forall (A : Type),
        element_ctx_of (F := T) = mapdt (G := const (subset (E * A))) (B := False) (ret (T := subset)).
    Proof.
      intros.
      rewrite ctx_elements_to_foldMapd.
      reflexivity.
    Qed.

    Corollary ctx_elements_to_mapdt2 : forall (A fake : Type),
        element_ctx_of (F := T) =
          mapdt (G := const (subset (E * A))) (B := fake) (ret (T := subset)).
    Proof.
      intros.
      rewrite ctx_elements_to_mapdt1.
      rewrite (mapdt_constant_applicative1 (B := fake)).
      reflexivity.
    Qed.

    (** *** Factoring through <<runBatch>> *)
    (******************************************************************************)
    Corollary ctx_elements_through_runBatch1 {A : Type} :
      element_ctx_of (F := T) = runBatch (B := False) (F := const (subset (E * A)))
                  (ret (T := subset)) ∘ toBatch6.
    Proof.
      rewrite (ctx_elements_to_mapdt1 A).
      now rewrite (mapdt_to_runBatch).
    Qed.

    Corollary ctx_elements_through_runBatch2 {A tag : Type} :
      element_ctx_of (F := T) = runBatch (B := tag) (F := const (subset (E * A)))
                  (ret (T := subset)) ∘ toBatch6.
    Proof.
      rewrite (ctx_elements_to_mapdt2 A tag).
      now rewrite (mapdt_to_runBatch).
    Qed.

    (** *** Composing <<elementsd>> and <<mapd>>/<<map>> *)
    (******************************************************************************)
    Lemma ctx_elements_mapd : forall `(f : E * A -> B),
        element_ctx_of (F := T) ∘ mapd f = foldMapd (ret (T := subset) ∘ cobind f).
    Proof.
      intros.
      rewrite ctx_elements_to_foldMapd.
      rewrite foldMapd_mapd.
      reflexivity.
    Qed.

    Lemma ctx_elements_map : forall `(f : A -> B),
        element_ctx_of (F := T) ∘ map f = foldMapd (ret (T := subset) ∘ map (F := (E ×)) f).
    Proof.
      intros.
      rewrite ctx_elements_to_foldMapd.
      rewrite foldMapd_map.
      reflexivity.
    Qed.

    Lemma elements_mapd : forall `(f : E * A -> B),
        element_of ∘ mapd f = foldMapd (ret (T := subset) ∘ f).
    Proof.
      intros.
      rewrite element_of_to_foldMap.
      rewrite foldMap_to_foldMapd.
      rewrite foldMapd_mapd.
      reassociate -> on left.
      rewrite kcom_cobind0.
      reflexivity.
    Qed.

  (** *** <<elementsd>> is natural *)
  (******************************************************************************)
    #[export] Instance Natural_Elementd_Mapdt : Natural (@element_ctx_of E T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - apply Functor_instance_0.
      - intros.
        (* LHS *)
        rewrite ctx_elements_to_foldMapd.
        assert (Monoid_Morphism (subset (E * A)) (subset (E * B)) (map f)).
        { constructor; try typeclasses eauto.
          admit. admit.
        }
        rewrite (foldMapd_morphism (M1 := subset (E * A)) (M2 := subset (E * B))).
        (*
        rewrite env_map_spec.
        rewrite (natural (ϕ := @ret list _)); unfold_ops @Map_I.
        (* RHS *)
        rewrite ctx_tolist_to_foldMapd.
        rewrite foldMapd_map.
        reflexivity.
         *)
    Admitted.

    (** *** Relating <<element_of>> and <<elementsd>> *)
    (******************************************************************************)
    Lemma element_to_element_ctx_of : forall (A : Type),
        element_of (F := T) (A := A) = map (F := subset) extract ∘ element_ctx_of.
    Proof.
      intros.
      rewrite element_of_to_foldMap.
      rewrite foldMap_to_foldMapd.
      rewrite ctx_elements_to_foldMapd.
      rewrite foldMapd_morphism.
      rewrite (natural (ϕ := @ret subset _)).
      reflexivity.
    Qed.

    #[export] Instance Compat_Elements_ElementsCtx_Mapdt:
      `{Compat_Elements_ElementsCtx (E := E) (T := T)}.
    Proof.
      hnf.
      ext A B.
      rewrite element_to_element_ctx_of.
      reflexivity.
    Qed.

    (** ** Characterizing <<∈d>> *)
    (******************************************************************************)
    Lemma ind_iff_in_ctx_tolist1 : forall (A : Type) (e : E) (a : A) (t : T A),
        (e, a) ∈d t <-> (e, a) ∈ (ctx_tolist t : list (E * A)).
    Proof.
      reflexivity.
    Qed.

    Lemma ind_iff_in_ctx_tolist2 : forall (A : Type) (e : E) (a : A) (t : T A),
        (e, a) ∈d t <-> (e, a) ∈d ctx_tolist t.
    Proof.
      reflexivity.
    Qed.

    (** ** Quantification over elements *)
    (******************************************************************************)
    Definition Forall_ctx `(P : E * A -> Prop) : T A -> Prop :=
      @foldMapd T _ Prop Monoid_op_and Monoid_unit_true A P.

    Definition Forany_ctx `(P : E * A -> Prop) : T A -> Prop :=
      @foldMapd T _ Prop Monoid_op_or Monoid_unit_false A P.

    Lemma forall_ctx_iff `(P : E * A -> Prop) (t : T A) :
      Forall_ctx P t <-> forall (e : E) (a : A), (e, a) ∈d t -> P (e, a).
    Proof.
      unfold Forall_ctx.
      setoid_rewrite element_to_foldMapd2.
      rewrite (foldMapd_through_runBatch1 _).
      assert (lemma : forall (e : E) (a : A),
                 foldMapd (eq (e, a))
                   (op := or) (unit := False) t =
                   (runBatch (B := False)
          (H0 := @Mult_const Prop Monoid_op_or)
          (H1 := @Pure_const Prop Monoid_unit_false)
          (eq (e, a)) ∘ toBatch6) t).
      { intros; now rewrite (foldMapd_through_runBatch1 _). }
      setoid_rewrite lemma.
      unfold compose.
      induction (toBatch6 t).
      - split.
        + intros hyp e a contra.
          inversion contra.
        + intros. exact I.
      - specialize (IHb lemma).
        rewrite runBatch_rw2.
        split.
        + intros [hyp_b hyp_a] e a' hyp.
          rewrite IHb in hyp_b.
          rewrite runBatch_rw2 in hyp.
          inversion hyp; subst; auto.
        + intro hyp.
          cbn. split.
          * rewrite IHb.
            intros e a' hyp2.
            apply hyp. now left.
          * destruct a as [e a'].
            eapply hyp.
            rewrite runBatch_rw2.
            now right.
    Qed.

    Lemma forany_ctx_iff `(P : E * A -> Prop) (t : T A) :
      Forany_ctx P t <-> exists (e : E) (a : A), (e, a) ∈d t /\ P (e, a).
    Proof.
      intros.
    Abort.

    (** ** Characterizing <<∈d>> and <<mapd>> *)
    (******************************************************************************)
    Theorem ind_mapd_iff :
      forall `(f : E * A -> B) (t : T A) (e : E) (b : B),
        (e, b) ∈d mapd f t <-> exists (a : A), (e, a) ∈d t /\ f (e, a) = b.
    Proof.
      intros.
      unfold_ops @ElementsCtx_CtxTolist.
      change_left ((evalAt (e, b) ∘ element_of (F := list) ∘ ctx_tolist ∘ mapd (T := T) f) t).
      change_right ((evalAt (e, b) ∘ mapd (T := ctxset E) f ∘ element_of (F := list) ∘ ctx_tolist) t).
      enough (lemma : element_of (F := list) ∘ ctx_tolist ∘ mapd f =
                        mapd (T := ctxset E) f ∘ element_of (F := list) ∘ ctx_tolist).
      change_left ((evalAt (e, b) ∘ (element_of (F := list) ∘ ctx_tolist ∘ mapd f)) t).
      rewrite lemma. reflexivity.
      { reassociate -> on left.
        change (list (prod ?E ?X)) with (env E X). (* hidden *)
        rewrite <- (mapd_ctx_tolist f).
        reassociate <- on left.
        fequal.
        rewrite (env_mapd_spec).
        rewrite (ctxset_mapd_spec).
        change (env ?E ?X) with (list (prod E X)). (* hidden *)
        rewrite <- (natural (ϕ := @element_of list _)).
        reflexivity.
      }
    Qed.

    Lemma mapd_respectful :
      forall A B (t : T A) (f g : E * A -> B),
        (forall (e : E) (a : A), (e, a) ∈d t -> f (e, a) = g (e, a))
        -> mapd f t = mapd g t.
    Proof.
      introv hyp.
      do 2 rewrite mapd_through_runBatch.
      rewrite (ctx_elements_through_runBatch2 (tag := B)) in hyp.
      unfold compose in *.
      induction (toBatch6 (B := B) t).
      - reflexivity.
      - destruct a as [e a]. cbn.
        rewrite IHb.
        rewrite hyp.
        reflexivity.
        + cbn. now right.
        + introv hyp2.
          apply hyp.
          now left.
    Qed.

  End tosetd.

End decorated_traversable_functor_theory.
