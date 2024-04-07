From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Kleisli.DecoratedShapelyFunctor.

#[local] Generalizable Variable E T M ϕ A B C G.

Import DecoratedContainerFunctor.Notations.
Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import Subset.Notations.
Import Product.Notations.

About element_of.

(** * <<mapdt>> with constant applicative functors *)
(******************************************************************************)
Section mapdt_constant_applicatives.

  Context
    {E: Type} {T: Type -> Type}
      `{Mapdt_inst: Mapdt E T}
      `{Map_inst: Map T}
      `{! Compat_Map_Mapdt}
      `{! DecoratedTraversableFunctor E T}
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

End mapdt_constant_applicatives.

(** * The <<foldmapd>> operation *)
(******************************************************************************)
Definition foldMapd {T : Type -> Type} `{Mapdt E T}
  `{op : Monoid_op M} `{unit : Monoid_unit M}
  {A : Type} (f : E * A -> M) : T A -> M :=
  mapdt (G := const M) (B := False) f.

Section mapdt_foldMapd.

  Context
    {E: Type} {T: Type -> Type}
      `{Mapdt_inst: Mapdt E T}
      `{Mapd_inst: Mapd E T}
      `{Traverse_inst: Traverse T}
      `{Map_inst: Map T}
      `{! Compat_Map_Mapdt}
      `{! Compat_Mapd_Mapdt}
      `{! Compat_Traverse_Mapdt}
      `{! DecoratedTraversableFunctor E T}.

  (** ** Rewriting to mapdt *)
  (******************************************************************************)
  Lemma foldMapd_to_mapdt1 `{Monoid M} `(f : E * A -> M) :
    foldMapd (T := T) (M := M) (A := A) f =
      mapdt (G := const M) (B := False) f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMapd_to_mapdt2 `{Monoid M} `(f : E * A -> M) : forall (fake : Type),
      foldMapd (T := T) (M := M) (A := A) f =
        mapdt (G := const M) (B := fake) f.
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_constant_applicative1 (B := fake)).
    reflexivity.
  Qed.
  (** *** <<foldMapd>> composition with <<mapd>> and <<map>> *)
  (******************************************************************************)
  Lemma foldMapd_mapd `{Monoid M} {B : Type} :
    forall `(g : E * B -> M) `(f : E * A -> B),
      foldMapd g ∘ mapd f = foldMapd (T := T) (g ∘ cobind f).
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
  Lemma foldMap_to_foldMapd: forall `{Monoid M} `(f : A -> M),
      foldMap (T := T) f = foldMapd (T := T) (f ∘ extract).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_to_mapdt.
    reflexivity.
  Qed.

End mapdt_foldMapd.

(** * The <<ctx_tolist>> operation *)
(******************************************************************************)

#[export] Instance CtxTolist_Mapdt
  `{Mapdt E T}: CtxTolist E T :=
  fun A => foldMapd (ret (T := list)).

Section mapdt_ctx_tolist.

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

  (** ** <<ctx_tolist>> as a special case of <<foldMapd>>/<<mapdt>>*)
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

  (** ** <<ctx_tolist>> is a natural transformation *)
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

    (** ** Composing <<ctx_tolist>> with <<mapd>> *)
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
        ctx_tolist (F := T) ∘ map f =
          foldMapd (ret (T := list) ∘ map (F := (E ×)) f).
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

    (** ** Naturality for <<ctx_tolist>> *)
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
    Corollary foldMapd_through_ctx_tolist `{Monoid M}:
      forall (A : Type) (f : E * A -> M),
        foldMapd f = foldMap (T := list) f ∘ ctx_tolist.
    Proof.
      intros.
      unfold_ops @CtxTolist_Mapdt.
      rewrite foldMap_list_eq.
      rewrite (foldMapd_morphism (M1 := list (E * A)) (M2 := M)).
      fequal. ext a. cbn. rewrite monoid_id_l.
      reflexivity.
    Qed.

    Lemma foldMapd_through_List_foldMap `{Monoid M}:
      forall (A : Type) (f : E * A -> M),
        foldMapd f = foldMap_list f ∘ ctx_tolist.
    Proof.
      intros.
      rewrite foldMapd_through_ctx_tolist.
      rewrite foldMap_list_eq.
      reflexivity.
    Qed.

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

End mapdt_ctx_tolist.

(** * Elements and <<∈d>> *)
(******************************************************************************)

(* TODO generalize this with a Compat class or something *)
#[export] Instance ElementsCtx_CtxTolist `{CtxTolist E T} : ElementsCtx E T :=
  fun A => element_ctx_of ∘ ctx_tolist.

Section mapdt_element_ctx_of.

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

  (** ** Factoring <<ctx_elements_of>> through <<ctx_tolist>>/<<foldMapd>> *)
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

  Lemma ctx_elements_to_foldMapd : forall (A : Type),
      element_ctx_of (F := T) (A := A) = foldMapd (ret (T := subset)).
  Proof.
    intros.
    rewrite ctx_elements_through_foldMapd.
    rewrite (foldMapd_morphism (ϕ := element_of)).
    rewrite element_of_list_hom1.
    reflexivity.
  Qed.

  (** ** Rewriting <<ctx_elements_of>> and <<∈d>> to <<foldMapd>> *)
  (******************************************************************************)
  Lemma ind_to_foldMapd : forall (A : Type) (e : E) (a : A) (t : T A),
      element_ctx_of t (e, a) =
        foldMapd (op := Monoid_op_or)
          (unit := Monoid_unit_false) (eq (e, a)) t.
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

  (** ** Naturality for <<element_ctx_of>> *)
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

  Lemma elements_mapd
    `{Elements T} `{! Compat_Elements_Traverse T} : forall `(f : E * A -> B),
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

  #[export] Instance Natural_Elementd_Mapdt : Natural (@element_ctx_of E T _).
  Proof.
    apply Natural_compose_Natural.
    typeclasses eauto.
    typeclasses eauto.
  Qed.

  (** *** Relating <<element_of>> and <<elementsd>> *)
  (******************************************************************************)
  Lemma element_to_element_ctx_of
    `{Elements T} `{! Compat_Elements_Traverse T}: forall (A : Type),
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

  #[export] Instance Compat_Elements_ElementsCtx_Mapdt
    `{Elements T} `{! Compat_Elements_Traverse T}:
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

End mapdt_element_ctx_of.

(** * Quantification over elements *)
(******************************************************************************)
Section quantification.

  Context
    `{DecoratedTraversableFunctor E T}.

  Definition Forall_ctx `(P : E * A -> Prop) : T A -> Prop :=
    @foldMapd T E _ Prop Monoid_op_and Monoid_unit_true A P.

  Definition Forany_ctx `(P : E * A -> Prop) : T A -> Prop :=
    @foldMapd T E _ Prop Monoid_op_or Monoid_unit_false A P.

  Lemma forall_ctx_iff `(P : E * A -> Prop) (t : T A) :
    Forall_ctx P t <-> forall (e : E) (a : A), (e, a) ∈d t -> P (e, a).
  Proof.
    unfold Forall_ctx.
    rewrite foldMapd_through_ctx_tolist.
    unfold_ops @ElementsCtx_CtxTolist.
    unfold compose at 1 2.
    induction (ctx_tolist t) as [|[e a] rest IHrest].
    - cbv. intuition.
    - rewrite foldMap_list_eq;
        simpl_list;
        rewrite <- foldMap_list_eq.
      rewrite IHrest; clear IHrest.
      unfold_ops @ElementsCtx_env.
      simpl_list.
      setoid_rewrite subset_in_add.
      change ({{(e, a)}} (?e0, ?a0)) with ((e, a) = (e0, a0)).
      setoid_rewrite pair_equal_spec.
      unfold_all_transparent_tcs.
      intuition (subst; auto).
  Qed.

  Lemma forany_ctx_iff `(P : E * A -> Prop) (t : T A) :
    Forany_ctx P t <-> exists (e : E) (a : A), (e, a) ∈d t /\ P (e, a).
  Proof.
    intros.
  Abort.

End quantification.
