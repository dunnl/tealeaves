From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.DecoratedShapelyFunctor.

#[local] Generalizable Variable E T M ϕ A B C G.

Import DecoratedContainerFunctor.Notations.
Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import Subset.Notations.
Import Product.Notations.



(** *** "Full" typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctorFull
  (E : Type) (T : Type -> Type)
  `{Map_inst: Map T}
  `{Mapd_inst: Mapd E T}
  `{Traverse_inst: Traverse T}
  `{Mapdt_inst: Mapdt E T} :=
  { kdtfunf_dtf :> DecoratedTraversableFunctor E T;
    kdtfunf_map_compat :> Compat_Map_Mapdt;
    kdtfunf_mapd_compat :> Compat_Mapd_Mapdt;
    kdtfunf_traverse_compat :> Compat_Traverse_Mapdt;
  }.




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

(** * The <<toctxlist>> operation *)
(******************************************************************************)

#[export] Instance ToCtxlist_Mapdt
  `{Mapdt E T}: ToCtxlist E T :=
  fun A => foldMapd (ret (T := list)).

Section mapdt_toctxlist.

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

  (** ** <<toctxlist>> as a special case of <<foldMapd>>/<<mapdt>>*)
  (******************************************************************************)
  Lemma toctxlist_to_foldMapd : forall (A : Type),
      toctxlist (F := T) = foldMapd (ret (T := list) (A := E * A)).
  Proof.
    reflexivity.
  Qed.

  Corollary toctxlist_to_mapdt1 : forall (A : Type),
      toctxlist = mapdt (G := const (list (E * A))) (B := False) (ret (T := list)).
  Proof.
    reflexivity.
  Qed.

  Corollary toctxlist_to_mapdt2 : forall (A fake : Type),
      toctxlist = mapdt (G := const (list (E * A))) (B := fake) (ret (T := list)).
  Proof.
    intros.
    rewrite toctxlist_to_mapdt1.
    rewrite (mapdt_constant_applicative1 (B := fake)).
    reflexivity.
  Qed.

  (** ** <<toctxlist>> is a natural transformation *)
  (******************************************************************************)
  #[export] Instance Natural_ToCtxlist_Mapdt : Natural (@toctxlist E T _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      (* LHS *)
      change (list ○ prod E) with (env E). (* hidden *)
      rewrite toctxlist_to_foldMapd.
      assert (Monoid_Morphism (list (E * A)) (list (E * B)) (map f)).
      { rewrite env_map_spec.
        apply Monmor_list_map. }
      rewrite (foldMapd_morphism (M1 := list (E * A)) (M2 := list (E * B))).
      rewrite env_map_spec.
      rewrite (natural (ϕ := @ret list _)); unfold_ops @Map_I.
      (* RHS *)
      rewrite toctxlist_to_foldMapd.
      rewrite foldMapd_map.
      reflexivity.
  Qed.

    (** ** Composing <<toctxlist>> with <<mapd>> *)
    (******************************************************************************)
    Lemma toctxlist_mapd : forall `(f : E * A -> B),
        toctxlist (F := T) ∘ mapd f = foldMapd (ret (T := list) ∘ cobind f).
    Proof.
      intros.
      rewrite toctxlist_to_foldMapd.
      rewrite foldMapd_mapd.
      reflexivity.
    Qed.

    Lemma toctxlist_map : forall `(f : A -> B),
        toctxlist (F := T) ∘ map f =
          foldMapd (ret (T := list) ∘ map (F := (E ×)) f).
    Proof.
      intros.
      rewrite toctxlist_to_foldMapd.
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

    (** ** Naturality for <<toctxlist>> *)
    (******************************************************************************)
    Lemma mapd_toctxlist : forall `(f : E * A -> B),
        mapd f ∘ toctxlist (F := T) = toctxlist ∘ mapd f.
    Proof.
      intros.
      rewrite toctxlist_mapd.
      rewrite toctxlist_to_foldMapd.
      assert (Monoid_Morphism (env E A) (env E B) (mapd f)).
      { unfold env. rewrite env_mapd_spec.
        typeclasses eauto. }
      rewrite (foldMapd_morphism).
      fequal. now ext [e a].
      (* TODO ^ generalize this part *)
    Qed.

    Lemma map_toctxlist : forall `(f : A -> B),
        map f ∘ toctxlist (F := T) =
          toctxlist (F := T) ∘ map f.
    Proof.
      intros.
      rewrite toctxlist_to_foldMapd.
      rewrite toctxlist_to_foldMapd.
      rewrite foldMapd_map.
      assert (Monoid_Morphism (env E A) (env E B) (map f)).
      { unfold env at 1 2. rewrite env_map_spec.
        typeclasses eauto. }
      rewrite (foldMapd_morphism).
      fequal.
      rewrite env_map_spec.
      now rewrite (natural (ϕ := @ret list _) (A := E * A) (B := E * B)).
    Qed.

    (** *** Factoring <<foldMapd>> through <<toctxlist>> *)
    (******************************************************************************)
    Corollary foldMapd_through_toctxlist `{Monoid M}:
      forall (A : Type) (f : E * A -> M),
        foldMapd f = foldMap (T := list) f ∘ toctxlist.
    Proof.
      intros.
      unfold_ops @ToCtxlist_Mapdt.
      rewrite foldMap_list_eq.
      rewrite (foldMapd_morphism (M1 := list (E * A)) (M2 := M)).
      fequal. ext a. cbn. rewrite monoid_id_l.
      reflexivity.
    Qed.

    Lemma foldMapd_through_List_foldMap `{Monoid M}:
      forall (A : Type) (f : E * A -> M),
        foldMapd f = foldMap_list f ∘ toctxlist.
    Proof.
      intros.
      rewrite foldMapd_through_toctxlist.
      rewrite foldMap_list_eq.
      reflexivity.
    Qed.

    (** *** Relating <<tolist>> and <<toctxlist>> *)
    (******************************************************************************)
    Lemma tolist_to_toctxlist : forall (A : Type),
        tolist (F := T) (A := A) = map (F := list) extract ∘ toctxlist.
    Proof.
      intros.
      rewrite tolist_to_foldMap.
      rewrite foldMap_to_foldMapd.
      rewrite toctxlist_to_foldMapd.
      rewrite (foldMapd_morphism).
      rewrite (natural (ϕ := @ret list _)).
      reflexivity.
    Qed.

End mapdt_toctxlist.

(** * Elements and <<∈d>> *)
(******************************************************************************)

(* TODO generalize this with a Compat class or something *)
#[export] Instance ToCtxset_ToCtxlist `{ToCtxlist E T} : ToCtxset E T :=
  fun A => toctxset ∘ toctxlist.

Section mapdt_toctxset.

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

  (** ** Factoring <<toctxset_of>> through <<toctxlist>>/<<foldMapd>> *)
  (******************************************************************************)
  Lemma toctxset_through_toctxlist : forall (A : Type),
      toctxset (F := T) (A := A) =
        tosubset (F := list) ∘ toctxlist (F := T).
  Proof.
    reflexivity.
  Qed.

  Lemma toctxset_through_toctxlist2 : forall (A : Type),
      toctxset (F := T) (A := A) =
        toctxset (F := env E) ∘ toctxlist (F := T).
  Proof.
    reflexivity.
  Qed.

  Lemma toctxset_through_foldMapd : forall (A : Type),
      toctxset (F := T) (A := A) =
        tosubset ∘ foldMapd (ret (T := list)).
  Proof.
    reflexivity.
  Qed.

  (** ** Rewriting <<toctxset_of>> and <<∈d>> to <<foldMapd>> *)
  (******************************************************************************)
  Lemma toctxset_to_foldMapd : forall (A : Type),
      toctxset (F := T) (A := A) = foldMapd (ret (T := subset)).
  Proof.
    intros.
    rewrite toctxset_through_foldMapd.
    rewrite (foldMapd_morphism (ϕ := tosubset)).
    rewrite tosubset_list_hom1.
    reflexivity.
  Qed.

  Corollary toctxset_to_mapdt1 : forall (A : Type),
      toctxset (F := T) =
        mapdt (G := const (subset (E * A))) (B := False) (ret (T := subset)).
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    reflexivity.
  Qed.

  Corollary toctxset_to_mapdt2 : forall (A fake : Type),
      toctxset (F := T) =
        mapdt (G := const (subset (E * A))) (B := fake) (ret (T := subset)).
  Proof.
    intros.
    rewrite toctxset_to_mapdt1.
    rewrite (mapdt_constant_applicative1 (B := fake)).
    reflexivity.
  Qed.

  Lemma element_ctx_of_to_foldMapd
    `{ToSubset T} `{! Compat_ToSubset_Traverse T}
    : forall (A : Type) (p: E * A),
      element_ctx_of (T := T) (A := A) p =
        foldMapd (op := Monoid_op_or)
          (unit := Monoid_unit_false) {{p}}.
  Proof.
    intros.
    rewrite element_ctx_of_toctxset.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_morphism.
    now (fequal; ext [e' a']; propext; intuition).
  Qed.

  Lemma element_ctx_of_to_foldMapd2
    `{ToSubset T} `{! Compat_ToSubset_Traverse T}
    : forall (A : Type),
      element_ctx_of (T := T) (A := A) =
        foldMapd (op := Monoid_op_or)
          (unit := Monoid_unit_false) ∘ ret (T := subset).
  Proof.
    intros. ext p.
    apply element_ctx_of_to_foldMapd.
  Qed.

  (** ** Naturality for <<toctxset>> *)
  (******************************************************************************)
  Lemma toctxset_mapd : forall `(f : E * A -> B),
      toctxset (F := T) ∘ mapd f = foldMapd (ret (T := subset) ∘ cobind f).
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_mapd.
    reflexivity.
  Qed.

  Lemma toctxset_map : forall `(f : A -> B),
      toctxset (F := T) ∘ map f = foldMapd (ret (T := subset) ∘ map (F := (E ×)) f).
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_map.
    reflexivity.
  Qed.

  Lemma tosubset_mapd
    `{ToSubset T} `{! Compat_ToSubset_Traverse T} : forall `(f : E * A -> B),
      tosubset ∘ mapd f = foldMapd (ret (T := subset) ∘ f).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_mapd.
    reassociate -> on left.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  #[export] Instance Natural_Elementd_Mapdt : Natural (@toctxset E T _).
  Proof.
    apply Natural_compose_Natural.
    typeclasses eauto.
    typeclasses eauto.
  Qed.

  (** *** Relating <<tosubset>> and <<elementsd>> *)
  (******************************************************************************)
  Lemma tosubset_to_toctxset
    `{ToSubset T} `{! Compat_ToSubset_Traverse T}: forall (A : Type),
      tosubset (F := T) (A := A) = map (F := subset) extract ∘ toctxset.
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_to_foldMapd.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_morphism.
    rewrite (natural (ϕ := @ret subset _)).
    reflexivity.
  Qed.

  #[export] Instance Compat_ToSubset_ToCtxset_Mapdt
    `{ToSubset T} `{! Compat_ToSubset_Traverse T}:
    `{Compat_ToSubset_ToCtxset (E := E) (T := T)}.
  Proof.
    hnf.
    ext A B.
    rewrite tosubset_to_toctxset.
    reflexivity.
  Qed.

  (** ** Characterizing <<∈d>> *)
  (******************************************************************************)
  Lemma ind_iff_in_toctxlist1 : forall (A : Type) (e : E) (a : A) (t : T A),
      (e, a) ∈d t <-> (e, a) ∈ (toctxlist t : list (E * A)).
  Proof.
    reflexivity.
  Qed.

  Lemma ind_iff_in_toctxlist2 : forall (A : Type) (e : E) (a : A) (t : T A),
      (e, a) ∈d t <-> (e, a) ∈d toctxlist t.
  Proof.
    reflexivity.
  Qed.

  (** ** Preordered monoids *)
  (******************************************************************************)
  Lemma foldMapd_mono {M R op unit}
    `{@PreOrderedMonoid M R op unit}:
    forall `(f : E * A -> M) (g : E * A -> M)
      (t: T A),
    (forall e a, (e, a) ∈d t ->
            R (f (e, a)) (g (e, a))) ->
    R (foldMapd f t) (foldMapd g t).
  Proof.
    introv Hin.
    setoid_rewrite ind_iff_in_toctxlist1 in Hin.
    do 2 rewrite foldMapd_through_List_foldMap.
    unfold compose.
    induction (toctxlist t).
    - cbv. reflexivity.
    - rename a into hd.
      rename e into tl.
      destruct hd as [e a].
      setoid_rewrite element_of_list_cons in Hin.
      do 2 rewrite foldMap_list_cons.
      apply pompos_both.
      + auto.
      + apply IHe. intuition.
  Qed.

  Lemma foldMapd_pompos {M R op unit}
      `{@PreOrderedMonoidPos M R op unit}:
    forall `(f : E * A -> M) (t: T A),
    forall e a, (e, a) ∈d t -> R (f (e, a)) (foldMapd f t).
  Proof.
    introv Hin.
    rewrite ind_iff_in_toctxlist1 in Hin.
    rewrite foldMapd_through_List_foldMap.
    unfold compose.
    induction (toctxlist t).
    - inversion Hin.
    - rename a0 into hd.
      rename e0 into tl.
      destruct hd as [e' a'].
      rewrite element_of_list_cons in Hin.
      rewrite foldMap_list_cons.
      destruct Hin as [Hin | Hin].
      + inversion Hin.
        apply pompos_incr_r.
      + transitivity (foldMap_list f tl).
        * auto.
        * apply pompos_incr_l.
  Qed.

End mapdt_toctxset.

(** * Quantification over elements *)
(******************************************************************************)
Section quantification.

  Context
    `{DecoratedTraversableFunctor E T}
      `{Traverse T}
      `{ToSubset T}
      `{! Compat_ToSubset_Traverse T}.

  Definition Forall_ctx `(P : E * A -> Prop) : T A -> Prop :=
    @foldMapd T E _ Prop Monoid_op_and Monoid_unit_true A P.

  Definition Forany_ctx `(P : E * A -> Prop) : T A -> Prop :=
    @foldMapd T E _ Prop Monoid_op_or Monoid_unit_false A P.

  Lemma forall_ctx_iff `(P : E * A -> Prop) (t : T A) :
    Forall_ctx P t <-> forall (e : E) (a : A), (e, a) ∈d t -> P (e, a).
  Proof.
    unfold Forall_ctx.
    rewrite foldMapd_through_toctxlist.
    setoid_rewrite ind_iff_in_toctxlist2.
    unfold compose at 1.
    induction (toctxlist t) as [|[e a] rest IHrest].
    - cbv. intuition.
    - rewrite foldMap_list_eq;
        simpl_list;
        rewrite <- foldMap_list_eq.
      rewrite IHrest; clear IHrest.
      unfold element_ctx_of.
      unfold_ops @ToCtxset_env.
      change (tosubset ?t ?p) with (p ∈ t).
      setoid_rewrite element_of_list_cons.
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
