From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.DecoratedShapelyFunctor
  Classes.Kleisli.Theory.DecoratedContainerFunctor
  Functors.Early.Environment.

From Coq.Logic Require Import Decidable.

#[local] Generalizable Variable E T M ϕ A B C G.

Import DecoratedContainerFunctor.Notations.
Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import Subset.Notations.
Import Product.Notations.

Import Kleisli.DecoratedTraversableFunctor.DerivedInstances.

(** * Theory of Decorated Traversable Functors *)
(**********************************************************************)

(** ** <<mapdt>> with constant applicative functors *)
(**********************************************************************)
Section mapdt_constant_applicatives.

  Context
    {E: Type}
    {T: Type -> Type}
    `{Mapdt_inst: Mapdt E T}
    `{Map_inst: Map T}
    `{! Compat_Map_Mapdt E T}
    `{! DecoratedTraversableFunctor E T}
    `{Monoid M}.

  Lemma mapdt_constant_applicative1 {A B: Type}
    `(f: E * A -> const M B):
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

  Lemma mapdt_constant_applicative2 (B fake1 fake2: Type)
    `(f: E * A -> const M B):
    mapdt (G := const M) (B := fake1) f =
      mapdt (G := const M) (B := fake2) f.
  Proof.
    intros.
    rewrite (mapdt_constant_applicative1 (B := fake1)).
    rewrite (mapdt_constant_applicative1 (B := fake2)).
    easy.
  Qed.

End mapdt_constant_applicatives.

(** * Derived Operation <<mapdReduce>> *)
(**********************************************************************)
Definition mapdReduce {T: Type -> Type} `{Mapdt E T}
  `{op: Monoid_op M} `{unit: Monoid_unit M}
  {A: Type} (f: E * A -> M): T A -> M :=
  mapdt (G := const M) (B := False) f.

Section mapdt_mapdReduce.

  Context
    {E: Type}
    {T: Type -> Type}
    `{Mapdt_inst: Mapdt E T}
    `{Mapd_inst: Mapd E T}
    `{Traverse_inst: Traverse T}
    `{Map_inst: Map T}
    `{! Compat_Map_Mapdt E T}
    `{! Compat_Mapd_Mapdt E T}
    `{! Compat_Traverse_Mapdt E T}
    `{! DecoratedTraversableFunctor E T}.

  (** ** Rewriting Laws *)
  (********************************************************************)
  Lemma mapdReduce_to_mapdt1 `{Monoid M} `(f: E * A -> M):
    mapdReduce (T := T) (M := M) (A := A) f =
      mapdt (G := const M) (B := False) f.
  Proof.
    reflexivity.
  Qed.

  Lemma mapdReduce_to_mapdt2 `{Monoid M} `(f: E * A -> M):
    forall (fake: Type),
      mapdReduce (T := T) (M := M) (A := A) f =
        mapdt (G := const M) (B := fake) f.
  Proof.
    intros.
    rewrite mapdReduce_to_mapdt1.
    rewrite (mapdt_constant_applicative1 (B := fake)).
    reflexivity.
  Qed.

  (** ** Composition Laws with <<mapd>> and <<map>> *)
  (********************************************************************)
  Lemma mapdReduce_mapd `{Monoid M} {B: Type}:
    forall `(g: E * B -> M) `(f: E * A -> B),
      mapdReduce g ∘ mapd f = mapdReduce (T := T) (g ∘ cobind f).
  Proof.
    intros.
    rewrite mapdReduce_to_mapdt1.
    rewrite (mapdt_mapd g f).
    reflexivity.
  Qed.

  Corollary mapdReduce_map `{Monoid M}:
    forall `(g: E * B -> M) `(f: A -> B),
      mapdReduce g ∘ map f = mapdReduce (g ∘ map (F := prod E) f).
  Proof.
    intros.
    rewrite map_to_mapdt.
    replace (mapdt (G := fun A => A) (f ∘ extract))
      with (mapd (f ∘ extract)).
    - rewrite mapdReduce_mapd.
      reflexivity.
    - rewrite mapd_to_mapdt.
      reflexivity.
  Qed.

  (** ** Composition with Monoid Homomorphisms *)
  (********************************************************************)
  Lemma mapdReduce_morphism
    `{morphism: Monoid_Morphism M1 M2 ϕ}: forall `(f: E * A -> M1),
      ϕ ∘ mapdReduce f = mapdReduce (ϕ ∘ f).
  Proof.
    intros.
    inversion morphism.
    rewrite mapdReduce_to_mapdt1.
    change ϕ with (const ϕ (T False)).
    rewrite (kdtf_morph (G1 := const M1) (G2 := const M2)).
    reflexivity.
  Qed.

  (** *** <<mapdReduce>> as a generalization of <<mapReduce>> *)
  (********************************************************************)
  Lemma mapReduce_to_mapdReduce: forall `{Monoid M} `(f: A -> M),
      mapReduce (T := T) f = mapdReduce (T := T) (f ∘ extract).
  Proof.
    intros.
    rewrite mapReduce_to_traverse1.
    rewrite traverse_to_mapdt.
    reflexivity.
  Qed.

End mapdt_mapdReduce.

(** * The <<toctxlist>> operation *)
(**********************************************************************)
#[local] Instance ToCtxlist_Mapdt
  `{Mapdt E T}: ToCtxlist E T :=
  fun A => mapdReduce (ret (T := list)).

Class Compat_ToCtxlist_Mapdt
  (E: Type)
  (T: Type -> Type)
  `{ToCtxlist_inst: ToCtxlist E T}
  `{Mapdt_inst: Mapdt E T}: Prop :=
  compat_toctxlist_mapdt:
    ToCtxlist_inst = @ToCtxlist_Mapdt E T Mapdt_inst.

#[export] Instance Compat_ToCtxlist_Mapdt_Self
  `{Mapdt_ET: Mapdt E T}:
  @Compat_ToCtxlist_Mapdt E T ToCtxlist_Mapdt Mapdt_ET
  := ltac:(reflexivity).

Lemma toctxlist_to_mapdt
  `{ToCtxlist_inst: ToCtxlist E T}
  `{Mapdt_ET: Mapdt E T}
  `{! Compat_ToCtxlist_Mapdt E T}:
  forall (A: Type),
    toctxlist = mapdReduce (ret (T := list) (A := E * A)).
Proof.
  intros.
  rewrite compat_toctxlist_mapdt.
  reflexivity.
Qed.

Section mapdt_toctxlist.

  Context
    {E: Type}
    {T: Type -> Type}
    `{Mapdt_inst: Mapdt E T}
    `{Mapd_inst: Mapd E T}
    `{Traverse_inst: Traverse T}
    `{Map_inst: Map T}
    `{Toctxlist_inst: ToCtxlist E T}
    `{! Compat_Map_Mapdt E T}
    `{! Compat_Mapd_Mapdt E T}
    `{! Compat_Traverse_Mapdt E T}
    `{! Compat_ToCtxlist_Mapdt E T}
    `{! DecoratedTraversableFunctor E T}.

  (** ** Rewriting to <<mapdReduce>>/<<mapdt>>*)
  (********************************************************************)
  Lemma toctxlist_to_mapdReduce: forall (A: Type),
      toctxlist (F := T) = mapdReduce (ret (T := list) (A := E * A)).
  Proof.
    intros.
    rewrite toctxlist_to_mapdt.
    reflexivity.
  Qed.

  Corollary toctxlist_to_mapdt1: forall (A: Type),
      toctxlist =
        mapdt (G := const (list (E * A))) (B := False) (ret (T := list)).
  Proof.
    intros.
    rewrite toctxlist_to_mapdt.
    reflexivity.
  Qed.

  Corollary toctxlist_to_mapdt2: forall (A fake: Type),
      toctxlist =
        mapdt (G := const (list (E * A))) (B := fake) (ret (T := list)).
  Proof.
    intros.
    rewrite toctxlist_to_mapdt1.
    rewrite (mapdt_constant_applicative1 (B := fake)).
    reflexivity.
  Qed.

  (** ** Naturality *)
  (********************************************************************)
  #[export] Instance Natural_ToCtxlist_Mapdt: Natural (@toctxlist E T _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros.
      (* LHS *)
      change (list ○ prod E) with (env E). (* hidden *)
      rewrite toctxlist_to_mapdReduce.
      assert (Monoid_Morphism (list (E * A)) (list (E * B)) (map f)).
      { rewrite env_map_spec.
        apply Monmor_list_map. }
      rewrite (mapdReduce_morphism
                 (M1 := list (E * A)) (M2 := list (E * B))).
      rewrite env_map_spec.
      rewrite (natural (ϕ := @ret list _)); unfold_ops @Map_I.
      (* RHS *)
      rewrite toctxlist_to_mapdReduce.
      rewrite mapdReduce_map.
      reflexivity.
  Qed.

  (** ** Composing <<toctxlist>> with <<mapd>> *)
  (********************************************************************)
  Lemma toctxlist_mapd: forall `(f: E * A -> B),
      toctxlist (F := T) ∘ mapd f =
        mapdReduce (ret (T := list) ∘ cobind f).
  Proof.
    intros.
    rewrite toctxlist_to_mapdReduce.
    rewrite mapdReduce_mapd.
    reflexivity.
  Qed.

  Lemma toctxlist_map: forall `(f: A -> B),
      toctxlist (F := T) ∘ map f =
        mapdReduce (ret (T := list) ∘ map (F := (E ×)) f).
  Proof.
    intros.
    rewrite toctxlist_to_mapdReduce.
    rewrite mapdReduce_map.
    reflexivity.
  Qed.

  Lemma tolist_mapd: forall `(f: E * A -> B),
      tolist ∘ mapd f = mapdReduce (ret (T := list) ∘ f).
  Proof.
    intros.
    rewrite tolist_to_mapReduce.
    rewrite mapReduce_to_mapdReduce.
    rewrite mapdReduce_mapd.
    reassociate -> on left.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  (** ** Naturality for <<toctxlist>> *)
  (********************************************************************)
  Lemma mapd_toctxlist: forall `(f: E * A -> B),
      mapd f ∘ toctxlist (F := T) = toctxlist ∘ mapd f.
  Proof.
    intros.
    rewrite toctxlist_mapd.
    rewrite toctxlist_to_mapdReduce.
    assert (Monoid_Morphism (env E A) (env E B) (mapd f)).
    { unfold env. rewrite env_mapd_spec.
      typeclasses eauto. }
    rewrite (mapdReduce_morphism).
    fequal. now ext [e a].
    (* TODO ^ generalize this part *)
  Qed.

  Lemma map_toctxlist: forall `(f: A -> B),
      map f ∘ toctxlist (F := T) =
        toctxlist (F := T) ∘ map f.
  Proof.
    intros.
    rewrite toctxlist_to_mapdReduce.
    rewrite toctxlist_to_mapdReduce.
    rewrite mapdReduce_map.
    assert (Monoid_Morphism (env E A) (env E B) (map f)).
    { unfold env at 1 2. rewrite env_map_spec.
      typeclasses eauto. }
    rewrite (mapdReduce_morphism).
    fequal.
    rewrite env_map_spec.
    now rewrite (natural (ϕ := @ret list _) (A := E * A) (B := E * B)).
  Qed.

  (** ** Factoring <<mapdReduce>> through <<toctxlist>> *)
  (********************************************************************)
  Corollary mapdReduce_through_toctxlist `{Monoid M}:
    forall (A: Type) (f: E * A -> M),
      mapdReduce f = mapReduce (T := list) f ∘ toctxlist.
  Proof.
    intros.
    rewrite toctxlist_to_mapdReduce.
    rewrite mapReduce_eq_mapReduce_list.
    rewrite (mapdReduce_morphism (M1 := list (E * A)) (M2 := M)).
    rewrite mapReduce_list_ret.
    reflexivity.
  Qed.

  (** ** Relating <<tolist>> and <<toctxlist>> *)
  (********************************************************************)
  Lemma tolist_to_toctxlist: forall (A: Type),
      tolist (F := T) (Tolist := Tolist_Traverse) (A := A) =
        map (F := list) extract ∘ toctxlist.
  Proof.
    intros.
    rewrite tolist_to_mapReduce.
    rewrite mapReduce_to_mapdReduce.
    rewrite toctxlist_to_mapdReduce.
    rewrite (mapdReduce_morphism).
    rewrite (natural (ϕ := @ret list _)).
    reflexivity.
  Qed.

End mapdt_toctxlist.

(** * <<toctxset>> and <<∈d>> *)
(**********************************************************************)
#[local] Instance ToCtxset_Mapdt
  `{Mapdt E T}: ToCtxset E T :=
  fun A => mapdReduce (ret (T := subset) (A := E * A)).

Class Compat_ToCtxset_Mapdt
  (E: Type)
  (T: Type -> Type)
  `{ToCtxset_inst: ToCtxset E T}
  `{Mapdt_inst: Mapdt E T}: Prop :=
  compat_toctxset_mapdt:
    ToCtxset_inst = @ToCtxset_Mapdt E T Mapdt_inst.

#[export] Instance Compat_ToCtxset_Mapdt_Self
  `{Mapdt_ET: Mapdt E T}:
  @Compat_ToCtxset_Mapdt E T ToCtxset_Mapdt Mapdt_ET
  := ltac:(reflexivity).

Lemma toctxset_to_mapdt
  `{ToCtxset_inst: ToCtxset E T}
  `{Mapdt_ET: Mapdt E T}
  `{! Compat_ToCtxset_Mapdt E T}:
  forall (A: Type),
    toctxset = mapdReduce (ret (T := subset) (A := E * A)).
Proof.
  intros.
  rewrite compat_toctxset_mapdt.
  reflexivity.
Qed.

(** A <<tosubset>> that is compatible with <<traverse>>
    is compatible with the <<toctxset>> that is compatible with <<mapdt>>,
    if <<traverse>> is compatible with <<mapdt>> *)
#[export] Instance Compat_ToSubset_ToCtxset_Traverse
  `{Mapdt E T}
  `{Traverse T}
  `{ToSubset_T: ToSubset T}
  `{! Compat_Traverse_Mapdt E T}
  `{! Compat_ToSubset_Traverse T}
  `{! DecoratedTraversableFunctor E T}:
  Compat_ToSubset_ToCtxset E T (ToSubset_T := ToSubset_T).
Proof.
  hnf.
  rewrite compat_tosubset_traverse.
  unfold_ops @ToSubset_Traverse.
  unfold ToSubset_ToCtxset.
  unfold_ops @ToCtxset_Mapdt.
  ext A.
  rewrite mapReduce_to_mapdReduce.
  rewrite mapdReduce_morphism.
  rewrite (natural (ϕ := @ret subset _)).
  reflexivity.
Qed.

Section mapdt_toctxset.

  Context
    {E: Type}
    {T: Type -> Type}
    `{Mapdt_inst: Mapdt E T}
    `{Mapd_inst: Mapd E T}
    `{Traverse_inst: Traverse T}
    `{Map_inst: Map T}
    `{ToCtxset_inst: ToCtxset E T}
    `{! Compat_Map_Mapdt E T}
    `{! Compat_Mapd_Mapdt E T}
    `{! Compat_Traverse_Mapdt E T}
    `{! Compat_ToCtxset_Mapdt E T}
    `{! DecoratedTraversableFunctor E T}.

  (** ** Rewriting <<toctxset_of>> and <<∈d>> to <<mapdReduce>> *)
  (********************************************************************)
  Lemma toctxset_to_mapdReduce: forall (A: Type),
      toctxset (F := T) (A := A) = mapdReduce (ret (T := subset)).
  Proof.
    intros.
    rewrite toctxset_to_mapdt.
    reflexivity.
  Qed.

  Corollary toctxset_to_mapdt1: forall (A: Type),
      toctxset (F := T) =
        mapdt (G := const (subset (E * A)))
          (B := False) (ret (T := subset)).
  Proof.
    intros.
    rewrite toctxset_to_mapdReduce.
    reflexivity.
  Qed.

  Corollary toctxset_to_mapdt2: forall (A fake: Type),
      toctxset (F := T) =
        mapdt (G := const (subset (E * A)))
          (B := fake) (ret (T := subset)).
  Proof.
    intros.
    rewrite toctxset_to_mapdt1.
    rewrite (mapdt_constant_applicative1 (B := fake)).
    reflexivity.
  Qed.

  Lemma element_ctx_of_to_mapdReduce
    `{ToSubset T} `{! Compat_ToSubset_Traverse T}
    : forall (A: Type) (p: E * A),
      element_ctx_of (T := T) (A := A) p =
        mapdReduce (op := Monoid_op_or)
          (unit := Monoid_unit_false) {{p}}.
  Proof.
    intros.
    rewrite element_ctx_of_toctxset.
    rewrite toctxset_to_mapdReduce.
    rewrite mapdReduce_morphism.
    unfold evalAt, compose.
    now (fequal; ext [e' a']; propext; intuition).
  Qed.

  Lemma element_ctx_of_to_mapdReduce2
    `{ToSubset T} `{! Compat_ToSubset_Traverse T}
   : forall (A: Type),
      element_ctx_of (T := T) (A := A) =
        mapdReduce (op := Monoid_op_or)
          (unit := Monoid_unit_false) ∘ ret (T := subset).
  Proof.
    intros. ext p.
    apply element_ctx_of_to_mapdReduce.
  Qed.

  (** ** Factoring <<toctxset_of>> through <<toctxlist>>/<<mapdReduce>> *)
  (********************************************************************)
  Lemma toctxset_through_toctxlist: forall (A: Type),
      toctxset (F := T) (A := A) =
        tosubset (F := list) ∘ toctxlist (F := T).
  Proof.
    intros.
    rewrite toctxlist_to_mapdReduce.
    rewrite mapdReduce_morphism.
    rewrite toctxset_to_mapdReduce.
    rewrite (Monad.kmon_hom_ret (ϕ := @tosubset list _)).
    reflexivity.
  Qed.

  Lemma tosubset_eq_toctxset_env: forall (A: Type),
      tosubset (F := list) (A := E * A) =
        toctxset (F := env E).
  Proof.
    intros. ext l.
    induction l.
    - reflexivity.
    - simpl_list.
      destruct a as [e a].
      cbn.
      unfold_ops @Pure_const.
      rewrite monoid_id_l.
      rewrite <- IHl.
      reflexivity.
  Qed.

  Lemma toctxset_through_toctxlist2: forall (A: Type),
      toctxset (F := T) (A := A) =
        toctxset (F := env E) ∘ toctxlist (F := T).
  Proof.
    intros.
    rewrite toctxset_through_toctxlist.
    rewrite tosubset_eq_toctxset_env.
    reflexivity.
  Qed.

  Lemma toctxset_through_mapdReduce: forall (A: Type),
      toctxset (F := T) (A := A) =
        tosubset ∘ mapdReduce (ret (T := list)).
  Proof.
    intros.
    apply toctxset_through_toctxlist.
  Qed.

  (** ** Fusion Laws for <<toctxset>> *)
  (********************************************************************)
  Lemma toctxset_mapd_fusion: forall `(f: E * A -> B),
      toctxset (F := T) ∘ mapd f =
        mapdReduce (ret (T := subset) ∘ cobind f).
  Proof.
    intros.
    rewrite toctxset_to_mapdReduce.
    rewrite mapdReduce_mapd.
    reflexivity.
  Qed.

  Lemma toctxset_map_fusion: forall `(f: A -> B),
      toctxset (F := T) ∘ map f =
        mapdReduce (ret (T := subset) ∘ map (F := (E ×)) f).
  Proof.
    intros.
    rewrite toctxset_to_mapdReduce.
    rewrite mapdReduce_map.
    reflexivity.
  Qed.

  Lemma tosubset_mapd_fusion
    `{ToSubset T} `{! Compat_ToSubset_Traverse T}: forall `(f: E * A -> B),
      tosubset ∘ mapd f = mapdReduce (ret (T := subset) ∘ f).
  Proof.
    intros.
    rewrite tosubset_to_mapReduce.
    rewrite mapReduce_to_mapdReduce.
    rewrite mapdReduce_mapd.
    reassociate -> on left.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  (** ** Naturality for <<toctxset>> *)
  (********************************************************************)
  Instance DecoratedHom_ret_subst: (*TODO Move me *)
    DecoratedHom E (E ×) (ctxset E) (@ret subset _ ○ (E ×)).
  Proof.
    constructor.
    intros A B f.
    ext [e a].
    unfold compose.
    unfold_ops @Return_subset.
    unfold_ops @Mapd_ctxset.
    unfold mapd, Mapd_Reader.
    ext [e' b]. cbn. propext.
    - intros [a'' [Heq Hf]].
      inversion Heq. rewrite Hf.
      reflexivity.
    - intro H.
      exists a. now inversion H.
  Qed.

  Lemma toctxset_mapd: forall `(f: E * A -> B),
      toctxset (F := T) ∘ mapd f = mapd f ∘ toctxset.
  Proof.
    intros.
    rewrite toctxset_to_mapdReduce.
    rewrite toctxset_to_mapdReduce.
    rewrite mapdReduce_mapd.
    rewrite mapdReduce_morphism.
    change (cobind f) with (mapd (T := (E ×)) f).
    change (@ret subset _ (E * B))
      with ((@ret subset _ ○ (E ×)) B).
    rewrite <- dhom_natural.
    reflexivity.
  Qed.

  Lemma toctxset_map: forall `(f: A -> B),
      toctxset (F := T) ∘ map f = map f ∘ toctxset.
  Proof.
    intros.
    rewrite ctxset_map_spec.
    rewrite toctxset_to_mapdReduce.
    rewrite mapdReduce_map.
    rewrite toctxset_to_mapdReduce.
    rewrite mapdReduce_morphism.
    rewrite (natural (ϕ := @ret subset _) (A := E * A) (B := E * B)).
    reflexivity.
  Qed.

  (*
    Theorem ind_mapd_iff_core:
    forall `(f: E * A -> B),
    mapd f ∘ toctxset = toctxset ∘ mapd (T := T) f.
    Proof.
    intros.
    rewrite toctxset_through_toctxlist.
    rewrite toctxset_through_toctxlist.
    reassociate -> on right.
    change (list (prod ?E ?X)) with (env E X). (* hidden *)
    rewrite <- (mapd_toctxlist f).
    rewrite env_mapd_spec.
    reassociate <- on right.
    rewrite ctxset_mapd_spec.
    change (env ?E ?X) with (list (prod E X)). (* hidden *)
    unfold ctxset.
    rewrite <- (natural (ϕ := @tosubset list _)).
    reflexivity.
    Qed.
   *)

  #[export] Instance Natural_Elementd_Mapdt: Natural (@toctxset E T _).
  Proof.
    constructor;
      try typeclasses eauto.
    intros. rewrite toctxset_map.
    reflexivity.
  Qed.

  (** ** Relating <<tosubset>> and <<toctxset>> *)
  (********************************************************************)
  Lemma tosubset_to_toctxset
    `{ToSubset T} `{! Compat_ToSubset_Traverse T}: forall (A: Type),
      tosubset (F := T) (A := A) =
        map (F := subset) extract ∘ toctxset.
  Proof.
    intros.
    rewrite tosubset_to_mapReduce.
    rewrite mapReduce_to_mapdReduce.
    rewrite toctxset_to_mapdReduce.
    rewrite mapdReduce_morphism.
    rewrite (natural (ϕ := @ret subset _)).
    reflexivity.
  Qed.

  (** ** Characterizing <<∈d>> *)
  (********************************************************************)
  Lemma ind_iff_in_toctxlist1: forall (A: Type) (e: E) (a: A) (t: T A),
      (e, a) ∈d t <-> (e, a) ∈ (toctxlist t: list (E * A)).
  Proof.
    intros.
    unfold element_ctx_of.
    rewrite toctxset_through_toctxlist.
    reflexivity.
  Qed.

  Lemma ind_iff_in_toctxlist2: forall (A: Type) (e: E) (a: A) (t: T A),
      (e, a) ∈d t <-> (e, a) ∈d toctxlist t.
  Proof.
    intros.
    unfold element_ctx_of.
    rewrite <- tosubset_eq_toctxset_env.
    rewrite toctxset_through_toctxlist.
    reflexivity.
  Qed.

  (** ** Folding by Preordered Monoids *)
  (********************************************************************)
  Lemma mapdReduce_mono {M R op unit}
    `{@PreOrderedMonoid M R op unit}:
    forall `(f: E * A -> M) (g: E * A -> M)
      (t: T A),
      (forall e a, (e, a) ∈d t ->
              R (f (e, a)) (g (e, a))) ->
      R (mapdReduce f t) (mapdReduce g t).
  Proof.
    introv Hin.
    setoid_rewrite ind_iff_in_toctxlist1 in Hin.
    rewrite mapdReduce_through_toctxlist.
    rewrite mapdReduce_through_toctxlist.
    unfold compose.
    induction (toctxlist t).
    - cbv. reflexivity.
    - rename a into hd.
      rename e into tl.
      destruct hd as [e a].
      setoid_rewrite element_of_list_cons in Hin.
      do 2 rewrite mapReduce_eq_mapReduce_list.
      do 2 rewrite mapReduce_list_cons.
      apply pompos_both.
      + auto.
      + do 2 rewrite <- mapReduce_eq_mapReduce_list.
        apply IHe. intuition.
  Qed.

  Lemma mapdReduce_pompos {M R op unit}
    `{@PreOrderedMonoidPos M R op unit}:
    forall `(f: E * A -> M) (t: T A),
    forall e a, (e, a) ∈d t -> R (f (e, a)) (mapdReduce f t).
  Proof.
    introv Hin.
    rewrite ind_iff_in_toctxlist1 in Hin.
    rewrite mapdReduce_through_toctxlist.
    unfold compose.
    induction (toctxlist t).
    - inversion Hin.
    - rename a0 into hd.
      rename e0 into tl.
      destruct hd as [e' a'].
      rewrite element_of_list_cons in Hin.
      rewrite mapReduce_eq_mapReduce_list.
      rewrite mapReduce_list_cons.
      rewrite <- mapReduce_eq_mapReduce_list.
      destruct Hin as [Hin | Hin].
      + inversion Hin.
        apply pompos_incr_r.
      + transitivity (mapReduce f tl).
        * auto.
        * apply pompos_incr_l.
  Qed.

End mapdt_toctxset.

(** * Quantification with Context: <<Forall_ctx>> and <<Forany_ctx>> *)
(**********************************************************************)
Section quantification.

  Context
    `{DecoratedTraversableFunctor E T}
    `{ToCtxset E T}
    `{! Compat_ToCtxset_Mapdt E T}.

  Definition Forall_ctx `(P: E * A -> Prop): T A -> Prop :=
    @mapdReduce T E _ Prop Monoid_op_and Monoid_unit_true A P.

  Definition Forany_ctx `(P: E * A -> Prop): T A -> Prop :=
    @mapdReduce T E _ Prop Monoid_op_or Monoid_unit_false A P.

  Lemma forall_ctx_iff `(P: E * A -> Prop) (t: T A):
    Forall_ctx P t <-> forall (e: E) (a: A), (e, a) ∈d t -> P (e, a).
  Proof.
    unfold Forall_ctx.
    rewrite mapdReduce_through_toctxlist.
    setoid_rewrite ind_iff_in_toctxlist2.
    unfold compose at 1.
    induction (toctxlist t) as [|[e a] rest IHrest].
    - cbv. intuition.
    - rewrite mapReduce_eq_mapReduce_list;
        simpl_list;
        rewrite <- mapReduce_eq_mapReduce_list.
      rewrite IHrest; clear IHrest.
      unfold element_ctx_of.
      rewrite <- tosubset_eq_toctxset_env.
      rewrite tosubset_list_cons.
      change (tosubset ?t ?p) with (p ∈ t).
      setoid_rewrite element_of_list_cons.
      setoid_rewrite pair_equal_spec.
      unfold_all_transparent_tcs.
      intuition (subst; auto).
  Qed.

  Corollary forall_ctx_iff_eq `(P: E * A -> Prop) (t: T A):
    Forall_ctx P t = forall (e: E) (a: A), (e, a) ∈d t -> P (e, a).
  Proof.
    apply propositional_extensionality.
    apply forall_ctx_iff.
  Qed.

  Lemma forany_ctx_iff `(P: E * A -> Prop) (t: T A):
    Forany_ctx P t <-> exists (e: E) (a: A), (e, a) ∈d t /\ P (e, a).
  Proof.
    unfold Forany_ctx.
    rewrite mapdReduce_through_toctxlist.
    setoid_rewrite ind_iff_in_toctxlist2.
    unfold compose at 1.
    induction (toctxlist t) as [|[e a] rest IHrest].
    - cbv. intuition.
      firstorder.
    - rewrite mapReduce_eq_mapReduce_list;
        simpl_list;
        rewrite <- mapReduce_eq_mapReduce_list.
      rewrite IHrest; clear IHrest.
      unfold element_ctx_of.
      rewrite <- tosubset_eq_toctxset_env.
      rewrite tosubset_list_cons.
      change (tosubset ?t ?p) with (p ∈ t).
      setoid_rewrite element_of_list_cons.
      setoid_rewrite pair_equal_spec.
      unfold_all_transparent_tcs.
      split.
      { intros [hyp | hyp].
        - exists e a. split.
          now left. assumption.
        - destruct hyp as [e' [a' [Hin HP]]].
          exists e' a'. split.
          now right. assumption.
      }
      { intros [e' [a' [hyp1 hyp2]]].
        destruct hyp1 as [hyp1 | hyp1].
        - left. inversion hyp1; subst.
          assumption.
        - right. exists e' a'. easy.
      }
  Qed.

  Corollary forany_ctx_iff_eq `(P: E * A -> Prop) (t: T A):
    Forany_ctx P t = exists (e: E) (a: A), (e, a) ∈d t /\ P (e, a).
  Proof.
    apply propositional_extensionality.
    apply forany_ctx_iff.
  Qed.

  Lemma element_ctx_of_env_cons {A}: forall e a e' a' (rest: env E A),
      (e, a) ∈d ((e', a') :: rest) =
        ((e = e' /\ a = a') \/ (e, a) ∈d rest).
  Proof.
    intros.
    unfold element_ctx_of.
    rewrite toctxset_to_mapdt.
    rewrite mapdReduce_to_mapdt1.
    cbn.
    unfold const at 1.
    simplify_applicative_const.
    repeat simplify_monoid_subset.
    setoid_rewrite monoid_subset_rw.
    simplify_map_const.
    simpl_subset.
    unfold_ops @Return_subset.
    propext.
    - setoid_rewrite pair_equal_spec. firstorder.
    - setoid_rewrite pair_equal_spec. firstorder.
  Qed.

  (** ** Decidability of <<Forall_ctx>> and <<Forany_ctx>> *)
  (**********************************************************************)
  Lemma decidable_Forall_ctx `(P: E * A -> Prop) `(Dec: decidable_pred P):
    decidable_pred (Forall_ctx P).
  Proof.
    unfold decidable_pred.
    intro t.
    unfold Forall_ctx.
    rewrite mapdReduce_through_toctxlist.
    change (decidable (Forall (T := list) P (toctxlist t))).
    apply decidable_Forall.
    assumption.
  Qed.

  Lemma decidable_Forany_ctx `(P: E * A -> Prop) (Dec: decidable_pred P):
    decidable_pred (Forany_ctx P).
  Proof.
    unfold decidable_pred.
    intro t.
    unfold Forany_ctx.
    rewrite mapdReduce_through_toctxlist.
    change (decidable (Forany (T := list) P (toctxlist t))).
    apply decidable_Forany.
    assumption.
  Qed.

  Lemma decidable_Forall_element_ctx
    `(P: E * A -> Prop) `(Dec: decidable_pred P) (t: T A):
    decidable (forall (e: E) (a: A), (e, a) ∈d t -> P (e, a)).
  Proof.
    rewrite <- forall_ctx_iff_eq.
    apply decidable_Forall_ctx.
    assumption.
  Qed.

  Lemma decidable_Forany_element_ctx
    `(P: E * A -> Prop) `(Dec: decidable_pred P) (t: T A):
    decidable (exists (e: E) (a: A), (e, a) ∈d t /\ P (e, a)).
  Proof.
    rewrite <- forany_ctx_iff_eq.
    apply decidable_Forany_ctx.
    assumption.
  Qed.

  Lemma not_Forall_ctx_Forany_ctx_lemma1
    `(P: E * A -> Prop) (Dec: decidable_pred P) (t: T A):
      ~ (Forall_ctx P t) -> Forany_ctx (not ∘ P) t.
  Proof.
    unfold Forall_ctx, Forany_ctx.
    rewrite mapdReduce_through_toctxlist.
    rewrite mapdReduce_through_toctxlist.
    unfold compose.
    induction (toctxlist t).
    - cbv. firstorder.
    - do 2 rewrite mapReduce_eq_mapReduce_list in *.
      simpl_list.
      simplify_monoid_conjunction.
      simplify_monoid_disjunction.
      firstorder.
  Qed.

  Lemma not_Forall_ctx_Forany_ctx
    `(P: E * A -> Prop) (Dec: decidable_pred P) (t: T A):
      ~ (Forall_ctx P t) <-> Forany_ctx (not ∘ P) t.
  Proof.
    unfold not at 2, compose at 1.
    destruct (decidable_Forall_ctx P Dec t) as [YesAll | NotAll].
    - split.
      + contradiction.
      + rewrite forall_ctx_iff, forany_ctx_iff in *.
        intros [e [a [Hin HP]]] _.
        intuition.
    - split.
      + apply not_Forall_ctx_Forany_ctx_lemma1.
        assumption.
      + easy.
  Qed.

  Lemma not_forall_ctx_iff `(P: E * A -> Prop) (Dec: decidable_pred P) (t: T A):
    ~ Forall_ctx P t <-> exists (e: E) (a: A), (e, a) ∈d t /\ ~ P (e, a).
  Proof.
    rewrite not_Forall_ctx_Forany_ctx; auto.
    rewrite forany_ctx_iff.
    reflexivity.
  Qed.

  (** ** Booleans *)
  (**********************************************************************)
  Definition Forall_ctx_b `(P: E * A -> bool): T A -> bool :=
    @mapdReduce T E _ bool Monoid_op_bool_and Monoid_unit_bool_true A P.

  Lemma decidable_Forall_ctx_b `(P: E * A -> Prop) `(Q: E * A -> bool)
    (Qspec: forall p, Q p = true <-> P p) (t: T A):
    Forall_ctx P t <-> Forall_ctx_b Q t = true.
  Proof.
    unfold Forall_ctx.
    unfold Forall_ctx_b.
    rewrite mapdReduce_through_toctxlist.
    rewrite mapdReduce_through_toctxlist.
    unfold compose.
    induction (toctxlist t).
    - cbv. easy.
    - do 2 rewrite mapReduce_eq_mapReduce_list in *.
      simpl_list.
      repeat simplify_applicative_const.
      repeat simplify_monoid_conjunction.
      unfold transparent tcs.
      split.
      + rewrite IHe; clear IHe.
        rewrite <- Qspec.
        intros [X Y]; rewrite X; rewrite Y.
        reflexivity.
      + intro Hyp.
        rewrite Bool.andb_true_iff in Hyp.
        rewrite IHe.
        rewrite <- Qspec.
        assumption.
  Qed.

End quantification.
