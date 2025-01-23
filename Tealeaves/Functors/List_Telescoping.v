From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.Theory.DecoratedTraversableFunctor
  Functors.List
  Misc.NaturalNumbers
  Theory.DecoratedTraversableFunctor.

Import Applicative.Notations.
Import Monoid.Notations.
Import DecoratedTraversableFunctor.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import Subset.Notations.

(** * Telescoping Decoration for the List Functor *)
(******************************************************************************)

(** ** The <<decorate_telescoping_list>> Operation *)
(******************************************************************************)
Fixpoint decorate_telescoping_list_rec (n: nat) {A: Type} (l: list A):
  list (nat * A) :=
  match l with
  | nil => nil
  | x :: xs =>
      (n, x) :: decorate_telescoping_list_rec (S n) xs
  end.

Definition decorate_telescoping_list {A: Type} (l: list A):
  list (nat * A) := decorate_telescoping_list_rec 0 l.

(** ** Alternative Characterization of <<decorate_telescoping_list>> *)
(******************************************************************************)
Fixpoint decorate_telescoping_list_alt {A: Type} (l: list A):
  list (nat * A) :=
  match l with
  | nil => nil
  | x :: xs =>
      (0, x) :: map (F := list) (incr 1) (decorate_telescoping_list_alt xs)
  end.

(** ** Rewriting Rules for <<decorate_telescoping_list>> *)
(******************************************************************************)
Section decorate_telescoping_list_rw.

  Context {A: Type}.

  Lemma decorate_telescoping_list_rw_nil:
    decorate_telescoping_list_alt (@nil A) = @nil (nat * A).
  Proof.
    reflexivity.
  Qed.

  Lemma decorate_telescoping_list_rw_cons: forall (a: A) (l: list A),
      decorate_telescoping_list_alt (a :: l) =
        (0, a) :: map (F := list) (incr 1) (decorate_telescoping_list_alt l).
  Proof.
    reflexivity.
  Qed.

  Lemma decorate_telescoping_list_rw_app: forall (l1 l2: list A),
      decorate_telescoping_list_alt (l1 ++ l2) =
        decorate_telescoping_list_alt l1 ++
          map (F := list) (incr (length l1)) (decorate_telescoping_list_alt l2).
  Proof.
    intros.
    generalize dependent l2.
    induction l1; intro l2.
    - cbn.
      change 0 with (Ƶ: nat).
      rewrite incr_zero.
      rewrite fun_map_id.
      reflexivity.
    - rewrite <- List.app_comm_cons.
      rewrite decorate_telescoping_list_rw_cons.
      rewrite IHl1.
      simpl_list.
      compose near (decorate_telescoping_list_alt l2) on left.
      rewrite (fun_map_map).
      rewrite incr_incr.
      change (1 ● length l1) with (length (a :: l1)).
      reflexivity.
  Qed.

End decorate_telescoping_list_rw.

(** ** Equivalence *)
(******************************************************************************)
Lemma decorate_telescoping_list_equiv: forall (A: Type) (l: list A),
    decorate_telescoping_list l = decorate_telescoping_list_alt l.
Proof.
  intros.
  unfold decorate_telescoping_list.
  assert
    (forall n, decorate_telescoping_list_rec n l =
            map (incr n) (decorate_telescoping_list_alt l)).
  { induction l.
    - reflexivity.
    - intros. cbn.
      rewrite IHl.
      change 0 with (Ƶ: nat) at 1.
      rewrite monoid_id_l.
      compose near (decorate_telescoping_list_alt l) on right.
      rewrite (fun_map_map).
      rewrite incr_incr.
      replace (n ● 1) with (S n) by (unfold_ops @Monoid_op_plus; lia).
      reflexivity. }
  specialize (H 0).
  replace (incr 0) with (@id (nat * A)) in H.
  rewrite (fun_map_id) in H.
  assumption.
  change 0 with (Ƶ: nat).
  now rewrite incr_zero.
Qed.

(** ** Associated <<mapdt>> Operation *)
(******************************************************************************)
Fixpoint mapdt_telescoping_list
           {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
           {A B : Type} (f : nat * A -> G B) (l : list A)
  : G (list B) :=
  match l with
  | nil => pure (@nil B)
  | x :: xs =>
      pure (@List.cons B) <⋆> f (0, x) <⋆>
        mapdt_telescoping_list (f ⦿ 1) xs
  end.

#[export] Instance Mapdt_Telescoping_List:
  Mapdt nat list := @mapdt_telescoping_list.

Lemma mapdt_telescoping_list_spec:
  forall {G} `{Applicative G} {A B : Type} (f : nat * A -> G B) (l : list A),
    mapdt f l = traverse f (decorate_telescoping_list_alt l).
Proof.
  intros.
  generalize dependent f.
  induction l; intro f.
  - reflexivity.
  - cbn. fequal.
    rewrite IHl.
    compose near (decorate_telescoping_list_alt l) on right.
    rewrite (traverse_map).
    reflexivity.
Qed.

(** ** Rewriting Rules for <<decorate_telescoping_list>> *)
(******************************************************************************)
Section mapdt_telescoping_list_rw.

  Context {A B: Type}.

  Context
    {G: Type -> Type}
    `{Applicative G}.

  Implicit Type (f: nat * A -> G B).

  Lemma mapdt_telescoping_list_rw_nil: forall f,
    mapdt_telescoping_list f (@nil A) = pure (@nil B).
  Proof.
    reflexivity.
  Qed.

  Lemma mapdt_telescoping_list_rw_cons: forall f (a: A) (l: list A),
      mapdt_telescoping_list f (a :: l) =
        pure cons
          <⋆> f (0, a)
          <⋆> mapdt_telescoping_list (f ⦿ 1) l.
  Proof.
    reflexivity.
  Qed.

  Lemma mapdt_telescoping_list_rw_app: forall f (l1 l2: list A),
      mapdt_telescoping_list f (l1 ++ l2) =
        pure (@app B)
          <⋆> mapdt_telescoping_list f l1
          <⋆> mapdt_telescoping_list (f ⦿ length l1) l2.
  Proof.
    intros.
    rewrite mapdt_telescoping_list_spec.
    rewrite decorate_telescoping_list_rw_app.
    rewrite (traverse_list_app G).
    rewrite <- mapdt_telescoping_list_spec.
    compose near (decorate_telescoping_list_alt l2).
    rewrite traverse_map.
    rewrite <- mapdt_telescoping_list_spec.
    reflexivity.
  Qed.

End mapdt_telescoping_list_rw.

(** ** Typeclass Instance *)
(******************************************************************************)
#[export] Instance DecoratedTraversableFunctor_List_Telescope:
  @DecoratedTraversableFunctor
    nat list Mapdt_Telescoping_List.
Proof.
  constructor;
    unfold_ops @Mapdt_Telescoping_List;
    intros; ext l.
  - induction l.
    + rewrite mapdt_telescoping_list_rw_nil.
      reflexivity.
    + rewrite mapdt_telescoping_list_rw_cons.
      rewrite Writer.extract_preincr.
      rewrite IHl.
      reflexivity.
  - generalize dependent f.
    generalize dependent g.
    induction l; intros g f.
    + unfold compose.
      rewrite mapdt_telescoping_list_rw_nil.
      rewrite app_pure_natural.
      rewrite mapdt_telescoping_list_rw_nil.
      rewrite mapdt_telescoping_list_rw_nil.
      reflexivity.
    + unfold compose.
      (* left *)
      rewrite mapdt_telescoping_list_rw_cons.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      (* right *)
      rewrite mapdt_telescoping_list_rw_cons.
      unfold_ops @Pure_compose.
      rewrite kc3_preincr.
      rewrite kc3_spec.
      rewrite <- IHl.
      unfold compose at 4.
      rewrite (ap_compose2 G2 G1).
      rewrite (ap_compose2 G2 G1).
      rewrite app_pure_natural.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite <- ap_map.
      rewrite app_pure_natural.
      reflexivity.
  - generalize dependent f.
    induction l; intro f.
    + unfold compose. cbn.
      now rewrite appmor_pure.
    + unfold compose at 1.
      rewrite mapdt_telescoping_list_rw_cons.
      rewrite ap_morphism_1.
      rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite mapdt_telescoping_list_rw_cons.
      compose near l on left.
      rewrite IHl.
      reflexivity.
Qed.

(** ** Derived Operation Compatibility *)
(******************************************************************************)
#[export] Instance ToBatch3_Telescoping_List: ToBatch3 nat list
    := DerivedOperations.ToBatch3_Mapdt (H := Mapdt_Telescoping_List).

#[export] Instance Mapd_List_Telescope: Mapd nat list :=
  DerivedOperations.Mapd_Mapdt.

#[export] Instance Compat_Mapd_Mapdt_Telescoping_List:
  Compat_Mapd_Mapdt nat list := ltac:(typeclasses eauto).
#[export] Instance Compat_Traverse_Mapdt_Telescoping_List:
  @Compat_Traverse_Mapdt nat list Traverse_list Mapdt_Telescoping_List.
Proof.
  hnf.
  ext G MapG PureG MultG.
  ext A B f l.
  change_left (traverse f l).
  unfold DerivedOperations.Traverse_Mapdt.
  induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. fequal.
    rewrite IHrest.
    rewrite Writer.extract_preincr2.
    reflexivity.
Qed.

#[export] Instance Compat_Map_Mapdt_Telescoping_List:
  @Compat_Map_Mapdt nat list Map_list Mapdt_Telescoping_List.
Proof.
  unfold Compat_Map_Mapdt.
  ext A B f l.
  induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. fequal.
    rewrite IHrest.
    rewrite Writer.extract_preincr2.
    reflexivity.
Qed.

(** ** Associated <<toctxlist>> and <<toctxset>> Operations *)
(******************************************************************************)
#[export] Instance ToCtxlist_List_Telescoping:
  ToCtxlist nat list := ToCtxlist_Mapdt.

#[export] Instance ToCtxset_List_Telescoping:
  ToCtxset nat list := ToCtxset_Mapdt.

#[export] Instance Compat_ToSubset_ToCtxset_List_Telescoping:
  @Compat_ToSubset_ToCtxset
    nat list ToCtxset_List_Telescoping ToSubset_list.
Proof.
  unfold Compat_ToSubset_ToCtxset.
  ext A l a.
  change_left (tosubset l a).
  unfold_ops @ToSubset_ToCtxset.
  unfold_ops @ToCtxset_List_Telescoping.
  unfold_ops @ToCtxset_Mapdt.
  rewrite foldMapd_morphism.
  rewrite tosubset_to_foldMap.
  rewrite foldMap_to_foldMapd.
  rewrite (natural (ϕ := @ret subset _)).
  reflexivity.
Qed.


(** * Fully Recursive Decoration for the List Functor *)
(******************************************************************************)

(** ** The <<decorate_list_full>> Operation *)
(******************************************************************************)
Definition decorate_list_full {A: Type} (l: list A):
  list (nat * A) :=
  map (pair (length l)) l.

(** ** The Associated <<mapdt_list_full>> Operation *)
(******************************************************************************)
Definition mapdt_list_full
           {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
           {A B : Type} (f : nat * A -> G B) (l : list A)
  : G (list B) :=
  traverse (T := list) (G := G) (f ∘ pair (length l)) l.

#[export] Instance Mapdt_List_Full: Mapdt nat list := @mapdt_list_full.

(** ** <<DecoratedTraversableFunctor>> Typeclass Instance *)
(******************************************************************************)
#[export] Instance DecoratedTraversableFunctor_List_Full:
  @DecoratedTraversableFunctor
    nat list Mapdt_List_Full.
Proof.
  constructor; intros; ext l;
    unfold_ops @Mapdt_List_Full;
    unfold mapdt_list_full.
  - rewrite Writer.extract_pair.
    now rewrite trf_traverse_id.
  - unfold compose at 1.
    assert (kc_spec: kc3 (G1 := G1)(G2 := G2) g f ∘ pair (length l) =
                       kc2 (g ∘ pair (length l)) (f ∘ pair (length l))).
    { ext a. unfold kc3, kc2, compose; cbn.
      compose near (f (length l, a)) on left.
      now rewrite (fun_map_map (F := G1)). }
    Set Keyed Unification.
    rewrite kc_spec.
    Unset Keyed Unification.
    rewrite <- trf_traverse_traverse.
    rewrite traverse_repr.
    change (map ?g (map ?f ?x)) with ((map g ∘ map f) x).
    rewrite (fun_map_map).
    cbn beta.
    unfold compose at 1.
    assert (cut: (fun (a: Vector (plength l) B) =>
                traverse (g ∘ pair (length (trav_make l a))) (trav_make l a))
             =
               (fun (a: Vector (plength l) B) =>
                  traverse (g ∘ pair (length l)) (trav_make l a))).
    { ext a.
      rewrite <- list_plength_length.
      rewrite <- list_plength_length.
      rewrite <- TraversableFunctor.plength_trav_make.
      reflexivity. }
    rewrite cut.
    change (?g ○ trav_make l) with (g ∘ trav_make l).
    rewrite <- (fun_map_map).
    unfold compose at 1.
    rewrite <- traverse_repr.
    reflexivity.
  - reassociate -> on right.
    rewrite <- (trf_traverse_morphism).
    reflexivity.
Qed.

(** ** Compatibility Instances *)
(******************************************************************************)
#[export] Instance ToBatch3_List_Full: ToBatch3 nat list
  := DerivedOperations.ToBatch3_Mapdt (H := Mapdt_List_Full).

#[export] Instance Mapd_List_Full: Mapd nat list :=
  @DerivedOperations.Mapd_Mapdt nat list Mapdt_List_Full.

#[export] Instance Compat_Traverse_Mapdt_List_Full:
  @Compat_Traverse_Mapdt nat list Traverse_list Mapdt_List_Full.
Proof.
  unfold Compat_Traverse_Mapdt.
  reflexivity.
Qed.

#[export] Instance Compat_Mapd_Mapdt_List_Full:
  Compat_Mapd_Mapdt nat list :=
  ltac:(typeclasses eauto).

#[export] Instance Compat_Map_Mapdt_List_Full:
  @Compat_Map_Mapdt nat list Map_list Mapdt_List_Full.
Proof.
  unfold Compat_Map_Mapdt.
  unfold_ops @DerivedOperations.Map_Mapdt.
  unfold_ops @Mapdt_List_Full.
  unfold mapdt_list_full.
  ext A B f l.
  reassociate -> on right.
  rewrite Writer.extract_pair.
  change (?f ∘ id) with f.
  rewrite <- map_to_traverse.
  reflexivity.
Qed.

#[export] Instance ToCtxlist_List_Full:
  ToCtxlist nat list := ToCtxlist_Mapdt.

#[export] Instance ToCtxset_List_Full:
  ToCtxset nat list := ToCtxset_Mapdt.

#[export] Instance Compat_ToSubset_ToCtxset_List_Full:
  @Compat_ToSubset_ToCtxset
    nat list ToCtxset_List_Full ToSubset_list.
Proof.
  apply Compat_ToSubset_ToCtxset_Traverse.
Qed.
