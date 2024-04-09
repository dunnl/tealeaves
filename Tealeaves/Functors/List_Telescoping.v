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

Lemma toctxset_nil: forall (E A: Type),
    toctxset (F := env E) (@nil (E * A)) = subset_empty.
Proof.
  reflexivity.
Qed.

Import Subset.Notations.
Lemma toctxset_cons: forall (E A: Type) (e: E) (a: A) (l: env E A),
    toctxset (F := env E) ((e, a) :: l) =
      {{(e, a)}} ∪ (toctxset l).
Proof.
  reflexivity.
Qed.

Fixpoint decorate_telescoping_list_rec (n: nat) {A: Type} (l: list A):
  list (nat * A) :=
  match l with
  | nil => nil
  | x :: xs =>
      (n, x) :: decorate_telescoping_list_rec (S n) xs
  end.

Definition decorate_telescoping_list {A: Type} (l: list A):
  list (nat * A) := decorate_telescoping_list_rec 0 l.

Fixpoint decorate_telescoping_list_alt {A: Type} (l: list A):
  list (nat * A) :=
  match l with
  | nil => nil
  | x :: xs =>
      (0, x) :: map (F := list) (incr 1) (decorate_telescoping_list_alt xs)
  end.

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

Fixpoint mapdt_list_telescope
           {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
           {A B : Type} (f : nat * A -> G B) (l : list A)
  : G (list B) :=
  match l with
  | nil => pure (@nil B)
  | x :: xs =>
      pure (@List.cons B) <⋆> f (0, x) <⋆>
        mapdt_list_telescope (f ⦿ 1) xs
  end.

#[export] Instance Mapdt_List_Telescope: Mapdt nat list := @mapdt_list_telescope.
#[export] Instance Mapd_List_Telescope: Mapd nat list := Mapd_Mapdt.
#[export] Instance: Compat_Mapd_Mapdt := ltac:(typeclasses eauto).
#[export] Instance: @Compat_Traverse_Mapdt nat list Traverse_list Mapdt_List_Telescope.
Proof.
  unfold Compat_Traverse_Mapdt.
  intros. ext A B f l.
  induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. fequal.
    rewrite IHrest.
    rewrite extract_preincr2.
    reflexivity.
Qed.
#[export] Instance: @Compat_Map_Mapdt nat list Map_list Mapdt_List_Telescope.
Proof.
  unfold Compat_Map_Mapdt.
  ext A B f l.
  induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. fequal.
    rewrite IHrest.
    rewrite extract_preincr2.
    reflexivity.
Qed.

Lemma mapdt_list_spec:
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

#[export] Instance CtxToList_List_Telescoping:
  ToCtxlist nat list := ToCtxlist_Mapdt.

#[export] Instance ToCtxset_List_Telescoping:
  ToCtxset nat list := ToCtxset_ToCtxlist.

#[export] Instance Compat_ToSubset_ToCtxset_List_Telescoping:
  @Compat_ToSubset_ToCtxset
    nat list ToCtxset_List_Telescoping ToSubset_list.
Proof.
  unfold Compat_ToSubset_ToCtxset.
  ext A l a.
  unfold_ops @ToSubset_ToCtxset
               @ToCtxset_List_Telescoping
               @ToCtxset_ToCtxlist.
  unfold_ops @CtxToList_List_Telescoping
               @ToCtxlist_Mapdt.
  rewrite foldMapd_to_mapdt1.
  rewrite <- (preincr_zero ret).
  generalize (Ƶ: nat).
  induction l; intro n.
  - cbv. propext.
    + easy.
    + intros [[n' a'] [contra rest]]. easy.
  - rename a0 into a'.
    unfold compose in *; cbn.
    rewrite toctxset_cons.
    autorewrite with tea_set.
    rewrite preincr_preincr.
    rewrite <- (IHl (n ● 1)).
    change 0 with (Ƶ:nat); now rewrite monoid_id_l.
Qed.

#[export] Instance DecoratedTraversableFunctor_List_Telescope:
  @DecoratedTraversableFunctor
    nat list Mapdt_List_Telescope.
Proof.
  constructor; intros.
  - ext l. induction l.
    + reflexivity.
    + cbn.
      rewrite extract_preincr.
      now rewrite IHl.
  - ext l.
    generalize dependent f.
    generalize dependent g.
    induction l; intros f g.
    + unfold compose; cbn.
      rewrite app_pure_natural.
      reflexivity.
    + unfold compose; cbn.
      (* left *)
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      change (fun a => G1 (G2 a)) with (G1 ∘ G2).
      (* right *)
      unfold_ops @Pure_compose.
      rewrite_strat innermost (terms (ap_compose2 G2 G1)).
      rewrite app_pure_natural.
      replace ((f ⋆6 g) (0, a)) with (* this is annoying *)
        (map (f ∘ pair 0) (g (0, a))) by now rewrite kc6_spec.
      rewrite <- ap_map.
      rewrite app_pure_natural.
      rewrite_strat innermost (terms (ap_compose2 G2 G1)).
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite kc6_preincr.
      rewrite <- IHl.
      unfold compose at 5.
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      reflexivity.
  - ext l.
    generalize dependent f.
    induction l; intro f.
    + unfold compose. cbn.
      now rewrite appmor_pure.
    + unfold compose. cbn.
      rewrite ap_morphism_1.
      rewrite ap_morphism_1.
      compose near l on right.
      rewrite <- IHl.
      rewrite appmor_pure.
      reflexivity.
Qed.


Definition decorate_list_full {A: Type} (l: list A):
  list (nat * A) :=
  map (pair (length l)) l.

Definition mapdt_list_full
           {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
           {A B : Type} (f : nat * A -> G B) (l : list A)
  : G (list B) :=
  traverse (T := list) (G := G) (f ∘ pair (length l)) l.

#[export] Instance Mapdt_List_Full: Mapdt nat list := @mapdt_list_full.
#[export] Instance Mapd_List_Full: Mapd nat list :=
  @Mapd_Mapdt nat list Mapdt_List_Full.
#[export] Instance: Compat_Mapd_Mapdt := ltac:(typeclasses eauto).
#[export] Instance: @Compat_Map_Mapdt nat list Map_list Mapdt_List_Full.
Proof.
  unfold Compat_Map_Mapdt.
  unfold_ops @Map_Mapdt.
  unfold_ops @Mapdt_List_Full.
  unfold mapdt_list_full.
  ext A B f l.
  reassociate -> on right.
  rewrite extract_pair.
  change (?f ∘ id) with f.
  rewrite <- map_to_traverse.
  reflexivity.
Qed.

#[export] Instance CtxToList_List_Full:
  ToCtxlist nat list := ToCtxlist_Mapdt.

#[export] Instance ToCtxset_List_Full:
  ToCtxset nat list := ToCtxset_ToCtxlist.

#[export] Instance Compat_ToSubset_ToCtxset_List_Full:
  @Compat_ToSubset_ToCtxset
    nat list ToCtxset_List_Full ToSubset_list.
Proof.
  unfold Compat_ToSubset_ToCtxset.
  ext A l a.
  unfold_ops @ToSubset_ToCtxset
               @ToCtxset_List_Full
               @ToCtxset_ToCtxlist.
  unfold_ops @CtxToList_List_Full
               @ToCtxlist_Mapdt.
  rewrite foldMapd_to_mapdt1.
  unfold_ops @ToCtxset_env.
  reassociate <-.
  change (fun s : env nat A => @tosubset list ToSubset_list (nat * A) s)
    with (@tosubset list ToSubset_list (nat * A)).
  unfold compose. unfold_ops @Mapdt_List_Full.
  unfold mapdt_list_full.
  generalize (length l).
  induction l; intro n.
  - cbv. propext.
    + easy.
    + intros [[n' a'] [contra rest]]. easy.
  - rename a0 into a'.
    autorewrite with tea_list tea_set.
    cbn.
    rewrite tosubset_list_cons.
    rewrite map_set_add, map_set_one.
    cbn.
    rewrite subset_in_add.
    rewrite (IHl n).
    reflexivity.
Qed.

#[export] Instance DecoratedTraversableFunctor_List_Full:
  @DecoratedTraversableFunctor
    nat list Mapdt_List_Full.
Proof.
  constructor; intros; ext l;
    unfold_ops @Mapdt_List_Full;
    unfold mapdt_list_full.
  - rewrite extract_pair.
    now rewrite trf_traverse_id.
  - unfold compose at 1.
    assert (Functor G1) by now inversion H3.
    assert (Functor G2) by now inversion H7.
    assert (kc_spec: kc6 (G1 := G1)(G2 := G2) g f ∘ pair (length l) =
                       kc2 (g ∘ pair (length l)) (f ∘ pair (length l))).
    { ext a. unfold kc6, kc2, compose; cbn.
      compose near (f (length l, a)) on left.
      now rewrite (fun_map_map (F := G1)). }
    Set Keyed Unification.
    rewrite kc_spec.
    Unset Keyed Unification.
    rewrite <- trf_traverse_traverse.
    #[local] Existing Instance ToBatch_Traverse.
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
  - unfold compose.
    compose near l on right.
    rewrite (trf_traverse_morphism).
    reflexivity.
Qed.
