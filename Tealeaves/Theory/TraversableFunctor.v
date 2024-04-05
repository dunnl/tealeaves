From Tealeaves Require Export
  Classes.Coalgebraic.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Functors.List
(*  Functors.Vector *)
  Functors.VectorRefinement
  Functors.ProductFunctor
  Functors.Constant
  Functors.Identity
  Functors.ProductFunctor
  Misc.Prop
  Classes.Kleisli.TraversableFunctor.

Import Subset.Notations.
Import Applicative.Notations.
Import ContainerFunctor.Notations.
Import ProductFunctor.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import Batch.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables T G A B C M ϕ.

(** * Traversals by specific applicatives *)
(******************************************************************************)
Section traversable_functor_special_applicatives.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}.

  (** ** Cartesian product of applicative functors (F ◻ G) *)
  (******************************************************************************)
  Definition applicative_arrow_combine {F G A B}
    `(f : A -> F B) `(g : A -> G B) : A -> (F ◻ G) B :=
    fun a => product (f a) (g a).

  #[local] Notation "f <◻> g" :=
    (applicative_arrow_combine f g) (at level 60) : tealeaves_scope.

  Section traversable_product.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Variables
      (A B : Type)
        (f : A -> G1 B)
        (g : A -> G2 B).

    Lemma traverse_product1 : forall (t : T A),
        pi1 (traverse (f <◻> g) t) = traverse f t.
    Proof.
      intros.
      pose (ApplicativeMorphism_pi1 G1 G2).
      compose near t on left.
      rewrite trf_traverse_morphism.
      reflexivity.
    Qed.

    Lemma traverse_product2 : forall (t : T A),
        pi2 (traverse (f <◻> g) t) = traverse g t.
    Proof.
      intros.
      pose (ApplicativeMorphism_pi2 G1 G2).
      compose near t on left.
      rewrite trf_traverse_morphism.
      reflexivity.
    Qed.

    Theorem traverse_product_spec :
      traverse (f <◻> g) = traverse f <◻> traverse g.
    Proof.
      intros.
      ext t.
      unfold applicative_arrow_combine at 2.
      erewrite <- traverse_product1.
      erewrite <- traverse_product2.
      rewrite <- product_eta.
      reflexivity.
    Qed.

  End traversable_product.

  (** *** Constant applicative functors *)
  (******************************************************************************)
  Section constant_applicatives.

    Context
      `{Monoid M}.

    Lemma traverse_const1: forall {A : Type} (B : Type) `(f : A -> M),
        traverse (G := const M) (B := False) f =
          traverse (G := const M) (B := B) f.
    Proof.
      intros.
      change_left (map (F := const M) (A := T False)
                     (B := T B) (map (F := T) (A := False) (B := B) exfalso)
                     ∘ traverse (T := T) (G := const M)
                     (B := False) (f : A -> const M False)).
      rewrite (map_traverse (G1 := const M)).
      reflexivity.
    Qed.

    Lemma traverse_const2: forall {A : Type} (f : A -> M) (fake1 fake2 : Type),
        traverse (G := const M) (B := fake1) f =
          traverse (G := const M) (B := fake2) f.
    Proof.
      intros.
      rewrite <- (traverse_const1 fake1).
      rewrite -> (traverse_const1 fake2).
      reflexivity.
    Qed.

  End constant_applicatives.

End traversable_functor_special_applicatives.

(** * The <<foldmap>> operation *)
(******************************************************************************)
Section foldMap.

  Definition foldMap
               {T : Type -> Type} `{Traverse T} `{op : Monoid_op M} `{unit : Monoid_unit M}
               {A : Type} (f : A -> M) : T A -> M := traverse (G := const M) (B := False) f.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  (** *** As a special case of <<traverse>> *)
  (******************************************************************************)
  Lemma foldMap_to_traverse1 `{Monoid M} : forall `(f : A -> M),
      foldMap (T := T) f =
        traverse (G := const M) (B := False) f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_to_traverse2 `{Monoid M} : forall (fake : Type) `(f : A -> M),
      foldMap f = traverse (G := const M) (B := fake) f.
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite (traverse_const1 fake f).
    reflexivity.
  Qed.

  (** *** Factoring through <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMap_through_runBatch1 {A : Type} `{Monoid M} : forall `(f : A -> M),
      foldMap f = runBatch (const M) f (T False) ∘ toBatch (A := A) (A' := False).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_through_runBatch2 `{Monoid M} : forall (A fake : Type) `(f : A -> M),
      foldMap f = runBatch (const M) f (T fake) ∘ toBatch (A' := fake).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    change (fun _ : Type => M) with (const (A := Type) M).
    rewrite (traverse_const1 fake).
    rewrite (traverse_through_runBatch (G := const M)).
    reflexivity.
  Qed.

  (** *** Composition with <<traverse>> and <<map>> *)
  (******************************************************************************)
  Lemma foldMap_traverse `{Monoid M} (G : Type -> Type) {B : Type} `{Applicative G} :
    forall `(g : B -> M) `(f : A -> G B),
      map (A := T B) (B := M) (foldMap g) ∘ traverse f =
        foldMap (map g ∘ f).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite (trf_traverse_traverse (T := T) (G1 := G) (G2 := const M) A B False).
    rewrite foldMap_to_traverse1.
    rewrite map_compose_const.
    rewrite mult_compose_const.
    reflexivity.
  Qed.

  Corollary foldMap_map `{Monoid M} : forall `(g : B -> M) `(f : A -> B),
      foldMap g ∘ map f = foldMap (g ∘ f).
  Proof.
    intros.
    rewrite map_to_traverse.
    change (foldMap g) with (map (F := fun A => A) (A := T B) (B := M) (foldMap g)).
    now rewrite (foldMap_traverse (fun X => X)).
  Qed.

  (** *** Homomorphism law *)
  (******************************************************************************)
  Lemma foldMap_morphism (M1 M2 : Type) `{morphism : Monoid_Morphism M1 M2 ϕ} :
    forall `(f : A -> M1), ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
  Proof.
    intros.
    inversion morphism.
    rewrite foldMap_to_traverse1.
    change ϕ with (const ϕ (T False)).
    rewrite (trf_traverse_morphism (T := T)
               (G1 := const M1) (G2 := const M2) A False).
    reflexivity.
  Qed.

End foldMap.

(** * <<tolist>> *)
(******************************************************************************)
Section tolist.

  #[export] Instance Tolist_Traverse {T} `{Traverse T} : Tolist T :=
  fun A => foldMap (ret (T := list)).

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  Lemma foldMap_list_eq `{Monoid M} : forall (A : Type) (f : A -> M),
      foldMap f = List.foldMap f.
  Proof.
    intros. ext l. induction l.
    - cbn. reflexivity.
    - cbn. change (monoid_op ?x ?y) with (x ● y).
      unfold_ops @Pure_const.
      rewrite monoid_id_r.
      rewrite IHl.
      reflexivity.
  Qed.

  (** The <<tolist>> operation provided by the traversability of <<list>> is the identity. *)
  Lemma Tolist_list_id : forall (A : Type),
      @tolist list (@Tolist_Traverse list Traverse_list) A = @id (list A).
  Proof.
    intros.
    unfold_ops @Tolist_Traverse.
    rewrite foldMap_list_eq.
    rewrite foldMap_list_ret_id.
    reflexivity.
  Qed.

  Corollary tolist_to_foldMap : forall (A : Type),
      tolist (F := T) = foldMap (ret (T := list) (A := A)).
  Proof.
    reflexivity.
  Qed.

  Corollary tolist_to_traverse1 : forall (A : Type),
      tolist = traverse (G := const (list A)) (B := False) (ret (T := list)).
  Proof.
    reflexivity.
  Qed.

  Corollary tolist_to_traverse2 : forall (A fake : Type),
      tolist = traverse (G := const (list A)) (B := fake) (ret (T := list)).
  Proof.
    intros.
    rewrite tolist_to_traverse1.
    rewrite (traverse_const1 fake).
    reflexivity.
  Qed.

  #[export] Instance Natural_Tolist_Traverse : Natural (@tolist T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Tolist_Traverse.
    rewrite (foldMap_morphism (list A) (list B)).
    rewrite foldMap_map.
    rewrite (natural (ϕ := @ret list _)).
    reflexivity.
  Qed.

  (** *** Factoring through <<runBatch>> *)
  (******************************************************************************)
  Corollary tolist_through_runBatch {A : Type} (tag : Type) `(t : T A) :
    tolist t =
      runBatch (const (list A))
               (ret (T := list) : A -> const (list A) tag)
               (T tag) (toBatch (A' := tag) t).
  Proof.
    rewrite (tolist_to_traverse2 A tag).
    rewrite (traverse_through_runBatch (G := const (list A))).
    reflexivity.
  Qed.

  (** *** Factoring <<foldMap>> through <<tolist>> *)
  (******************************************************************************)
  Corollary foldMap_through_tolist `{Monoid M} : forall (A : Type) (f : A -> M),
      foldMap f = foldMap (T := list) f ∘ tolist.
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_list_eq.
    rewrite (foldMap_morphism (list A) M).
    rewrite foldMap_list_ret.
    reflexivity.
  Qed.

End tolist.

(** * Proof that traversable functors are shapely over lists *)
(******************************************************************************)
Section shapeliness.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  Lemma shapeliness_tactical : forall (A : Type) (b1 b2 : Batch A A (T A)),
      runBatch (const (list A)) (ret (T := list)) _ b1 =
        runBatch (const (list A)) (ret (T := list) (A := A)) _ b2 ->
      mapfst_Batch A unit (const tt) b1 = mapfst_Batch A unit (const tt) b2 ->
      runBatch (fun A => A) id (T A) b1 = runBatch (fun A => A) id (T A) b2.
  Proof.
    introv Hlist Hshape.
    induction b1 as [C c1 | C rest1 IHrest1 a1];
      destruct b2 as [c2 | rest2 a2]; cbn in *.
    - inversion Hshape. reflexivity.
    - inversion Hshape.
    - inversion Hshape.
    - unfold monoid_op, Monoid_op_list in *.
      assert (Hleft := Hlist); apply list_app_inv_l2 in Hleft.
      rename Hlist into Hright;  apply list_app_inv_r2 in Hright.
      injection Hshape; clear Hshape; intro Hshape.
      subst. erewrite IHrest1; auto.
  Qed.

  Theorem shapeliness : forall A (t1 t2 : T A),
      shape t1 = shape t2 /\ tolist t1 = tolist t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    assert (hyp1' : (toBatch (A := unit) (A' := A) ∘ shape) t1 =
                      (toBatch (A := unit) (A' := A) ∘ shape) t2).
    { unfold compose, shape in *. now rewrite hyp1. }
    clear hyp1; rename hyp1' into hyp1.
    unfold shape in hyp1.
    rewrite toBatch_mapfst in hyp1.
    rewrite (tolist_through_runBatch A t1) in hyp2.
    rewrite (tolist_through_runBatch A t2) in hyp2.
    change (id t1 = id t2).
    rewrite id_through_runBatch.
    unfold compose. auto using shapeliness_tactical.
  Qed.

End shapeliness.

(** ** Elements of traversable functors *)
(******************************************************************************)
Section elements.

  Section Elements_Traverse.

    #[local] Instance Elements_Traverse {T} `{Traverse T} : Elements T :=
    fun A => foldMap (ret (T := subset)).

  End Elements_Traverse.

  Class Compat_Elements_Traverse
          (T : Type -> Type)
          `{Elements_inst : Elements T}
          `{Traverse_inst : Traverse T} : Prop :=
    compat_element_traverse :
      @element_of T Elements_inst =
        @element_of T (@Elements_Traverse T Traverse_inst).

  Context
    `{TraversableFunctor T}
     `{Map T}
     `{! Compat_Map_Traverse T}
     `{ToBatch T}
     `{! Compat_ToBatch_Traverse}.

  #[export] Instance Compat_Elements_Traverse_Self :
    @Compat_Elements_Traverse T Elements_Traverse _.
  Proof.
    reflexivity.
  Qed.

  Lemma element_of_to_foldMap
          `{Elements T}
          `{! Compat_Elements_Traverse T}:
    forall (A : Type),
      @element_of T _ A = foldMap (ret (T := subset)) (A := A).
  Proof.
    rewrite compat_element_traverse.
    reflexivity.
  Qed.

  Lemma in_to_foldMap
    `{Elements T}
    `{! Compat_Elements_Traverse T}:
    forall (A : Type) (t : T A),
    forall (a : A), a ∈ t = foldMap (op := Monoid_op_or)
                         (unit := Monoid_unit_false) (eq a) t.
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    change_left (evalAt a (foldMap (ret (T := subset)) t)).
    compose near t on left.
    rewrite (foldMap_morphism
               (subset A) Prop (ϕ := evalAt a)
               (ret (T := subset))).
    fequal. ext b. cbv. now propext.
  Qed.

  #[export] Instance Natural_Element_Traverse :
    Natural (@element_of T Elements_Traverse).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f.
    unfold element_of, Elements_Traverse.
    rewrite (foldMap_morphism (subset A) (subset B)).
    rewrite foldMap_map.
    rewrite (natural (ϕ := @ret subset _)).
    reflexivity.
  Qed.

  #[export] Instance Compat_Elements_Traverse_Tolist :
    @Compat_Elements_Tolist T (@Elements_Traverse T _)
                            (@Tolist_Traverse T _).
  Proof.
    hnf.
    unfold_ops @Elements_Traverse.
    unfold_ops @Elements_Tolist.
    unfold_ops @Tolist_Traverse.
    ext A.
    rewrite (foldMap_morphism (list A) (subset A)
                              (ϕ := @element_of list Elements_list A)).
    rewrite element_of_list_hom1.
    reflexivity.
  Qed.

  Context
    `{Elements T}
     `{! Compat_Elements_Traverse T}.

  (** *** Factoring through <<runBatch>> *)
  (******************************************************************************)
  Lemma element_through_runBatch1 : forall (A : Type),
      element_of = runBatch (const (A -> Prop))
                            (ret (T := subset) (A := A)) (T False) ∘ toBatch (A' := False).
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite foldMap_through_runBatch1.
    reflexivity.
  Qed.

  Lemma element_through_runBatch2 : forall (A tag : Type),
      element_of = runBatch (const (A -> Prop))
                            (ret (T := subset)) (T tag) ∘ toBatch (A' := tag).
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite (foldMap_through_runBatch2 A tag).
    reflexivity.
  Qed.

  (** ** Pointwise reasoning for operations *)
  (******************************************************************************)
  Lemma traverse_respectful :
    forall (G : Type -> Type)
      `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse f1 t = traverse f2 t.
  Proof.
    introv ? hyp.
    do 2 rewrite traverse_through_runBatch.
    rewrite (element_through_runBatch2 A B) in hyp.
    unfold compose in *.
    unfold ret in *.
    induction (toBatch t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros.
        apply hyp. now left.
      + apply hyp. now right.
  Qed.

  (** *** Corollaries *)
  (******************************************************************************)
  Corollary traverse_respectful_pure :
    forall (G : Type -> Type)
      `{Applicative G} `(f1 : A -> G A) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = pure a) -> traverse f1 t = pure t.
  Proof.
    intros.
    rewrite <- traverse_purity1.
    now apply traverse_respectful.
  Qed.

  Corollary traverse_respectful_map {A B} :
    forall (G : Type -> Type)
      `{Applicative G} (t : T A) (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure (g a)) -> traverse f t = pure (map g t).
  Proof.
    intros. rewrite <- (traverse_purity1 (G := G)).
    compose near t on right.
    rewrite traverse_map.
    apply (traverse_respectful G).
    assumption.
  Qed.

  Corollary traverse_respectful_id {A} :
    forall (t : T A) (f : A -> A),
      (forall a, a ∈ t -> f a = id a) -> traverse (G := fun A => A) f t = t.
  Proof.
    intros.
    change t with (pure (F := fun A => A) t) at 2.
    apply (traverse_respectful_pure (fun A => A)).
    assumption.
  Qed.

  Corollary map_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> map f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite map_to_traverse.
    rewrite map_to_traverse.
    apply (traverse_respectful (fun A => A)).
    assumption.
  Qed.

  #[export] Instance ContainerFunctor_Traverse :
    ContainerFunctor T.
  Proof.
    constructor.
    - rewrite compat_element_traverse.
      typeclasses eauto.
    - typeclasses eauto.
    - intros. now apply map_respectful.
  Qed.

End elements.

(** * Quantification over elements *)
(******************************************************************************)
Section quantification.

  Context
    `{TraversableFunctor T}
    `{! Elements T}
     `{! Compat_Elements_Traverse T}.

  #[local] Arguments foldMap T%function_scope M%type_scope op unit
   {H1} {A}%type_scope f%function_scope _ : rename.

  Definition Forall `(P : A -> Prop) : T A -> Prop :=
    @foldMap T _ Prop Monoid_op_and Monoid_unit_true A P.

  Definition Forany `(P : A -> Prop) : T A -> Prop :=
    @foldMap T _ Prop Monoid_op_or Monoid_unit_false A P.

  Lemma forall_iff `(P : A -> Prop) (t : T A) :
    Forall P t <-> forall (a : A), a ∈ t -> P a.
  Proof.
    unfold Forall.
    rewrite foldMap_through_runBatch1.
    rewrite element_through_runBatch1.
    unfold compose.
    induction (toBatch t).
    - cbn. split.
      + cbv. intuition.
      + cbv. intuition.
    - rewrite runBatch_rw2.
      rewrite runBatch_rw2.
      rewrite IHb.
      unfold ap.
      unfold_ops @Mult_const @Monoid_op_and.
      unfold_ops @Monoid_op_subset @Return_subset.
      unfold subset_add.
      firstorder subst; auto.
  Qed.

  Lemma forany_iff `(P : A -> Prop) (t : T A) :
    Forany P t <-> exists (a : A), a ∈ t /\ P a.
  Proof.
    unfold Forany.
    rewrite foldMap_through_runBatch1.
    rewrite element_through_runBatch1.
    unfold compose.
    induction (toBatch t).
    - cbn. split.
      + cbv. intuition.
      + cbv. firstorder.
    - rewrite runBatch_rw2.
      rewrite runBatch_rw2.
      rewrite IHb.
      unfold ap.
      unfold_ops @Mult_const @Monoid_op_or.
      unfold_ops @Monoid_op_subset @Return_subset.
      unfold subset_add.
      firstorder subst; auto.
  Qed.

End quantification.

(** * New length *)
(******************************************************************************)
Definition plength `{Traverse T}: forall {A}, T A -> nat :=
  fun A => foldMap (fun _ => 1).

(*
  Definition plength: forall {A}, T A -> nat :=
    fun A => traverse (B := False) (G := const nat) (fun _ => 1).
 *)

Section length.

  Context
    `{TraversableFunctor T} `{Map T}
     `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  Lemma plength_eq_length :
    forall {A} {B} (t: T A),
      plength t = length_Batch (toBatch (A' := B) t).
  Proof.
    intros.
    unfold plength.
    rewrite (foldMap_through_runBatch2 A B).
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn.
      rewrite IHb.
      unfold_ops @NaturalNumbers.Monoid_op_plus.
      lia.
  Qed.

  Lemma plength_eq_length': forall {A} (t: T A),
      length_Batch (toBatch (A' := False) t) = plength t.
  Proof.
    intros.
    symmetry.
    apply plength_eq_length.
  Qed.

  Lemma length_Batch_independent: forall `(t: T A) B C,
      length_Batch (toBatch (A' := B) t) =
        length_Batch (toBatch (A' := C) t).
  Proof.
    intros.
    rewrite length_Batch_spec.
    rewrite length_Batch_spec.
    compose near t on left.
    compose near t on right.
    rewrite <- traverse_through_runBatch.
    rewrite <- traverse_through_runBatch.
    rewrite (traverse_const2 _ B C).
    reflexivity.
  Qed.

End length.

(** * Deconstructing with refinement-type vectors *)
(******************************************************************************)
Section deconstruction.

  Context
    `{Traverse T}
    `{! Kleisli.TraversableFunctor.TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  Definition toContents_ {A B} (t: T A):
    Vector (length_Batch (toBatch (A' := B) t)) A :=
    Batch_to_Vector2 (toBatch t).

  Definition toMake_ {A} (t: T A) B:
    Vector (length_Batch (toBatch (A' := B) t)) B -> (T B) :=
    Batch_to_Make2 (toBatch t).

  Lemma tolist_toContents_ {A B} (t: T A):
    to_list A (toContents_ (B := B) t) = List.rev (tolist t).
  Proof.
    intros.
    unfold toContents_.
    rewrite (tolist_through_runBatch B).
    induction (toBatch t).
    - reflexivity.
    - rewrite runBatch_rw2.
      rewrite Batch_to_Vector2_rw2.
      cbn. (* hidden evaluation of Batch_length *)
      rewrite to_list_vcons.
      rewrite IHb.
      unfold_ops @Monoid_op_list.
      unfold_ops @Return_list.
      rewrite List.rev_unit.
      reflexivity.
  Qed.

  Lemma toMake_toContents {A} (t: T A):
    toMake_ t A (toContents_ t) = t.
  Proof.
    unfold toMake_.
    unfold toContents_.
    rewrite Batch_repr.
    compose near t on left.
    rewrite trf_extract.
    reflexivity.
  Qed.

  Lemma traverse_repr {A} (t: T A) {B} `{Applicative G} `(f: A -> G B):
    traverse f t =
      map (toMake_ t B) (traverse f (toContents_ t)).
  Proof.
    rewrite traverse_through_runBatch.
    unfold compose.
    rewrite <- VectorRefinement.runBatch_repr.
    reflexivity.
  Qed.

  Definition toContents {A} (t: T A):
    Vector (plength t) A :=
    coerce_Vector_length (length_Batch (toBatch (A' := False) t))
                         (plength t)
                         (plength_eq_length' t)
                         (toContents_ t).


  (*
  Goal forall `{Applicative G} A B C (t: T A) v1  (f: B -> G C),
      traverse f (toMake t B v1) =
        traverse f (toMake t B v1).
    intros.
    Check  (traverse (T := Vector (length_Batch (toBatch t))) f v1).
    About toBatch.
    (* G (Vector (length_Batch (toBatch t)) C) *)
    Check  map (F := G) (toMake t C).
    (*  G (Vector (length_Batch (toBatch t)) C) -> G (T C) *)
    Fail Check map (F := G) (toMake t C)
              (traverse (G := G) (T := Vector (length_Batch (toBatch t))) f v1).
  Abort.
   *)


Lemma traverse_cons_inj1:
  forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    `{! Applicative G} {A B} (f: A -> G B)
    (l1 l2: list A)
    (a1 a2: A),
    pure cons <⋆> f a1 <⋆> traverse f l1 =
      pure cons <⋆> f a2 <⋆> traverse f l2 ->
    True.
Proof.
  introv Happl Heq.
  induction l1.
  - cbn in Heq.
    induction l2.
Abort.

Lemma Vector_trav_eq1:
  forall (A: Type) (n: nat)
    (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    `{! Applicative G}
    {B : Type} (f : A -> G B)
    (v1 v2: Vector n A),
    (traverse f (proj1_sig v1) = traverse f (proj1_sig v2)) ->
    map (F := G) (@proj1_sig (list B) (fun l => length l = n))
        (traverse (G := G) (T := Vector n) f v1) =
      map (F := G) (@proj1_sig (list B) (fun l => length l = n)) (traverse (T := Vector n) f v2).
Proof.
  introv Happl; introv hyp.
  apply (Vector_induction2 A n
        (fun m v1 v2 =>
    (traverse f (proj1_sig v1) = traverse f (proj1_sig v2)) ->
    map (F := G) (@proj1_sig (list B) (fun l => length l = m))
        (traverse (G := G) (T := Vector m) f v1) =
      map (F := G) (@proj1_sig (list B) (fun l => length l = m))
          (traverse (T := Vector m) f v2))).
  - cbn. reflexivity.
  - clear hyp v1 v2.
    intros m a a' v v'.
    introv hyp1 hyp2.
    rewrite proj_vcons in *.
    rewrite proj_vcons in *.
    cbn in *.
    do 2 rewrite traverse_Vector_vcons.
    rewrite map_to_ap.
    do 2 rewrite <- ap4.
    do 3 rewrite ap2.
    rewrite map_to_ap.
    do 2 rewrite <- ap4.
    do 3 rewrite ap2.
Abort.

Lemma Vector_trav_eq1:
  forall (A: Type) (n: nat) (l1 l2 : list A)
    (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {B : Type} (f : A -> G B)
    (p1 : length l1 = n)
    (p2 : length l2 = n),
    (traverse f l1 = traverse f l2) ->
      traverse f (exist (fun l => length l = n) l1 p1) =
        traverse f (exist _ l2 p2).
Proof.
  intros.
  generalize dependent l2.
  generalize dependent l1.
Abort.

  (*
Lemma Vector_trav_eq_eq:
  forall (A: Type) (n: nat) (l1 l2 : list A)
    (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {B : Type} (f : A -> G B)
    (p1 : length l1 = n)
    (p2 : length l2 = n),
    (traverse f l1 = traverse f l2) <->
      traverse f (exist (fun l => length l = n) l1 p1) =
        traverse f (exist _ l2 p2).
Proof.
  dup.
  { intros.
    assert (Vector_induction2_alt:
  forall m (A: Type) (P: forall m, Vector m A -> Vector m A -> Prop)
    (IHnil: P 0 vnil vnil)
    (IHcons:
      forall m (a1 a2: A) (v1 v2: Vector m A),
        P m v1 v2 ->
        P (S m) (vcons m a1 v1) (vcons m a2 v2)),
  forall (v1 v2: Vector m A), P m v1 v2).
    { intros. apply Vector_induction2; eauto. }
    split.
    - intros.
      apply (Vector_induction2_alt n A
                                   (fun m v1 v2 =>
                                           traverse f v1 =
                                             traverse f v2)).
      + reflexivity.
      + intros.
        rewrite traverse_Vector_vcons.
        rewrite traverse_Vector_vcons.
        rewrite H8.
        admit.
Abort.
   *)

Lemma Vector_trav_eq: forall
    (A: Type) (n: nat)
    (v1 v2: Vector n A)
    (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {B : Type} (f : A -> G B),
    traverse f (proj1_sig v1) = traverse f (proj1_sig v2) ->
    traverse f v1 = traverse f v2.
Proof.
  introv hyp.
  destruct v1.
  destruct v2.
  (*
  erewrite <- Vector_trav_eq_eq.
  apply hyp.
Defined.
   *)
Abort.

End deconstruction.

(* I think this has been moved into <<Batch>>
(** * Deconstructing <<Batch A B C>> into shape and contents *)
(******************************************************************************)
Section deconstruction.

  #[local] Arguments Done {A B C}%type_scope _.
  #[local] Arguments Step {A B C}%type_scope _.

  Context {A B: Type}.

  Fixpoint Batch_to_contents {C} (b: Batch A B C):
    Vector (length_Batch b) A :=
    match b return (Vector (length_Batch b) A) with
    | Done c => vnil
    | Step rest a => vcons (length_Batch rest) a (Batch_to_contents rest)
    end.

  Print Batch_to_Vector2.
  Print Batch_to_Make2.

  #[program] Fixpoint Batch_to_makeFn {C} (b: Batch A B C):
    Vector (length_Batch b) B -> C :=
    match b return (Vector (length_Batch b) B -> C) with
    | Done c =>
        const c
    | Step rest a =>
        fun (v: Vector (S (length_Batch rest)) B) =>
          (_ (Batch_to_makeFn rest))
    end.

  Next Obligation.
    destruct (vuncons _ v).
    apply x.
    exact s. assumption.
  Defined.

End deconstruction.
*)


(** ** Elements of <<Batch>> *)
(******************************************************************************)
Require Import ContainerFunctor.

Import ContainerFunctor.Notations.
Import Applicative.Notations.

#[export] Instance Elements_Batch1 {B C}: Elements (BATCH1 B C) :=
  Elements_Traverse.

Section pw_Batch.

  Lemma foldMap_Batch_rw2: forall {A B C: Type} `{Monoid M}
      (f : A -> M) (a: A) (rest: Batch A B (B -> C)),
      foldMap (T := BATCH1 B C) f (rest ⧆ a) =
        foldMap f rest ● f a.
  Proof.
    intros.
    unfold foldMap.
    rewrite traverse_Batch_rw2.
    reflexivity.
  Qed.

  Definition element_of_Step1 {A B C:Type}:
    forall (a' : A) (rest: Batch A B (B -> C)),
      forall (a : A),
      element_of (F := BATCH1 B (B -> C)) rest a ->
      element_of (F := BATCH1 B C) (Step rest a') a.
  Proof.
    introv.
    unfold_ops @Elements_Batch1 @Elements_Traverse.
    introv Hin.
    change ((evalAt a ∘ foldMap (T := BATCH1 B (B -> C))
                    (ret (T := subset))) rest) in Hin.
    change ((evalAt a ∘ foldMap (T := BATCH1 B C)
                    (ret (T := subset))) (rest ⧆ a')).
    rewrite (foldMap_morphism
               (T := BATCH1 B (B -> C))
               _ _ (ϕ := evalAt a)) in Hin.
    rewrite (foldMap_morphism
               (T := BATCH1 B C)
               _ _ (ϕ := evalAt a)).
    rewrite foldMap_Batch_rw2.
    now left.
  Defined.

  Definition element_of_Step2 {A B C:Type}:
    forall (rest: Batch A B (B -> C)) (a: A),
      element_of (F := BATCH1 B C) (Step rest a) a.
  Proof.
    intros.
    unfold_ops @Elements_Batch1 @Elements_Traverse.
    change ((evalAt a ∘ foldMap (T := BATCH1 B C)
                    (ret (T := subset))) (rest ⧆ a)).
    rewrite (foldMap_morphism
               (T := BATCH1 B C)
               _ _ (ϕ := evalAt a)).
    rewrite foldMap_Batch_rw2.
    now right.
  Qed.

  Lemma element_of_Step_spec: forall `(b: Batch A B (B -> C)) a a',
      a' ∈ (b ⧆ a) = (a' ∈ b \/ a' = a).
  Proof.
    intros.
    rewrite in_to_foldMap.
    rewrite in_to_foldMap.
    rewrite foldMap_Batch_rw2.
    reflexivity.
  Qed.

  Definition sigMapP (A: Type) (P Q: A -> Prop) (Himpl: forall a, P a -> Q a):
    sig P -> sig Q :=
    fun σ => match σ with
          | exist _ a h => exist Q a (Himpl a h)
          end.

  Fixpoint elt_decorate
   {A B C: Type}
   (b : Batch A B C):
    Batch {a|element_of (F := BATCH1 B C) b a} B C :=
    match b with
    | Done c => Done c
    | Step rest a =>
        Step (map (F := BATCH1 B (B -> C))
                  (sigMapP A
                           (element_of (F := BATCH1 B (B -> C)) rest)
                           (element_of (F := BATCH1 B C) (Step rest a))
                           (element_of_Step1 a rest)
                  )
                  (elt_decorate rest))
             (exist _ a (element_of_Step2 rest a))
    end.


  Definition runBatch_pw
               {A B C} (G : Type -> Type)
               `{Applicative G}:
    forall (b: Batch A B C) `(f1 : {a | element_of (F := BATCH1 B C) b a} -> G B), G C.
  Proof.
    intros.
    induction b.
    - apply (pure c).
    - apply (ap G (A := B)).
      apply IHb.
      + intros [a' a'in].
        apply f1.
        exists a'.
        rewrite element_of_Step_spec.
        now left.
      + apply f1.
        exists a.
        rewrite element_of_Step_spec.
        now right.
  Defined.

End pw_Batch.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "f <◻> g" := (applicative_arrow_combine f g) (at level 60) : tealeaves_scope.
End Notations.
