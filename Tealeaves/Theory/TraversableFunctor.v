From Tealeaves Require Export
  Classes.Coalgebraic.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Theory.Batch
  Functors.List
  Functors.ProductFunctor
  Functors.Constant
  Functors.Identity
  Functors.ProductFunctor
  Misc.Prop.

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
    forall `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
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
    forall `{Applicative G} `(f1 : A -> G A) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = pure a) -> traverse f1 t = pure t.
  Proof.
    intros.
    rewrite <- traverse_purity1.
    now apply traverse_respectful.
  Qed.

  Corollary traverse_respectful_map {A B} :
    forall `{Applicative G} (t : T A) (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure (g a)) -> traverse f t = pure (map g t).
  Proof.
    intros. rewrite <- (traverse_purity1 (G := G)).
    compose near t on right.
    rewrite traverse_map.
    apply traverse_respectful.
    assumption.
  Qed.

  Corollary traverse_respectful_id {A} :
    forall (t : T A) (f : A -> A),
      (forall a, a ∈ t -> f a = id a) -> traverse (G := fun A => A) f t = t.
  Proof.
    intros.
    change t with (pure (F := fun A => A) t) at 2.
    apply (traverse_respectful_pure (G := fun A => A)).
    assumption.
  Qed.

  Corollary map_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> map f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite map_to_traverse.
    rewrite map_to_traverse.
    apply (traverse_respectful (G := fun A => A)).
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

Section length.

  Context
    `{TraversableFunctor T} `{Map T}
     `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  Lemma plength_eq_length :
    forall {A} {B} (t: T A),
     length_Batch (toBatch (A' := B) t) = plength t.
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
      plength t = length_Batch (toBatch (A' := False) t).
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
    `{! Compat_ToBatch_Traverse}
    `{! Elements T}
     `{! Compat_Elements_Traverse T}.

  Definition trav_contents {A} (t: T A):
    Vector (plength t) A :=
    let v : Vector (length_Batch (toBatch (A' := False) t)) A
      := Batch_contents (toBatch t)
    in coerce_Vector_length (plength_eq_length t) v.

  Definition trav_contents_list {A} (t: T A):
    Vector (plength t) A :=
    let v : Vector (length_Batch (toBatch (A' := False) t)) A
      := Batch_contents (toBatch t)
    in coerce_Vector_length (plength_eq_length t) v.

  Definition trav_make {A B} (t: T A):
    Vector (plength t) B -> T B :=
    (fun v =>
       let v' := coerce_Vector_length (eq_sym (plength_eq_length t)) v
       in Batch_make (toBatch t) v').

  Generalizable Variable v.

  (** ** Lemmas regarding <<trav_make>> *)
  (******************************************************************************)
  Section trav_make_lemmas.

    Context
      {A B : Type}.

    Lemma trav_make_sim1:
      forall (t : T A) `{v1 ~~ v2},
        trav_make (B := B) t v1 = trav_make t v2.
    Proof.
      intros.
      unfold trav_make.
      apply Batch_make_sim1.
      vector_sim.
    Qed.

    Lemma trav_make_sim2:
      forall `(t1 : T A) (t2: T A)
        `(v1: Vector (plength t1) B)
        `(v2: Vector (plength t2) B),
        t1 = t2 ->
        Vector_sim v1 v2 ->
        trav_make t1 v1 = trav_make t2 v2.
    Proof.
      intros.
      subst.
      now apply trav_make_sim1.
    Qed.

  End trav_make_lemmas.

  (** ** Miscellaneous *)
  (******************************************************************************)
  Section list.

    Lemma tolist_trav_contents `{t: T A}:
      Vector_to_list A (trav_contents t) = List.rev (tolist t).
    Proof.
      intros.
      unfold trav_contents.
      rewrite (tolist_through_runBatch False).
      generalize (plength_eq_length (B := False) t).
      intros Heq.
      generalize dependent (plength t).
      induction (toBatch (A' := False) t); intros n Heq.
      - reflexivity.
      - rewrite runBatch_rw2.
        rewrite Batch_contents_rw2.
        unfold Vector_to_list.
        rewrite <- coerce_Vector_contents.
        unfold length_Batch at 1. (* hidden *)
        rewrite proj_vcons.
        cbn.
        unfold_ops @Monoid_op_list.
        unfold_ops @Return_list.
        rewrite List.rev_unit.
        fequal.
        cbn in Heq.
        assert (Hlen: length_Batch b = (n -1)) by lia.
        specialize (IHb (n - 1) Hlen).
        change (fun a => a :: nil) with (@ret list _ A).
        cbn in IHb.
        change (@app A) with (@Monoid_op_list A).
        rewrite <- IHb.
        unfold Vector_to_list.
        rewrite <- coerce_Vector_contents.
        reflexivity.
    Qed.

    Lemma Batch_contents_tolist:
      forall {A B} (t: T A),
        Vector_to_list A (Batch_contents (toBatch (A' := B) t)) =
          List.rev (tolist t).
    Proof.
      intros.
      rewrite tolist_to_foldMap.
      rewrite (foldMap_through_runBatch2 A B).
      unfold compose.
      induction (toBatch t).
      - reflexivity.
      - cbn.
        rewrite Vector_to_list_vcons.
        rewrite IHb.
        unfold_ops @Monoid_op_list @Return_list.
        rewrite List.rev_unit.
        reflexivity.
    Qed.

    Lemma Batch_contents_toBatch_sim:
      forall {A B B'} (t: T A),
        Batch_contents
          (toBatch (A' := B) t) ~~
          Batch_contents (toBatch (A' := B') t).
    Proof.
      intros.
      unfold Vector_sim.
      change (proj1_sig ?v) with (Vector_to_list _ v).
      rewrite Batch_contents_tolist.
      rewrite Batch_contents_tolist.
      reflexivity.
    Qed.

    Lemma shape_toBatch_spec: forall (A B: Type) (t: T A),
        shape (toBatch (A' := B) t) =
          toBatch (A' := B) (shape t).
    Proof.
      intros.
      compose near t on right.
      unfold shape at 2.
      rewrite toBatch_mapfst.
      reflexivity.
    Qed.

    Lemma toBatch_shape:
      forall {A' B} `(t1: T A) (t2: T A'),
        shape t1 = shape t2 ->
        shape (F := BATCH1 B (T B))
              (toBatch (A' := B) t1) =
          shape (F := BATCH1 B (T B))
                (toBatch (A' := B) t2).
    Proof.
      introv Hshape.
      do 2 rewrite shape_toBatch_spec.
      rewrite Hshape.
      reflexivity.
    Qed.

    (** ** Batch_to_list *)
    (******************************************************************************)
    Section Batch.

      Definition Batch_to_list: forall `(b: Batch A B C), list A.
      Proof.
        intros. apply (tolist (F := BATCH1 B C) b).
      Defined.

      Lemma Batch_contents_list: forall `(b: Batch A B C),
          proj1_sig (Batch_contents b) = List.rev (Batch_to_list b).
      Proof.
        intros.
        induction b.
        - reflexivity.
        - cbn.
          rewrite proj_vcons.
          rewrite IHb.
          rewrite <- List.rev_unit.
          reflexivity.
      Qed.

      Lemma Batch_to_list_rw2 {A B C}: forall (b: Batch A B (B -> C)) (a: A),
          Batch_to_list (b ⧆ a) = Batch_to_list b ++ (a::nil).
      Proof.
        intros.
        cbn.
        reflexivity.
      Qed.

    End Batch.

  End list.

  (** ** Lens-like laws *)
  (******************************************************************************)
  Section lens_laws.

    (** *** get-put *)
    (******************************************************************************)
    Lemma trav_get_put `{t: T A}:
      trav_make t (trav_contents t) = t.
    Proof.
      unfold trav_make, trav_contents.
      enough (cut: Batch_make
                     (toBatch t)
                     (coerce eq_sym (plength_eq_length t)
                       in coerce (plength_eq_length (B := False) t)
                         in Batch_contents (toBatch t)) =
                     Batch_make (toBatch t) (Batch_contents (toBatch t))).
      rewrite cut.
      rewrite Batch_make_contents.
      compose near t.
      now rewrite trf_extract.
      { apply Batch_make_sim1.
        vector_sim.
        apply Batch_contents_toBatch_sim.
      }
    Qed.

    Lemma toBatch_trav_make {A A' B} {t: T A} {v: Vector (plength t) B}:
      toBatch (A' := A') (trav_make t v) =
        Batch_replace_contents
          (toBatch (A' := A') t)
          (coerce eq_sym (plength_eq_length t) in v).
    Proof.
      unfold trav_make.
      rewrite Batch_make_compose_rw1.
      rewrite Batch_replace_spec.
      apply Batch_make_sim2; vector_sim.
      compose near t.
      now rewrite <- trf_duplicate.
    Qed.

    (** *** put-get *)
    (******************************************************************************)
    Lemma trav_contents_make {A} {t: T A} {v: Vector (plength t) A}:
      trav_contents (trav_make t v) ~~ v.
    Proof.
      unfold trav_contents.
      vector_sim.
      rewrite toBatch_trav_make.
      rewrite Batch_put_get.
      vector_sim.
    Qed.

    (** *** put-put *)
    (******************************************************************************)
    Lemma trav_make_make
            `(t: T A) `(v: Vector (plength t) B)
            `(v1: Vector _ B')
            (v2: Vector _ B')
            (pf: v1 ~~ v2):
      trav_make (trav_make t v) v1 =
        trav_make t v2.
    Proof.
      unfold trav_make at 1.
      unfold trav_make at 7.
      apply Batch_make_sim3.
      - symmetry.
        rewrite toBatch_trav_make.
        apply Batch_shape_replace_contents.
      - vector_sim.
    Qed.

    Notation "'precoerce' Hlen 'in' F" :=
      (F ○ coerce_Vector_length Hlen)
        (at level 10, F at level 20).

    Lemma trav_same_shape
            `(t1: T A) `(t2: T A'):
      shape t1 = shape t2 ->
      forall B, trav_make (B := B) t1 ~!~ trav_make t2.
    Proof.
      intros.
      unfold trav_make.
      apply Vector_coerce_fun_sim_l'.
      apply Vector_coerce_fun_sim_r'.
      apply Batch_make_shape.
      apply toBatch_shape.
      assumption.
    Qed.

  End lens_laws.

  (** ** Representation theorems *)
  (******************************************************************************)
  Lemma traverse_repr:
    forall `{Applicative G} (A B: Type) (t: T A) (f: A -> G B),
      traverse f t =
        map (trav_make t) (forwards (traverse (mkBackwards ∘ f) (trav_contents t))).
  Proof.
    intros.
    rewrite traverse_through_runBatch.
    unfold compose.
    rewrite runBatch_repr2.
    unfold trav_make, trav_contents.
    rewrite (traverse_Vector_coerce _ _ _ (plength_eq_length t)).
    change_left (
        map (Batch_make (toBatch t))
            (map
               (fun v : Vector (plength t) B =>
                  coerce eq_sym (plength_eq_length (B := B) t) in v)
               (forwards
                  (traverse (mkBackwards ∘ f)
                            (coerce (plength_eq_length (B := B) t) in
                              Batch_contents (toBatch t)))))).
    compose near ((forwards
                     (traverse (mkBackwards ∘ f)
                               (coerce (plength_eq_length (B := B) t)
                                 in Batch_contents (toBatch t))))).
    rewrite (fun_map_map).
    fequal.
    fequal.
    fequal.
    apply Vector_eq.
    apply Vector_coerce_sim_l'.
    apply Vector_coerce_sim_r'.
    eapply Batch_contents_toBatch_sim.
  Qed.

  (** ** Lemmas regarding <<plength>> *)
  (******************************************************************************)
  Lemma plength_trav_make: forall `(t: T A) `(v: Vector _ B),
      plength t = plength (trav_make t v).
  Proof.
    intros.
    unfold plength at 1 2.
    do 2 change (fun (x:?X) => 1) with (const (A := X) 1).
    do 2 rewrite (foldMap_through_runBatch2 _ B).
    unfold compose.
    rewrite (@toBatch_trav_make A B B t v).
    rewrite <- (runBatch_const_contents (G := @const Type Type nat)).
    reflexivity.
  Qed.

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

End deconstruction.

#[export] Instance Elements_Vector {n}: Elements (Vector n).
unfold Vector.
intro X.
intros [l pf].
intro x.
exact (x ∈ l).
Defined.


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
Abort.

(** * Elements of <<Batch>> *)
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

Lemma list_plength_length: forall (A: Type) (l: list A),
    plength l = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - cbn. now rewrite IHl.
Qed.

#[export] Instance Compat_Elements_Traverse_List :
  @Compat_Elements_Traverse list Elements_list Traverse_list.
Proof.
  unfold Compat_Elements_Traverse.
  ext A l a.
  induction l.
  - cbn. reflexivity.
  - apply propositional_extensionality.
    autorewrite with tea_list tea_set.
    cbn.
    unfold_ops @Pure_const.
    unfold_ops @Monoid_op_subset.
    autorewrite with tea_set.
    rewrite IHl.
    firstorder.
Qed.
