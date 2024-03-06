From Tealeaves Require Export
  Classes.Coalgebraic.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Functors.List
  Functors.Vector
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

#[local] Generalizable Variables T G A B M ϕ.

(** * Theory of traversable functors *)
(******************************************************************************)
Section traversable_functor_theory.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  (** ** Lemmas for particular applicative functors *)
  (******************************************************************************)

  (** *** Cartesian product of applicative functors (F ◻ G) *)
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

  (** ** The <<foldmap>> operation *)
  (******************************************************************************)

  (* We define <<foldMap>> with a fresh <<T>> so we can specialize (T := list) later *)
  Definition foldMap {T : Type -> Type} `{Traverse T} `{op : Monoid_op M} `{unit : Monoid_unit M}
    {A : Type} (f : A -> M) : T A -> M := traverse (G := const M) (B := False) f.

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

  (* TODO Relocate the next two lemmas *)
  Lemma map_compose_const {F} `{Functor F} `{M : Type} :
    @Map_compose F (const M) _ _ = @Map_const (F M).
  Proof.
    ext A' B' f' t.
    unfold_ops @Map_compose @Map_const.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma mult_compose_const `{Applicative G} `{Monoid M} :
    @Mult_compose G (const M) _ _ _ = @Mult_const (G M) (Monoid_op_applicative G M).
  Proof.
    ext A' B' [m1 m2].
    reflexivity.
  Qed.

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

  (** ** <<tolist>> *)
  (******************************************************************************)
  Section tolist.

    #[export] Instance Tolist_Traverse {T} `{Traverse T} : Tolist T :=
    fun A => foldMap (ret (T := list)).

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

  (** ** Proof that traversable functors are shapely over lists *)
  (******************************************************************************)
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
      @Compat_Elements_Tolist T
        (@Elements_Traverse T _)
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

    (** * Pointwise reasoning for operations *)
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

  (*
  (** ** Quantification over elements *)
  (******************************************************************************)
  Section quantification.

    #[local] Arguments foldMap T%function_scope M%type_scope op unit
      {H1} {A}%type_scope f%function_scope _ : rename.

    Definition Forall `(P : A -> Prop) : T A -> Prop :=
      @foldMap T _ Prop Monoid_op_and Monoid_unit_true A P.

    Definition Forany `(P : A -> Prop) : T A -> Prop :=
      @foldMap T _ Prop Monoid_op_or Monoid_unit_false A P.

    Lemma forall_iff `(P : A -> Prop) (t : T A) :
      Forall P t <-> forall (a : A), a ∈ t -> P a.
    Proof.
      unfold_ops @Elements_Tolist.
      unfold compose at 1.
      rewrite <- forall_iff.
      unfold Forall_List.
      rewrite <- foldMap_list_eq.
      compose near t on right;
        rewrite <- foldMap_through_tolist.
      reflexivity.
    Qed.

    Lemma forany_iff `(P : A -> Prop) (t : T A) :
      Forany P t <-> exists (a : A), a ∈ t /\ P a.
    Proof.
      unfold_ops @Elements_Tolist.
      unfold compose at 1.
      rewrite <- forany_iff.
      unfold Forany.
      unfold Forany_List.
      rewrite <- foldMap_list_eq.
      compose near t on right;
        rewrite <- foldMap_through_tolist.
      reflexivity.
    Qed.

  End quantification.
  *)

End traversable_functor_theory.

(*
Module monomorphic.

  Section aksdjflasdf.

    Context
      T (A:Type) G `{Applicative G}
        `{Kleisli.TraversableFunctor.TraversableFunctor T}.

    Definition toLen: forall (t : T A), nat.
      intro t.
      exact (length_Batch (B := A) (toBatch t)).
    Defined.

    Definition toMake: forall (t : T A),
        Vector.t A (toLen t) -> (T A).
    Proof.
      intros t B.
      unfold toLen.
      apply (Batch_to_makeFn (toBatch t)).
      assumption.
    Defined.

    Definition toContents: forall (t : T A),
        Vector.t A (toLen t).
    Proof.
      intro t.
      unfold toLen.
      apply (Batch_to_contents (toBatch t)).
    Defined.

    Lemma repr: forall `(t : T A),
        t = toMake t (toContents t).
    Proof.
      intros.
      unfold toMake, toContents.
      change t with (id t) at 1.
      rewrite <- trf_extract.
      unfold compose at 1.
      eapply (
          Batch_ind A A
                    (fun (T1 : Type) (b0 : Batch A A T1) =>
                       extract_Batch b0 =
                         Batch_to_makeFn b0 (Batch_to_contents b0))).
      - reflexivity.
      - intros.
        rewrite Batch_to_makeFn_rw2.
        rewrite Batch_to_contents_rw2.
        cbn.
        rewrite H5.
        reflexivity.
    Qed.

  End aksdjflasdf.

End monomorphic.
*)

Section polymorphic.

  Context
    T G
      `{Applicative G}
      `{Kleisli.TraversableFunctor.TraversableFunctor T}
      `{Map T}
      `{ToBatch T}
      `{! Compat_Map_Traverse T}
      `{! Compat_ToBatch_Traverse}.

  Lemma toBatch_mapsnd : forall (A B B' : Type) (f : B -> B'),
      mapsnd_Batch B B' f ∘ toBatch (A := A) (A' := B') =
        map (F := Batch A B) (map f) ∘ toBatch (A := A) (A' := B).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism
               (G1 := Batch A B')
               (ϕ := fun A => mapsnd_Batch B B' f)).
    rewrite (map_traverse).
    rewrite ret_dinatural.
    reflexivity.
  Qed.

  Definition toLen_poly {A} (B: Type): forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := B) (toBatch t)).
  Defined.

  Definition toLen {A}: forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := False) (toBatch t)).
  Defined.

  Lemma length_Batch1: forall (A B: Type) (t : T A),
      length_Batch (B := B) (toBatch t) =
        length_Batch (B := B) (toBatch (map (fun _ => tt) t)).
  Proof.
    intros.
    rewrite (batch_length_mapfst (fun _ => tt)
                                 (@toBatch T _ A B t)).
    compose near t on left.
    rewrite <- (toBatch_mapfst (T := T) A unit (fun _ => tt) B).
    unfold compose.
    reflexivity.
  Qed.

  Lemma length_Batch2: forall (A B B': Type) (t : T A),
      length_Batch (B := B) (toBatch t) =
        length_Batch (B := B') (toBatch t).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite toBatch_to_traverse.
    rewrite batch_length1.
    rewrite batch_length1.
    compose near t.
    rewrite (trf_traverse_morphism
               (G1 := Batch A B)
               (G2 := const (list A))).
    rewrite (trf_traverse_morphism
               (G1 := Batch A B')
               (G2 := const (list A))).
    rewrite runBatch_batch; try typeclasses eauto.
    rewrite runBatch_batch; try typeclasses eauto.
    rewrite <- (traverse_const1 (M := list A) (T := T) B).
    rewrite <- (traverse_const1 (M := list A) (T := T) B').
    reflexivity.
  Defined.

  Lemma contents_Batch1: forall (A B B': Type) (t : T A),
      Batch_to_contents (B := B) (toBatch t) =
        @eq_rect nat (@length_Batch A B' (T B') (@toBatch T H6 A B' t))
                 (fun n : nat => Vector.t A n)
                 (Batch_to_contents (B := B') (toBatch t))
                 (@length_Batch A B (T B) (@toBatch T H6 A B t))
                 (length_Batch2 A B' B t).
  Proof.
  Abort.

  Lemma toLen_poly1: forall A B,
      toLen_poly (A := A) B =
        toLen_poly (A := unit) B ∘ map (fun _ => tt).
  Proof.
    intros.
    ext t.
    unfold toLen_poly.
    rewrite length_Batch1.
    reflexivity.
  Qed.

  Lemma toLen_poly2: forall A B B', toLen_poly (A := A) B = toLen_poly B'.
  Proof.
    intros.
    ext t.
    unfold toLen_poly.
    erewrite length_Batch2.
    reflexivity.
  Qed.

  Corollary toLen_poly_canonical: forall (A B: Type) (t: T A),
      toLen t = toLen_poly B t.
  Proof.
    intros. rewrite (toLen_poly2 A B False).
    reflexivity.
  Qed.

  Definition toMake_poly {A}: forall (t : T A) (B C: Type),
      Vector.t B (toLen_poly C t) -> (T B).
  Proof.
    intros t B C.
    rewrite (toLen_poly2 A C B).
    apply (Batch_to_makeFn (toBatch t)).
  Defined.

  Definition toMake_mono {A}: forall (t : T A) (B: Type),
      Vector.t B (toLen_poly B t) -> (T B).
  Proof.
    intros t B.
    apply (Batch_to_makeFn (toBatch t)).
  Defined.

  Definition toMake {A}: forall (t : T A) (B: Type),
      Vector.t B (toLen t) -> (T B).
  Proof.
    intros t B.
    unfold toLen.
    pose (lemma:= toMake_poly t B False).
    unfold toLen_poly in lemma.
    assumption.
  Defined.

  (*
  Lemma toMake_poly1: forall (A: Type) (t : T A) (B C C': Type),
      toMake_poly t B C =
        toMake_poly t B C'.
    Restart.
    intros t B.
    apply (toMake_poly t B False).
   *)

  Definition toContents_poly {A}: forall (B: Type) (t : T A),
      Vector.t A (toLen_poly B t).
  Proof.
    intros B t.
    apply (Batch_to_contents (toBatch t)).
  Defined.

  Definition toContents {A}: forall (t : T A),
      Vector.t A (toLen t).
  Proof.
    intro t.
    apply (Batch_to_contents (toBatch t)).
  Defined.

  Definition toContents_generic {A}:
    forall (t : T A) (n : nat) (Heq: n = toLen t),
      Vector.t A n.
  Proof.
    intros.
    rewrite Heq.
    apply (Batch_to_contents (toBatch t)).
  Defined.

  Definition toMake_generic {A}:
    forall (t : T A) (B: Type) (n : nat) (Heq: n = toLen t),
      Vector.t B n -> (T B).
  Proof.
    intros t B.
    unfold toLen.
    introv Heq.
    rewrite Heq.
    pose (lemma:= toMake_poly t B False).
    unfold toLen_poly in lemma.
    assumption.
  Defined.

  Lemma toLen_toMake_poly {A B C D E}:
    forall (t : T A) (v: Vector.t B (toLen_poly C t)),
      toLen_poly D (toMake_poly t B C v) = toLen_poly E (toMake_poly t B C v).
  Proof.
    intros.
    rewrite (toLen_poly2 B D E).
    reflexivity.
  Qed.

  Lemma traverse_repr {A}: forall `(t : T A) B (f : A -> G B),
      traverse f t = pure (toMake_mono t B) <⋆>
                       (traverse (T := VEC (toLen_poly B t)) f
                                 (toContents_poly B t)).
  Proof.
    intros.
    rewrite traverse_through_runBatch.
    unfold compose.
    rewrite runBatch_repr.
    reflexivity.
  Qed.

  Lemma repr {A}: forall `(t : T A),
      t = toMake_mono t A (toContents_poly A t).
  Proof.
    intros.
    unfold toMake, toContents.
    change t with (id t) at 1.
    rewrite <- trf_extract.
    unfold compose at 1.
    eapply (
        Batch_ind A A
                  (fun (T1 : Type) (b0 : Batch A A T1) =>
                     extract_Batch b0 =
                       Batch_to_makeFn b0 (Batch_to_contents b0))).
    - reflexivity.
    - introv Heq.
      intros.
      rewrite Batch_to_makeFn_rw2.
      rewrite Batch_to_contents_rw2.
      cbn.
      rewrite Heq.
      reflexivity.
  Qed.

  (*
  Lemma toLen_toMake_generic {A B}:
    forall (t : T A)
      (n m : nat)
      (v1: Vector.t B m)
      (v2: Vector.t B m)
      (Heq: n = m),
      toLen (toMake_generic t B n Heq v1) =
        toLen (toMake_generic t B n Heq v2).
  Proof.
    intros.
    generalize dependent n.
    apply (Vector.rect2
             (P := fun n =>
    induction v.
    - replace (@toLen A t) with 0.
      assert (
      destruct Heq.
    unfold toMake_generic
    cbn.
   *)

  Lemma toLen_toMake {A B}:
    forall (t : T A) (v: Vector.t B (toLen_poly B t)),
      toLen (toMake_mono t B v) = toLen t.
  Proof.
    intros.
    Search toLen.
    unfold toLen.
    rewrite batch_length1.
    rewrite batch_length1.
    compose near t.
    rewrite <- (foldMap_through_runBatch2
                 A False (M := list A)
                 (ret (T := list))
              ).
    compose near (toMake_mono t B v).
    rewrite <- (foldMap_through_runBatch2
                 B False (M := list B)
                 (ret (T := list))
              ).
  Admitted.

End polymorphic.

From Tealeaves Require Import
               Misc.NaturalNumbers
               Classes.Kleisli.TraversableMonad.

Lemma length_foldMap: forall `(l: list A),
    length l = foldMap (fun _ => 1) l.
Proof.
  intros. induction l.
  - reflexivity.
  - rewrite foldMap_list_eq.
    rewrite foldMap_list_cons.
    cbn. rewrite IHl.
    rewrite <- foldMap_list_eq.
    reflexivity.
Qed.

Lemma list_toLen: forall (A B: Type) (l: list A),
    length l = toLen_poly list B l.
Proof.
  intros.
  rewrite length_foldMap.
  unfold toLen_poly.
  rewrite foldMap_to_traverse1.
  rewrite traverse_through_runBatch.
  unfold compose.
  rewrite (length_Batch2 list A B False).
  rewrite length_Batch_spec.
  reflexivity.
Qed.

Lemma toMake_helper: forall A B (l:list A) (l' : Vector.t B (toLen_poly list B l)),
    toMake_mono list l B l' = Vector.to_list l'.
Proof.
  intros.
  assert (l = Vector.to_list (toContents list l)).
  { intros.
    induction l.
    - reflexivity.
    - Check toContents list (a :: l).
Abort.

Lemma length_helper: forall A B (l:list A) (l' : Vector.t B (toLen list l)),
    length (toMake list l B l') = length l.
Proof.
  intros.
  rewrite (repr list l) at 2.
Admitted.


Lemma length_helper_mono: forall A B (l:list A) (l' : Vector.t B (toLen_poly list B l)),
    length (toMake_mono list l B l') = length l.
Proof.
  intros.
Admitted.


(** * Element-wise operations *)
(******************************************************************************)
Require Import ContainerFunctor.

Import ContainerFunctor.Notations.
Import Applicative.Notations.

#[export] Instance Elements_Batch1 {B C}: Elements (BATCH1 B C) :=
  Elements_Traverse.

Section pw.

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

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}.

  Existing Instance Elements_Traverse.

  Definition traverse_pw
               {A B} (G : Type -> Type)
               `{Applicative G} : forall (t: T A) `(f1 : {a | a ∈ t} -> G B), G (T B).
  Proof.
    intro t.
    change t with (id t).
    rewrite id_through_runBatch.
    unfold compose.
    destruct (@toBatch T _ A A t).
    intro. cbn in f1.
    -
  Abort.

End pw.

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

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "f <◻> g" := (applicative_arrow_combine f g) (at level 60) : tealeaves_scope.
End Notations.
