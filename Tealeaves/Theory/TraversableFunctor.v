From Tealeaves Require Export
  Classes.Kleisli.TraversableFunctor
  Classes.Coalgebraic.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Functors.List
  Functors.ProductFunctor
  Functors.Constant
  Functors.Identity
  Functors.ProductFunctor
  Misc.Prop.

Import Subset.Notations.
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
    `{TraversableFunctorFull T}.

  (** * Interaction with <<pure>> *)
  (******************************************************************************)
  Theorem traverse_purity1 :
    forall `{Applicative G},
      `(traverse (G := G) pure = @pure G _ (T A)).
  Proof.
    intros.
    change (@pure G _ A) with (@pure G _ A ∘ id).
    rewrite <- (trf_traverse_morphism (G1 := fun A => A) (G2 := G)).
    rewrite trf_traverse_id.
    reflexivity.
  Qed.

  Lemma traverse_purity2 :
    forall `{Applicative G2}
      `{Applicative G1}
      `(f : A -> G1 B),
      traverse (G := G2 ∘ G1) (pure (F := G2) ∘ f) = pure (F := G2) ∘ traverse f.
  Proof.
    intros.
    assert (ApplicativeMorphism G1 (G2 ∘ G1) (@pure G2 _ ○ G1)).
    - change G1 with ((fun X => X) ∘ G1) at 1.
      change H6 with (Map_compose (fun X => X) G1) at 1.
      change H7 with (@pure G1 _) at 1.
      rewrite <- (Pure_compose_identity2 G1).
      change H8 with (@mult G1 _) at 1.
      rewrite <- (Mult_compose_identity2 G1).
      apply (ApplicativeMorphism_parallel_left (fun X => X) G1 G2 (ϕ1 := @pure G2 _)).
    - rewrite (trf_traverse_morphism (T := T) f
                 (G1 := G1) (G2 := G2 ∘ G1) (ϕ := (fun A => @pure G2 _ (G1 A)))).
      reflexivity.
  Qed.

  (** * Lemmas for particular applicative functors *)
  (******************************************************************************)

  (** ** Cartesian product of applicative functors (F ◻ G) *)
  (******************************************************************************)
  Definition applicative_arrow_combine {F G A B} `(f : A -> F B) `(g : A -> G B) : A -> (F ◻ G) B :=
    fun a => product (f a) (g a).

  #[local] Notation "f <◻> g" := (applicative_arrow_combine f g) (at level 60) : tealeaves_scope.

  Section traversable_product.

    #[local] Arguments traverse (T)%function_scope {Traverse}
      G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Variables
      (A B : Type)
        (f : A -> G1 B)
        (g : A -> G2 B).

    Lemma traverse_product1 : forall (t : T A),
        pi1 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G1 f t.
    Proof.
      intros.
      pose (ApplicativeMorphism_pi1 G1 G2).
    compose near t on left.
    now rewrite trf_traverse_morphism.
  Qed.

  Lemma traverse_product2 : forall (t : T A),
    pi2 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G2 g t.
  Proof.
    intros. pose (ApplicativeMorphism_pi2 G1 G2).
    compose near t on left.
    now rewrite trf_traverse_morphism.
  Qed.

  Theorem traverse_product_spec :
    traverse T (G1 ◻ G2) (f <◻> g) = (traverse T G1 f) <◻> (traverse T G2 g).
  Proof.
    intros.
    ext t.
    unfold applicative_arrow_combine at 2.
    erewrite <- traverse_product1.
    erewrite <- traverse_product2.
    rewrite <- product_eta.
    reflexivity.
  Qed.

(* Theorem dist_combine : forall (t : T A),
    dist T (G1 ◻ G2) (map T (f <◻> g) t) =
    product (traverse T G1 f t) (traverse T G2 g t).
  Proof.
    intros. compose near t on left.
    erewrite <- (dist_combine1).
    erewrite <- (dist_combine2).
    now rewrite <- product_eta.
  Qed.
 *)

  End traversable_product.

  (** ** Constant applicative functors *)
  (******************************************************************************)
  Section constant_applicatives.

    Context
      `{Monoid M}.

    Lemma traverse_const1: forall {A : Type} (B : Type) `(f : A -> M),
        traverse (G := const M) (B := False) f = traverse (G := const M) (B := B) f.
    Proof.
      intros.
      change_left (map (F := const M) (A := T False) (B := T B) (map (F := T) (A := False) (B := B) exfalso)
                     ∘ traverse (T := T) (G := const M) (B := False) (f : A -> const M False)).
      rewrite (map_traverse T (const M)).
      reflexivity.
    Qed.

    Lemma traverse_const2: forall {A : Type} (f : A -> M) (fake1 fake2 : Type),
        traverse (G := const M) (B := fake1) f = traverse (G := const M) (B := fake2) f.
    Proof.
      intros.
      rewrite <- (traverse_const1 fake1).
      rewrite (traverse_const1 fake2).
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
  Lemma foldMap_to_traverse1 (M : Type) `{Monoid M} : forall `(f : A -> M),
      foldMap (T := T) f = traverse (G := const M) (B := False) f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_to_traverse2 (M : Type) `{Monoid M} : forall (fake : Type) `(f : A -> M),
      foldMap f = traverse (G := const M) (B := fake) f.
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    rewrite (traverse_const1 fake f).
    reflexivity.
  Qed.

  (** *** As a special case of <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMap_to_runBatch1 (A : Type) `{Monoid M} : forall `(f : A -> M),
      foldMap f = runBatch (const M) f (T False) ∘ toBatch T A False.
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    rewrite (traverse_to_runBatch (G := const M)).
    reflexivity.
  Qed.

  Lemma foldMap_to_runBatch2 `{Monoid M} : forall (A fake : Type) `(f : A -> M),
      foldMap f = runBatch (const M) f (T fake) ∘ toBatch T A fake.
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    change (fun _ : Type => M) with (const (A := Type) M).
    rewrite (traverse_const1 fake).
    rewrite (traverse_to_runBatch (G := const M)).
    reflexivity.
  Qed.

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma foldMap_traverse `{Monoid M} (G : Type -> Type) {B : Type} `{Applicative G} :
    forall `(g : B -> M) `(f : A -> G B),
      map (A := T B) (B := M) (foldMap g) ∘ traverse f =
        foldMap (map g ∘ f).
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    rewrite (trf_traverse_traverse (T := T) (G1 := G) (G2 := const M) (B := B) (C := False)).
    rewrite (foldMap_to_traverse1 (G M)).
    (* TODO abstract this step *)
    assert (hidden1 : @Map_compose G (const M) _ _ = @Map_const (G M)).
    { ext A' B' f' t.
      unfold_ops @Map_compose @Map_const.
      rewrite (fun_map_id (F := G)).
      reflexivity. }
    assert (hidden2 : @Mult_compose G (const M) _ _ _ = @Mult_const (G M) (Monoid_op_applicative G M)).
    { ext A' B' [m1 m2].
      reflexivity. }
    rewrite hidden1, hidden2.
    reflexivity.
  Qed.

  (** *** Composition with <<map>> *)
  (******************************************************************************)
  Corollary foldMap_map `{Monoid M} : forall `(g : B -> M) `(f : A -> B),
      foldMap g ∘ map f = foldMap (g ∘ f).
  Proof.
    intros.
    rewrite (trff_map_to_traverse (T := T)).
    change (foldMap g) with (map (F := fun A => A) (A := T B) (B := M) (foldMap g)).
    now rewrite (foldMap_traverse (fun X => X)).
  Qed.

  (** *** Homomorphism law *)
  (******************************************************************************)
  Lemma foldMap_morphism (M1 M2 : Type) `{morphism : Monoid_Morphism M1 M2 ϕ} : forall `(f : A -> M1),
      ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
  Proof.
    intros.
    inversion morphism.
    rewrite (foldMap_to_traverse1 M1).
    change ϕ with (const ϕ (T False)).
    rewrite (trf_traverse_morphism (T := T) (G1 := const M1) (G2 := const M2)).
    reflexivity.
  Qed.

  (** ** <<tolist>> *)
  (******************************************************************************)
  Section tolist.

    #[export] Instance Tolist_Traverse `{Traverse T} : Tolist T :=
    fun A => foldMap (ret (T := list)).

    #[export] Instance Natural_Tolist_Traverse : Natural (@tolist T _).
    Proof.
      constructor; try typeclasses eauto.
      intros. unfold_ops @Tolist_Traverse.
      rewrite (foldMap_morphism (list A) (list B)).
      rewrite foldMap_map.
      rewrite (natural (ϕ := @ret list _)).
      reflexivity.
    Qed.

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

    Lemma tolist_to_foldMap : forall (A : Type),
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

    Corollary tolist_to_runBatch {A : Type} (tag : Type) `(t : T A) :
      tolist t =
        runBatch (const (list A))
          (ret (T := list) : A -> const (list A) tag)
          (T tag) (toBatch T A tag t).
    Proof.
      rewrite (tolist_to_traverse2 A tag).
      now rewrite (traverse_to_runBatch (G := const (list A))).
    Qed.

    Corollary foldMap_to_tolist `{Monoid M} : forall (A : Type) (f : A -> M),
        foldMap f = foldMap (T := list) f ∘ tolist.
    Proof.
      intros.
      rewrite tolist_to_foldMap.
      rewrite foldMap_list_eq.
      rewrite (foldMap_morphism (list A) M).
      fequal. ext a. cbn. rewrite monoid_id_l.
      reflexivity.
    Qed.

  End tolist.

  (** ** Elements of traversable functors *)
  (******************************************************************************)
  Section elements.

    Lemma element_to_foldMap1 : forall (A : Type),
        element_of (F := T) (A := A) = foldMap (ret (T := subset)).
    Proof.
      intros.
      unfold_ops @Elements_Tolist.
      rewrite foldMap_to_tolist.
      rewrite foldMap_list_elements1.
      rewrite foldMap_list_eq.
      reflexivity.
    Qed.

    Lemma element_to_foldMap2 : forall (A : Type) (a : A) (t : T A),
        element_of t a = foldMap (op := or) (unit := False) (eq a) t.
    Proof.
      intros.
      unfold_ops @Elements_Tolist.
      rewrite foldMap_to_tolist.
      unfold compose.
      rewrite foldMap_list_elements2.
      rewrite foldMap_list_eq.
      reflexivity.
    Qed.

    (* Relate elements to those obtained by enumeration *)
    (* Note: <<el list A>> (like <<el T A>>) is provided by <<Toset_Traverse>> *)
    Lemma element_to_tolist : forall (A : Type),
        element_of (A := A) = element_of ∘ tolist.
    Proof.
      reflexivity.
    Qed.

    Lemma in_iff_in_tolist : forall (A : Type) (a : A) (t : T A),
        a ∈ t <-> a ∈ tolist t.
    Proof.
      intros.
      rewrite element_to_tolist.
      reflexivity.
    Qed.

    Lemma element_to_toBatch1 : forall (A : Type),
        element_of = runBatch (const (A -> Prop)) (ret (T := subset) (A := A)) (T False) ∘ toBatch T A False.
    Proof.
      intros.
      rewrite element_to_foldMap1.
      rewrite (foldMap_to_runBatch1 _).
      reflexivity.
    Qed.

    Lemma element_to_toBatch2 : forall (A tag : Type),
        element_of = runBatch (const (A -> Prop)) (ret (T := subset)) (T tag) ∘ toBatch T A tag.
    Proof.
      intros.
      rewrite element_to_foldMap1.
      rewrite (foldMap_to_runBatch2 A tag).
      reflexivity.
    Qed.

    Theorem in_map_iff :
      forall (A B : Type) (f : A -> B) (t : T A) (b : B),
        b ∈ map f t <-> exists (a : A), a ∈ t /\ f a = b.
    Proof.
      intros.
      rewrite element_to_foldMap2.
      compose near t on left.
      rewrite foldMap_map.
      rewrite element_to_tolist.
      unfold compose at 2.
      rewrite <- (ContainerFunctor.forany_iff ((fun a => f a = b))).
      unfold Forany.
      rewrite <- foldMap_list_eq.
      rewrite foldMap_to_tolist.
      unfold compose; cbn.
      replace (eq b ○ f) with (fun a => f a = b).
      - reflexivity.
      - ext x. propext; auto.
    Qed.

  End elements.

  (** * Quantification over elements *)
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
      rewrite <- (ContainerFunctor.forall_iff).
      unfold ContainerFunctor.Forall.
      rewrite <- foldMap_list_eq.
      compose near t on right;
        rewrite <- foldMap_to_tolist.
      reflexivity.
    Qed.

    Lemma forany_iff `(P : A -> Prop) (t : T A) :
      Forany P t <-> exists (a : A), a ∈ t /\ P a.
    Proof.
      unfold_ops @Elements_Tolist.
      unfold compose at 1.
      rewrite <- (ContainerFunctor.forany_iff).
      unfold ContainerFunctor.Forany.
      rewrite <- foldMap_list_eq.
      compose near t on right;
        rewrite <- foldMap_to_tolist.
      reflexivity.
    Qed.

  End quantification.

  (** ** Proof that traversable functors are shapely over lists *)
  (******************************************************************************)
  Lemma shapeliness_tactical : forall (A : Type) (b1 b2 : Batch A A (T A)),
      runBatch (const (list A)) (ret (T := list)) _ b1 = runBatch (const (list A)) (ret (T := list) (A := A)) _ b2 ->
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
    assert (hyp1' : (toBatch T unit A ∘ shape) t1 = (toBatch T unit A ∘ shape) t2).
    { unfold compose, shape in *. now rewrite hyp1. }
    clear hyp1; rename hyp1' into hyp1.
    unfold shape in hyp1.
    rewrite toBatch_mapfst in hyp1.
    rewrite (tolist_to_runBatch A t1) in hyp2.
    rewrite (tolist_to_runBatch A t2) in hyp2.
    change (id t1 = id t2).
    rewrite id_to_runBatch.
    unfold compose. auto using shapeliness_tactical.
  Qed.

  (** * Pointwise reasoning for operations *)
  (******************************************************************************)
  Lemma traverse_respectful :
    forall (G : Type -> Type)
      `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse f1 t = traverse f2 t.
  Proof.
    introv ? hyp.
    do 2 rewrite traverse_to_runBatch.
    rewrite (element_to_toBatch2 A B) in hyp.
    unfold compose in *.
    induction (toBatch T A B t).
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
    rewrite (traverse_map T G).
    apply (traverse_respectful G).
    assumption.
  Qed.

  Corollary map_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> map f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite trff_map_to_traverse.
    apply (traverse_respectful (fun A => A)).
    assumption.
  Qed.

  (** *** Identity laws *)
  (******************************************************************************)
  Corollary traverse_respectful_id {A} :
    forall (G : Type -> Type)
      `{Applicative G} (t : T A) (f : A -> G A),
      (forall a, a ∈ t -> f a = pure a) -> traverse f t = pure t.
  Proof.
    intros. rewrite <- traverse_purity1.
    now apply traverse_respectful.
  Qed.

  Corollary map_respectful_id : forall `(f1 : A -> A) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = a) -> map f1 t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (fun_map_id (F := T)).
    apply map_respectful.
    assumption.
  Qed.

End traversable_functor_theory.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "f <◻> g" := (applicative_arrow_combine f g) (at level 60) : tealeaves_scope.
End Notations.
