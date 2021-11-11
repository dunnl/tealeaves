From Tealeaves Require Export
     Singlesorted.Classes.Functor
     Singlesorted.Classes.Applicative
     Singlesorted.Classes.ListableFunctor
     Singlesorted.Functors.Constant.

Import List.ListNotations.
#[local] Open Scope list_scope.

Import Functor.Notations.
Import SetlikeFunctor.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

(** * Traversable functors *)
(******************************************************************************)
Section TraversableFunctor_operation.

  Context
    (F : Type -> Type).

  Class Dist :=
    dist : forall (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}, F ○ G ⇒ G ○ F.

End TraversableFunctor_operation.

Section TraversableFunctor.

  Context
    (F : Type -> Type)
    `{Functor F}
    `{Dist F}.

  Class TraversableFunctor :=
    { trav_functor :> Functor F;
      dist_natural : forall `{Applicative G} `(f : A -> B),
          fmap (G ∘ F) f ∘ dist F G A = dist F G B ∘ fmap (F ∘ G) f;
      dist_morph : forall `{ApplicativeMorphism G1 G2 ϕ} A,
          dist F G2 A ∘ fmap F (ϕ A) = ϕ (F A) ∘ dist F G1 A;
      dist_unit :
        `(dist F (fun A => A) A = id);
      dist_linear : forall `{Applicative G1} `{Applicative G2},
          `(dist F (G1 ∘ G2) A = fmap G1 (dist F G2 A) ∘ dist F G1 (G2 A));
    }.

End TraversableFunctor.

#[local] Notation "'δ'" := (dist).

(* Mark the type argument implicit *)
Arguments dist F%function_scope {Dist} G%function_scope {H H0 H1} {A}%type_scope.

(** ** Distribution-respecting natural transformations *)
(******************************************************************************)
Section TraversableMorphism.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  Class TraversableMorphism (ϕ : T ⇒ U) :=
    { trvmor_trv_F : TraversableFunctor T;
      trvmor_trv_G : TraversableFunctor U;
      trvmor_nat :> Natural ϕ;
      trvmor_hom : forall `{Applicative G},
          `(fmap G (ϕ A) ∘ dist T G = dist U G ∘ ϕ (G A));
    }.

End TraversableMorphism.

(** * Monoid structure of traversable functors *)
(******************************************************************************)

(** ** The identity functor is traversable *)
(******************************************************************************)
Instance Dist_I : Dist (fun A => A) := fun F fmap mult pure A a => a.

#[program] Instance Traversable_I : TraversableFunctor (fun A => A).

Next Obligation.
  unfold transparent tcs. ext a.
  symmetry. now rewrite (fun_fmap_id G1).
Qed.

(** ** Traversable functors are closed under composition *)
(******************************************************************************)
Section TraversableFunctor_compose.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  #[global] Instance Dist_compose : Dist (T ∘ U) :=
    fun G map mult pure A =>
      dist T G ∘ fmap T (dist U G (A := A)).

  Lemma dist_unit_compose : forall A,
      dist (T ∘ U) (fun A => A) = @id (T (U A)).
  Proof.
    intros. unfold transparent tcs.
    rewrite (dist_unit T).
    rewrite (dist_unit U).
    now rewrite (fun_fmap_id T).
  Qed.

  Lemma dist_natural_compose : forall `{Applicative G} `(f : X -> Y),
      fmap (G ∘ (T ∘ U)) f ∘ dist (T ∘ U) G = dist (T ∘ U) G ∘ fmap ((T ∘ U) ∘ G) f.
  Proof.
    intros. unfold transparent tcs.
    change_left (fmap (G ∘ T) (fmap U f) ∘ dist T G ∘ fmap T (dist U G)).
    rewrite (dist_natural T (fmap U f)).
    unfold_ops @Fmap_compose.
    reassociate -> on left.
    reassociate -> on right.
    rewrite (fun_fmap_fmap T).
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f).
    now rewrite <- (dist_natural U (G := G) f).
  Qed.

  Lemma dist_morph_compose : forall `{ApplicativeMorphism G1 G2 ϕ} (A : Type),
      dist (T ∘ U) G2 ∘ fmap (T ∘ U) (ϕ A) = ϕ (T (U A)) ∘ dist (T ∘ U) G1.
  Proof.
    intros. unfold transparent tcs.
    reassociate -> on left.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    rewrite (dist_morph U).
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on left.
    now rewrite (dist_morph T).
  Qed.

  Lemma dist_linear_compose : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (T ∘ U) (G1 ∘ G2) = fmap G1 (dist (T ∘ U) G2) ∘ dist (T ∘ U) G1 (A := G2 A).
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap G1).
    reassociate -> on right;
      change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f);
      reassociate <- near (fmap (G1 ∘ T) (dist U G2)).
    rewrite (dist_natural T (dist U G2) (G := G1)).
    reassociate -> on right;
      unfold_ops @Fmap_compose;
      rewrite (fun_fmap_fmap T).
    #[local] Set Keyed Unification.
    rewrite (dist_linear U).
    rewrite (dist_linear T).
    #[local] Unset Keyed Unification.
    reflexivity.
  Qed.

  #[global] Instance Traversable_compose : TraversableFunctor (T ∘ U) :=
    {| dist_natural := @dist_natural_compose;
       dist_morph := @dist_morph_compose;
       dist_unit := @dist_unit_compose;
       dist_linear := @dist_linear_compose;
    |}.

End TraversableFunctor_compose.

(** * Basic properties of traversable functors *)
(******************************************************************************)

(** ** Purity laws *)
(******************************************************************************)
Section pure_as_applicative_transformation.

  Context
    `{Applicative G}.

  Lemma pure_appmor_1 : forall A B (f : A -> B) (t : A),
      pure G (fmap (fun A : Type => A) f t) = fmap G f (pure G t).
  Proof.
    intros. now rewrite (app_pure_natural G).
  Qed.

  Lemma pure_appmor_2 : forall (A : Type) (a : A),
      pure G (pure (fun A => A) a) = pure G a.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma pure_appmor_3 : forall (A B : Type) (a : A) (b : B),
      pure G (mult (fun A => A) (a, b)) = mult G (pure G a, pure G b).
  Proof.
    unfold transparent tcs. intros. now rewrite (app_mult_pure G).
  Qed.

  #[global] Instance ApplicativeMorphism_pure :
    ApplicativeMorphism (fun A => A) G (@pure G _) :=
    {| appmor_natural := pure_appmor_1;
       appmor_pure := pure_appmor_2;
       appmor_mult := pure_appmor_3;
    |}.

End pure_as_applicative_transformation.

Section purity_law.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Corollary fmap_purity_1 `{Applicative G} : forall A,
    dist T G ∘ fmap T (pure G) (A := A) = pure G.
  Proof.
    intros. rewrite (dist_morph T (ϕ := @pure G _)).
    now rewrite (dist_unit T).
  Qed.

  Corollary fmap_purity_2 `{Applicative G1} `{Applicative G2} : forall `(f : A -> G1 B),
      dist T (G2 ∘ G1) ∘ fmap T (pure G2 ∘ f) = pure G2 ∘ dist T G1 ∘ fmap T f.
  Proof.
    intros. rewrite <- (fun_fmap_fmap T).
    reassociate <-. rewrite (dist_linear T).
    reassociate -> near (fmap T (pure G2)).
    rewrite fmap_purity_1.
    fequal. ext t. unfold compose.
    now rewrite (app_pure_natural G2).
  Qed.

End purity_law.

(** * Kleisi presentation of traversable functors *)
(******************************************************************************)
Definition traverse (T : Type -> Type) (G : Type -> Type)
           `{Fmap T} `{Dist T}
           `{Fmap G} `{Pure G} `{Mult G}
           `(f : A -> G B) : T A -> G (T B)
  := dist T G ∘ fmap T f.

(* We don't give a dedicated name or notation to the composition
   operation <<g ⋆ f = fmap F g ∘ f>> because it is trivial and one
   wants to avoid making up too many notations. *)

(** ** Specification for <<fmap>>  *)
(******************************************************************************)
Section TraversableFunctor_fmap.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Corollary fmap_to_traverse : forall `(f : A -> B),
      fmap T f = traverse T (fun A => A) f.
  Proof.
    intros. unfold traverse. ext t.
    now rewrite (dist_unit T).
  Qed.

End TraversableFunctor_fmap.

(** ** Kleisi presentation of traversable functors *)
(******************************************************************************)
Section TraversableFunctor_kleisli.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Theorem traverse_id : forall (A : Type),
      traverse T (fun A => A) id = @id (T A).
  Proof.
    intros. unfold traverse. ext t. rewrite (dist_unit T).
    now rewrite (fun_fmap_id T).
  Qed.

  Theorem traverse_id_purity : forall `{Applicative G} (A : Type),
      traverse T G (pure G) = @pure G _ (T A).
  Proof.
    intros. unfold traverse. ext t. now rewrite fmap_purity_1.
  Qed.

  Lemma traverse_traverse `{Applicative G2} `{Applicative G1} :
    forall `(g : B -> G2 C) `(f : A -> G1 B),
      fmap G1 (traverse T G2 g) ∘ traverse T G1 f = traverse T (G1 ∘ G2) (fmap G1 g ∘ f).
  Proof.
    introv. unfold traverse.
    rewrite (dist_linear T).
    repeat reassociate <-.
    rewrite <- (fun_fmap_fmap T).
    repeat reassociate <-.
    reassociate -> near (fmap T (fmap G1 g)).
    change (fmap T (fmap G1 g)) with (fmap (T ∘ G1) g).
    rewrite <- (dist_natural T g (G := G1)).
    unfold_ops @Fmap_compose.
    reassociate <-.
    unfold_compose_in_compose.
    now rewrite (fun_fmap_fmap G1).
  Qed.

  Lemma traverse_morphism `{morph : ApplicativeMorphism G1 G2 ϕ} : forall `(f : A -> G1 B),
      ϕ (T B) ∘ traverse T G1 f = traverse T G2 (ϕ B ∘ f).
  Proof.
    intros. unfold traverse. reassociate <-.
    inversion morph.
    rewrite <- (dist_morph T).
    reassociate ->.
    now rewrite (fun_fmap_fmap T).
  Qed.

End TraversableFunctor_kleisli.

(** ** Purity laws *)
(******************************************************************************)
Section traverse_purity_law.

  Context
    `{TraversableFunctor T}
    `{Applicative G1}
    `{Applicative G2}.

  Corollary traverse_purity : forall A B (f : A -> G1 B),
      traverse T (G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ traverse T G1 f.
  Proof.
    intros. unfold traverse.
    now rewrite (fmap_purity_2 T (G2 := G2) f).
  Qed.

End traverse_purity_law.

(** ** Composition with sub-operations  *)
(******************************************************************************)
Section TraversableFunctor_composition.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G}.

  Corollary fmap_traverse : forall `(g : B -> C) `(f : A -> G B),
      fmap G (fmap T g) ∘ traverse T G f = traverse T G (fmap G g ∘ f).
  Proof.
    intros. unfold traverse. ext t.
    repeat reassociate <-.
    change (fmap G (fmap T g)) with (fmap (G ∘ T) g).
    rewrite (dist_natural T g (G := G)).
    reassociate ->.
    unfold_ops @Fmap_compose.
    now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary traverse_fmap : forall `(g : B -> G C) `(f : A -> B),
      traverse T G g ∘ fmap T f = traverse T G (g ∘ f).
  Proof.
    intros. unfold traverse. ext t.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

End TraversableFunctor_composition.

(** * Characterization of distribution w.r.t. (F ◻ G) *)
(******************************************************************************)
Section traversable_product.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G1}
    `{Applicative G2}.

  Variables
    (A B : Type)
    (f : A -> G1 B) (g : A -> G2 B).

  Lemma dist_combine1 : forall (t : T A),
    pi1 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G1 f t.
  Proof.
    intros. pose (ApplicativeMorphism_pi1 G1 G2).
    compose near t on left.
    now rewrite (traverse_morphism T).
  Qed.

  Lemma dist_combine2 : forall (t : T A),
    pi2 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G2 g t.
  Proof.
    intros. pose (ApplicativeMorphism_pi2 G1 G2).
    compose near t on left.
    now rewrite (traverse_morphism T).
  Qed.

  Theorem dist_combine : forall (t : T A),
    dist T (G1 ◻ G2) (fmap T (f <◻> g) t) =
    product (traverse T G1 f t) (traverse T G2 g t).
  Proof.
    intros. compose near t on left.
    erewrite <- (dist_combine1).
    erewrite <- (dist_combine2).
    now rewrite <- product_eta.
  Qed.

  Theorem traverse_combine :
    traverse T (G1 ◻ G2) (f <◻> g) = (traverse T G1 f) <◻> (traverse T G2 g).
  Proof.
    intros. unfold traverse.
    ext t. unfold compose.
    now rewrite dist_combine.
  Qed.

End traversable_product.

(** * Traversable functors are listable *)
(******************************************************************************)
(* set <<tag := False>> to emphasize this type is arbitrary *)
#[global] Instance Tolist_Traversable `{Fmap T} `{Dist T} : Tolist T :=
  fun A => unconst ∘ dist T (Const (list A)) ∘
                fmap T (mkConst (tag := False) ∘ ret list (A := A)).

Section TraversableFunctor_tolist_spec.

  Context
    {A : Type}.

  Instance Fmap_list_const : Fmap (const (list A)) :=
    fun X Y f t => t.

  Theorem fmap_list_const_spec : forall (X Y : Type) (f : X -> Y),
      fmap (const (list A)) f = id.
  Proof.
    reflexivity.
  Qed.

  Instance Pure_list_const : Pure (const (list A)) :=
    fun X x => nil.

  Instance Mult_list_monoid : Mult (const (list A)) :=
    fun X Y '(x, y) => List.app x y.

  Instance Applicative_list_monoid :
    Applicative (const (list A)).
  Proof.
    constructor; intros; try reflexivity.
    - constructor; reflexivity.
    - cbn. now rewrite List.app_assoc.
    - cbn. now List.simpl_list.
  Qed.

  Instance ApplicativeMorphism_unconst :
    ApplicativeMorphism
      (Const (list A)) (const (list A))
      (fun X => unconst).
  Proof.
    constructor; try typeclasses eauto; reflexivity.
  Qed.

  Theorem tolist_spec (T : Type -> Type)
          `{TraversableFunctor T} :
    @tolist T Tolist_Traversable A
    = @dist T _ (const (list A))
            (Fmap_list_const)
            (Pure_list_const)
            (Mult_list_monoid) False
            ∘ fmap T (ret list).
  Proof.
    intros. unfold tolist, Tolist_Traversable.
    rewrite <- (fun_fmap_fmap T). reassociate <-.
    fequal. rewrite <- (dist_morph T (ϕ := @unconst _)).
    reassociate -> on left. rewrite (fun_fmap_fmap T).
    change (unconst ∘ mkConst) with (@id (list A)).
    now rewrite (fun_fmap_id T).
  Qed.

  Definition retag {A X Y : Type} :
    const (list A) X -> const (list A) Y := @id (list A).

  Instance ApplicativeMorphism_id
           `{Applicative G} :
    ApplicativeMorphism G G (fun A => @id (G A)).
  Proof.
    constructor; try typeclasses eauto; reflexivity.
  Qed.

  Definition exfalso {X : Type} : False -> X.
    intuition.
  Defined.

  Context
    `{TraversableFunctor T}.

  #[local] Set Keyed Unification.
  Theorem traversable_tolist1 : forall (X : Type),
      (@dist T _ (@const Type Type (list A))
             (Fmap_list_const) (Pure_list_const)
             (Mult_list_monoid) X)
      =
      (@dist T _ (fun _ : Type => list A)
             (Fmap_list_const) (Pure_list_const)
             (Mult_list_monoid) False).
  Proof.
    intros. symmetry. change (?f = ?g) with (f = g ∘ (@id (T (list A)))).
    rewrite <- (fun_fmap_id T).
    change (@id (list A)) with
        (fmap (A := False) (B:=X) (const (list A)) exfalso).
    change (fmap T (fmap (const (list A)) ?f))
      with (fmap (T ∘ const (list A)) f).
    rewrite <- (dist_natural T (B := X) (A := False) (G := const (list A))).
    reflexivity.
  Qed.

End TraversableFunctor_tolist_spec.

Section ListableFunctor_of_TraversableFunctor.

  Context
    `{TraversableFunctor T}.

  Instance Natural_tolist_Traversable : Natural (@tolist T Tolist_Traversable).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Tolist_Traversable.
    repeat reassociate <-.
    rewrite (mapConst_2 (fmap list f)).
    repeat reassociate -> on left;
      reassociate <- near (mapConst (fmap list f)).
    rewrite <- (dist_morph T).
    repeat reassociate ->.
    repeat rewrite (fun_fmap_fmap T).
    reflexivity.
  Qed.

  Axiom traversable_functors_are_shapely : shapeliness T.

  #[global] Instance ListableFunctor_Traversable : ListableFunctor T :=
    {| lfun_shapeliness := traversable_functors_are_shapely |}.

End ListableFunctor_of_TraversableFunctor.

(** * Traversable instance for [list] *)
(******************************************************************************)
Instance Dist_list : Dist list :=
  fun G map mlt pur A =>
    (fix dist (l : list (G A)) :=
       match l with
       | nil => pure G nil
       | cons x xs =>
         (pure G (@cons A) <⋆> x) <⋆> (dist xs)
       end).

(** ** Rewriting lemmas for <<dist>> *)
(******************************************************************************)
Section list_dist_rewrite.

  Context
    `{Applicative G}.

  Variable (A : Type).

  Lemma dist_list_nil :
    dist list G (@nil (G A)) = pure G nil.
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_1 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      (pure G cons <⋆> x) <⋆> (dist list G xs).
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_2 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      (fmap G (@cons A) x) <⋆> (dist list G xs).
  Proof.
    intros. rewrite dist_list_cons_1.
    now rewrite fmap_to_ap.
  Qed.

  Lemma dist_list_one (a : G A) : dist list G [ a ] = fmap G (ret list) a.
  Proof.
    cbn. rewrite fmap_to_ap. rewrite ap3.
    rewrite <- ap4. now do 2 rewrite ap2.
  Qed.

  Lemma dist_list_app : forall (l1 l2 : list (G A)),
      dist list G (l1 ++ l2) = pure G (@app _) <⋆> dist list G l1 <⋆> dist list G l2.
  Proof.
    intros. induction l1.
    - cbn. rewrite ap2. change (app []) with (@id (list A)).
      now rewrite ap1.
    - cbn [app]. rewrite dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl1; clear IHl1.
      rewrite <- fmap_to_ap.
      rewrite <- fmap_to_ap.
      rewrite <- ap4. rewrite <- fmap_to_ap.
      fequal. rewrite <- ap7.
      rewrite ap6. fequal.
      compose near a.
      rewrite (fun_fmap_fmap G).
      rewrite (fun_fmap_fmap G).
      compose near a on left.
      now rewrite (fun_fmap_fmap G).
  Qed.

End list_dist_rewrite.

Hint Rewrite @dist_list_nil @dist_list_cons_1
     @dist_list_one @dist_list_app : tea_list.

Section dist_list_properties.

  #[local] Arguments dist _%function_scope {Dist} _%function_scope {H H0 H1}
   A%type_scope _.

  Lemma dist_list_1 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      fmap G (fmap list f) ((fmap G (@cons A) a) <⋆> dist list G A l) =
      (fmap G (@cons B ○ f) a) <⋆> fmap G (fmap list f) (dist list G A l).
  Proof.
    intros. rewrite ap6. rewrite <- ap7.
    fequal. compose near a. now rewrite 2(fun_fmap_fmap G).
  Qed.

  Lemma dist_list_2 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      fmap G (fmap list f) ((pure G (@cons A) <⋆> a) <⋆> dist list G A l) =
      (pure G cons <⋆> fmap G f a) <⋆> fmap G (fmap list f) (dist list G A l).
  Proof.
    intros. rewrite <- fmap_to_ap.
    rewrite ap6.
    compose near a on left.
    rewrite (fun_fmap_fmap G).
    rewrite ap5.
    unfold ap. rewrite (app_mult_natural G).
    rewrite (app_mult_natural_1 G).
    compose near ((a ⊗ dist list G A l)) on right.
    rewrite (fun_fmap_fmap G). fequal. ext [? ?].
    reflexivity.
  Qed.

  Lemma dist_natural_list : forall `{Applicative G} `(f : A -> B),
      fmap (G ∘ list) f ∘ dist list G A =
      dist list G B ∘ fmap (list ∘ G) f.
  Proof.
    intros; cbn. unfold_ops @Fmap_compose. unfold compose.
    ext l. induction l.
    + cbn. now rewrite (app_pure_natural G).
    + rewrite dist_list_cons_2.
      rewrite fmap_list_cons, dist_list_cons_2.
      rewrite <- IHl. rewrite dist_list_1.
      compose near a on right. now rewrite (fun_fmap_fmap G).
  Qed.

  Lemma dist_morph_list : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist list G2 A ∘ fmap list (ϕ A) = ϕ (list A) ∘ dist list G1 A.
  Proof.
    intros. ext l. unfold compose. induction l.
    - cbn. now rewrite (appmor_pure G1 G2).
    - inversion H0. (* get Applicative instances *)
      rewrite fmap_list_cons, dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl. rewrite ap_morphism_1.
      fequal. now rewrite (appmor_natural A).
  Qed.

  Lemma dist_unit_list : forall (A : Type),
      dist list (fun A => A) A = @id (list A).
  Proof.
    intros. ext l. induction l.
    - reflexivity.
    - cbn. now rewrite IHl.
  Qed.

  #[local] Set Keyed Unification.
  Lemma dist_linear_list
    : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist list (G1 ∘ G2) A =
      fmap G1 (dist list G2 A) ∘ dist list G1 (G2 A).
  Proof.
    intros. unfold compose. ext l. induction l.
    - cbn. unfold_ops @Pure_compose.
      rewrite fmap_to_ap. now rewrite ap2.
    - rewrite (dist_list_cons_2 (G := G1 ○ G2)).
      rewrite (dist_list_cons_2 (G := G1)).
      rewrite IHl; clear IHl.
      unfold_ops @Mult_compose @Pure_compose @Fmap_compose.
      rewrite (ap_compose_1 G2 G1).
      rewrite (app_mult_natural G1).
      unfold ap at 2. rewrite (app_mult_natural_1 G1).
      fequal. compose near (a ⊗ dist list G1 (G2 A) l).
      repeat rewrite (fun_fmap_fmap G1). fequal.
      ext [? ?]. cbn. now rewrite fmap_to_ap.
  Qed.
  #[local] Unset Keyed Unification.

End dist_list_properties.

Instance Traversable_list : TraversableFunctor list :=
  {| dist_natural := @dist_natural_list;
     dist_morph := @dist_morph_list;
     dist_unit := @dist_unit_list;
     dist_linear := @dist_linear_list;
  |}.

(** * Traversable instance for <<prod>> *)
(******************************************************************************)
Section TraversableFunctor_prod.

  Context
    (X : Type).

  #[global] Instance Dist_prod : Dist (prod X) :=
    fun F map mlt pur A '(x, a) => fmap F (pair x) a.

  Lemma dist_natural_prod : forall `{Applicative G} `(f : A -> B),
      fmap (G ∘ prod X) f ∘ dist (prod X) G = dist (prod X) G ∘ fmap (prod X ∘ G) f.
  Proof.
    intros; unfold compose; cbn. ext [x a]; cbn.
    unfold_ops @Fmap_compose. compose near a.
    now do 2 rewrite (fun_fmap_fmap G).
  Qed.

  Lemma dist_morph_prod : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist (prod X) G2 ∘ fmap (prod X) (ϕ A) = ϕ (X * A) ∘ dist (prod X) G1.
  Proof.
    intros; unfold compose; cbn. ext [x a]; cbn.
    inversion H0. now rewrite appmor_natural.
  Qed.

  Lemma dist_unit_prod : forall (A : Type),
      dist (prod X) (fun A => A) = @id (prod X A).
  Proof.
    intros; unfold compose; cbn. ext [x a]; now cbn.
  Qed.

  Lemma dist_linear_prod : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (prod X) (G1 ∘ G2) (A := A) =
      fmap G1 (dist (prod X) G2) ∘ dist (prod X) G1.
  Proof.
    intros; unfold compose; cbn. ext [x a].
    unfold_ops @Dist_prod @Fmap_compose.
    compose near a on right. now rewrite (fun_fmap_fmap G1).
  Qed.

  #[global] Instance Traversable_prod : TraversableFunctor (prod X) :=
    {| dist_natural := @dist_natural_prod;
       dist_morph := @dist_morph_prod;
       dist_unit := @dist_unit_prod;
       dist_linear := @dist_linear_prod;
    |}.

End TraversableFunctor_prod.

(** * Respectfulness properties *)
(******************************************************************************)
Section TraversableFunctor_respectfulness.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G}.

  Lemma traverse_respectful {A B} : forall t (f g : A -> G B),
      (forall a, a ∈ t -> f a = g a) -> traverse T G f t = traverse T G g t.
  Proof.
    intros. unfold traverse, compose. fequal.
    now apply (fmap_respectful T).
  Qed.

  Lemma traverse_respectful_fmap {A B} : forall t (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure G (g a)) -> traverse T G f t = pure G (fmap T g t).
  Proof.
    intros. rewrite <- (traverse_id_purity T). compose near t on right.
    rewrite (traverse_fmap T). apply (traverse_respectful).
    auto.
  Qed.

  Corollary traverse_respectful_id {A} : forall t (f : A -> G A),
      (forall a, a ∈ t -> f a = pure G a) -> traverse T G f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity T).
    now apply traverse_respectful.
  Qed.

End TraversableFunctor_respectfulness.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'δ'" := (dist) : tealeaves_scope.
End Notations.
