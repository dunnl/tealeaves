From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.ContainerFunctor
  Functors.List
  Functors.Subset.

Import ContainerFunctor.Notations.
Import Subset.Notations.
Import Classes.Functor.Notations.
Import List.ListNotations.

#[local] Generalizable Variables G F A B.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.

Definition shapeliness (F : Type -> Type)
  `{Map F} `{Tolist F} := forall A (t1 t2 : F A),
    shape t1 = shape t2 /\ tolist t1 = tolist t2 -> t1 = t2.

Class ShapelyFunctor
  (F : Type -> Type) `{Map F} `{Tolist F} :=
  { shp_natural :> Natural (@tolist F _);
    shp_functor :> Functor F;
    shp_shapeliness : shapeliness F;
  }.

(** ** Shapely natural transformations *)
(******************************************************************************)
Class ShapelyTransformation
      {F G : Type -> Type}
      `{! Map F} `{Tolist F}
      `{! Map G} `{Tolist G}
      (ϕ : F ⇒ G) :=
  { ltrans_commute : `(tolist (F := F) = tolist (F := G) ∘ ϕ A);
    ltrans_natural : Natural ϕ;
  }.

(** ** Instance for [list] *)
(** As a reasonability check, we prove that [list] is a listable functor. *)
(******************************************************************************)
Section ShapelyFunctor_list.

  Instance Tolist_list : Tolist list := fun A l => l.

  Instance: Natural (@tolist list _).
  Proof.
    constructor; try typeclasses eauto.
    reflexivity.
  Qed.

  Theorem shapeliness_list : shapeliness list.
  Proof.
    intros A t1 t2. intuition.
  Qed.

  Instance: ShapelyFunctor list :=
    {| shp_shapeliness := shapeliness_list; |}.

End ShapelyFunctor_list.

(** ** Reasoning principles for <<shape>> on listable functors *)
(** These principles are predicated just on <<tolist>> being a natural
    transformation and can be used to prove [shapeliness] for a given
    functor. *)
(******************************************************************************)
Section listable_shape_lemmas.

  Context
    (F : Type -> Type)
    `{Functor F}
    `{Tolist F} `{! Natural (@tolist F _)}.

  (* Values with the same shape have equal-length contents *)
  Lemma shape_tolist : forall `(t : F A) `(u : F B),
      shape t = shape u ->
      shape (tolist t) = shape (tolist u).
  Proof.
    introv heq. compose near t. compose near u.
    unfold shape in *. rewrite 2(natural).
    unfold compose.
    fequal. apply heq.
  Qed.

  Corollary shape_l : forall A (l1 l2 : F A) (x y : list A),
      shape l1 = shape l2 ->
      (tolist l1 ++ x = tolist l2 ++ y) ->
      tolist l1 = tolist l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_ll, shape_tolist.
  Qed.

  Corollary shape_r : forall A (l1 l2 : F A) (x y : list A),
      shape l1 = shape l2 ->
      (x ++ tolist l1 = y ++ tolist l2) ->
      tolist l1 = tolist l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_rr, shape_tolist.
  Qed.

End listable_shape_lemmas.

(** * Respectfulness conditions for shapely functors *)
(******************************************************************************)
Section listable_functor_respectful_definitions.

  Context
    (F : Type -> Type)
    `{Map F} `{Tolist F}.

  Definition tolist_map_injective := forall A B (t1 t2 : F A) (f g : A -> B),
      map F f t1 = map F g t2 ->
      shape t1 = shape t2 /\
      map list f (tolist t1) = map list g (tolist t2).

  Definition tolist_map_respectful := forall A B (t1 t2 : F A) (f g : A -> B),
      shape t1 = shape t2 ->
      map list f (tolist t1) = map list g (tolist t2) ->
      map F f t1 = map F g t2.

  Definition tolist_map_respectful_iff := forall A B (t1 t2 : F A) (f g : A -> B),
      shape t1 = shape t2 /\
      map list f (tolist t1) = map list g (tolist t2) <->
      map F f t1 = map F g t2.

End listable_functor_respectful_definitions.

Ltac unfold_list_properness :=
  unfold shapeliness,
  tolist_map_respectful,
    tolist_map_respectful_iff in *.

(** * Shapely functors are containers *)
(******************************************************************************)
#[export] Instance Elements_Tolist `{Tolist F} : Elements F :=
  fun A => element_of ∘ tolist.

#[export] Instance: forall `{ShapelyFunctor F}, Natural (@element_of F _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold element_of, Elements_Tolist. ext t.
  reassociate <- on left. rewrite (natural (G := subset)).
  reassociate -> on left. now rewrite natural.
Qed.

Theorem in_iff_in_list `{Tolist F} : forall (A : Type) (t : F A) (a : A),
    a ∈ t <-> a ∈ tolist t.
Proof.
  reflexivity.
Qed.

(** ** <<element_of>> as a hom *)
(******************************************************************************)
Lemma element_of_list_hom1 : forall (A : Type),
    element_of ∘ ret list A = ret subset A.
Proof.
  intros.
  unfold_ops @Elements_Tolist.
  ext a b. propext;
  cbv; intuition.
Qed.

Lemma element_of_list_hom2 : forall (A B : Type) (f : A -> list B),
    element_of ∘ bind f = bind (T := subset) (element_of ∘ f) ∘ element_of.
Proof.
  intros. ext l b. induction l.
  - propext; cbv.
    intuition.
    intros [a [absurd]]; contradiction.
  - unfold compose in *.
    autorewrite with tea_list tea_set.
    rewrite IHl.
    reflexivity.
Qed.

Lemma element_of_list_map : forall (A B : Type) (f : A -> B),
    element_of ∘ map list f = map subset f ∘ element_of.
Proof.
  intros. ext l. unfold compose. ext b.
  unfold_ops @Elements_list @Map_list.
  induction l.
  - cbn. propext.
    + contradiction.
    + intros [? [? ?]].
      contradiction.
  - cbn. rewrite IHl.
    cbv. propext.
    + intros [Hleft | Hright].
      * eauto.
      * preprocess. eauto.
    + intros. preprocess.
      destruct H as [Hleft | Hright].
      * left. now fequal.
      * right. eauto.
Qed.

#[export] Instance Monad_Hom_list_elements : MonadHom list subset (@element_of list _) :=
  {| kmon_hom_ret := element_of_list_hom1;
    kmon_hom_bind := element_of_list_hom2;
  |}.

Section ShapelyFunctor_setlike.

  Context
    (F : Type -> Type)
    `{ShapelyFunctor F}.

  Lemma shapeliness_iff :
    forall (A : Type) (t u : F A),
      t = u <-> shape t = shape u /\ tolist t = tolist u.
  Proof.
    intros. split.
    + intros; subst; auto.
    + apply (shp_shapeliness).
  Qed.

  (** Two maps over [t] are equal exactly when they're equal on t's contents. *)
  Lemma shapely_map_eq_iff :
    forall (A B : Type) (t : F A) (f g : A -> B),
      map F f t = map F g t <->
      map list f (tolist t) = map list g (tolist t).
  Proof.
    intros.
    compose near t on right. rewrite 2(natural).
    unfold compose. split.
    - introv heq. now rewrite heq.
    - intros. apply (shp_shapeliness). rewrite 2(shape_map).
      auto.
  Qed.

  Theorem shapely_pointwise_iff :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) <-> map F f t = map F g t.
  Proof.
    introv. rewrite shapely_map_eq_iff.
    setoid_rewrite in_iff_in_list.
    now rewrite map_rigidly_respectful_list.
  Qed.

  Corollary shapely_pointwise :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) -> map F f t = map F g t.
  Proof.
   introv. rewrite shapely_pointwise_iff. auto.
 Qed.

  #[export] Instance ContainerFunctor_Shapely : ContainerFunctor F :=
    {| cont_pointwise := shapely_pointwise; |}.

End ShapelyFunctor_setlike.


(** ** Equivalence with shapeliness *)
(******************************************************************************)
Section tolist_respectfulness_characterizations.

  Context
    `{ShapelyFunctor F}.

  Theorem tolist_map_injective_proof : tolist_map_injective F.
  Proof.
    introv heq. split.
    - cut (shape (map F f t1) = shape (map F g t2)).
      + now rewrite 2(shape_map).
      + now rewrite heq.
    - compose near t1; compose near t2.
      do 2 rewrite natural.
      unfold compose.
      now rewrite heq.
  Qed.

  Lemma shapeliness_equiv_1 : shapeliness F -> tolist_map_respectful F.
  Proof.
    unfold tolist_map_respectful.
    introv hyp hshape hcontents.
    apply hyp. split.
    - now rewrite 2(shape_map).
    - compose near t1 on left; compose near t2 on right.
      now rewrite <- 2(natural).
  Qed.

  Lemma shapeliness_equiv_2: tolist_map_respectful F -> tolist_map_respectful_iff F.
  Proof.
    unfold tolist_map_respectful, tolist_map_respectful_iff.
    intros. split.
    - introv [? ?]. auto.
    - apply tolist_map_injective_proof.
  Qed.

  Lemma shapeliness_equiv_3: tolist_map_respectful_iff F -> shapeliness F.
  Proof.
    unfold shapeliness, tolist_map_respectful_iff.
    introv hyp1 hyp2.
    replace t1 with (map F id t1) by (now rewrite (fun_map_id (F := F))).
    replace t2 with (map F id t2) by (now rewrite (fun_map_id (F := F))).
    apply hyp1. now rewrite (fun_map_id (F := list)).
  Qed.

End tolist_respectfulness_characterizations.

(** * Respectfulness conditions for shapely functors *)
(******************************************************************************)
Section ShapelyFunctor_theory.

  Context
    (F : Type -> Type)
    `{ShapelyFunctor F}.

  Corollary shapely_map_id_iff :
    forall (A : Type) (t : F A) (f : A -> A),
      (forall (a : A), a ∈ t -> f a = a) <-> map F f t = t.
  Proof.
    introv. replace t with (map F id t) at 2
      by now rewrite (fun_map_id (F := F)).
    now rewrite (shapely_pointwise_iff F).
  Qed.

End ShapelyFunctor_theory.

(*

(** * [fold] and [foldMap] operations *)
(******************************************************************************)
Section fold.

  Generalizable Variable M ϕ.

  Context
    `{ShapelyFunctor F}.

  Definition fold `{Monoid_op M} `{Monoid_unit M} : F M -> M :=
    List.fold ∘ tolist F.

  Definition foldMap {A} `{Monoid_op M} `{Monoid_unit M} (f : A -> M) : F A -> M :=
    fold ∘ map F f.

  Lemma fold_mon_hom : forall `(ϕ : M1 -> M2) `{Hϕ : Monoid_Morphism M1 M2 ϕ},
      ϕ ∘ fold = fold ∘ map F ϕ.
  Proof.
    intros ? ? ϕ; intros.
    change left (ϕ ∘ List.fold ∘ tolist F).
    change right (List.fold ∘ (tolist F ∘ map F ϕ)).
    rewrite <- natural.
    now rewrite (List.fold_mon_hom ϕ).
  Qed.

  Lemma foldMap_map {A B} `{Monoid M} {f : A -> B} {g : B -> M} :
    foldMap g ∘ map F f = foldMap (g ∘ f).
  Proof.
    intros. unfold foldMap.
    now rewrite <- (fun_map_map (F := F)).
  Qed.

  Theorem foldMap_hom {A} `{Monoid_Morphism M1 M2 ϕ} {f : A -> M1} :
    ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
  Proof.
    intros. unfold foldMap.
    reassociate <- on left.
    rewrite (fold_mon_hom ϕ).
    now rewrite <- (fun_map_map (F := F)).
  Qed.

End fold.

(** ** Folding over identity and composition functors *)
(******************************************************************************)
Section fold_monoidal_structure.

  Theorem fold_I (A : Type) `(Monoid A) : forall (a : A),
      fold a = a.
  Proof.
    intros. cbn. now rewrite (monoid_id_l).
  Qed.

End fold_monoidal_structure.

*)
