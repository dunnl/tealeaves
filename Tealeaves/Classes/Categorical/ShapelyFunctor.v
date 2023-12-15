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
    shape F t1 = shape F t2 /\ tolist _ t1 = tolist _ t2 -> t1 = t2.

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
      (η : F ⇒ G) :=
  { ltrans_commute : `(tolist F = tolist G ∘ η A);
    ltrans_natural : Natural η;
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
      shape F t = shape F u ->
      shape list (tolist F t) = shape list (tolist F u).
  Proof.
    introv heq. compose near t. compose near u.
    unfold shape in *. rewrite 2(natural). unfold compose.
    now rewrite heq.
  Qed.

  Corollary shape_l : forall A (l1 l2 : F A) (x y : list A),
      shape F l1 = shape F l2 ->
      (tolist F l1 ++ x = tolist F l2 ++ y) ->
      tolist F l1 = tolist F l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_ll, shape_tolist.
  Qed.

  Corollary shape_r : forall A (l1 l2 : F A) (x y : list A),
      shape F l1 = shape F l2 ->
      (x ++ tolist F l1 = y ++ tolist F l2) ->
      tolist F l1 = tolist F l2.
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
      shape F t1 = shape F t2 /\
      map list f (tolist F t1) = map list g (tolist F t2).

  Definition tolist_map_respectful := forall A B (t1 t2 : F A) (f g : A -> B),
      shape F t1 = shape F t2 ->
      map list f (tolist F t1) = map list g (tolist F t2) ->
      map F f t1 = map F g t2.

  Definition tolist_map_respectful_iff := forall A B (t1 t2 : F A) (f g : A -> B),
      shape F t1 = shape F t2 /\
      map list f (tolist F t1) = map list g (tolist F t2) <->
      map F f t1 = map F g t2.

End listable_functor_respectful_definitions.

Ltac unfold_list_properness :=
  unfold shapeliness,
  tolist_map_respectful,
    tolist_map_respectful_iff in *.

(** * Shapely functors are containers *)
(******************************************************************************)
#[export] Instance Elements_Tolist `{Tolist F} : Elements F :=
  fun A => element_of list ∘ tolist F.

#[export] Instance: forall `{ShapelyFunctor F}, Natural (@element_of F _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold element_of, Elements_Tolist. ext t.
  reassociate <- on left. rewrite (natural (G := subset)).
  reassociate -> on left. now rewrite natural.
Qed.

Theorem in_iff_in_list `{Tolist F} : forall (A : Type) (t : F A) (a : A),
    a ∈ t <-> a ∈ tolist F t.
Proof.
  reflexivity.
Qed.

Section ShapelyFunctor_setlike.

  Context
    (F : Type -> Type)
    `{ShapelyFunctor F}.

  Lemma shapeliness_iff :
    forall (A : Type) (t u : F A),
      t = u <-> shape F t = shape F u /\ tolist F t = tolist F u.
  Proof.
    intros. split.
    + intros; subst; auto.
    + apply (shp_shapeliness).
  Qed.

  (** Two maps over [t] are equal exactly when they're equal on t's contents. *)
  Lemma shapely_map_eq_iff :
    forall (A B : Type) (t : F A) (f g : A -> B),
      map F f t = map F g t <->
      map list f (tolist F t) = map list g (tolist F t).
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
    - cut (shape F (map F f t1) = shape F (map F g t2)).
      + now rewrite 2(shape_map).
      + now rewrite heq.
    - compose near t1; compose near t2.
      rewrite 2natural.
      unfold compose; now rewrite heq.
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
