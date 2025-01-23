From Tealeaves Require Export
  Classes.Categorical.ContainerFunctor
  Functors.Early.List.

Import Monoid.
Import Subset.Notations.
Import Functor.Notations.
Import List.ListNotations.
Import ContainerFunctor.Notations.

#[local] Generalizable Variables G F A B.

(** * The <<Tolist>> Operation *)
(******************************************************************************)
Import Classes.Functor.Notations.

Class Tolist (F: Type -> Type) :=
  tolist: F ⇒ list.

#[global] Arguments tolist {F}%function_scope {Tolist} {A}%type_scope _.

(** * Shapely functors *)
(******************************************************************************)

(** ** The [shape] operation *)
(******************************************************************************)
Definition shape `{Map F} {A: Type}: F A -> F unit :=
  map (const tt).

(** *** Basic reasoning principles for <<shape>> *)
(******************************************************************************)
Theorem shape_map `{Functor F}: forall (A B: Type) (f: A -> B) (t: F A),
    shape (F := F) (map f t) =
      shape (F := F) t.
Proof.
  intros. compose near t on left.
  unfold shape. now rewrite fun_map_map.
Qed.

Theorem shape_shape `{Functor F}: forall (A: Type) (t: F A),
    shape (shape t) = shape t.
Proof.
  intros.  compose near t on left.
  unfold shape. now rewrite fun_map_map.
Qed.


Lemma shape_map_eq `{Functor F}: forall (A1 A2 B: Type) (f: A1 -> B) (g: A2 -> B) t u,
    map f t = map g u -> shape t = shape u.
Proof.

  introv hyp. cut (shape (map f t) = shape (map g u)).
  - now rewrite 2(shape_map).
  - now rewrite hyp.
Qed.

(** ** Shapeliness *)
(******************************************************************************)
Definition shapeliness (F: Type -> Type)
  `{Map F} `{Tolist F} := forall A (t1 t2: F A),
    shape t1 = shape t2 /\ tolist t1 = tolist t2 -> t1 = t2.

(** ** Typeclass for shapely functors *)
(******************************************************************************)
Class ShapelyFunctor
  (F: Type -> Type) `{Map F} `{Tolist F} :=
  { shp_natural :> Natural (@tolist F _);
    shp_functor :> Functor F;
    shp_shapeliness: shapeliness F;
  }.

(** ** Shapely natural transformations *)
(******************************************************************************)
Class ShapelyTransformation
      {F G: Type -> Type}
      `{! Map F} `{Tolist F}
      `{! Map G} `{Tolist G}
      (ϕ: F ⇒ G) :=
  { ltrans_commute: `(tolist (F := F) = tolist (F := G) ∘ ϕ A);
    ltrans_natural: Natural ϕ;
  }.

(** * Various characterizations of shapeliness *)
(******************************************************************************)
Section listable_functor_respectful_definitions.

  Context
    (F: Type -> Type)
    `{Map F} `{Tolist F}.

  Definition tolist_map_injective := forall A B (t1 t2: F A) (f g: A -> B),
      map f t1 = map g t2 ->
      shape t1 = shape t2 /\
      map f (tolist t1) = map g (tolist t2).

  Definition tolist_map_respectful := forall A B (t1 t2: F A) (f g: A -> B),
      shape t1 = shape t2 ->
      map f (tolist t1) = map g (tolist t2) ->
      map f t1 = map g t2.

  Definition tolist_map_respectful_iff := forall A B (t1 t2: F A) (f g: A -> B),
      shape t1 = shape t2 /\
      map f (tolist t1) = map g (tolist t2) <->
      map f t1 = map g t2.

End listable_functor_respectful_definitions.

Ltac unfold_list_properness :=
  unfold shapeliness,
  tolist_map_respectful,
    tolist_map_respectful_iff in *.

(** ** Equivalences *)
(******************************************************************************)
Section tolist_respectfulness_characterizations.

  Context
    `{Functor F}
    `{Tolist F}
    `{! Natural (@tolist F _)}.

  Theorem tolist_map_injective_proof: tolist_map_injective F.
  Proof.
    introv heq. split.
    - cut (shape (map f t1) = shape (map g t2)).
      + now rewrite 2(shape_map).
      + now rewrite heq.
    - compose near t1; compose near t2.
      do 2 rewrite natural.
      unfold compose.
      now rewrite heq.
  Qed.

  Lemma shapeliness_equiv_1: shapeliness F -> tolist_map_respectful F.
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
    replace t1 with (map id t1) by (now rewrite (fun_map_id (F := F))).
    replace t2 with (map id t2) by (now rewrite (fun_map_id (F := F))).
    apply hyp1. now rewrite (fun_map_id (F := list)).
  Qed.

End tolist_respectfulness_characterizations.

(*
(** ** [fold] and [foldMap] operations *)
(******************************************************************************)
Section fold.

  Generalizable Variable M ϕ.

  Context
    `{ShapelyFunctor F}.

  Definition crush
    `{monoid_op: Monoid_op M}
    `{monoid_unit: Monoid_unit M}:
    F M -> M := crush_list ∘ tolist.

  Definition foldMap {A}
    `{monoid_op: Monoid_op M}
    `{monoid_unit: Monoid_unit M}
    (f: A -> M): F A -> M :=
    crush ∘ map f.

  Lemma crush_mon_hom: forall `(ϕ: M1 -> M2) `{Hϕ: Monoid_Morphism M1 M2 ϕ},
      ϕ ∘ crush = crush ∘ map ϕ.
  Proof.
    intros ? ? ϕ; intros.
    change left (ϕ ∘ crush_list ∘ tolist).
    change right (crush_list ∘ (tolist ∘ map ϕ)).
    rewrite <- natural.
    rewrite (crush_list_mon_hom ϕ).
    reflexivity.
  Qed.

  Lemma foldMap_map {A B} `{Monoid M} {f: A -> B} {g: B -> M} :
    foldMap g ∘ map f = foldMap (g ∘ f).
  Proof.
    intros. unfold foldMap.
    now rewrite <- (fun_map_map (F := F)).
  Qed.

  Theorem foldMap_hom {A} `{Monoid_Morphism M1 M2 ϕ} {f: A -> M1} :
    ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
  Proof.
    intros. unfold foldMap.
    reassociate <- on left.
    rewrite (crush_mon_hom ϕ).
    now rewrite <- (fun_map_map (F := F)).
  Qed.

End fold.
*)

(*
(** ** Folding over identity and composition functors *)
(******************************************************************************)
Section fold_monoidal_structure.

  Theorem fold_I (A: Type) `(Monoid A): forall (a: A),
      foldMap a = a.
  Proof.
    intros. cbn. now rewrite (monoid_id_l).
  Qed.

End fold_monoidal_structure.
*)

(** * Enumerating elements of listable functors *)
(******************************************************************************)
Section ToSubset_Tolist.

  #[local] Instance ToSubset_Tolist `{Tolist F}: ToSubset F :=
  fun A => tosubset ∘ tolist.

End ToSubset_Tolist.

Class Compat_ToSubset_Tolist
  (F: Type -> Type)
  `{H_tosubset: ToSubset F}
  `{H_tolist: Tolist F}: Prop :=
  compat_element_tolist :
    @tosubset F H_tosubset =
      @tosubset F (@ToSubset_Tolist F H_tolist).

Lemma tosubset_to_tolist `{Compat_ToSubset_Tolist F} :
  forall (A: Type),
    tosubset (F := F) (A := A) = tosubset (F := list) ∘ tolist.
Proof.
  now rewrite compat_element_tolist.
Qed.

Theorem in_iff_in_tolist `{Compat_ToSubset_Tolist F} :
  forall (A: Type) (t: F A) (a: A),
    a ∈ t <-> a ∈ tolist t.
Proof.
  intros. unfold element_of.
  now rewrite compat_element_tolist.
Qed.

#[export] Instance Natural_Element_Tolist :
  forall `{ShapelyFunctor F}, Natural (@tosubset F ToSubset_Tolist).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold tosubset, ToSubset_Tolist.
  reassociate <- on left.
  rewrite (natural (G := subset)).
  reassociate -> on left. now rewrite natural.
Qed.

(** * Shapely functors are container-like *)
(******************************************************************************)
Section ShapelyFunctor_setlike.

  Context
    `{ShapelyFunctor F}.

  Lemma shapeliness_iff :
    forall (A: Type) (t u: F A),
      t = u <-> shape t = shape u /\ tolist t = tolist u.
  Proof.
    intros. split.
    + intros; subst; auto.
    + apply (shp_shapeliness).
  Qed.

  Lemma shapely_map_eq_iff :
    forall (A B: Type) (t: F A) (f g: A -> B),
      map f t = map g t <->
      map f (tolist t) = map g (tolist t).
  Proof.
    intros.
    compose near t on right. rewrite 2(natural).
    unfold compose. split.
    - introv heq. now rewrite heq.
    - intros. apply (shp_shapeliness). rewrite 2(shape_map).
      auto.
  Qed.

  Context
    `{ToSubset F}
    `{! Compat_ToSubset_Tolist F}.

  Lemma compat_element_tolist_natural :
    `{Natural (@tosubset F _)}.
  Proof.
    constructor; try typeclasses eauto.
    intros.
    rewrite compat_element_tolist.
    rewrite (natural (Natural := Natural_Element_Tolist)).
    reflexivity.
  Qed.

  Theorem shapely_pointwise_iff :
    forall (A B: Type) (t: F A) (f g: A -> B),
      (forall (a: A), a ∈ t -> f a = g a) <-> map f t = map g t.
  Proof.
    introv.
    rewrite shapely_map_eq_iff.
    setoid_rewrite in_iff_in_tolist.
    rewrite map_rigidly_respectful_list.
    reflexivity.
  Qed.

  Corollary shapely_pointwise :
    forall (A B: Type) (t: F A) (f g: A -> B),
      (forall (a: A), a ∈ t -> f a = g a) -> map f t = map g t.
  Proof.
   introv. rewrite shapely_pointwise_iff. auto.
  Qed.

  #[export] Instance ContainerFunctor_ShapelyFunctor :
    ContainerFunctor F :=
    {| cont_natural := compat_element_tolist_natural;
       cont_pointwise := shapely_pointwise; |}.

End ShapelyFunctor_setlike.
