From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.ContainerFunctor
  Misc.List
  Misc.Subset.

Import ContainerFunctor.Notations.
Import Subset.Notations.
Import Classes.Functor.Notations.
Import List.ListNotations.

#[local] Generalizable Variables G F A B.

(** * Shapely functors *)
(******************************************************************************)

(** ** The [shape] operation *)
(******************************************************************************)
Definition shape `{Map F} {A : Type} : F A -> F unit :=
  map (const tt).

(** *** Basic reasoning principles for <<shape>> *)
(******************************************************************************)
Theorem shape_map `{Functor F} : forall (A B : Type) (f : A -> B) (t : F A),
    shape (F := F) (map f t) =
      shape (F := F) t.
Proof.
  intros. compose near t on left.
  unfold shape. now rewrite fun_map_map.
Qed.

Theorem shape_shape `{Functor F} : forall (A : Type) (t : F A),
    shape (shape t) = shape t.
Proof.
  intros.  compose near t on left.
  unfold shape. now rewrite fun_map_map.
Qed.


Lemma shape_map_eq `{Functor F} : forall (A1 A2 B : Type) (f : A1 -> B) (g : A2 -> B) t u,
    map f t = map g u -> shape t = shape u.
Proof.

  introv hyp. cut (shape (map f t) = shape (map g u)).
  - now rewrite 2(shape_map).
  - now rewrite hyp.
Qed.

(** ** Shapeliness *)
(******************************************************************************)
Definition shapeliness (F : Type -> Type)
  `{Map F} `{Tolist F} := forall A (t1 t2 : F A),
    shape t1 = shape t2 /\ tolist t1 = tolist t2 -> t1 = t2.

(** ** Typeclass for shapely functors *)
(******************************************************************************)
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

(** * Various characterizations of shapeliness *)
(******************************************************************************)
Section listable_functor_respectful_definitions.

  Context
    (F : Type -> Type)
    `{Map F} `{Tolist F}.

  Definition tolist_map_injective := forall A B (t1 t2 : F A) (f g : A -> B),
      map f t1 = map g t2 ->
      shape t1 = shape t2 /\
      map f (tolist t1) = map g (tolist t2).

  Definition tolist_map_respectful := forall A B (t1 t2 : F A) (f g : A -> B),
      shape t1 = shape t2 ->
      map f (tolist t1) = map g (tolist t2) ->
      map f t1 = map g t2.

  Definition tolist_map_respectful_iff := forall A B (t1 t2 : F A) (f g : A -> B),
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

  Theorem tolist_map_injective_proof : tolist_map_injective F.
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
    replace t1 with (map id t1) by (now rewrite (fun_map_id (F := F))).
    replace t2 with (map id t2) by (now rewrite (fun_map_id (F := F))).
    apply hyp1. now rewrite (fun_map_id (F := list)).
  Qed.

End tolist_respectfulness_characterizations.

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
