From Tealeaves Require Import
  Classes.Algebraic.Listable.Functor
  Theory.Algebraic.Listable.Shape
  Theory.Algebraic.Listable.Functor.Category.

Import Sets.Notations.
Import Setlike.Functor.Notations.
Import Sets.Notations.
Import List.ListNotations.
#[local] Open Scope list_scope.
#[local] Generalizable Variables F M A B ϕ.

(** * Properties of listable functors *)
(******************************************************************************)

(** ** Respectfulness conditions for listable functors *)
(******************************************************************************)
Section listable_functor_respectful_definitions.

  Context
    (F : Type -> Type)
    `{Fmap F} `{Tolist F}.

  Definition tolist_fmap_injective := forall A B (t1 t2 : F A) (f g : A -> B),
      fmap F f t1 = fmap F g t2 ->
      shape F t1 = shape F t2 /\
      fmap list f (tolist F t1) = fmap list g (tolist F t2).

  Definition tolist_fmap_respectful := forall A B (t1 t2 : F A) (f g : A -> B),
      shape F t1 = shape F t2 ->
      fmap list f (tolist F t1) = fmap list g (tolist F t2) ->
      fmap F f t1 = fmap F g t2.

  Definition tolist_fmap_respectful_iff := forall A B (t1 t2 : F A) (f g : A -> B),
      shape F t1 = shape F t2 /\
      fmap list f (tolist F t1) = fmap list g (tolist F t2) <->
      fmap F f t1 = fmap F g t2.

End listable_functor_respectful_definitions.

Ltac unfold_list_properness :=
  unfold shapeliness,
  tolist_fmap_respectful,
    tolist_fmap_respectful_iff in *.

(** ** Listable functors are set-like *)
(******************************************************************************)
#[export] Instance Toset_Tolist `{Tolist F} : Toset F :=
  fun A => toset list ∘ tolist F.

#[export] Instance: forall `{ListableFunctor F}, Natural (@toset F _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold toset, Toset_Tolist. ext t.
  reassociate <- on left. rewrite (natural (G:=set)).
  reassociate -> on left. now rewrite natural.
Qed.

Theorem in_iff_in_list `{Tolist F} : forall (A : Type) (t : F A) (a : A),
    a ∈ t <-> a ∈ tolist F t.
Proof.
  reflexivity.
Qed.

Section ListableFunctor_setlike.

  Context
    `{ListableFunctor F}.

  Lemma listable_equal_iff :
    forall (A : Type) (t u : F A),
      t = u <-> shape F t = shape F u /\ tolist F t = tolist F u.
  Proof.
    intros. split.
    + intros; subst; auto.
    + apply (lfun_shapeliness F).
  Qed.

  (** Two maps over [t] are equal when they're equal on t's contents. *)
  Lemma listable_fmap_equal :
    forall (A B : Type) (t : F A) (f g : A -> B),
      fmap F f t = fmap F g t <->
      fmap list f (tolist F t) = fmap list g (tolist F t).
  Proof.
    unfold_list_properness. intros.
    compose near t on right. rewrite 2(natural).
    unfold compose. split.
    - introv heq. now rewrite heq.
    - intros. apply (lfun_shapeliness F). rewrite 2(shape_fmap).
      auto.
  Qed.

  (** Listable functors satisfy the "rigid" version of the respectfulness property. *)
  Theorem listable_rigidly_respectful :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) <-> fmap F f t = fmap F g t.
  Proof.
    introv. rewrite listable_fmap_equal.
    setoid_rewrite in_iff_in_list.
    now rewrite fmap_rigidly_respectful_list.
  Qed.

  Corollary listable_respectful :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) -> fmap F f t = fmap F g t.
  Proof.
   intros. now rewrite <- listable_rigidly_respectful.
 Qed.

  #[export] Instance SetlikeFunctor_Listable : SetlikeFunctor F :=
    {| xfun_respectful := listable_respectful; |}.

End ListableFunctor_setlike.


(** ** Equivalence with shapeliness *)
(******************************************************************************)
Section tolist_respectfulness_characterizations.

  Context
    `{ListableFunctor F}.

  Theorem tolist_fmap_injective_proof : tolist_fmap_injective F.
  Proof.
    introv heq. split.
    - cut (shape F (fmap F f t1) = shape F (fmap F g t2)).
      + now rewrite 2(shape_fmap).
      + now rewrite heq.
    - compose near t1; compose near t2.
      rewrite 2natural.
      unfold compose; now rewrite heq.
  Qed.

  Lemma shapeliness_equiv_1 : shapeliness F -> tolist_fmap_respectful F.
  Proof.
    unfold tolist_fmap_respectful.
    introv hyp hshape hcontents.
    apply hyp. split.
    - now rewrite 2(shape_fmap).
    - compose near t1 on left; compose near t2 on right.
      now rewrite <- 2(natural).
  Qed.

  Lemma shapeliness_equiv_2: tolist_fmap_respectful F -> tolist_fmap_respectful_iff F.
  Proof.
    unfold tolist_fmap_respectful, tolist_fmap_respectful_iff.
    intros. split.
    - introv [? ?]. auto.
    - apply tolist_fmap_injective_proof.
  Qed.

  Lemma shapeliness_equiv_3: tolist_fmap_respectful_iff F -> shapeliness F.
  Proof.
    unfold shapeliness, tolist_fmap_respectful_iff.
    introv hyp1 hyp2.
    replace t1 with (fmap F id t1) by (now rewrite (fun_fmap_id F)).
    replace t2 with (fmap F id t2) by (now rewrite (fun_fmap_id F)).
    apply hyp1. now rewrite (fun_fmap_id list).
  Qed.

End tolist_respectfulness_characterizations.

(** ** Miscellaneous properties of listable functors *)
(******************************************************************************)
Section ListableFunctor_theory.

  Context
    (F : Type -> Type)
    `{ListableFunctor F}.

  Corollary tolist_fmap `(t : F A) `(f : A -> B) (a : A) :
    tolist F (fmap F f t) = fmap list f (tolist F t).
  Proof.
    intros. compose near t on left.
    now rewrite <- natural.
  Qed.

  Corollary tolist_fmap_rigidly_respectful_id :
    forall (A : Type) (t : F A) (f : A -> A),
      (forall (a : A), a ∈ t -> f a = a) <-> fmap F f t = t.
  Proof.
    introv. replace t with (fmap F id t) at 2
      by now rewrite (fun_fmap_id F).
    now rewrite listable_rigidly_respectful.
  Qed.

End ListableFunctor_theory.

(** * [fold] and [foldMap] operations *)
(******************************************************************************)
Section fold.

  Context
    `{ListableFunctor F}.

  Definition fold `{Monoid_op M} `{Monoid_unit M} : F M -> M :=
    List.fold ∘ tolist F.

  Definition foldMap {A} `{Monoid_op M} `{Monoid_unit M} (f : A -> M) : F A -> M :=
    fold ∘ fmap F f.

  Lemma fold_mon_hom : forall `(ϕ : M1 -> M2) `{Hϕ : Monoid_Morphism M1 M2 ϕ},
      ϕ ∘ fold = fold ∘ fmap F ϕ.
  Proof.
    intros ? ? ϕ; intros.
    change left (ϕ ∘ List.fold ∘ tolist F).
    change right (List.fold ∘ (tolist F ∘ fmap F ϕ)).
    rewrite <- natural.
    now rewrite (List.fold_mon_hom ϕ).
  Qed.

  Lemma foldMap_fmap {A B} `{Monoid M} {f : A -> B} {g : B -> M} :
    foldMap g ∘ fmap F f = foldMap (g ∘ f).
  Proof.
    intros. unfold foldMap.
    now rewrite <- (fun_fmap_fmap F).
  Qed.

  Theorem foldMap_hom {A} `{Monoid_Morphism M1 M2 ϕ} {f : A -> M1} :
    ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
  Proof.
    intros. unfold foldMap.
    reassociate <- on left.
    rewrite (fold_mon_hom ϕ).
    now rewrite <- (fun_fmap_fmap F).
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
