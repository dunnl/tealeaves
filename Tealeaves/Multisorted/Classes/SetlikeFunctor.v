From Tealeaves.Multisorted Require Import
     Classes.Functor
     Functors.MSets.

Import Multisorted.Category.Notations.
#[local] Open Scope tealeaves_multi_scope.

(** * The [tomset] operation *)
Class Tomset `{ix : Index} (F : Type -> Type) :=
  tomset : forall (A : Type), F A -> mset A.

Arguments tomset {ix} F%function_scope {Tomset} {A}%type_scope _ _.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈m t" :=
    (tomset _ t x) (at level 50) : tealeaves_multi_scope.

End Notations.

Import Notations.

(** * Typeclasses for set-like functors *)
(******************************************************************************)
Section SetlikeMultisortedFunctor.

  Context
    `{ix : Index}
    (F : Type -> Type) `{! MFmap F} `{! Tomset F}.

  Class SetlikeMultisortedFunctor :=
    { qmfun_functor :> MultisortedFunctor F;
      qmfun_natural :> MultisortedNatural (@tomset ix F _);
    }.

  Class MSetPreservingTransformation
        {F G : Type -> Type}
        `{! MFmap F} `{! Tomset F}
        `{! MFmap G} `{! Tomset G}
        (η : forall A, F A -> G A) :=
    { qtrans_natural : MultisortedNatural η;
      qtrans_commute : forall A, tomset F = tomset G ∘ η A;
    }.

End SetlikeMultisortedFunctor.

(** * Notations and tactics *)
(******************************************************************************)
Ltac preimage t name :=
  match type of t with
  | mfmap mset ?f ?s ?x =>
    let hyp1 := fresh "img_in_" name in
    let hyp2 := fresh "img_eq_" name in
    destruct (proj1 preimage_fmap t) as [name [hyp1 hyp2]]
  | _ => fail "Not of the right form"
  end.

(** * Interaction between [tomset] and [fmap] *)
(******************************************************************************)
Section SetlikeMultisortedFunctor_theory.

  Context
    (F : Type -> Type)
    `{SetlikeMultisortedFunctor F}.

  Theorem in_mfmap_iff {A B} : forall (k : K) (t : F A) (b : B) (f : K -> A -> B),
      (k, b) ∈m mfmap F f t <-> exists a, (k, a) ∈m t /\ f k a = b.
  Proof.
    intros ? t ? f. compose near t on left.
    rewrite <- (mnaturality f). unfold compose.
    now rewrite preimage_fmap.
  Qed.

  Corollary in_mfmap_mono {A B} : forall (k : K) (t : F A)(a : A) (f : K -> A -> B),
      (k, a) ∈m t -> (k, f k a) ∈m mfmap F f t.
  Proof.
    intros ? ? a ? hyp. rewrite in_mfmap_iff. now exists a.
  Qed.

End SetlikeMultisortedFunctor_theory.

(** * Interaction between [tomset] and [fmapk] *)
(******************************************************************************)
Section SetlikeMultisortedFunctor_targeted_theory.

  Context
    (F : Type -> Type)
    `{SetlikeMultisortedFunctor F}.

  Theorem in_fmapk_eq_iff {A} : forall k b (t : F A) (f : A -> A),
      (k, b) ∈m fmapk F k f t <-> exists a, (k, a) ∈m t /\ f a = b.
  Proof.
    introv. unfold fmapk. rewrite (in_mfmap_iff F).
    now autorewrite* with tea_tgt.
  Qed.

  Theorem in_fmapk_neq_iff {A} : forall k1 k2 b (t : F A) (f : A -> A),
      k1 <> k2 ->
      (k2, b) ∈m fmapk F k1 f t <-> (k2, b) ∈m t.
  Proof.
    intros ? ? b ? ? neq. unfold fmapk.
    rewrite (in_mfmap_iff F). autorewrite with tea_tgt. split.
    - intros [? [? ?]]; now subst.
    - intros ?. now (exists b).
  Qed.

  Corollary in_fmapk_mono_eq {A} : forall k t a (f : A -> A),
      (k, a) ∈m t -> (k, f a) ∈m fmapk F k f t.
  Proof.
    intros ? ? a ? hyp. unfold fmapk.
    rewrite (in_mfmap_iff F). autorewrite* with tea_tgt.
    now exists a.
  Qed.

End SetlikeMultisortedFunctor_targeted_theory.
