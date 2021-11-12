From Tealeaves.Multisorted Require Import
     Functors MSets.

Import Multisorted.Category.Notations.
Local Open Scope tealeaves_multi_scope.

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
Section quantifiable_typeclasses.

  Context
    `{ix : Index}.

  (** ** Quantifiable functors *)
  (******************************************************************************)
  Class QuantifiableMFunctor (F : Type -> Type) `{! Mfmap F} `{! Tomset F}  :=
    { qmfun_functor :> MFunctor F _;
      qmfun_natural :> Natural (@tomset ix F _);
    }.

  Class MsetreservingTransformation
        {F G : Type -> Type}
        `{! Mfmap F} `{! Tomset F}
        `{! Mfmap G} `{! Tomset G}
        (η : forall A, F A -> G A) :=
    { qtrans_natural : Natural η;
      qtrans_commute : forall A, tomset F = tomset G ∘ η A;
    }.

  (** ** Quantifiable monad systems *)
  (******************************************************************************)
  Section quantifiable_monad_class.

    Context
      (T : K -> Type -> Type)
      `{! Mreturn T}
      `{forall k, Mbind (T k) T}
      `{forall k, Tomset (T k)}.

    Class QuantifiableMMonad : Prop :=
      { qmmon_monad :> MMonad T;
        qmmon_mret : forall {A k},
            tomset (T k) ∘ mret T k (A:=A) = mret (const mset) k;
        qmmon_mbind : forall {A B k} (f : forall k, A -> T k B),
            tomset (T k) ∘ mbind (T k) f = mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset (T k);
      }.

  End quantifiable_monad_class.

  (** ** Quantifiable modules *)
  (******************************************************************************)
  Section quantifiable_module_class.

    Context
      (F : Type -> Type)
      (T : K -> Type -> Type)
      `{! Mfmap F}
      `{! Tomset F}
      `{! Mreturn T}
      `{! forall k, Mbind (T k) T}
      `{! Mbind F T}
      `{forall k, Tomset (T k)}.

    Class QuantifiableRightModule : Prop :=
      { qrmod_module :> RightModule F T;
        qrmod_monad :> QuantifiableMMonad T;
        qrmod_mbind : forall {A B} (f : forall k, A -> T k B),
            tomset F ∘ mbind F f = mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset F;
      }.

  End quantifiable_module_class.

  (** ** Typeclass inclusions *)
  (** *** Quantifiable monads are quantifiable modules *)
  (******************************************************************************)
  Section quantifiable_monad_to_module.

    Context
      `{QuantifiableMMonad T}.

    Instance Quantifiable_Module_MMonad {k} :
      QuantifiableRightModule (T k) T :=
      {| qrmod_mbind := fun A B => qmmon_mbind T;
         qrmod_module := Module_MMonad k;
      |}.

  End quantifiable_monad_to_module.

  (** *** Carriers of quantifiable modules form quantifiable functors *)
  (******************************************************************************)
  Section quantifiable_functor_module.

    Context
      (F : Type -> Type)
      (T : K -> Type -> Type)
      `{QuantifiableRightModule F T}.

    #[global] Instance Natural_module_tomset : Natural (@tomset _ F _).
    Proof.
      introv. unfold_mfmap @Mfmap_rmod. ext t b.
      rewrite (qrmod_mbind F T).
      do 2 fequal. ext k.
      reassociate <- on right.
      now rewrite (qmmon_mret T).
    Qed.

    #[global] Instance: QuantifiableMFunctor F := {}.

  End quantifiable_functor_module.

End quantifiable_typeclasses.

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
Section quantifiable_functor_theory.

  Context
    (F : Type -> Type)
    `{QuantifiableMFunctor F}.

  Theorem in_mfmap_iff {A B} : forall (k : K) (t : F A) (b : B) (f : K -> A -> B),
      (k, b) ∈m mfmap F f t <-> exists a, (k, a) ∈m t /\ f k a = b.
  Proof.
    intros ? t ? f. compose near t on left.
    rewrite <- (naturality f). unfold compose.
    now rewrite preimage_fmap.
  Qed.

  Corollary in_mfmap_mono {A B} : forall (k : K) (t : F A)(a : A) (f : K -> A -> B),
      (k, a) ∈m t -> (k, f k a) ∈m mfmap F f t.
  Proof.
    intros ? ? a ? hyp. rewrite in_mfmap_iff. now exists a.
  Qed.

End quantifiable_functor_theory.

(** * Interaction between [tomset] and [fmapk] *)
(******************************************************************************)
Section quantifiable_functor_targeted_theory.

  Context
    (F : Type -> Type)
    `{QuantifiableMFunctor F}.

  (** ** Interaction between [tomset] and [fmapk] *)
  (******************************************************************************)
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

End quantifiable_functor_targeted_theory.

(** * Properties of quantifiable modules *)
(******************************************************************************)
Section quantifiable_module_theory.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{QuantifiableRightModule (ix:=ix) F T}.

  (** ** Interaction between [toset] and [ret], [bind] *)
  (******************************************************************************)
  Theorem in_mret_iff {A} : forall (k k' : K) (a a' : A),
      (k', a') ∈m mret T k a <-> k' = k /\ a' = a.
  Proof.
    intros ? ? a ?. compose near a on left.
    rewrite (qmmon_mret T).
    split; intro hyp; now inverts hyp.
  Qed.

  Corollary in_mret_iff_eq {A} : forall (k : K) (a a' : A),
      (k, a') ∈m mret T k a <-> a' = a.
  Proof.
    intros. rewrite in_mret_iff. intuition.
  Qed.

  Corollary in_mret_iff_neq {A} : forall (k k' : K) (a a' : A),
      k <> k' -> (k', a') ∈m mret T k a <-> False.
  Proof.
    introv. rewrite in_mret_iff. intuition.
  Qed.

  Theorem in_mbind_iff {A B} : forall (t : F A) (k : K) (b : B) (f : forall k, A -> T k B),
      (k, b) ∈m mbind F f t <->
      exists (k1 : K) (a : A), (k1, a) ∈m t /\ (k, b) ∈m f k1 a.
  Proof.
    introv. compose near t on left.
    now rewrite (qrmod_mbind F T), mbind_mset_spec.
  Qed.

End quantifiable_module_theory.

(** * Properties of targeted substitution *)
(******************************************************************************)
Section quantifiable_module_targeted_theory.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{QuantifiableRightModule (ix:=ix) F T}.

  (** ** [tomset] and [bindk] *)
  (******************************************************************************)
  Theorem in_bindk_iff_eq {A} : forall (t : F A) (k : K) (b : A) (f : A -> T k A),
      (k, b) ∈m bindk F k f t <->
      exists (a : A), (k, a) ∈m t /\ (k, b) ∈m f a.
  Proof.
    intros t k ? ?. unfold bindk. rewrite (in_mbind_iff F T). split.
    - intros [k' [a [h1 h2]]]. destruct_eq_args k k'.
      + rewrite btg_eq in h2. now (exists a).
      + rewrite btg_neq in h2; auto.
        rewrite (in_mret_iff F T) in h2.
        now inverts h2.
    - intros [a [h1 h2]]. exists k a. now rewrite btg_eq.
  Qed.

  Theorem in_bindk_iff_neq {A} : forall (t : F A) (k k' : K) (b : A) (f : A -> T k A),
      k <> k' ->
      (k', b) ∈m bindk F k f t <-> (k', b) ∈m t \/ exists (a : A),
          (k, a) ∈m t /\ (k', b) ∈m f a.
  Proof.
    intros t k k' b ? neq. unfold bindk. rewrite (in_mbind_iff F T). split.
    - intros [k'' [a [h1 h2]]]. destruct_eq_args k k''.
      + rewrite btg_eq in h2. now (right; exists a).
      + rewrite btg_neq in h2; auto.
        rewrite (in_mret_iff F T) in h2.
        left. now inverts h2.
    - intros [h | [a [h1 h2]]].
      + exists k' b.
        rewrite (btg_neq); auto.
        now rewrite (in_mret_iff F T).
      + exists k a. now rewrite (btg_eq).
  Qed.

End quantifiable_module_targeted_theory.
