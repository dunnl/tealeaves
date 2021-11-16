From Tealeaves.Multisorted Require Export
     Classes.Monad
     Classes.SetlikeFunctor
     Functors.MSets.

Import Multisorted.Classes.SetlikeFunctor.Notations.
Import Multisorted.Category.Notations.
#[local] Open Scope tealeaves_multi_scope.

(** * Set-like multisorted monads *)
(******************************************************************************)
Section SetlikeMultisortedMonad.

  Context
    `{ix : Index}
    (T : K -> Type -> Type)
    `{! MReturn T}
    `{forall k, MBind (T k) T}
    `{forall k, Tomset (T k)}.

  Class SetlikeMultisortedMonad :=
    { qmmon_monad :> MultisortedMonad T;
      qmmon_mret :
        `(tomset (T k) ∘ mret T k = mret (const mset) k (A := A));
      qmmon_mbind : forall `(f : A ~k~> T B) (k : K),
          tomset (T k) ∘ mbind (T k) f = mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset (T k);
    }.

End SetlikeMultisortedMonad.

(** * Set-like multisorted modules *)
(******************************************************************************)
Section SetlikeMultisortedModule.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{! MFmap F} `{! Tomset F} `{! MBind F T}
    `{! MReturn T} `{! forall k, MBind (T k) T} `{forall k, Tomset (T k)}.

  Class SetlikeMultisortedModule : Prop :=
    { qrmod_module :> MultisortedRightModule F T;
      qrmod_monad :> SetlikeMultisortedMonad T;
      qrmod_mbind : forall `(f : A ~k~> T B),
          tomset F ∘ mbind F f = mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset F;
    }.

End SetlikeMultisortedModule.

(** * Typeclass inclusions *)
(******************************************************************************)

(** ** Set-like monads are set-like right modules *)
(******************************************************************************)
Section quantifiable_monad_to_module.

  Context
    `{SetlikeMultisortedMonad T}
    (k : K).

  Instance SetlikeMultisortedModule_Monad :
    SetlikeMultisortedModule (T k) T :=
    {| qrmod_mbind := fun A B f => qmmon_mbind T f k;
       qrmod_module := MultisortedRightModule_Monad k;
    |}.

End quantifiable_monad_to_module.

(** ** Carriers of quantifiable modules form quantifiable functors *)
(******************************************************************************)
Section quantifiable_functor_module.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{SetlikeMultisortedModule (ix := ix) F T}.

  #[global] Instance Natural_module_tomset : MultisortedNatural (@tomset _ F _).
  Proof.
    introv. unfold_ops @MFmap_rmod. ext t b.
    rewrite (qrmod_mbind F T).
    do 2 fequal. ext k.
    reassociate <- on right.
    now rewrite (qmmon_mret T).
  Qed.

  #[global] Instance: SetlikeMultisortedFunctor F := {}.

End quantifiable_functor_module.

(** * Properties of quantifiable modules *)
(******************************************************************************)
Section quantifiable_module_theory.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{SetlikeMultisortedModule (ix:=ix) F T}.

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
    `{SetlikeMultisortedModule (ix:=ix) F T}.

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
