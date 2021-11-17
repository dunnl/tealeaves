From Tealeaves Require Import
     Multisorted.Classes.Monad
     Multisorted.Functors.MSets
     Multisorted.Functors.Tag
     Multisorted.Classes.SetlikeMonad
     Multisorted.Classes.ListableFunctor
     Multisorted.Functors.MList.

Import List.Notations.
Import Multisorted.Category.Notations.
Import Multisorted.Functors.MSets.Notations.
Import Singlesorted.Classes.SetlikeFunctor.Notations.
Import Multisorted.Classes.SetlikeFunctor.Notations.
#[local] Open Scope list_scope.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

(** The statements for <<mbind>> involve an auxiliary function
    <<pack>> to wrap subtrees in existentials, as lists of type
    <<mlist>> cannot be heterogenous. *)
Section pack.

  Context `{Index} (T : K -> Type -> Type) {A B} (f : A ~k~> T B).

  Definition pack := fun k : K => fun a : A => existT (fun k => T k B) k (f k a).

End pack.

(** * Listable multisorted monads *)
(******************************************************************************)
Section ListableMultisortedMonad.

  Context
    `{ix : Index}
    (T : K -> Type -> Type)
    `{! MReturn T}
    `{forall k, MBind (T k) T}
    `{forall k, Tomlist (T k)}.

  Class ListableMultisortedMonad : Prop :=
    { lmmon_monad :> MultisortedMonad T;
      lmmon_mret : forall {A k},
          tomlist (T k) ∘ mret T k (A:=A) = mret (const mlist) k;
      lmmon_mbind : forall k {A B} (f : forall k, A -> T k B),
          tomlist (T k) ∘ mbind (T k) f =
          mbind mlist (fun k => tomlist (T k) ∘ f k) ∘ tomlist (T k);
      lmmon_respectful : forall k A B (x y : T k A) (f g : A ~k~> T B),
          mshape (T k) x = mshape (T k) y ->
          mfmap mlist (pack T f) (tomlist (T k) x) = mfmap mlist (pack T g) (tomlist (T k) y) ->
          mbind (T k) f x = mbind (T k) g y
    }.

End ListableMultisortedMonad.

(** * Listable multisorted modules *)
(******************************************************************************)
Section ListableMultisortedModule.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{! MReturn T}
    `{! forall k, MBind (T k) T}
    `{ forall k, Tomlist (T k)}
    `{! Tomlist F} `{! MBind F T}.

  Class ListableMultisortedModule : Prop :=
    { lrmod_rmod :> MultisortedRightModule F T;
      lrmod_monad :> ListableMultisortedMonad T;
      lrmod_mbind : forall `(f : A ~k~> T B),
          tomlist F ∘ mbind F f = mbind mlist (fun k => tomlist (T k) ∘ f k) ∘ tomlist F;
      lrmod_respectful : forall A B (x y : F A) (f g : A ~k~> T B),
          mshape F x = mshape F y ->
          mfmap mlist (pack T f) (tomlist F x) = mfmap mlist (pack T g) (tomlist F y) ->
          mbind F f x = mbind F g y
    }.

End ListableMultisortedModule.

(** * [mlist] is a listable monad *)
(** For good measure, we prove here that [mlist] is indeed a listable monad. We
do not expose this instance globally because it is probably not useful and may
be annoying when one infers quantifiable instances from generic listable
instances. *)
(******************************************************************************)
Section mlist_is_listable.

  Context
    `{ix : Index}.

  #[global] Instance tomlist_mlist `{Index} : Tomlist mlist :=
    fun A => @id (mlist A).

  Theorem lmmon_mret_mlist : forall {A k},
      tomlist (const mlist k) ∘ mret (const mlist) k (A:=A) = mret (const mlist) k.
  Proof.
    reflexivity.
  Qed.

  Theorem lmmon_mbind_mlist : forall {A B} (f : forall k, A -> const mlist k B),
      tomlist mlist ∘ mbind mlist f =
      mbind mlist (fun k => tomlist (const mlist k) ∘ f k) ∘ tomlist mlist.
  Proof.
    reflexivity.
  Qed.

End mlist_is_listable.

(** * Respectfulness conditions *)
(******************************************************************************)
Section ListableMonad_respectfulness.

  Context
    `{ListableMultisortedMonad T}.

  Lemma setlike_respectful_listable_monad : forall k A B (t : T k A) (f g : A ~k~> T B),
      (forall k a, (k, a) ∈m t -> f k a = g k a) -> mbind (T k) f t = mbind (T k) g t.
  Proof.
    introv hyp. apply (lmmon_respectful T).
    - reflexivity.
    - setoid_rewrite in_iff_in_mlist in hyp. induction (tomlist (T k) t).
      + reflexivity.
      + destruct a as [k' a]. rewrite mfmap_mlist_cons; cbn.
        fequal.
        { fequal. cbv. fequal. apply hyp. now left. }
        { apply IHm. intros. apply hyp. now right. }
  Qed.

  Lemma shapeliness_listable_monad : forall k A (x y : T k A),
      mshape (T k) x = mshape (T k) y ->
      tomlist (T k) x = tomlist (T k) y ->
      x = y.
  Proof.
    intros. replace x with (mbind (T k) (mret T) x)
      by now (rewrite (mmon_mbind_mret T)).
    replace y with (mbind (T k) (mret T) y)
      by now (rewrite (mmon_mbind_mret T)).
    apply (lmmon_respectful T).
    - auto.
    - generalize dependent (tomlist (T k) y). induction (tomlist (T k) x).
      + introv hyp. cbn. rewrite <- hyp. reflexivity.
      + introv hyp. destruct a as [j a]. rewrite <- hyp.
        rewrite mfmap_mlist_cons; cbn. fequal.
  Qed.

End ListableMonad_respectfulness.

Section ListableModule_respectfulness.

  Context
    `{ListableMultisortedModule F T}.

  Lemma setlike_respectful_listable_module : forall A B (t : F A) (f g : A ~k~> T B),
      (forall k a, (k, a) ∈m t -> f k a = g k a) -> mbind F f t = mbind F g t.
    Proof.
      introv hyp. apply (lrmod_respectful F T).
      - reflexivity.
      - setoid_rewrite in_iff_in_mlist in hyp. induction (tomlist F t).
        + reflexivity.
        + destruct a as [k' a]. rewrite mfmap_mlist_cons; cbn.
          fequal.
          { fequal. cbv. fequal. apply hyp. now left. }
          { apply IHm. intros. apply hyp. now right. }
    Qed.

    Lemma shapeliness_listable_module : forall A (x y : F A),
        mshape F x = mshape F y ->
        tomlist F x = tomlist F y ->
        x = y.
    Proof.
      intros. replace x with (mbind F (mret T) x)
        by now (rewrite (rmod_mret F T)).
      replace y with (mbind F (mret T) y)
        by now (rewrite (rmod_mret F T)).
      apply (lrmod_respectful F T).
      - auto.
      - generalize dependent (tomlist F y). induction (tomlist F x).
        + introv hyp. cbn. rewrite <- hyp. reflexivity.
        + introv hyp. destruct a as [k a]. rewrite <- hyp.
          rewrite mfmap_mlist_cons; cbn. fequal.
    Qed.

End ListableModule_respectfulness.

(** * Listable monads  are set-like *)
(******************************************************************************)
Section SetlikeMonad_Listable.

  Context
    `{ListableMultisortedMonad T}.

  Theorem qmmon_mret_Listable : forall (k : K) (A : Type),
      tomset (T k) ∘ mret T k (A:=A) = mret (const mset) k.
  Proof.
    introv. unfold tomset, tomset_Listable, compose. ext a.
    compose near a on left. rewrite (lmmon_mret T).
    compose near a on left. rewrite (qmmon_mret_mlist).
    reflexivity.
  Qed.

  Theorem qmmon_mbind_Listable : forall A B (f : A ~k~> T B) (k : K),
      tomset (T k) ∘ mbind (T k) f =
      mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset (T k).
  Proof.
    intros. unfold tomset, tomset_Listable, compose. ext t.
    compose near t on left. rewrite (lmmon_mbind T). unfold compose.
    compose near (tomlist (T k) t). rewrite (qmmon_mbind_mlist). unfold compose.
    reflexivity.
  Qed.

  #[global] Instance SetlikeMultisortedMonad_Listable : SetlikeMultisortedMonad T :=
    {| qmmon_mret := qmmon_mret_Listable;
       qmmon_mbind := qmmon_mbind_Listable;
       qmmon_respectful := setlike_respectful_listable_monad;
    |}.

End SetlikeMonad_Listable.

(** * Listable modules are set-like *)
(******************************************************************************)
Section quantifiable_of_listable_module.

  Context
    `{ListableMultisortedModule F T}.

  Theorem qrmod_mbind_Listable : forall A B (f : A ~k~> T B),
      tomset F ∘ mbind F f = mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset F.
  Proof.
    intros. unfold tomset, tomset_Listable, compose. ext t.
    compose near t on left. rewrite (lrmod_mbind F T). unfold compose.
    compose near (tomlist F t). rewrite (qmmon_mbind_mlist). unfold compose.
    reflexivity.
  Qed.

  #[global] Instance SetlikeMultisortedModule_Listable : SetlikeMultisortedModule F T :=
    {| qrmod_mbind := qrmod_mbind_Listable;
       qrmod_respectful := setlike_respectful_listable_module;
    |}.

End quantifiable_of_listable_module.

(** * Typeclass inclusions *)
(******************************************************************************)

(** ** Listable monads are listable modules *)
(******************************************************************************)
Section listable_module_of_monad.

  Context
    `{ListableMultisortedMonad T}.

  Instance ListableMultisortedModule_Monad {k} : ListableMultisortedModule (T k) T :=
    {| lrmod_mbind := fun A B => lmmon_mbind T k;
       lrmod_rmod := MultisortedRightModule_Monad k;
       lrmod_respectful := lmmon_respectful T k;
    |}.

End listable_module_of_monad.

(** ** Carriers of listable modules form listable functors *)
(******************************************************************************)
Section listable_functor_of_module.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{ListableMultisortedModule (ix:=ix) F T}.

  #[global] Instance Natural_module_tomlist : MultisortedNatural (@tomlist ix F _).
  Proof.
    introv. unfold_ops @MFmap_rmod.
    rewrite (lrmod_mbind F T). do 2 fequal.
    ext k. reassociate <- on right.
    now rewrite (lmmon_mret T).
  Qed.

  #[global] Instance ListableFunctor_Module : ListableMultisortedFunctor F :=
    {| lfun_shapeliness := shapeliness_listable_module; |}.

End listable_functor_of_module.

(** * Properties of global [mbind] over listable functors *)
(******************************************************************************)
Section listable_module_global.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{ListableMultisortedModule (ix:=ix) F T}.

  Theorem tomlist_mbind {A B} : forall (f : A ~k~> T B),
      tomlist F ∘ mbind F f = mbind mlist (fun k => tomlist (T k) ∘ f k) ∘ tomlist F.
  Proof.
    introv. now rewrite <- (lrmod_mbind F T).
  Qed.

  Existing Instance lrmod_monad.

  (** ** Interaction between [tomlist] and [bindk] *)
  (******************************************************************************)
  Theorem tomlist_bindk {A} k : forall (f : A -> T k A),
      tomlist F ∘ bindk F k f = bindk mlist k (tomlist (T k) ∘ f) ∘ tomlist F.
  Proof.
    introv. unfold bindk. rewrite (lrmod_mbind F T).
    fequal. fequal. ext k'. destruct_eq_args k k'.
    - now do 2 rewrite btg_eq.
    - do 2 (rewrite btg_neq; auto).
      now rewrite (lmmon_mret T).
  Qed.

  Theorem tolistk_bindk_eq {A} k : forall (f : A -> T k A),
      tolistk F k ∘ bindk F k f =
      bind list (tolistk (T k) k ∘ f) ∘ tolistk F k.
  Proof.
    introv. unfold tolistk.
    reassociate -> on left. rewrite tomlist_bindk.
    reassociate <- on left. rewrite (filterk_bindk_eq).
    reflexivity.
  Qed.

  Theorem tolistk_bindk_neq {A} k j : forall (f : A -> T k A),
      k <> j ->
      tolistk F j ∘ bindk F k f =
      filterk j ∘ bindk mlist k (tomlist (T k) ∘ f) ∘ tomlist F.
  Proof.
    introv neq. unfold tolistk.
    reassociate -> on left. now rewrite tomlist_bindk.
  Qed.

End listable_module_global.
