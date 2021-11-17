From Tealeaves Require Import
     Multisorted.Classes.Monad
     Multisorted.Functors.MSets
     Multisorted.Functors.Tag
     Multisorted.Classes.SetlikeMonad
     Multisorted.Functors.MList.

Import List.Notations.
Import Multisorted.Category.Notations.
Import Multisorted.Functors.MSets.Notations.
Import Singlesorted.Classes.SetlikeFunctor.Notations.
Import Multisorted.Classes.SetlikeFunctor.Notations.
#[local] Open Scope list_scope.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

(** * The [mshape] operation *)
(** [mshape] is a multisorted analogue of [shape]. The operation
    replaces each leaf of a term <<t : F A>> with the sole element
    <<tt>> of type [unit]. *)
(******************************************************************************)
Definition mshape (F : Type -> Type) `{MFmap F} {A} : F A -> F unit :=
  mfmap F (fun A a => tt).

(** ** General  properties of [mshape] *)
(******************************************************************************)
Section mshape_lemmas.

  Context
    `{MultisortedFunctor F}.

  Lemma mshape_mfmap1 : forall A B (f : A -k-> B),
      mshape F ∘ mfmap F f = mshape F.
  Proof.
    intros. unfold mshape. now rewrite (mfun_mfmap_mfmap F).
  Qed.

  Corollary mshape_mfmap2 : forall A B (f : A -k-> B) (t : F A),
      mshape F (mfmap F f t) = mshape F t.
  Proof.
    intros. compose near t on left. now rewrite (mshape_mfmap1).
  Qed.

  Lemma mshape_mshape : forall A,
      mshape F ∘ mshape (A:=A) F = mshape F.
  Proof.
    intros. unfold mshape.
    now rewrite (mfun_mfmap_mfmap F).
  Qed.

End mshape_lemmas.

(** ** Reasoning principles for [mshape] on <<mlist>>s *)
(******************************************************************************)
Section mshape_mlist.

  Context
    `{Index}.

  Lemma mshape_mlist_nil : forall A,
      mshape mlist (@nil (K * A)) = @nil (K * unit).
  Proof.
    reflexivity.
  Qed.

  Lemma mshape_mlist_one : forall A (k : K) (a : A),
      mshape mlist [ (k, a) ] = [ (k, tt) ].
  Proof.
    reflexivity.
  Qed.

  Lemma mshape_mlist_cons : forall A (k : K) (a : A) (l : mlist A),
      mshape mlist ((k, a) :: l) = (k, tt) :: mshape mlist l.
  Proof.
    reflexivity.
  Qed.

  Lemma mshape_mlist_app : forall A (l1 l2 : mlist A),
      mshape mlist (l1 ++ l2) = mshape mlist l1 ++ mshape mlist l2.
  Proof.
    intros. unfold mshape. now rewrite mfmap_mlist_app.
  Qed.

  Lemma mshape_mlist_nil_iff : forall A (l : mlist A),
      mshape mlist l = @nil (Tag unit) <-> l = [].
  Proof.
    induction l as [| a ? ?]. easy.
    split; intro contra; destruct a; now inverts contra.
  Qed.

  Theorem mshape_inv_app_r : forall A (l1 l2 r1 r2: mlist A),
      mshape mlist r1 = mshape mlist r2 ->
      mshape mlist (l1 ++ r1) = mshape mlist (l2 ++ r2) <->
      mshape mlist l1 = mshape mlist l2.
  Proof.
    introv heq. rewrite 2(mshape_mlist_app). rewrite heq.
    split.
    - intros. unfold mlist in l1, l2, r1, r2.
      eapply List.app_inv_tail. eassumption.
    - intros hyp; now rewrite hyp.
  Qed.

  Theorem mshape_mlist_inv_app_l : forall A (l1 l2 r1 r2: mlist A),
      mshape mlist l1 = mshape mlist l2 ->
      mshape mlist (l1 ++ r1) = mshape mlist (l2 ++ r2) <->
      mshape mlist r1 = mshape mlist r2.
  Proof.
    introv heq. rewrite 2(mshape_mlist_app). rewrite heq.
    split.
    - intros; eapply List.app_inv_head; eassumption.
    - intros hyp; now rewrite hyp.
  Qed.

  Theorem mshape_mlist_inv_cons_iff : forall A (l1 l2 : mlist A) (k1 k2 : K) (a1 a2 : A),
      mshape mlist ((k1, a1) :: l1) = mshape mlist ((k2, a2) :: l2) <->
      k1 = k2 /\ mshape mlist l1 = mshape mlist l2.
  Proof.
    introv. rewrite 2(mshape_mlist_cons).
    split; [introv hyp | introv [hyp1 hyp2]]. now inverts hyp.
    now rewrite hyp1, hyp2.
  Qed.

  Corollary mshape_mlist_inv_cons_iff_eq : forall A (l1 l2 : mlist A) (k : K) (a1 a2 : A),
      mshape mlist ((k, a1) :: l1) = mshape mlist ((k, a2) :: l2) <->
      mshape mlist l1 = mshape mlist l2.
  Proof.
    introv. rewrite mshape_mlist_inv_cons_iff. intuition.
  Qed.

  Corollary mshape_mlist_inv_cons_tail : forall A (l1 l2 : mlist A) (k1 k2 : K) (a1 a2 : A),
      mshape mlist ((k1, a1) :: l1) = mshape mlist ((k2, a2) :: l2) ->
      mshape mlist l1 = mshape mlist l2.
  Proof.
    introv. rewrite mshape_mlist_inv_cons_iff. intuition.
  Qed.
  Theorem mlist_inv_app_ll : forall A (l1 l2 r1 r2 : mlist A),
      mshape mlist l1 = mshape mlist l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| (k1, a1) ? IHl1 ];
                induction l2 as [| (k2, a2) ? IHl2 ].
    - reflexivity.
    - introv mshape_eq hyp. now inverts mshape_eq.
    - introv mshape_eq hyp. now inverts mshape_eq.
    - introv mshape_eq heq.
      rewrite mshape_mlist_inv_cons_iff in mshape_eq;
        destruct mshape_eq as [? ?].
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem mlist_inv_app_rl : forall A (l1 l2 r1 r2 : mlist A),
      mshape mlist r1 = mshape mlist r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| (?, ?) ? IHl1 ];
                induction l2 as [| (?, ?) ? IHl2 ].
    - reflexivity.
    - introv mshape_eq heq. apply (mlist_inv_app_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- mshape_inv_app_r. now rewrite heq. auto.
      + assumption.
    - introv mshape_eq heq. apply (mlist_inv_app_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- mshape_inv_app_r. now rewrite heq. auto.
      + assumption.
    - introv mshape_eq heq.
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem mlist_inv_app_lr : forall A (l1 l2 r1 r2 : mlist A),
      mshape mlist l1 = mshape mlist l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eapply List.app_inv_head; eassumption. }
    { eauto using mlist_inv_app_ll. }
  Qed.

  Theorem mlist_inv_app_rr : forall A (l1 l2 r1 r2 : mlist A),
      mshape mlist r1 = mshape mlist r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eapply List.app_inv_head; eassumption. }
    { eauto using mlist_inv_app_rl. }
  Qed.

  Theorem inv_app_eq : forall A (l1 l2 r1 r2 : mlist A),
      mshape mlist l1 = mshape mlist l2 \/ mshape mlist r1 = mshape mlist r2 ->
      l1 ++ r1 = l2 ++ r2 <-> l1 = l2 /\ r1 = r2.
  Proof.
    introv [hyp | hyp]; split.
    - introv heq. split. eapply mlist_inv_app_ll; eauto.
      eapply mlist_inv_app_lr; eauto.
    - introv [? ?]. now subst.
    - introv heq. split. eapply mlist_inv_app_rl; eauto.
      eapply mlist_inv_app_rr; eauto.
    - introv [? ?]. now subst.
  Qed.

End mshape_mlist.

(** ** Inverting equalities between <<mfmap>> over lists *)
(******************************************************************************)
Section mlist_mfmap_inversion.

  Context
    `{Index}.

  Lemma mfmap_mlist_app_inv_l : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l1 = mfmap mlist g l1.
  Proof.
    introv hyp. rewrite 2(mfmap_mlist_app) in hyp.
    eapply mlist_inv_app_rl. 2: eauto.
    now rewrite 2(mshape_mfmap2).
  Qed.

  Lemma mfmap_mlist_app_inv_r : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l2 = mfmap mlist g l2.
  Proof.
    introv hyp. rewrite 2(mfmap_mlist_app) in hyp.
    eapply mlist_inv_app_lr. 2: eauto.
    now rewrite 2(mshape_mfmap2).
  Qed.

  Lemma mfmap_mlist_app_inv : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l1 = mfmap mlist g l1 /\
      mfmap mlist f l2 = mfmap mlist g l2.
  Proof.
    intros; split; eauto using mfmap_mlist_app_inv_l, mfmap_mlist_app_inv_r.
  Qed.

End mlist_mfmap_inversion.

(** * Listable Multisorted Functors *)
(******************************************************************************)
Section ListableMultisortedFunctor.

  Context
    `{ix : Index}.

  Section ListableMultisortedFunctor_operations.

    Context
      (F : Type -> Type).

    Class Tomlist :=
      tomlist : F ⇒ mlist.

  End ListableMultisortedFunctor_operations.

  Section ListableMultisortedFunctor.

    Context
      (F : Type -> Type)
      `{! MFmap F} `{! Tomlist F}.

    Class ListableMultisortedFunctor :=
      { lfun_natural :> MultisortedNatural (@tomlist F _);
        lfun_functor :> MultisortedFunctor F;
        lfun_shapeliness :  forall A (x y : F A),
            mshape F x = mshape F y ->
            tomlist F A x = tomlist F A y ->
            x = y;
      }.

  End ListableMultisortedFunctor.

  #[global] Arguments tomlist F%function_scope {Tomlist} {A}%type_scope.

  (** ** [tomlist]-preserving natural transformations *)
  (******************************************************************************)
  Class TomlistPreservingTransformation
        {T1 T2 : Type -> Type}
        `{! MFmap T1} `{! Tomlist T1}
        `{! MFmap T2} `{! Tomlist T2}
        (ϕ :  T1 ⇒ T2) :=
    { ltrans_natural : MultisortedNatural ϕ;
      ltrans_commute : forall A, tomlist T1 = tomlist T2 ∘ ϕ A;
    }.

End ListableMultisortedFunctor.

(** * Reasoning principles for [mshape] on listable functors *)
(** The following lemmas are useful when <<F>> is not already known to
    satisfy the shapeliness condition, and can be used to prove that
    property. Hence we do not assume <<F>> is listable, just that
    <<tomlist>> is natural. *)
(******************************************************************************)
Section mshape_lemmas.

  Context
    `{Index}
    `{! MFmap F}
    `{! MultisortedFunctor F }
    `{! Tomlist F} `{! MultisortedNatural (@tomlist _ F _)}.

  Theorem mshape_eq_impl_tomlist : forall A (t s : F A),
      mshape F t = mshape F s ->
      mshape mlist (tomlist F t) = mshape mlist (tomlist F s).
  Proof.
    introv heq. compose near t on left; compose near s on right.
    unfold mshape in *. rewrite mnaturality.
    unfold compose. now rewrite heq.
  Qed.

  Corollary mshape_l : forall A (l1 l2 : F A) (x y : mlist A),
      mshape F l1 = mshape F l2 ->
      tomlist F l1 ++ x = tomlist F l2 ++ y ->
      tomlist F l1 = tomlist F l2.
  Proof.
    introv mshape_eq heq.
    eauto using mlist_inv_app_ll, mshape_eq_impl_tomlist.
  Qed.

  Corollary mshape_r : forall A (l1 l2 : F A) (x y : mlist A),
      mshape F l1 = mshape F l2 ->
      x ++ tomlist F l1 = y ++ tomlist F l2 ->
      tomlist F l1 = tomlist F l2.
  Proof.
    introv mshape_eq heq.
    eauto using mlist_inv_app_rr, mshape_eq_impl_tomlist.
  Qed.

  Corollary mshape_l_mfmap : forall A B (l1 l2 : F A) (f g : A -k-> B) (x y : mlist B),
      mshape F l1 = mshape F l2 ->
      mfmap mlist f (tomlist F l1) ++ x = mfmap mlist g (tomlist F l2) ++ y ->
      mfmap mlist f (tomlist F l1) = mfmap mlist g (tomlist F l2).
  Proof.
    introv mshape_eq. compose near l1. compose near l2.
    rewrite 2(mnaturality). unfold compose; intro heq.
    eapply mshape_l. compose near l1; compose near l2.
    rewrite 2(mshape_mfmap1). assumption. eassumption.
  Qed.

  Corollary mshape_r_mfmap : forall A B (l1 l2 : F A) (f g : A -k-> B) (x y : mlist B),
      mshape F l1 = mshape F l2 ->
      x ++ mfmap mlist f (tomlist F l1) = y ++ mfmap mlist g (tomlist F l2) ->
      mfmap mlist f (tomlist F l1) = mfmap mlist g (tomlist F l2).
  Proof.
    introv mshape_eq. compose near l1. compose near l2.
    rewrite 2(mnaturality). unfold compose; intro heq.
    eapply mshape_r. compose near l1; compose near l2.
    rewrite 2(mshape_mfmap1). assumption. eassumption.
  Qed.

End mshape_lemmas.

(** * Shapeliness and respectfulness conditions *)
(******************************************************************************)
Instance tomset_Listable `{Index} `{Tomlist F} : Tomset F :=
  fun A => tomset mlist ∘ tomlist F.

Lemma in_iff_in_mlist `{Index} `{Tomlist F} : forall A (t : F A) (k : K) (a : A),
    (k, a) ∈m t <-> (k, a) ∈m tomlist F t.
Proof.
  reflexivity.
Qed.

Section listable_respectfulness.

  Context
    `{ListableMultisortedFunctor F}.

  Lemma tomlist_mfmap_respectful_inv :
    forall A B (x y : F A) (f g : A -k-> B),
      mfmap F f x = mfmap F g y ->
      mshape F x = mshape F y /\
      mfmap mlist f (tomlist F x) = mfmap mlist g (tomlist F y).
  Proof.
    introv hyp. split.
    assert (lemma : (mshape F (mfmap F f x) = mshape F (mfmap F g y)))
      by (now rewrite hyp).
    now rewrite 2(mshape_mfmap2) in lemma.
    assert (lemma : ((tomlist F ∘ mfmap F f) x) = (tomlist F ∘ mfmap F g) y)
      by (unfold compose; now rewrite hyp).
    now rewrite <- 2(mnaturality) in lemma.
  Qed.

  Theorem tomlist_mfmap_respectful :
    forall A B (x y : F A) (f g : A -k-> B),
      mshape F x = mshape F y ->
      mfmap mlist f (tomlist F x) = mfmap mlist g (tomlist F y) ->
      mfmap F f x = mfmap F g y.
  Proof.
    introv hshape hcontents. apply (lfun_shapeliness F).
    - compose near x on left; compose near y on right. now rewrite 2(mshape_mfmap1).
    - compose near x on left; compose near y on right. rewrite <- 2(mnaturality).
      assumption.
  Qed.

  Theorem tomlist_mfmap_respectful_iff :
    forall A B (x y : F A) (f g : A -k-> B),
      mshape F x = mshape F y /\ mfmap mlist f (tomlist F x) = mfmap mlist g (tomlist F y) <->
      mfmap F f x = mfmap F g y.
  Proof.
    intros. split.
    - intros [hshape heq]. now apply tomlist_mfmap_respectful.
    - intros. now apply tomlist_mfmap_respectful_inv.
  Qed.


  Theorem tomlist_setlike_respectful_inv :
    forall A B (t : F A) (f g : A -k-> B),
      mfmap F f t = mfmap F g t -> (forall k a, (k, a) ∈m t -> f k a = g k a).
    Proof.
      introv heq hin. specialize (tomlist_mfmap_respectful_inv A B t t f g).
      introv lemma. specialize (lemma heq). destruct lemma as [_ lemma].
      setoid_rewrite in_iff_in_mlist in hin. induction (tomlist F t).
      - inversion hin.
      - destruct hin as [hin|hin].
        + destruct a0; inverts hin. eauto using mfmap_inv_cons_hd.
        + destruct a0; apply mfmap_inv_cons_tl in lemma. auto.
    Qed.

    Theorem tomlist_setlike_respectful:
      forall A B (t : F A) (f g : A -k-> B),
        (forall k a, (k, a) ∈m t -> f k a = g k a) -> mfmap F f t = mfmap F g t.
    Proof.
      introv heq. apply (tomlist_mfmap_respectful A B t t f g).
      - reflexivity.
      - setoid_rewrite in_iff_in_mlist in heq. induction (tomlist F t).
        + reflexivity.
        + destruct a as [k a]. rewrite 2(mfmap_mlist_cons); cbn.
          fequal.
          { fequal. apply heq. now left. }
          { apply IHm. intros. apply heq. now right. }
    Qed.

End listable_respectfulness.

(** ** Listable functors are set-like *)
(******************************************************************************)
Section SetlikeFunctor_Listable.

  Context
    `{ListableMultisortedFunctor F}.

  (** The derived [tomset] operation on <<F>> is natural. *)
  Instance Natural_tomset_Listable : MultisortedNatural (@tomset ix F tomset_Listable).
  Proof.
    intros A B f. unfold tomset, tomset_Listable.
    reassociate <- on left. rewrite (mnaturality (η := @tomset _ mlist _) f).
    reassociate -> on left. rewrite (mnaturality (η := @tomlist _ F _) f).
    reflexivity.
  Qed.

  #[global] Instance SetlikeMultisortedFunctor_Listable :
    SetlikeMultisortedFunctor F :=
    { qmfun_respectful := tomlist_setlike_respectful; }.

End SetlikeFunctor_Listable.

(** * Derived operation [tolistk] *)
(******************************************************************************)
Definition tolistk F `{Tomlist F} {A} k : F A -> list A :=
  filterk k ∘ tomlist F.

Theorem in_tolistk_iff `{Tomlist F} : forall A (k : K) (t : F A) (a : A),
    a ∈ tolistk F k t <-> (k, a) ∈m tomlist F t.
Proof with tauto.
  intros. unfold tolistk, compose.
  induction (tomlist F t) as [| [k' a'] ? IH ].
  - cbv...
  - compare values k and k'; autorewrite* with tea_list.
    + rewrite filterk_cons_eq; autorewrite* with tea_list.
      rewrite IH...
    + rewrite filterk_cons_neq; auto. rewrite IH...
Qed.

(** * Properties of [mfmap] over listable functors *)
(******************************************************************************)
Section listable_functor_global.

  Context
    (F : Type -> Type)
    `{ListableMultisortedFunctor F}.

  Theorem tomlist_mfmap {A B} : forall (f : K -> A -> B),
      tomlist F ∘ mfmap F f = mfmap mlist f ∘ tomlist F.
  Proof.
    introv. now rewrite <- (mnaturality f).
  Qed.

  Theorem tolistk_mfmap {A B} : forall k (f : K -> A -> B),
      tolistk F k ∘ mfmap F f = fmap list (f k) ∘ tolistk F k.
  Proof.
    introv. unfold tolistk.
    reassociate -> on left. rewrite <- (mnaturality f).
    reassociate <- on left. now rewrite filterk_natural.
  Qed.

End listable_functor_global.

(** * Properties of [fmapk] over listable functors *)
(******************************************************************************)
Section listable_functor_local.

  Context
    (F : Type -> Type)
    `{ListableMultisortedFunctor F}.

  (** ** Interaction between [tomlist] and [fmapk] *)
  (******************************************************************************)
  Theorem tomlist_fmapk {A} k : forall (f : A -> A),
      tomlist F ∘ fmapk F k f = fmapk mlist k f ∘ tomlist F.
  Proof.
    introv. unfold fmapk.
    now rewrite <- (mnaturality (tgt k f)).
  Qed.

  (** ** Interaction between [tolistk] and [fmapk] *)
  (******************************************************************************)
  Theorem tolistk_fmapk_eq {A} k : forall (f : A -> A),
      tolistk F k ∘ fmapk F k f =  fmap list f ∘ tolistk F k.
  Proof.
    introv. unfold fmapk, tolistk.
    reassociate -> on left. rewrite <- (mnaturality (tgt k f)).
    reassociate <- on left. rewrite filterk_natural.
    now rewrite tgt_eq.
  Qed.

  Theorem tolistk_fmapk_neq {A} k j : forall (f : A -> A),
      k <> j ->
      tolistk F j ∘ fmapk F k f = tolistk F j.
  Proof.
    introv neq. unfold fmapk, tolistk.
    reassociate -> on left. rewrite <- (mnaturality (tgt k f)).
    reassociate <- on left. rewrite filterk_natural.
    rewrite tgt_neq; auto. now rewrite (fun_fmap_id list).
  Qed.

End listable_functor_local.
