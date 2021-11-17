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

(** * The [shape] operation *)
(** [shape] replaces each leaf of a term <<t : F A>> with the sole element of
    type [unit].  *)
(******************************************************************************)
Definition shape F `{MFmap F} {A} : F A -> F unit :=
  mfmap F (fun _ _ => tt).

(** As one would intuitively expect, mapping a function over a term <<t : F A>>
    preserves the shape of <<t>>. *)
Lemma shape_mfmap1 `{MultisortedFunctor F} : forall A B (f : A -k-> B),
    shape F ∘ mfmap F f = shape F.
Proof.
  intros. unfold shape. now rewrite (mfun_mfmap_mfmap F).
Qed.

Corollary shape_mfmap2 `{MultisortedFunctor F} : forall A B (f : A -k-> B) (t : F A),
    shape F (mfmap F f t) = shape F t.
Proof.
  intros. compose near t on left. now rewrite (shape_mfmap1).
Qed.

Theorem shape_shape `{MultisortedFunctor F} : forall A,
    shape F ∘ shape (A:=A) F = shape F.
Proof.
  intros. unfold shape.
  now rewrite (mfun_mfmap_mfmap F).
Qed.

(** ** Reasoning principles for [shape] on <<mlist>>s *)
(******************************************************************************)
Section shape_mlist.

  Context
    `{Index}.

  Lemma shape_nil : forall A,
      shape mlist (@nil (K * A)) = @nil (K * unit).
  Proof.
    reflexivity.
  Qed.

  Lemma shape_one : forall A (k : K) (a : A),
      shape mlist [ (k, a) ] = [ (k, tt) ].
  Proof.
    reflexivity.
  Qed.

  Lemma shape_cons : forall A (k : K) (a : A) (l : mlist A),
      shape mlist ((k, a) :: l) = (k, tt) :: shape mlist l.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_app : forall A (l1 l2 : mlist A),
      shape mlist (l1 ++ l2) = shape mlist l1 ++ shape mlist l2.
  Proof.
    intros. unfold shape. now rewrite mfmap_mlist_app.
  Qed.

  Lemma shape_nil_iff : forall A (l : mlist A),
      shape mlist l = @nil (Tag unit) <-> l = [].
  Proof.
    induction l as [| a ? ?]. easy.
    split; intro contra; destruct a; now inverts contra.
  Qed.

  Theorem shape_inv_app_r : forall A (l1 l2 r1 r2: mlist A),
      shape mlist r1 = shape mlist r2 ->
      shape mlist (l1 ++ r1) = shape mlist (l2 ++ r2) <->
      shape mlist l1 = shape mlist l2.
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split.
    - intros. unfold mlist in l1, l2, r1, r2.
      eapply List.app_inv_tail. eassumption.
    - intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_inv_app_l : forall A (l1 l2 r1 r2: mlist A),
      shape mlist l1 = shape mlist l2 ->
      shape mlist (l1 ++ r1) = shape mlist (l2 ++ r2) <->
      shape mlist r1 = shape mlist r2.
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split.
    - intros; eapply List.app_inv_head; eassumption.
    - intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_inv_cons_iff : forall A (l1 l2 : mlist A) (k1 k2 : K) (a1 a2 : A),
      shape mlist ((k1, a1) :: l1) = shape mlist ((k2, a2) :: l2) <->
      k1 = k2 /\ shape mlist l1 = shape mlist l2.
  Proof.
    introv. rewrite 2(shape_cons).
    split; [introv hyp | introv [hyp1 hyp2]]. now inverts hyp.
    now rewrite hyp1, hyp2.
  Qed.

  Corollary shape_inv_cons_iff_eq : forall A (l1 l2 : mlist A) (k : K) (a1 a2 : A),
      shape mlist ((k, a1) :: l1) = shape mlist ((k, a2) :: l2) <->
      shape mlist l1 = shape mlist l2.
  Proof.
    introv. rewrite shape_inv_cons_iff. intuition.
  Qed.

  Corollary shape_inv_cons_tail : forall A (l1 l2 : mlist A) (k1 k2 : K) (a1 a2 : A),
      shape mlist ((k1, a1) :: l1) = shape mlist ((k2, a2) :: l2) ->
      shape mlist l1 = shape mlist l2.
  Proof.
    introv. rewrite shape_inv_cons_iff. intuition.
  Qed.
  Theorem mlist_inv_app_ll : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist l1 = shape mlist l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| (k1, a1) ? IHl1 ];
                induction l2 as [| (k2, a2) ? IHl2 ].
    - reflexivity.
    - introv shape_eq hyp. now inverts shape_eq.
    - introv shape_eq hyp. now inverts shape_eq.
    - introv shape_eq heq.
      rewrite shape_inv_cons_iff in shape_eq;
        destruct shape_eq as [? ?].
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem mlist_inv_app_rl : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist r1 = shape mlist r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| (?, ?) ? IHl1 ];
                induction l2 as [| (?, ?) ? IHl2 ].
    - reflexivity.
    - introv shape_eq heq. apply (mlist_inv_app_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- shape_inv_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq. apply (mlist_inv_app_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- shape_inv_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq.
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem mlist_inv_app_lr : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist l1 = shape mlist l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eapply List.app_inv_head; eassumption. }
    { eauto using mlist_inv_app_ll. }
  Qed.

  Theorem mlist_inv_app_rr : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist r1 = shape mlist r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eapply List.app_inv_head; eassumption. }
    { eauto using mlist_inv_app_rl. }
  Qed.

  Theorem inv_app_eq : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist l1 = shape mlist l2 \/ shape mlist r1 = shape mlist r2 ->
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

End shape_mlist.

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
        lfun_shapeliness : forall A B (x y : F A) (f g : A -k-> B),
          shape F x = shape F y ->
          mfmap mlist f (tomlist F A x) = mfmap mlist g (tomlist F A y) ->
          mfmap F f x = mfmap F g y;
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

(** * Reasoning principles for [shape] on listable functors *)
(******************************************************************************)
Section shape_lemmas.

  Context
    `{Index}
    `{! MFmap F}
    `{! MultisortedFunctor F }
    `{! Tomlist F} `{! MultisortedNatural (@tomlist _ F _)}.

  Theorem shape_eq_impl_tomlist : forall A (t s : F A),
      shape F t = shape F s ->
      shape mlist (tomlist F t) = shape mlist (tomlist F s).
  Proof.
    introv heq. compose near t on left; compose near s on right.
    unfold shape in *. rewrite mnaturality.
    unfold compose. now rewrite heq.
  Qed.

  Corollary shape_l : forall A (l1 l2 : F A) (x y : mlist A),
      shape F l1 = shape F l2 ->
      tomlist F l1 ++ x = tomlist F l2 ++ y ->
      tomlist F l1 = tomlist F l2.
  Proof.
    introv shape_eq heq.
    eauto using mlist_inv_app_ll, shape_eq_impl_tomlist.
  Qed.

  Corollary shape_r : forall A (l1 l2 : F A) (x y : mlist A),
      shape F l1 = shape F l2 ->
      x ++ tomlist F l1 = y ++ tomlist F l2 ->
      tomlist F l1 = tomlist F l2.
  Proof.
    introv shape_eq heq.
    eauto using mlist_inv_app_rr, shape_eq_impl_tomlist.
  Qed.

  Corollary shape_l_mfmap : forall A B (l1 l2 : F A) (f g : A -k-> B) (x y : mlist B),
      shape F l1 = shape F l2 ->
      mfmap mlist f (tomlist F l1) ++ x = mfmap mlist g (tomlist F l2) ++ y ->
      mfmap mlist f (tomlist F l1) = mfmap mlist g (tomlist F l2).
  Proof.
    introv shape_eq. compose near l1. compose near l2.
    rewrite 2(mnaturality). unfold compose; intro heq.
    eapply shape_l. compose near l1; compose near l2.
    rewrite 2(shape_mfmap1). assumption. eassumption.
  Qed.

  Corollary shape_r_mfmap : forall A B (l1 l2 : F A) (f g : A -k-> B) (x y : mlist B),
      shape F l1 = shape F l2 ->
      x ++ mfmap mlist f (tomlist F l1) = y ++ mfmap mlist g (tomlist F l2) ->
      mfmap mlist f (tomlist F l1) = mfmap mlist g (tomlist F l2).
  Proof.
    introv shape_eq. compose near l1. compose near l2.
    rewrite 2(mnaturality). unfold compose; intro heq.
    eapply shape_r. compose near l1; compose near l2.
    rewrite 2(shape_mfmap1). assumption. eassumption.
  Qed.

End shape_lemmas.

(** * Listable functors are set-like *)
(******************************************************************************)
#[global] Instance tomset_Listable `{Index} `{Tomlist F} : Tomset F :=
  fun A => tomset mlist ∘ tomlist F.

(** A value <<a>> occurs in <<t>> if and only if <<a>> occurs in <<t>>'s
      contents. *)
Lemma in_iff_in_mlist `{Index} `{Tomlist F} : forall A (t : F A) (k : K) (a : A),
    (k, a) ∈m t <-> (k, a) ∈m tomlist F t.
Proof.
  reflexivity.
Qed.

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
    SetlikeMultisortedFunctor F := {}.

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

(** * Miscellaneous inversion lemmas for equality between [mlist] *)
(******************************************************************************)
Section mlist_inversion_principles.

  Context
    `{Index}.

  Lemma mlist_inv_cons : forall A (k1 k2 : K) (a1 a2 : A) (l1 l2 : mlist A),
      (k1, a1) :: l1 = (k2, a2) :: l2 -> k1 = k2 /\ a1 = a2 /\ l1 = l2.
  Proof.
    introv heq. inversion heq. subst. auto.
  Qed.

  Lemma mfmap_inv_cons : forall  {A B} {f g : A -k-> B} (k1 k2 : K) (a1 a2 : A) (l1 l2 : mlist A),
      mfmap mlist f ((k1, a1) :: l1) = mfmap mlist g ((k2, a2) :: l2) ->
      f k1 a1 = g k2 a2 /\ mfmap mlist f l1 = mfmap mlist g l2.
  Proof.
    introv hyp. rewrite mfmap_mlist_cons in hyp.
    cbn in hyp. apply mlist_inv_cons in hyp.
    intuition.
  Qed.

  Lemma mfmap_inv_cons_hd : forall  {A B} {f g : A -k-> B} (k1 k2 : K) (a1 a2 : A) (l1 l2 : mlist A),
      mfmap mlist f ((k1, a1) :: l1) = mfmap mlist g ((k2, a2) :: l2) ->
      f k1 a1 = g k2 a2.
  Proof.
    introv hyp. now apply mfmap_inv_cons in hyp.
  Qed.

  Lemma mfmap_inv_cons_tl : forall  {A B} {f g : A -k-> B} (k1 k2 : K) (a1 a2 : A) (l1 l2 : mlist A),
      mfmap mlist f ((k1, a1) :: l1) = mfmap mlist g ((k2, a2) :: l2) ->
      mfmap mlist f l1 = mfmap mlist g l2.
  Proof.
    introv hyp. now apply mfmap_inv_cons in hyp.
  Qed.

  Lemma mfmap_app_inv_l : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l1 = mfmap mlist g l1.
  Proof.
    introv hyp. rewrite 2(mfmap_mlist_app) in hyp.
    eapply mlist_inv_app_rl. 2: eauto.
    now rewrite 2(shape_mfmap2).
  Qed.

  Lemma mfmap_app_inv_r : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l2 = mfmap mlist g l2.
  Proof.
    introv hyp. rewrite 2(mfmap_mlist_app) in hyp.
    eapply mlist_inv_app_lr. 2: eauto.
    now rewrite 2(shape_mfmap2).
  Qed.

  Lemma map_app_inv : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l1 = mfmap mlist g l1 /\
      mfmap mlist f l2 = mfmap mlist g l2.
  Proof.
    intros; split; eauto using mfmap_app_inv_l, mfmap_app_inv_r.
  Qed.

End mlist_inversion_principles.
