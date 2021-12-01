From Tealeaves Require Export
     Singlesorted.Classes.DecoratedModule
     Singlesorted.Classes.SetlikeMonad
     Singlesorted.Classes.RightModule.

Import Monoid.Notations.
Import Sets.Notations.
Import SetlikeFunctor.Notations.
#[local] Open Scope tealeaves_scope.

(** * Set-like right modules *)
(******************************************************************************)
Section setlike_module_class.

  Context
    (F T : Type -> Type)
    `{SetlikeFunctor F}
    `{SetlikeMonad T}
    `{RightAction F T}.

  Class SetlikeModule : Prop :=
    { xrmod_rmod :> RightModule F T;
      xrmod_monad :> SetlikeMonad T;
      xrmod_functor :> SetlikeFunctor F;
      xrmod_action :
        `(toset (A:=A) F ∘ right_action F =
          join set ∘ toset F ∘ fmap F (toset T));
    }.

End setlike_module_class.

(** ** Set-like monads are setlike modules *)
(******************************************************************************)
Section setlike_module_of_monad.

  Existing Instance RightAction_Join.
  Existing Instance RightModule_Monad.

  Instance SetlikeModule_Monad `{SetlikeMonad T} :
    SetlikeModule T T :=
    {| xrmod_action := xmon_join T;
       xrmod_functor := xmon_functor T;
    |}.

End setlike_module_of_monad.

(** ** Basic properties of set-like modules *)
(******************************************************************************)
Section setlike_module_theory.

  Context
    (F T : Type -> Type)
    `{SetlikeModule F T}.

  (** [right_action] acts like a (unary) union operation. *)
  Theorem in_action_iff {A} : forall (t : F (T A)) a,
      a ∈ right_action F t <-> exists t', t' ∈ t /\ a ∈ t'.
  Proof.
    introv. compose near t on left.
    rewrite (xrmod_action F T).
    reassociate -> on left.
    rewrite <- (natural (B:=set A) (G:=(->Prop))).
    unfold transparent tcs; unfold compose.
    intuition (preprocess; eauto).
  Qed.

  Corollary in_sub_iff {A B} : forall t b (f : A -> T B),
      b ∈ sub F f t <->
      exists (a : A), a ∈ t /\ b ∈ f a.
  Proof.
    introv. unfold transparent tcs. unfold compose.
    rewrite (in_action_iff (fmap F f t)).
    setoid_rewrite (in_fmap_iff F).
    intuition (preprocess; eauto).
  Qed.

  Corollary sub_respectful : forall A B (t : F A) (f g : A -> T B),
      (forall a, a ∈ t -> f a = g a) -> sub F f t = sub F g t.
  Proof.
    introv hyp. unfold_ops @Sub_RightAction.
    unfold compose. fequal. now apply (fmap_respectful F).
  Qed.

  Corollary sub_respectful_id : forall A (t : F A) (f : A -> T A),
      (forall a, a ∈ t -> f a = ret T a) -> sub F f t = t.
  Proof.
    introv hyp. replace t with (sub F (ret T) t) at 2
      by now rewrite (RightModule.sub_id F T).
    now apply sub_respectful.
  Qed.

  Corollary sub_respectful_fmap {A} :
    forall (t : F A) (f : A -> T A) (g : A -> A),
      (forall a, a ∈ t -> f a = ret T (g a)) -> sub F f t = fmap F g t.
  Proof.
    intros. rewrite (RightModule.fmap_to_sub F T).
    now apply sub_respectful.
  Qed.

End setlike_module_theory.

(*
(** ** Respectfulness for <<fmap>> and <<sub>> are equivalent. *)
(******************************************************************************)
Section toset_resp_sub_equiv_fmap.

  Context
    F `{RightModule F T} `{Toset F}.

  #[global] Instance toset_sub_resp_of_fmap :
      (forall A B (t : F A), Proper (ext_rel t ++> eq_at t t) (fmap F (B:=B))) ->
      (forall A B (t : F A), Proper (ext_rel t ++> eq_at t t) (sub F (B:=B))).
  Proof.
    intros Hproper. unfold Proper, respectful, ext_rel, eq_at in *.
    intros A B t f g Heq. unfold transparent tcs. unfold compose.
    specialize (Hproper _ _ t f g). rewrite Hproper; auto.
  Qed.

  #[global] Instance toset_fmap_resp_of_sub :
    (forall A B (t : F A), Proper (ext_rel t ++> eq_at t t) (sub F (B:=B))) ->
    (forall A B (t : F A), Proper (ext_rel t ++> eq_at t t) (fmap F (B:=B))).
  Proof.
    unfold transparent tcs. intros Hproper.
    unfold Proper, respectful, ext_rel, eq_at, compose in *.
    intros A B t f g Heq. rewrite 2(fmap_to_sub F T). unfold compose.
    apply Hproper. intros; fequal; auto.
  Qed.

End toset_resp_sub_equiv_fmap.

(** ** Injective <<sub>> implies <<fmap>> if <<ret>> is injective. *)
(** We show elsewhere that <<set>> does not satisfy the converse of
    this statement. *)
(******************************************************************************)
Section toset_fmap_injective_of_sub.

  Context
    F `{RightModule F T} `{Toset F}.

  Hypothesis
    (ret_inj : forall A (x y : A),
        ret T x = ret T y -> x = y).

  Theorem toset_fmap_injective_of_sub :
    (forall A B (t : F A), Proper (ext_rel t <++ eq_at t t) (sub F (B:=B))) ->
    (forall A B (t : F A), Proper (ext_rel t <++ eq_at t t) (fmap F (B:=B))).
  Proof.
    intros hyp A B t f g heq. specialize (hyp A B t (ret T ∘ f) (ret T ∘ g)).
    rewrite <- 2(fmap_to_sub F T) in hyp; unfold compose in hyp.
    unfold Proper, respectful, ext_rel, eq_at in *.
    auto using ret_inj.
  Qed.

End toset_fmap_injective_of_sub.
*)

(** * Decorated set-like right modules *)
(******************************************************************************)

(** ** Basic properties *)
(******************************************************************************)
Section decorated_setlike_properties.

  Context
    (F : Type -> Type)
    `{Monoid W}
    `{Fmap F}  `{RightAction F T} `{Decorate W F} `{Toset F}
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T} `{Toset T}
    `{! DecoratedModule W F T}
    `{! SetlikeModule F T}.

  Theorem ind_subd_iff {A B} : forall t w b (f : W * A -> T B),
      (w, b) ∈d subd F f t <->
      exists (a : A) (w1 w2 : W),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a) /\ w = w1 ● w2.
  Proof.
    introv. unfold tosetd.
    compose near t on left.
    reassociate -> on left.
    rewrite  (dec_subd F).
    unfold subd. unfold compose.
    rewrite (in_sub_iff F T). split; intro hyp.
    - destruct hyp as [[w' a] [hyp1 hyp2]].
      cbn in hyp2; unfold id in hyp2.
      rewrite (in_shift_iff T) in hyp2.
      destruct hyp2 as [w2 [? ?]].
      exists a. exists w'. exists w2. split; auto.
    - destruct hyp as [a [w1 [w2 [? ?]]]].
      exists (w1, a). split; auto. cbn.
      rewrite (in_shift_iff T). exists w2. auto.
  Qed.

  (** *** Corollaries: [tosetd] and [sub] *)
  (******************************************************************************)
  Theorem ind_sub_iff {A B} : forall t w b (f : A -> T B),
      (w, b) ∈d sub F f t <->
      exists (a : A) (w1 w2 : W),
        (w1, a) ∈d t /\ (w2, b) ∈d f a /\ w = w1 ● w2.
  Proof.
    introv. rewrite (DecoratedModule.sub_to_subd F T).
    now rewrite ind_subd_iff.
  Qed.

  (** *** Corollaries: [toset] and [subd] *)
  (******************************************************************************)
  Theorem in_subd_iff {A B} : forall t b (f : W * A -> T B),
      b ∈ subd F f t <->
      exists (a : A) (w1 : W),
        (w1, a) ∈d t /\ b ∈ f (w1, a).
  Proof.
    introv. rewrite (ind_of_in F).
    setoid_rewrite ind_subd_iff. split.
    - intros. preprocess. do 2 eexists.
      split; eauto. eapply (in_of_ind T); eauto.
    - intros [a [w [in1 in2]]]. rewrite (ind_of_in T) in in2.
      destruct in2 as [w2 ?]. exists (w ● w2) a w w2.
      auto.
  Qed.

End decorated_setlike_properties.

(** ** Respectfulness properties *)
(******************************************************************************)
Section decorated_setlike_respectfulness.

  Context
    (F : Type -> Type)
    `{Monoid W}
    `{Fmap F}  `{RightAction F T} `{Decorate W F} `{Toset F}
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T} `{Toset T}
    `{! DecoratedModule W F T}
    `{! SetlikeModule F T}.

    Theorem subd_respectful {A B} : forall (t : F A) (f g : W * A -> T B),
        (forall w a, (w, a) ∈d t -> f (w, a) = g (w, a)) ->
        subd F f t = subd F g t.
    Proof.
      intros. unfold subd, compose.
      eapply (SetlikeModule.sub_respectful F T); auto.
      intros [? ?]; eauto.
    Qed.

    Corollary subd_respectful_id {A} : forall (t : F A) (f : W * A -> T A),
        (forall w a, (w, a) ∈d t -> f (w, a) = ret T a) ->
        subd F f t = t.
    Proof.
      intros. replace t with (subd F (ret T ∘ extract (prod W)) t) at 2
        by (now rewrite (DecoratedModule.subd_id F T)).
      now apply subd_respectful.
    Qed.

    Corollary subd_respectful_fmapd {A B} : forall (t : F A) (f : W * A -> T B) (g : W * A -> B),
        (forall w a, (w, a) ∈d t -> f (w, a) = ret T (g (w, a))) ->
        subd F f t = fmapd F g t.
    Proof.
      introv. rewrite (DecoratedModule.fmapd_to_subd F T).
      intros ?. now apply subd_respectful.
    Qed.

    Corollary subd_respectful_sub {A B} : forall (t : F A) (f : W * A -> T B) (g : A -> T B),
        (forall w a, (w, a) ∈d t -> f (w, a) = g a) ->
        subd F f t = sub F g t.
    Proof.
      introv. rewrite (DecoratedModule.sub_to_subd F T).
      intros ?. now apply subd_respectful.
    Qed.

    Corollary subd_respectful_fmap {A B} : forall (t : F A) (f : W * A -> T B) (g : A -> B),
        (forall w a, (w, a) ∈d t -> f (w, a) = ret T (g a)) ->
        subd F f t = fmap F g t.
    Proof.
      introv. rewrite (DecoratedModule.fmap_to_subd F T).
      intros; now apply subd_respectful.
    Qed.

End decorated_setlike_respectfulness.
