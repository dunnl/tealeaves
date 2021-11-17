From Tealeaves Require Import
     Sets.

From Tealeaves.Multisorted Require Import
     Functors
     MSets
     Quantifiable
     MList
     Listable
     Decorated.

Import Multisorted.Category.Notations.
Import Multisorted.Category.Notations.
Import Multisorted.MSets.Notations.
Import Multisorted.Quantifiable.Notations.
Local Open Scope tealeaves_multi_scope.

(** * Properness for [tomset] *)
(** We consider several potential properness conditions for the
    [tomset] operation and consider their consequences and
    relationships to each other. We later define a
    [QuantifiableModule] as one whose [tomset] operation satisfies
    [tomset_mbind_proper] (and therefore [tomset_mfmap_proper]). Quantifiable
    instances inferred via [ListableModule] instances will
    additionally satisfy [tomset_mfmap_strong_proper], and finally we expect
    most "syntax-like" functors to furthermore satisfy
    [tomset_mbind_strong_proper], although we do not actually require this
    conditions for instances of [SyntaxModule]. *)
(******************************************************************************)
Section definitions.

  Context
    `{ix : Index}.

  Definition tomset_mfmap_proper F `{! Mfmap F} `{! Tomset F} :=


  Definition tomset_mfmap_proper_inv F `{! Mfmap F} `{! Tomset F} :=
    forall A B (t : F A) (f g : A -k-> B),
      mfmap F f t = mfmap F g t -> (forall k a, (k, a) ∈m t -> f k a = g k a).

  Definition tomset_mfmap_proper_iff F `{! Mfmap F} `{! Tomset F} :=
    forall A B (t : F A) (f g : A -k-> B),
      (forall k a, (k, a) ∈m t -> f k a = g k a) <-> mfmap F f t = mfmap F g t.

  Definition tomset_mbind_proper F G `{! Mbind F G} `{! Tomset F} :=


  Definition tomset_mbind_proper_inv F G `{! Mbind F G} `{! Tomset F} :=
    forall A B (t : F A) (f g : forall k, A -> G k B),
      mbind F f t = mbind F g t -> (forall k a, (k, a) ∈m t -> f k a = g k a).

  Definition tomset_mbind_proper_iff F G `{! Mbind F G} `{! Tomset F} :=
    forall A B (t : F A) (f g : forall k, A -> G k B),
      (forall k a, (k, a) ∈m t -> f k a = g k a) <-> mbind F f t = mbind F g t.

  Class Mfmap_proper F `{! Mfmap F} `{! Tomset F} :=
    mfmap_properness : tomset_mfmap_proper F.

  Class Mfmap_proper_inv F `{! Mfmap F} `{! Tomset F} :=
    mfmap_properness_inv : tomset_mfmap_proper_inv F.

  Class Mfmap_proper_iff F `{! Mfmap F} `{! Tomset F} :=
    mfmap_properness_iff : tomset_mfmap_proper_iff F.

  Class Mbind_proper F {G} `{! Mbind F G} `{! Tomset F} :=
    mbind_properness : tomset_mbind_proper F G.

  Class Mbind_proper_inv F {G} `{! Mbind F G} `{! Tomset F} :=
    mbind_properness_inv : tomset_mbind_proper_inv F G.

  Class Mbind_proper_iff F {G} `{! Mbind F G} `{! Tomset F} :=
    mbind_properness_iff : tomset_mbind_proper_iff F G.

  #[global] Arguments mfmap_properness F%function_scope {Mfmap0 Tomset0 Mfmap_proper} {A B}.
  #[global] Arguments mfmap_properness_inv F%function_scope {Mfmap0 Tomset0 Mfmap_proper_inv} {A B}.
  #[global] Arguments mfmap_properness_iff F%function_scope {Mfmap0 Tomset0 Mfmap_proper_iff} {A B}.
  #[global] Arguments mbind_properness _%function_scope {G}%function_scope {Mbind0 Tomset0 Mbind_proper} {A B}.
  #[global] Arguments mbind_properness_inv _%function_scope {G}%function_scope {Mbind0 Tomset0 Mbind_proper_inv} {A B}.
  #[global] Arguments mbind_properness_iff _%function_scope {G}%function_scope {Mbind0 Tomset0 Mbind_proper_iff} {A B}.

End definitions.

Ltac unfold_mset_properness :=
  unfold Mfmap_proper, Mbind_proper,
  Mfmap_proper_inv, Mbind_proper_inv,
  Mfmap_proper_iff, Mbind_proper_iff,
  tomset_mfmap_proper, tomset_mbind_proper,
  tomset_mfmap_proper_inv, tomset_mbind_proper_inv,
  tomset_mfmap_proper_iff, tomset_mbind_proper_iff in *.

Ltac unfold_properness := unfold_mset_properness.

(** ** Mutual implications between [tomset] properness conditions *)
(** Because we cannot decompose [mbind] into a <<join>> operation
    composed with <<mfmap>>, we can no longer prove that properness
    for <<mfmap>> implies the same for <<mbind>>. However, we can
    still prove the converse direction. *)
(******************************************************************************)

(** *** Properness for [mbind] implies properness for [mfmap] *)
(** Properness for <<mbind>> implies properness for <<mfmap>>. In the
multisorted setting, without the ability to express <<mbind>> as
<<mjoin ∘ mfmap>>, it seems we can no longer prove the converse
direction. The inversion principle for <<mbind>> also implies the same
for <<mfmap>> if <<mret>> is injective (which is almost always the case). *)
(******************************************************************************)
Section mfmap_strong_of_mbind_strong.

  Context
    `{RightModule F T} `{! Tomset F}.


  #[global] Instance tomset_mfmap_proper_mbind_TC : `{Mbind_proper F} -> `{Mfmap_proper F}.
  Proof.
    apply tomset_mfmap_proper_mbind.
  Qed.

  Hypothesis
    (mret_inj : forall A k (x y : A),
        mret T k x = mret T k y -> x = y).

  Theorem tomset_mfmap_proper_inv_mbind :
    tomset_mbind_proper_inv F T -> tomset_mfmap_proper_inv F.
  Proof.
    unfold_properness. unfold_mfmap @Mfmap_rmod.
    introv hproper. introv heq. specialize (hproper _ _ _ _ _ heq).
    intros. apply mret_inj with (k := k). now apply hproper.
  Qed.

  Theorem tomset_mfmap_proper_iff_mbind :
    tomset_mbind_proper_iff F T -> tomset_mfmap_proper_iff F.
  Proof.

    unfold_properness.
    cbv [tomset_mbind_proper_iff tomset_mfmap_proper_iff].
    introv hyp. intros. unfold_mfmap @Mfmap_rmod.
    rewrite <- hyp. split; intros; unfold compose; fequal; eauto.
  Qed.

End mfmap_strong_of_mbind_strong.


(** * Derived operations [totsetr, totsetkr] *)
(******************************************************************************)
Definition tomlistr F `{Tomlist F} `{Decorate W F} {A} :
  F A -> mlist (W * A) := tomlist F ∘ decorate F.

Local Notation "x ∈mr t" :=
  (tomsetr _ t x) (at level 50) : tealeaves_multi_scope.

Local Notation "x @ k ∈mr t" :=
  (tomsetr _ t (k, x)) (k at level 5, at level 50) : tealeaves_multi_scope.


  (** *** Corollaries of [tomset_mfmap_strong_proper] *)
  Section tomsetr_mfmap_strong_proper.

    Context
      `{Hproper : ! Mfmap_proper_iff F}.

    (** **** Parallel context-sensitive maps *)
    Lemma mfmapr_proper_iff {A B} : forall (t : F A) (f g : W * A -k-> B),
        (forall k w a, (k, (w, a)) ∈mr t -> f k (w, a) = g k (w, a)) <->
        mfmapr F f t = mfmapr F g t.
    Proof.
      introv. unfold mfmapr, compose. unfold_properness.
      rewrite <- Hproper. split.
      - intros ? ? [? ?] ?; auto.
      - auto.
    Qed.

    Corollary mfmapr_proper_id_iff {A} : forall (t : F A) (f : W * A -k-> A),
        (forall k w a, (k, (w, a)) ∈mr t -> f k (w, a) = a) <->
        mfmapr F f t = t.
    Proof.
      intros. replace t with (mfmapr F (const snd) t) at 2
        by now rewrite (mfmapr_id F).
      now rewrite <- mfmapr_proper_iff.
    Qed.

    (** **** Targeted context-sensitive maps *)
    Lemma fmapkr_proper_iff {A} : forall k (t : F A) (f g : W * A -> A),
        (forall w a, (k, (w, a)) ∈mr t -> f (w, a) = g (w, a)) <->
        fmapkr F k f t = fmapkr F k g t.
    Proof.
      introv. unfold fmapkr. rewrite <- mfmapr_proper_iff. split.
      - intros ? j ? ?. compare values k and j;
        simpl_tgt_fallback; auto.
      - intros heq ? ?. specialize (heq k).
        simpl_tgt_fallback in heq; auto.
    Qed.

    Corollary fmapkr_proper_id_iff {A} : forall k (t : F A) (f : W * A -> A),
        (forall w a, (k, (w, a)) ∈mr t -> f (w, a) = a) <->
        fmapkr F k f t = t.
    Proof.
      intros. replace t with (fmapkr F k snd t) at 2
        by now rewrite (fmapkr_id F).
      now rewrite <- fmapkr_proper_iff.
    Qed.

  End tomsetr_mfmap_strong_proper.

End tomsetr_mfmap_properness_theorems.

(** ** Corollaries of properness for context-sensitive substitutions *)
(******************************************************************************)
Section tomset_mbind_properness_theorems.

  Context
    F `{DecoratedModule W F T} `{! Tomset F}.

  (** *** Corollaries of [tomset_mbind_proper] *)
  (******************************************************************************)
  Section tomset_mbind_proper.

    Context
      `{Hproper : ! Mbind_proper F}.


    (** **** Targeted context-sensitive substitutions *)

  End tomset_mbind_proper.

  (** *** Corollaries of [tomset_mbind_strong_proper] *)
  Section tomsetr_mbind_strong_proper.

    Context
      `{Hproper : ! Mbind_proper_iff F}.

    (** **** Global context-sensitive substitutions *)
    Theorem mbindr_proper_iff {A B} : forall (t : F A) (f g : forall k, W * A -> T k B),
        (forall k w a, (k, (w, a)) ∈mr t -> f k (w, a) = g k (w, a)) <->
        mbindr F f t = mbindr F g t.
    Proof.
      introv. unfold mbindr, compose. unfold_properness.
      rewrite <- Hproper. split.
      - intros ? ? [? ?] ?; auto.
      - auto.
    Qed.

    Corollary mbindr_proper_id_iff {A} : forall (t : F A) (f : forall k, W * A -> T k A),
        (forall k w a, (k, (w, a)) ∈mr t -> f k (w, a) = mret T k a) <->
        mbindr F f t = t.
    Proof.
      introv. replace t with (mbindr F (mret T ◻ const snd) t) at 2
        by (now rewrite (mbindr_id F)).
      now rewrite <- mbindr_proper_iff.
    Qed.

    Corollary mbindr_proper_mfmapr_iff {A B} : forall (t : F A) (f : forall k, W * A -> T k B) (g : W * A -k-> B),
        (forall k w a, (k, (w, a)) ∈mr t -> f k (w, a) = mret T k (g k (w, a)))
        <-> mbindr F f t = mfmapr F g t.
    Proof.
      introv. rewrite mfmapr_to_mbindr.
      now rewrite <- mbindr_proper_iff.
    Qed.

    Corollary mbindr_proper_mbind_iff {A B} : forall (t : F A) (f : forall k, W * A -> T k B) (g : forall k, A -> T k B),
        (forall k w a, (k, (w, a)) ∈mr t -> f k (w, a) = g k a)
        <-> mbindr F f t = mbind F g t.
    Proof.
      introv. rewrite (mbind_to_mbindr F).
      now rewrite <- mbindr_proper_iff.
    Qed.

    (** **** Targeted context-sensitive substitutions *)
    Lemma bindkr_proper_iff {A} : forall k (t : F A) (f g : W * A -> T k A),
        (forall w a, (k, (w, a)) ∈mr t -> f (w, a) = g (w, a))
        <-> bindkr F k f t = bindkr F k g t.
    Proof.
      introv. unfold bindkr, compose.
      rewrite <- mbindr_proper_iff. split.
      - intros ? j ? ?. destruct_eq_args k j.
        autorewrite with tea_tgt_eq using auto.
        autorewrite with tea_tgt_neq using auto.
      - intros heq ? ?. specialize (heq k).
        autorewrite with tea_tgt_eq in heq using auto.
    Qed.

    Lemma bindkr_proper_id_iff {A} : forall k (t : F A) (f : W * A -> T k A),
        (forall w a, (k, (w, a)) ∈mr t -> f (w, a) = mret T k a)
        <-> bindkr F k f t = t.
    Proof.
      introv. replace t with (bindkr F k (mret T k ∘ snd) t) at 2
        by (now rewrite (bindkr_id F)).
      now rewrite <- (bindkr_proper_iff).
    Qed.

    Corollary bindkr_proper_fmapkr_iff {A} : forall k (t : F A) (f : W * A -> T k A) (g : W * A -> A),
        (forall w a, (k, (w, a)) ∈mr t -> f (w, a) = mret T k (g (w, a)))
        <-> bindkr F k f t = fmapkr F k g t.
    Proof.
      introv. rewrite fmapkr_to_bindkr.
      now rewrite <- bindkr_proper_iff.
    Qed.

    Corollary bindkr_proper_bindk_iff {A} : forall k (t : F A) (f : W * A -> T k A) (g : A -> T k A),
        (forall w a, (k, (w, a)) ∈mr t -> f (w, a) = g a)
        <-> bindkr F k f t = bindk F k g t.
    Proof.
      introv. rewrite (bindk_to_bindkr F).
      now rewrite <- bindkr_proper_iff.
    Qed.

  End tomsetr_mbind_strong_proper.

End tomset_mbind_properness_theorems.

(** * Properness definitions for [tomlist] *)
(** We consider several potential properness conditions for the
    [tomlist] operation and consider their consequences and
    relationships to each other. We later define a
    [ListableModule] as one whose [tomlist] operation satisfies
    [tomlist_mbind_proper] (and therefore [tomlist_mfmap_proper]). Quantifiable
    instances inferred via [ListableModule] instances will
    additionally satisfy [tomlist_mfmap_proper_iff], and finally we expect
    most "syntax-like" functors to furthermore satisfy
    [mbind_proper_iff], although we do not actually require this
    conditions for instances of [SyntaxModule]. *)

(** The statements for <<mbind>> involve an auxiliary function
    <<pack>> to wrap subtrees in existentials, as lists of type
    <<mlist>> cannot be heterogenous. *)
Section pack.

  Context `{Index} (T : K -> Type -> Type) {A B} (f : A ~k~> T B).

  Definition pack := fun k : K => fun a : A => existT (fun k => T k B) k (f k a).

End pack.

Section properness.

  Context
    F `{MFunctor F} `{! Tomlist F}.

  Definition shapeliness :=

  Definition tomlist_mfmap_proper :=

        forall A B (x y : F A) (f g : A -k-> B),
          mshape F x = mshape F y ->
          mfmap mlist f (tomlist F A x) = mfmap mlist g (tomlist F A y) ->
          mfmap F f x = mfmap F g y;
      }.

  Definition tomlist_mfmap_proper_inv := forall A B (x y : F A) (f g : A -k-> B),
      mfmap F f x = mfmap F g y ->
      shape F x = shape F y /\ mfmap mlist f (tomlist F x) = mfmap mlist g (tomlist F y).

  Definition tomlist_mfmap_proper_iff := forall A B (x y : F A) (f g : A -k-> B),
      shape F x = shape F y /\ mfmap mlist f (tomlist F x) = mfmap mlist g (tomlist F y) <->
      mfmap F f x = mfmap F g y.

  Context
    `{! Mbind F T}.

  Definition tomlist_mbind_proper :=

  Definition tomlist_mbind_proper_inv := forall A B (x y : F A) (f g : A ~k~> T B),
      shape F x = shape F y ->
      mbind F f x = mbind F g y ->
      mfmap mlist (pack T f) (tomlist F x) = mfmap mlist (pack T g) (tomlist F y).

  Definition tomlist_mbind_proper_iff := forall A B (x y : F A) (f g : A ~k~> T B),
      shape F x = shape F y ->
      (mfmap mlist (pack T f) (tomlist F x) = mfmap mlist (pack T g) (tomlist F y) <->
       mbind F f x = mbind F g y).

End properness.

Ltac unfold_mlist_properness :=
  unfold shapeliness,
  tomlist_mfmap_proper, tomlist_mbind_proper,
  tomlist_mfmap_proper_inv, tomlist_mbind_proper_inv,
  tomlist_mfmap_proper_iff, tomlist_mbind_proper_iff in *.

Ltac unfold_properness ::=
  unfold_mset_properness; unfold_mlist_properness.

(** ** Inclusions between properness conditions *)
(** In the multisorted interface, without the ability to decompose
    <<mbind>> into <<join ∘ mfmap>>, the weak properness condition for
    <<mbind>> becomes stronger than that for <<mfmap>> (which remains
    equivalent to the stronger <<mfmap>> properness condition and to
    <<shapeliness>>).*)
Section properness_inclusions.

  Section with_functor.

    Context
      F `{MFunctor F} `{! Tomlist F} `{! Natural (@tomlist _ F _)}.

    Lemma shapeliness_1 : shapeliness F -> tomlist_mfmap_proper F.
    Proof.
      unfold_properness. introv hyp [hshape hcontents].
      apply hyp. split.
      - compose near x on left; compose near y on right. now rewrite 2(shape_mfmap_).
      - compose near x on left; compose near y on right. rewrite <- 2(naturality).
        assumption.
    Qed.

    Lemma shapeliness_2 : tomlist_mfmap_proper F -> tomlist_mfmap_proper_iff F.
    Proof.
      unfold_properness. introv hyp; introv. split.
      - auto.
      - apply shapeliness_0.
    Qed.

    Lemma shapeliness_3 : tomlist_mfmap_proper_iff F -> shapeliness F.
    Proof.
      unfold_properness. introv hyp [hshape hcontents].
      replace x with (mfmap F kid x) by (now rewrite (mfmap_id F)).
      replace y with (mfmap F kid y) by (now rewrite (mfmap_id F)).
      apply hyp. split; auto. now rewrite (mfmap_id mlist).
    Qed.

    Lemma shapeliness_equiv_1 : shapeliness F <-> tomlist_mfmap_proper_iff F.
    Proof.
      split.
      - intros. now apply shapeliness_2, shapeliness_1.
      - apply shapeliness_3.
    Qed.

    Lemma shapeliness_equiv_2 : tomlist_mfmap_proper_iff F <-> tomlist_mfmap_proper F.
    Proof.
      split.
      - intro hyp. unfold_properness. intros. now rewrite <- hyp.
      - apply shapeliness_2.
    Qed.

  End with_functor.

  Section with_module.

    Context
      F `{RightModule F T} `{! Tomlist F}.

    (* can't unfold mbind to reveal an fmap *)
    Goal tomlist_mfmap_proper F -> tomlist_mbind_proper F.
    Proof.
      unfold tomlist_mfmap_proper, tomlist_mbind_proper. introv hyp [? ?].
    Abort.

  End with_module.

End properness_inclusions.

(** * Properness for [tomlist] related to [tomset] *)
Section todo_rename_me.

  Section with_functor.

    Context
      F `{MFunctor F} `{! Tomlist F} `{! Natural (@tomlist _ F _)}.


  End with_functor.

End todo_rename_me.

(** Scraps *)

(*
Lemma tomset_mfmap_proper_qrmod : tomset_mfmap_proper F.
Proof.
  apply tomset_mfmap_proper_of_mbind.
  match goal with
  | H : QuantifiableRightModule F T
    |- _ => now inverts H
  end.
Qed.

Theorem tomset_mfmap_proper_iff_mlist : tomset_mfmap_proper_iff mlist.
Proof.
  Quantifiable.unfold_properness. intros.
  unfold mlist, Mreturn_mlist, Mbind_mlist. (** TODO <-- these are hidden *)
  rewrite 2(Monad_T_Tag_mfmap_spec (T:=list)).
  rewrite <- Ordinary.List.fmap_proper_iff_list.
  unfold tomset, tomset_mlist. split.
  - intros hyp [k a] p_in. fequal. auto.
  - intros hyp k a p_in. specialize (hyp (k, a) p_in).
    now inverts hyp.
Qed.

Theorem tomset_mbind_proper_mlist : tomset_mbind_proper mlist (const mlist).
Proof.
  Quantifiable.unfold_properness. intros A B t f g hyp.
  induction t as [| (?, ?) ? IHt].
  - reflexivity.
  - rewrite 2(mbind_mlist_cons). fequal.
    apply hyp. now left.
    apply IHt. intros. apply hyp. now right.
Qed.

Theorem ret_injective_mlist : forall (A : Type) (k : K) (a1 a2 : A),
    a1 = a2 <-> mret (const mlist) k a1 = mret (const mlist) k a2.
Proof.
  intros. cbv. splits.
  - intro h; now inverts h.
  - intro h; injection h; auto.
Qed.

Theorem tomset_mfmap_proper_iff_Listable : tomset_mfmap_proper_iff F.
Proof.
  intros A B t f g. rewrite mfmap_equal_iff_contents.
  apply tomset_mfmap_proper_iff_mlist.
Qed.

Corollary tomset_mfmap_proper_Listable : tomset_mfmap_proper F.
Proof.
  Quantifiable.unfold_properness.
  intros. apply tomset_mfmap_proper_iff_Listable; auto.
Qed.
{ qfun_properness := tomset_mfmap_proper_Listable; }.


Theorem bind_proper_Listable_mon : forall k, tomset_mbind_proper (T k) T.
Proof.
  introv hyp. apply mbind_equal_if_contents_mon.
  setoid_rewrite in_iff_in_mlist in hyp.
  induction (tomlist (T k) t) as [| (j, a) ? IHl].
  - reflexivity.
  - rewrite 2(mfmap_mlist_cons). cbn.
    fequal. fequal. unfold pack. fequal. apply hyp. now left.
    apply IHl. intros. apply hyp. now right.
Qed.

Theorem bind_proper_Listable_rmod : tomset_mbind_proper F T.
Proof.
  introv hyp. apply (mbind_equal_if_contents).
  setoid_rewrite in_iff_in_mlist in hyp.
  induction (tomlist F t) as [| (j, a) ? IHl].
  - reflexivity.
  - rewrite 2(mfmap_mlist_cons). cbn.
    fequal. fequal. unfold pack. fequal. apply hyp. now left.
    apply IHl. intros. apply hyp. now right.
Qed.

(** <<mfmap f t>> is entirely determined <<f>>'s effect on the contents of <<t>>.*)
Theorem mfmap_equal_iff_contents : forall A B (t : F A) (f g : A -k-> B),
    mfmap F f t = mfmap F g t <-> mfmap mlist f (tomlist F t) = mfmap mlist g (tomlist F t).
Proof.
  intros. split; intro hyp.
  - compose near t. rewrite 2(naturality (η := @tomlist ix F _)).
    unfold compose. now rewrite hyp.
  - assert (tomlist F (mfmap F f t) = tomlist F (mfmap F g t)). apply lfun_properness.  split.
    + compose near t. rewrite 2(shape_mfmap). reflexivity.
    + compose near t. now rewrite <- 2(naturality (η := @tomlist ix F _)).
Qed.


Theorem lfun_properness_rmod : forall A (x y : F A),
    shape F x = shape F y /\ tomlist F x = tomlist F y ->
    x = y.
Proof.
  introv [hshape hcontents]. change (id x = id y). rewrite <- (rmod_mret F T).
  apply (lrmod_properness F T). split; [assumption|].
  rewrite hcontents. clear hcontents. induction (tomlist F y).
  - trivial.
  - trivial.
Qed.


Theorem lmmon_properness_mlist : tomlist_mbind_proper mlist.
Proof.
  intros A B t u f g [hshape hcontents]. generalize dependent u.
  induction t as [| (?, a1) t IHt]; destruct u as [| (?, a2) u];
    introv hshape hcontents.
  - trivial.
  - now inverts hshape.
  - now inverts hshape.
  - inverts hcontents. unfold mbind, Mbind_mlist, Mbind_T_Tag.
    rewrite 2(bind_list_cons). apply shape_eq_cons_tail in hshape.
    cbn. fequal; auto. apply IHt; auto.
Qed.


(** <<mfmap f t>> is entirely determined <<f>>'s effect on the contents of <<t>>.*)
Theorem mbind_equal_if_contents_mon : forall k A B (t : T k A) (f g : A ~k~> T B),
    mfmap mlist (pack _ f) (tomlist (T k) t) =
    mfmap mlist (pack _ g) (tomlist (T k) t) ->
    mbind (T k) f t = mbind (T k) g t.
Proof.
  intros. apply (lmmon_properness T); split. reflexivity.
  assumption.
Qed.

Theorem mbind_equal_if_contents : forall A B (t : F A) (f g : A ~k~> T B),
    mfmap mlist (pack _ f) (tomlist F t) =
    mfmap mlist (pack _ g) (tomlist F t) ->
    mbind F f t = mbind F g t.
Proof.
  intros. now apply (lrmod_properness F T).
Qed.
*)
