From Tealeaves Require Export
     Singlesorted.Classes.Monoid
     Singlesorted.Classes.Monad
     Singlesorted.Functors.Writer
     Multisorted.Classes.DecoratedFunctor
     Multisorted.Classes.Monad
     Multisorted.Functors.Row
     Multisorted.Classes.Functor.

(** Import notations *)
Import Product.Notations.
Import Monoid.Notations.
Import Multisorted.Category.Notations.
Import Multisorted.Classes.Monad.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

#[local] Set Keyed Unification.

(** * Properties of <<shift>> *)
(******************************************************************************)
Section MultisortedMonad_shift.

  Context
    `{MultisortedMonad T}
    `{Monoid W}.

  Lemma shift_return {A} (k : K) (a : A) (w1 w2 : W) :
    shift (w2, mret T k (w1, a)) = mret T k (w2 ● w1, a).
  Proof.
    unfold shift. cbn. compose near (w1, a) on left.
    now rewrite Natural_mret.
  Qed.

End MultisortedMonad_shift.

(** * Typeclasses for decorated monads *)
(******************************************************************************)

(** ** Decorated pre-modules *)
(******************************************************************************)
Section DecoratedMultisortedPreModule.

  Context
    `{ix : Index}
    (W : Type)
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{! MReturn T} `{! forall k, MBind (T k) T} `{! MBind F T}
    `{Decorate W F} `{forall k, Decorate W (T k)}
    {mn_op : Monoid_op W}
    {mn_unit : Monoid_unit W}.

  Class DecoratedMultisortedPreModule :=
    {dpmod_premodule :> MultisortedPreModule F T;
     dpmod_monoid :> Monoid W;
      dpmod_dec_dec :
        `(decorate F ∘ decorate F (A:=A) = mfmap F (const (cojoin (W ×))) ∘ decorate F);
      dpmod_dec_extract :
        `(mfmap F (const (extract (W ×))) ∘ decorate F = @id (F A));
      dpmod_mbind : forall `(f : A ~k~> T B),
          decorate F ∘ mbind F f =
          mbind F (fun k => shift ∘ fmap (W ×) (decorate (T k) ∘ f k)) ∘ decorate F;
    }.

End DecoratedMultisortedPreModule.

(** ** Decorated monads *)
(******************************************************************************)
Section DecoratedMultisortedMonad.

  Context
    `{ix : Index}
    (W : Type)
    (T : K -> Type -> Type)
    `{! MReturn T} `{! forall k, MBind (T k) T}
    `{forall k, Decorate W (T k)}
    {mn_op : Monoid_op W}
    {mn_unit : Monoid_unit W}.

  Class DecoratedMultisortedMonad :=
    { dmmon_monad :> MultisortedMonad T;
      dmmon_monoid :> Monoid W;
      dmmon_premodule :> forall k, DecoratedMultisortedPreModule W (T k) T;
      dmmon_mret : forall {A} k,
          decorate (T k) ∘ mret T k = mret T k ∘ ret (W ×) (A:=A);
    }.

End DecoratedMultisortedMonad.

(** ** Decorated multisorted right modules *)
(******************************************************************************)
Section DecoratedMultisortedModule.

  Context
    `{ix : Index}
    (W : Type)
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{! MReturn T} `{! forall k, MBind (T k) T} `{! MBind F T}
    `{Decorate W F} `{forall k, Decorate W (T k)}
    {mn_op : Monoid_op W}
    {mn_unit : Monoid_unit W}.

  Class DecoratedMultisortedModule : Prop :=
    { drmod_monad :> DecoratedMultisortedMonad W T;
      drmod_premod :> DecoratedMultisortedPreModule W F T;
      drmod_module :> MultisortedRightModule F T
    }.

End DecoratedMultisortedModule.

(** ** Basic typeclass inclusions *)
(******************************************************************************)

(** *** A monad acts on itself as a module *)
(******************************************************************************)
Section DecoratedMultisortedModule.

  Context
    `{DecoratedMultisortedMonad W T}.

  Instance DecoratedMultisortedModule_Monad (k : K) :
    DecoratedMultisortedModule W (T k) T :=
    {| drmod_module := MultisortedRightModule_Monad k |}.

End DecoratedMultisortedModule.

(** *** The carrier of a dec. module is a dec. functor *)
(******************************************************************************)
Section DecoratedMultisortedModule_Functor.

  Context
    `{ix : Index}
    (W : Type)
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{! MReturn T} `{! forall k, MBind (T k) T} `{! MBind F T}
    `{Decorate W F} `{forall k, Decorate W (T k)}
    {mn_op : Monoid_op W}
    {mn_unit : Monoid_unit W}
    `{! DecoratedMultisortedPreModule W F T}
    `{! DecoratedMultisortedMonad W T}.

  Theorem decorate_natural : MultisortedNatural (fun A => decorate (W:=W) F (A:=A)).
  Proof.
    intros A B f.
    unfold mfmap at 2, MFmap_rmod.
    rewrite (dpmod_mbind W F T). f_equal.
    unfold mfmap, MFmap_compose_Fmap.
    unfold mfmap. f_equal. ext k.
    reassociate <-.
    rewrite (dmmon_mret W T).
    ext [w a]. unfold compose; cbn.
    change ((ret (prod W) (f k a))) with (Ƶ, f k a).
    compose near (Ƶ, f k a).
    rewrite (mnaturality (MultisortedNatural := Natural_mret)).
    unfold compose; cbn. now rewrite monoid_id_l.
  Qed.

  #[global] Instance DecoratedMultisortedFunctor_Module : DecoratedMultisortedFunctor W F.
  Proof.
    constructor; try typeclasses eauto.
    - apply decorate_natural.
    - intros. apply (dpmod_dec_dec W F T).
    - intros. apply (dpmod_dec_extract W F T).
  Qed.

End DecoratedMultisortedModule_Functor.

(** * Multisorted decorated Kleisli operation: [mbindd] *)
(******************************************************************************)
Definition mbindd (F : Type -> Type) {A B} `{MBind F T} `{Decorate W F}
           (f : W * A ~k~> T B) := mbind F f ∘ decorate F.

Definition mkcomposed `{Index} (T : K -> Type -> Type) {A B C} `{Monoid_op W}
           `{! forall k, Decorate W (T k)}`{! forall k, MBind (T k) T} `{! MReturn T}
           (g : W * B ~k~> T C)
           (f : W * A ~k~> T B) : W * A ~k~> T C
  := fun k => mbind (T k) g ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f k).

Theorem mkcomposed_spec `{DecoratedMultisortedModule W F T} A B C
        (g : forall k, W * B -> T k C)
        (f : forall k, W * A -> T k B) :
  mkcomposed T g f = fun (k : K) '(w, a) =>
                       (mbindd (T k) (fun k '(w', b) => g k ((w ● w', b))) ∘ f k) (w, a).
Proof.
  intros. unfold mkcomposed. ext k [w a].
  unfold mbindd, compose, shift; cbn.
  compose near (decorate (T k) (f k (w, a))) on left.
  rewrite (mbind_mfmap (T k)).
  fequal. now ext j [? ?].
Qed.

#[local] Notation "g ⋆md f" := (mkcomposed _ g f) (at level 60).

(** ** Composition with [mret] *)
(******************************************************************************)
Section DecoratedMultisortedMonad_mret.

  Context
    `{ix : Index}
    (T : K -> Type -> Type)
    `{DecoratedMultisortedMonad (ix := ix) W T}.

  Theorem dec_mret : forall (A : Type) (k : K),
      decorate (T k) ∘ mret T k = mret T k ∘ pair Ƶ (B:=A).
  Proof.
    introv. ext a. now rewrite (dmmon_mret W T).
  Qed.

  Lemma mbindd_comp_mret {A B} : forall (f : W * A ~k~> T B) (k : K),
      mbindd (T k) f ∘ mret T k = f k ∘ ret (W ×).
  Proof.
    introv. unfold mbindd.
    reassociate -> on left.
    rewrite (dmmon_mret W T).
    reassociate <- on left.
    now rewrite (mmon_mbind_comp_mret T).
  Qed.

End DecoratedMultisortedMonad_mret.

(** ** Sub-operations as special cases of [mbindd] *)
(******************************************************************************)
Section mbindd_special_cases.

  Context
    (F : Type -> Type)
    `{DecoratedMultisortedModule W F T}.

  Lemma mbind_to_mbindd {A B} (f : forall k, A -> T k B) :
    mbind F f = mbindd F (fun k => f k ∘ const snd k).
  Proof.
    unfold mbindd. rewrite <- (mbind_mfmap F).
    reassociate -> on right. now rewrite (decf_dec_extract W F).
  Qed.

  Lemma mfmapd_to_mbindd {A B} (f : W * A -k-> B) :
    mfmapd F f = mbindd F (fun k => mret T k ∘ f k).
  Proof.
    reflexivity.
  Qed.

  Lemma mfmap_to_mbindd {A B} (f : A -k-> B) :
    mfmap F f = mbindd F (fun k => mret T k ∘ f k ∘ snd).
  Proof.
    now rewrite (mfmap_to_mfmapd F).
  Qed.

End mbindd_special_cases.

(** ** Interaction between [decorate] and [ret], [mbindd], [bind] *)
(******************************************************************************)
Section decorate_bind.

  Context
    (F : Type -> Type)
    `{DecoratedMultisortedModule W F T}.

  Theorem dec_mbindd : forall A B (f : forall k, W * A -> T k B),
      decorate F ∘ mbindd F f =
      mbindd F (fun k => shift ∘ cobind (prod W) (decorate (T k) ∘ f k)).
  Proof.
    introv. unfold mbindd.
    reassociate <- on left.
    rewrite (dpmod_mbind W F T).
    reassociate -> on left.
    rewrite (decf_dec_dec W F).
    reassociate <- on left.
    rewrite (mbind_mfmap F).
    reflexivity.
  Qed.

  Corollary dec_mbind : forall A B (f : forall k, W * A -> T k B) ,
      decorate F ∘ mbind F f =
      mbindd F (fun k => shift ∘ fmap (prod W) (decorate (T k) ∘ f k)).
  Proof.
    introv. rewrite (mbind_to_mbindd F).
    rewrite dec_mbindd. fequal. ext k [? [? ?]].
    unfold compose. easy.
  Qed.

End decorate_bind.

(** ** Identity and composition laws for [mbindd] *)
(******************************************************************************)
Section id_composition_mbindd.

  Context
    (F : Type -> Type)
    `{DecoratedMultisortedModule W F T}.

  Theorem mbindd_mret {A} :
    mbindd F (mret T ◻ const snd) = @id (F A).
  Proof.
    introv. unfold mbindd.
    rewrite <- (mbind_mfmap F).
    reassociate -> on left.
    rewrite (decf_dec_extract W F).
    now rewrite (pmod_mbind_mret F T).
  Qed.

  Theorem mbindd_mbindd {A B C} : forall (g : W * B ~k~> T C) (f : W * A ~k~> T B),
      mbindd F g ∘ mbindd F f = mbindd F (g ⋆md f).
  Proof.
    introv. unfold mbindd at 1.
    reassociate -> on left.
    rewrite (dec_mbindd F).
    unfold mbindd.
    reassociate <- on left.
    now rewrite (pmod_mbind_mbind F T).
  Qed.

End id_composition_mbindd.

(** ** Utility lemmas for composition laws *)
(******************************************************************************)
Section composition_utility.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{Monoid W}
    `{! MBind F T} `{! MReturn T} `{forall k, MBind (T k) T}
    `{Decorate W F} `{forall k, Decorate W (T k)}
    `{! DecoratedMultisortedMonad (ix := ix) W T}
    `{! DecoratedMultisortedPreModule (ix := ix) W F T}.

  (** TODO: Document why this is an important lemma *)
  Lemma mkcomposed_1 : forall A B (f : W * A -> B) k,
      shift ∘ cobind (prod W) (decorate (T k) ∘ (mret T k ∘ f)) = mret T k ∘ cobind (prod W) f.
  Proof.
    introv.
    reassociate <- on left. rewrite (dmmon_mret W T).
    ext [? ?]. unfold compose; cbn.
    change ((ret (prod W) (f (w, a)))) with (Ƶ, f (w, a)).
    compose near (Ƶ, f (w, a)).
    rewrite (mnaturality (MultisortedNatural := Natural_mret)).
    unfold compose; cbn.
    now rewrite (monoid_id_l).
  Qed.

  Corollary mbindd_shift {A B} : forall (g : W * A ~k~> T B),
      mbind F g ∘ shift = fun '(w, t) => mbind F (fun k '(w', a) => g k (w ● w', a)) t.
  Proof.
    introv. rewrite shift_spec.
    reassociate <- on left.
    rewrite (mbind_mfmap F).
    rewrite mbind_mstrength.
    ext [? ?]. fequal. now ext k [? ?].
  Qed.

  Lemma mkcomposed_extract {A B} : forall k (f : W * A -> T k B),
      mfmap (T k) (const (extract (W ×))) ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f) = f.
  Proof.
    intros k ?.
    assert (MultisortedRightModule (T k) T) by apply MultisortedRightModule_Monad.
    rewrite shift_extract.
    reassociate -> on left.
    rewrite (extract_cobind (prod W)).
    reassociate <- on left.
    now rewrite (dpmod_dec_extract W (T k) T).
  Qed.

End composition_utility.

(** ** Composition with sub-operations *)
(******************************************************************************)
Section composition_misc_mbindd.

  Context
    (F : Type -> Type)
    `{DecoratedMultisortedModule W F T}.

  Corollary mbindd_mbind {A B C} : forall (g : W * B ~k~> T C) (f : A ~k~> T B),
      mbindd F g ∘ mbind F f = mbindd F (g ⋆md (fun k => f k ∘ extract (W ×))).
  Proof.
    introv. rewrite (mbind_to_mbindd F).
    now rewrite (mbindd_mbindd F).
  Qed.

  Corollary mbindd_mfmapd {A B C} : forall (g : forall k, W * B -> T k C) (f : W * A -k-> B),
      mbindd F g ∘ mfmapd F f =
      mbindd F (fun k '(w, a) => g k (w, f k (w, a))).
  Proof.
    introv. unfold mbindd, mfmapd.
    reassociate -> on left.
    reassociate <- near (decorate (A:=B) F).
    rewrite <- (mnaturality (η := @decorate W F _)).
    reassociate <- on left.
    unfold_ops @MFmap_compose_Fmap.
    reassociate <- on left.
    rewrite (mbind_mfmap F).
    reassociate -> on left.
    rewrite (dpmod_dec_dec W F T).
    reassociate <- on left.
    rewrite (mbind_mfmap F).
    do 2 fequal. now ext k [? ?].
  Qed.

  Corollary mbindd_mfmap {A B C} : forall (g : W * B ~k~> T C) (f : A -k-> B),
      mbindd F g ∘ mfmap F f =
      mbindd F (fun k '(w, a) => g k (w, f k a)).
  Proof.
    introv. rewrite (mfmap_to_mfmapd F).
    now rewrite mbindd_mfmapd.
  Qed.

  Corollary mbind_mfmapd {A B C} : forall (g : forall k, B -> T k C) (f : W * A -k-> B),
      mbind F g ∘ mfmapd F f =
      mbindd F (fun k '(w, a) => g k (f k (w, a))).
  Proof.
    introv. rewrite (mbind_to_mbindd F).
    now rewrite mbindd_mfmapd.
  Qed.

  Corollary mbind_mbindd {A B C} : forall (g : B ~k~> T C) (f : W * A ~k~> T B),
      mbind F g ∘ mbindd F f = mbindd F (g ⋆m f).
  Proof.
    intros g f.
    rewrite (mbind_to_mbindd F).
    rewrite (mbindd_mbindd F).
    f_equal. ext k [w a].
    unfold mkcomposed.
    assert (MultisortedRightModule (T k) T) by apply MultisortedRightModule_Monad.
    rewrite <- (mbind_mfmap (T k)).
    reassociate <- on left.
    (* this next reassociation is difficult to achieve with current tactic support *)
    change left ((mbind (T k) g ∘
                        (mfmap (T k) (const (extract (W ×))) ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f k))) (w, a)).
    now rewrite (mkcomposed_extract T).
  Qed.

  Corollary mfmapd_mbindd {A B C} : forall (g : W * B -k-> C) (f : W * A ~k~> T B),
      mfmapd F g ∘ mbindd F f = mbindd F ((fun k => mret T k ∘ g k) ⋆md f).
  Proof.
    introv. rewrite (mfmapd_to_mbindd).
    now rewrite (mbindd_mbindd F).
  Qed.

  Corollary mfmap_mbindd {A B C} : forall (g : B -k-> C) (f : W * A ~k~> T B),
      mfmap F g ∘ mbindd F f = mbindd F (fun k => mfmap (T k) g ∘ f k).
  Proof.
    introv. unfold_ops @MFmap_rmod.
    now rewrite (mbind_mbindd).
  Qed.

End composition_misc_mbindd.

(** ** Properties of Kleisli composition *)
(******************************************************************************)
Section kleisli_mbindd.

  Context
    (F : Type -> Type)
    `{DecoratedMultisortedModule W F T}
    {A B C D : Type}.

  Theorem mkcomposed_id_l : forall f : W * A ~k~> T B,
      (fun k => mret T k ∘ extract (W ×)) ⋆md f = f.
  Proof.
    introv. unfold mkcomposed. ext k.
    assert (MultisortedRightModule (T k) T) by apply MultisortedRightModule_Monad.
    change ((fun k => mret T k ∘ extract (W ×) (A := ?A)))
      with ((fun k => mret T k ∘ (const (extract (W ×) (A := A)) k))).
    rewrite <- (mbind_mfmap (T k)).
    change left (mbind (T k) (mret T) ∘
                       (mfmap (T k) (const (extract (W ×))) ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f k))).
    rewrite (mkcomposed_extract T).
    now rewrite (pmod_mbind_mret (T k) T).
  Qed.

  Theorem mkcomposed_id_r : forall f : W * A ~k~> T B,
      f ⋆md (fun k => mret T k ∘ extract (W ×)) = f.
  Proof.
    introv. unfold mkcomposed. ext k.
    reassociate -> on left.
    rewrite (mkcomposed_1 (W := W) T _ _ (extract (W ×)) k).
    reassociate <- on left.
    rewrite (mmon_mbind_comp_mret T).
    now ext [? ?].
  Qed.

  Lemma mkcomposed_assoc :
    forall (f : W * A ~k~> T B)
      (g : W * B ~k~> T C)
      (h : W * C ~k~> T D),
      h ⋆md (g ⋆md f) = (h ⋆md g) ⋆md f.
  Proof.
    introv. unfold mkcomposed. ext k.
  Admitted.

End kleisli_mbindd.

(** * Targeted substitution in decorated modules: [bindkd] *)
(******************************************************************************)

(** ** Operations [bindkd] and [mkcomposedk] *)
(******************************************************************************)

(** Build a k-substitution that targets only the leaves belonging to a partition
    [k]. This must be restricted to morphisms that do not change the leaf type. *)
#[program] Definition btgr `{Index} T `{! MReturn T} {W A} (k : K) (f : W * A -> T k A) :
  forall k, W * A -> T k A := btgd T k f (fun k' => mret T k' ∘ extract (W ×)).

Definition bindkd `{Index} F {W A} `{! MReturn T} `{! MBind F T}
           `{Decorate W F} (k : K) (f : W * A -> T k A) : F A -> F A
  := mbindd F (btgr T k f).

Definition kcomposekd `{Index} {A W} `{Monoid_op W}
           `{forall k, Decorate W (T k)} `{! MReturn T} `{! forall k, MBind (T k) T}
           (k : K)
           (g : W * A -> T k A)
           (f : W * A -> T k A) : W * A -> T k A
  := mbind (T k) (btgr T k g) ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f).

#[local] Notation "g ⋆kd f" := (kcomposekd _ g f) (at level 60).
#[local] Notation "g ⋆md f" := (mkcomposed _ g f) (at level 60).

Lemma btgr_eq `{Index} `{! MReturn T} {A W} (k : K) (f : W * A -> T k A) : btgr T k f k = f.
Proof.
  unfold btgr. now rewrite btgd_eq.
Qed.

Lemma btgr_neq `{Index} `{! MReturn T} {A W} (k k' : K) (p : k <> k') (f : W * A -> T k A) :
  btgr T k f k' = mret T k' ∘ extract (W ×).
Proof.
  unfold btgr. now rewrite btgd_neq.
Qed.

Hint Rewrite @btgr_eq : tea_tgt.
Hint Rewrite @btgr_eq : tea_tgt_eq.
Hint Rewrite @btgr_neq using auto : tea_tgt.
Hint Rewrite @btgr_neq using auto : tea_tgt_neq.

Theorem kcompkr_spec `{DecoratedMultisortedMonad W T} A k
        (g : W * A -> T k A) (f : W * A -> T k A) :
  kcomposekd k g f =
  fun '(w, a) => (bindkd (T k) k (fun '(w', a) => g (w ● w', a)) ∘ f) (w, a).
Proof.
  intros. unfold kcomposekd. ext [w a].
  unfold bindkd, mbindd, compose, shift; cbn.
  compose near (decorate (T k) (f (w, a))) on left.
  assert (MultisortedRightModule (T k) T) by apply MultisortedRightModule_Monad.
  rewrite (mbind_mfmap (T k)).
  unfold compose at 1; cbn.
  fequal. ext k' [? ?].
  compare values k and k'; now simpl_tgt_fallback.
Qed.

(** ** Properties specific to decorated monads *)
(******************************************************************************)
Section DecoratedMultisortedMonad_bindkd.

  Context
    `{ix : Index}
    (T : K -> Type -> Type)
    `{DecoratedMultisortedMonad (ix := ix) W T}.

  Lemma bindkd_comp_mret_eq {A} : forall k (f : W * A -> T k A) (a : A),
      bindkd (T k) k f (mret T k a) = f (Ƶ, a).
  Proof.
    introv. unfold bindkd.
    compose near a. rewrite (mbindd_comp_mret T).
    now simpl_tgt.
  Qed.

  Lemma bindkd_comp_mret_neq {A} : forall k1 k2 (f : W * A -> T k2 A) (a : A),
      k1 <> k2 ->
      bindkd (T k1) k2 f (mret T k1 a) = mret T k1 a.
  Proof.
    introv neq. unfold bindkd.
    compose near a on left. rewrite (mbindd_comp_mret T).
    now simpl_tgt.
  Qed.

  Lemma btgr_btgr_eq {A} (k : K) (g f : W * A -> T k A) :
    btgr T k (g ⋆kd f) = btgr T k g ⋆md btgr T k f.
  Proof.
    ext k'. destruct_eq_args k k'.
    - rewrite btgr_eq. unfold mkcomposed.
      now rewrite btgr_eq.
    - rewrite btgr_neq; auto. unfold mkcomposed.
      rewrite btgr_neq; auto.
      reassociate -> on right.
      rewrite (mkcomposed_1 T).
      reassociate <- on right.
      rewrite (mmon_mbind_comp_mret T).
      rewrite btgr_neq; auto.
      now ext [? ?].
  Qed.

End DecoratedMultisortedMonad_bindkd.

Section DecoratedMultisortedModule_theory.

  Context
    `{ix : Index}
    (F : Type -> Type)
    `{DecoratedMultisortedModule (ix:=ix) W F T}.

  (** ** Sub-operations of [bindkd] *)
  (******************************************************************************)
  Lemma bindk_to_bindkd {A} : forall (k : K) (f : A -> T k A),
      bindk F k f = (bindkd F k (f ∘ extract (W ×)) : F A -> F A).
  Proof.
    intros k ?. unfold bindk, bindkd.
    rewrite (mbind_to_mbindd F). fequal; ext k' [? ?].
    unfold compose; cbn. destruct_eq_args k k'.
    all: now autorewrite* with tea_tgt.
  Qed.

  Lemma fmapk_to_bindkd {A} : forall (k : K) (f : A -> A),
      fmapk F k f = (bindkd F k (mret T k ∘ f ∘ extract (W ×)) : F A -> F A).
  Proof.
    introv. rewrite fmapk_to_bindk.
    now rewrite bindk_to_bindkd.
  Qed.

  Lemma fmapkd_to_bindkd {A} : forall (k : K) (f : W * A -> A),
      fmapkd F k f = (bindkd F k (mret T k ∘ f) : F A -> F A).
  Proof.
    intros k ?. unfold fmapkd, mfmapd, bindkd, mbindd.
    unfold_ops @MFmap_rmod. do 2 f_equal.
    ext k'. destruct_eq_args k k'.
    all: now autorewrite* with tea_tgt.
  Qed.

  (** ** Interaction between [decorate] and [bindkd] *)
  (******************************************************************************)
  Lemma dec_bindkd {k A} : forall (f : W * A -> T k A),
      decorate F ∘ bindkd F k f =
      mbindd F (btgd T k (shift ∘ cobind (prod W) (decorate (T k) ∘ f)) (fun k => mret T k)).
  Proof.
    intros f. unfold bindkd. rewrite (dec_mbindd F).
    fequal. ext k'. destruct_eq_args k k'.
    - now autorewrite* with tea_tgt.
    - autorewrite* with tea_tgt.
      rewrite (mkcomposed_1 T). now ext [? ?].
  Qed.

  (** ** Functorial laws for [bindkd] *)
  (******************************************************************************)
  Theorem bindkd_mret : forall {A k},
      bindkd F k (mret T k ∘ extract (W ×)) = @id (F A).
  Proof.
    intros A k. unfold bindkd.
    replace (btgr T k (mret T k ∘ extract (W ×) (A := A)))
      with (fun k : K => mret T k ∘ (const (extract (W ×) (A := A)) k)).
    { apply (mbindd_mret F). }
    ext k'. destruct_eq_args k k'.
    all: now autorewrite* with tea_tgt.
  Qed.

  Theorem bindkd_bindkd_eq : forall A k (g : W * A -> T k A) (f :  W * A -> T k A),
      bindkd F k g ∘ bindkd F k f =
      bindkd F k (g ⋆kd f).
  Proof.
    introv. unfold bindkd.
    rewrite (mbindd_mbindd F).
    now rewrite (btgr_btgr_eq T).
  Qed.

  (** ** Kleisli composition laws for [bindkd] *)
  (******************************************************************************)
  Theorem kcomposekd_id_l {k A} : forall f : W * A -> T k A,
      (mret T k ∘ extract (W ×)) ⋆kd f = f.
  Proof.
    introv. unfold kcomposekd.
    unfold btgr.
    change (btgd T k (mret T k ∘ extract (W ×)) (fun k0 : K => mret T k0 ∘ extract (W ×)))
      with (btgd T k (((fun k0 : K => mret T k0 ∘ @snd W A) k)) (fun k0 : K => mret T k0 ∘ extract (W ×))).
    rewrite btgd_same.
    assert (MultisortedRightModule (T k) T) by apply MultisortedRightModule_Monad.
    rewrite <- (mbind_mfmap (T k)).
    change (fun _ => extract (W ×)) with (@const K _ (@snd W A)).
    rewrite (pmod_mbind_mret (T k) T).
    now rewrite <- (mkcomposed_extract T).
  Qed.

  Theorem kcomposekd_id_r {k A} : forall f : W * A -> T k A,
      f ⋆kd (mret T k ∘ extract (W ×)) = f.
  Proof.
    introv. unfold kcomposekd.
    reassociate -> on left.
    rewrite (mkcomposed_1 T).
    reassociate <- on left.
    rewrite (mmon_mbind_comp_mret T).
    ext [? ?]. now rewrite btgr_eq.
  Qed.

  (** ** Composition with sub-operations *)
  (******************************************************************************)
  Corollary bindkd_bindk {A} : forall k (g : W * A -> T k A) (f : A -> T k A),
      bindkd F k g ∘ bindk F k f = bindkd F k (g ⋆kd f ∘ extract (W ×)).
  Proof.
    introv. rewrite bindk_to_bindkd.
    now rewrite bindkd_bindkd_eq.
  Qed.

  Corollary bindkd_fmapkd {A} : forall k (g : W * A -> T k A) (f : W * A -> A),
      bindkd F k g ∘ fmapkd F k f =
      bindkd F k (g ∘ cobind (prod W) f).
  Proof.
    introv. rewrite fmapkd_to_bindkd.
    rewrite bindkd_bindkd_eq. f_equal.
    unfold kcomposekd. reassociate -> on left.
    rewrite (mkcomposed_1 T).
    reassociate <- on left.
    rewrite (mmon_mbind_comp_mret T).
    now rewrite btgr_eq.
  Qed.

  Corollary bindkd_fmapk {A} : forall k (g : W * A -> T k A) (f : A -> A),
      bindkd F k g ∘ fmapk F k f =
      bindkd F k (g ∘ map_snd f).
  Proof.
    introv. rewrite (fmapk_to_fmapkd F).
    rewrite bindkd_fmapkd.
    fequal. ext [? ?]. easy.
  Qed.

  Corollary bindk_bindkd {A} : forall k (g : A -> T k A) (f : W * A -> T k A),
      bindk F k g ∘ bindkd F k f =
      bindkd F k (bindk (T k) k g ∘ f).
  Proof.
    intros k ? ?. unfold bindkd, mbindd, bindk.
    reassociate <- on left.
    rewrite (mbind_mbind F).
    do 2 f_equal. ext k' [? a]. compare values k and k'.
    - unfold mkcompose, compose. now simpl_tgt_fallback.
    - unfold mkcompose, compose. simpl_tgt_fallback.
      unfold compose; cbn.
      compose near a on left.
      rewrite (mmon_mbind_comp_mret T).
      now simpl_tgt_fallback.
  Qed.

  Corollary fmapkd_bindkd {A} : forall k (g : W * A -> A) (f : W * A -> T k A),
      fmapkd F k g ∘ bindkd F k f =
      bindkd F k (mret T k ∘ g ⋆kd f).
  Proof.
    intros. rewrite fmapkd_to_bindkd.
    now rewrite bindkd_bindkd_eq.
  Qed.

  Corollary fmapk_bindkd {A} : forall k (g : A -> A) (f : W * A -> T k A),
      fmapk F k g ∘ bindkd F k f =
      bindkd F k (fmapk (T k) k g ∘ f).
  Proof.
    introv. unfold bindkd, fmapk. rewrite (mfmap_mbindd F).
    fequal. ext j. compare values k and j.
    - now simpl_tgt_fallback.
    - simpl_tgt_fallback.
      reassociate <- on left. rewrite (Natural_mret).
      fequal. unfold mfmap, MFmap_I_k.
      now simpl_tgt_fallback.
  Qed.

  Corollary bindk_fmapkd {A} : forall k (g : A -> T k A) (f : W * A -> A),
      bindk F k g ∘ fmapkd F k f =
      bindkd F k (g ∘ f).
  Proof.
    introv. rewrite bindk_to_bindkd.
    rewrite bindkd_fmapkd.
    reassociate -> on left.
    do 2 f_equal. now rewrite (extract_cobind (prod W)).
  Qed.

End DecoratedMultisortedModule_theory.

(** ** Rewrite Hint registration *)
(******************************************************************************)
Hint Rewrite @btgr_eq : tea_tgt.
Hint Rewrite @btgr_eq : tea_tgt_eq.
Hint Rewrite @btgr_neq using auto : tea_tgt.
Hint Rewrite @btgr_neq using auto : tea_tgt_neq.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "g ⋆md f" := (mkcomposed _ g f) (at level 60) : tealeaves_multi_scope.
  Notation "g ⋆kd f" := (kcomposekd _ g f) (at level 60) : tealeaves_multi_scope.
End Notations.
