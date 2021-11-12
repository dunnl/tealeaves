From Tealeaves Require Import
     Singlesorted.Classes.Monoid
     Singlesorted.Classes.Monad
     Singlesorted.Functors.Writer
     Multisorted.Functors.Row
     Multisorted.Classes.Functor.

(** Import notations *)
Import Monoid.Notations.
Import Multisorted.Category.Notations.
Import Product.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

#[local] Set Keyed Unification.

Lemma strength_return {A B} (k : K) (a : A) (b : B) :
  strength (b, mret T k a) = mret T k (b, a).
Proof.
  unfold strength. compose near a on left.
  now rewrite Natural_mret.
Qed.

Lemma shift_return {A} (k : K) (a : A) (w1 w2 : W) :
  shift (w2, mret T k (w1, a)) = mret T k (w2 ● w1, a).
Proof.
  unfold shift. cbn. compose near (w1, a) on left.
  now rewrite Natural_mret.
Qed.

(** ** Decorated monads *)
(******************************************************************************)
Section decorated_monad_class.

  Context
    (W : Type)
      {mn_op : Monoid_op W}
      {mn_unit : Monoid_unit W}
      (T : K -> Type -> Type)
      `{MMonad (ix:=ix) T}
      `{forall k, Decorate W (T k)}.

    Class DecoratedMMonad : Prop :=
      { dmmon_monad :> MMonad T;
        dmmon_monoid :> Monoid W;
        dmmon_mret : forall {A} k,
            decorate (T k) ∘ mret T k = mret T k ∘ pair Ƶ (B:=A);
        dmmon_mbind : forall {A B} (f : forall k, A -> T k B) k,
            decorate (T k) ∘ mbind (T k) f =
            mbind (T k) (fun k => shift ∘ map_snd (decorate (T k) ∘ f k)) ∘ decorate (T k);
        dmmon_read_read : forall {A} k,
            decorate (T k) ∘ decorate (T k) (A:=A) = mfmap (T k) (fun k => dup_left) ∘ decorate (T k);
        dmmon_read_proj : forall {A} k,
            mfmap (T k) (const snd) ∘ decorate (T k) = @id (T k A);

      }.

  End decorated_monad_class.

  (** *** Decorated modules *)
  (******************************************************************************)
  Section decorated_module_class.

    Context
      (W : Type)
      (F : Type -> Type)
      (T : K -> Type -> Type)
      {mn_op : Monoid_op W} {mn_unit : Monoid_unit W}
      (* ^ we name these two arguments to be particular about monoid instances later *)
      `{Mbind (ix:=ix) F T}
      `{Decorate W F}
      `{DecoratedMMonad W (mn_op:=mn_op) (mn_unit:=mn_unit) T}.

    Class DecoratedModule : Prop :=
      { drmod_monad :> DecoratedMMonad W T;
        drmod_module :> RightModule F T;
        drmod_mbind : forall {A B} (f : forall k, A -> T k B),
            decorate F ∘ mbind F f =
            mbind F (fun k => shift ∘ map_snd (decorate (T k) ∘ f k)) ∘ decorate F;
        drmod_read_read : forall {A},
            decorate F ∘ decorate F (A:=A) = mfmap F (fun k => dup_left) ∘ decorate F;
        drmod_read_proj : forall {A},
            mfmap F (const snd) ∘ decorate F = @id (F A);
      }.

  End decorated_module_class.

  (** ** Typeclass inclusions *)
  (** *** A monad acts on itself as a module *)
  (******************************************************************************)
  Section decorated_monad_to_module.

    Context
      `{DecoratedMMonad W T}.

    Instance Decorated_Module_MMonad {k} : DecoratedModule W (T k) T :=
      {| drmod_mbind := fun A B f => dmmon_mbind W T f k;
         drmod_read_read := fun A => dmmon_read_read W T k;
         drmod_read_proj := fun A => dmmon_read_proj W T k;
         drmod_module := Module_MMonad k;
      |}.

  End decorated_monad_to_module.

  (** *** The carrier of a dec. module is a dec. functor *)
  (******************************************************************************)
  Section decorated_module_to_functor.

    Context
      `{DecoratedModule W F G}.

    Theorem decorate_natural : Natural (fun A => decorate (W:=W) F (A:=A)).
    Proof.
      intros A B f.
      unfold mfmap at 2, Mfmap_rmod.
      rewrite (drmod_mbind W F G). f_equal.
      unfold mfmap, Mfmap_comp_Fmap.
      unfold mfmap. f_equal. ext k.
      rewrite Prelude.compose_assoc.
      rewrite (dmmon_mret W G).
      ext [w a]. unfold compose; cbn.
      compose near (Ƶ, f k a).
      rewrite (naturality (Natural := Natural_mret)).
      unfold compose; cbn. now rewrite monoid_id_l.
    Qed.

    #[global] Instance DecoratedMFunctor_rmod : DecoratedMFunctor W F.
    Proof.
      constructor; try typeclasses eauto.
      - intros. apply (drmod_read_read W F G).
      - intros. apply (drmod_read_proj W F G).
      - apply decorate_natural.
    Qed.

  End decorated_module_to_functor.


  (** * Parallel substitution in decorated modules, [mbindr] *)
  (******************************************************************************)
  Section decorated_module_parallel_substitution.

    (** ** Operations [mbindr] and [mkcompr] *)
    (******************************************************************************)
    Definition mbindr F {A B} `{Mbind (ix:=ix) F T} `{Decorate W F}
               (f : forall k, W * A -> T k B) := mbind F f ∘ decorate F.

    Definition mkcompr `{Index} T {A B C} `{Monoid_op W}
               `{! forall k, Decorate W (T k)}`{! forall k, Mbind (T k) T} `{! Mreturn T}
               (g : forall k, W * B -> T k C)
               (f : forall k, W * A -> T k B) : forall k, W * A -> T k C
      := fun k => mbind (T k) g ∘ (shift ∘ cobind (prod W) (decorate (T k) ∘ f k)).

    Theorem mkcompr_spec `{DecoratedModule W F T} A B C
            (g : forall k, W * B -> T k C)
            (f : forall k, W * A -> T k B) :
      mkcompr T g f =
      fun k '(w, a) => (mbindr (T k) (fun k '(w', b) => g k ((w ● w', b))) ∘ f k) (w, a).
    Proof.
      intros. unfold mkcompr. ext k [w a].
      unfold mbindr, compose, shift; cbn.
      compose near (decorate (T k) (f k (w, a))) on left.
    assert (RightModule (T k) T) by apply Module_MMonad.
    rewrite (mbind_mfmap (T k)).
    fequal. now ext j [? ?].
  Qed.

  Notation "g ∗mr f" := (mkcompr _ g f) (at level 60).

  (** ** [mfmap], [mfmapr], [mbind] as special cases of [mbindr] *)
  (******************************************************************************)
  Section mbindr_special_cases.

    Context
      F `{DecoratedModule W F T}.

    Lemma mbind_to_mbindr {A B} (f : forall k, A -> T k B) :
      mbind F f = mbindr F (fun k => f k ∘ const snd k).
    Proof.
      unfold mbindr. rewrite <- (mbind_mfmap F).
      reassociate -> on right. now rewrite (decf_read_proj W).
    Qed.

    Lemma mfmapr_to_mbindr {A B} (f : W * A -k-> B) :
      mfmapr F f = mbindr F (fun k => mret T k ∘ f k).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmap_to_mbindr {A B} (f : A -k-> B) :
      mfmap F f = mbindr F (fun k => mret T k ∘ f k ∘ snd).
    Proof.
      now rewrite (mfmap_to_mfmapr F).
    Qed.

  End mbindr_special_cases.

  (** ** Interaction between [decorate] and [ret], [mbindr], [bind] *)
  (******************************************************************************)
  Section decorate_bind.

    Context
      F `{DecoratedModule W F T}.

    Theorem dec_mret : forall A k,
        decorate (T k) ∘ mret T k = mret T k ∘ pair Ƶ (B:=A).
    Proof.
      introv. ext a. now rewrite (dmmon_mret W T).
    Qed.

    Theorem dec_mbindr : forall A B (f : forall k, W * A -> T k B),
        decorate F ∘ mbindr F f =
        mbindr F (fun k => shift ∘ cobind (prod W) (decorate (T k) ∘ f k)).
    Proof.
      introv. unfold mbindr.
      reassociate <- on left.
      rewrite (drmod_mbind W F T).
      reassociate -> on left.
      rewrite (decf_read_read W).
      reassociate <- on left.
      rewrite (mbind_mfmap F).
      reflexivity.
    Qed.

    Corollary dec_mbind : forall A B (f : forall k, W * A -> T k B) ,
        decorate F ∘ mbind F f =
        mbindr F (fun k => shift ∘ fmap (prod W) (decorate (T k) ∘ f k)).
    Proof.
      introv. rewrite (mbind_to_mbindr F).
      rewrite dec_mbindr. fequal. ext k [? [? ?]].
      unfold compose. easy.
    Qed.

  End decorate_bind.

  (** ** Identity and composition laws for [mbindr] *)
  (******************************************************************************)
  Section id_composition_mbindr.

    Context
      F `{DecoratedModule W F T}.

    Theorem mbindr_id {A} :
      mbindr F (mret T ◻ const snd) = @id (F A).
    Proof.
      introv. unfold mbindr.
      rewrite <- (mbind_mfmap F).
      reassociate -> on left.
      rewrite (decf_read_proj W).
      now rewrite (rmod_mret F T).
    Qed.

    Theorem mbindr_mbindr {A B C} : forall (g : W * B ~k~> T C) (f : W * A ~k~> T B),
        mbindr F g ∘ mbindr F f = mbindr F (g ∗mr f).
    Proof.
      introv. unfold mbindr at 1.
      reassociate -> on left.
      rewrite (dec_mbindr F).
      unfold mbindr.
      reassociate <- on left.
      now rewrite (rmod_mbind_mbind F T).
    Qed.

  End id_composition_mbindr.

  (** *** Utility lemmas for composition laws *)
  (******************************************************************************)
  Section composition_utility.

    Context
      F `{DecoratedModule W F T}.

    (** TODO: Document why this is an important lemma *)
    Lemma mkcompr_1 : forall A B (f : W * A -> B) k,
        shift ∘ cobind (prod W) (decorate (T k) ∘ (mret T k ∘ f)) = mret T k ∘ cobind (prod W) f.
    Proof.
      introv.
      reassociate <- on left.
      rewrite (dmmon_mret W T).
      ext [? ?]. unfold compose; cbn.
      compose near (Ƶ, f (w, a)).
      rewrite (naturality (Natural := Natural_mret)).
      unfold compose; cbn.
      now rewrite (monoid_id_l).
    Qed.

    Corollary mbind_strength {M X Y} : forall (g : M * X ~k~> T Y),
        mbind F g ∘ strength = fun '(w, t) => mbind F (fun k a => g k (w, a)) t.
    Proof.
      introv. unfold strength. ext [? t].
      unfold compose; cbn. compose near t on left.
      now rewrite (mbind_mfmap F).
    Qed.

    Corollary mbind_strength_T {M X Y k} : forall (g : M * X ~k~> T Y),
        mbind (T k) g ∘ strength = fun '(w, t) => mbind (T k) (fun k a => g k (w, a)) t.
    Proof.
      introv. unfold strength. ext [? t].
      unfold compose; cbn. compose near t on left.
      assert (RightModule (T k) T) by apply Module_MMonad.
      now rewrite (mbind_mfmap (T k)).
    Qed.

    Corollary mbindr_shift {A B} : forall (g : W * A ~k~> T B),
        mbind F g ∘ shift = fun '(w, t) => mbind F (fun k '(w', a) => g k (w ● w', a)) t.
    Proof.
      introv. rewrite shift_spec.
      reassociate <- on left.
      rewrite (mbind_mfmap F).
      rewrite mbind_strength.
      ext [? ?]. fequal. now ext k [? ?].
    Qed.

    Lemma mkcompr_discard {A B} : forall k (f : W * A -> T k B),
        mfmap (T k) (const snd) ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f) = f.
    Proof.
      intros k ?.
      assert (RightModule (T k) T) by apply Module_MMonad.
      rewrite shift_discard.
      reassociate -> on left.
      rewrite cobind_discard.
      reassociate <- on left.
      now rewrite (dmmon_read_proj W T).
    Qed.

  End composition_utility.

  (** *** Composition laws in special cases *)
  (******************************************************************************)
  Section composition_misc_mbindr.

    Context
      F `{DecoratedModule W F T}.

    Corollary mbindr_mbind {A B C} : forall (g : W * B ~k~> T C) (f : A ~k~> T B),
        mbindr F g ∘ mbind F f = mbindr F (g ∗mr (fun k => f k ∘ snd)).
    Proof.
      introv. rewrite (mbind_to_mbindr F).
      now rewrite (mbindr_mbindr F).
    Qed.

    Corollary mbindr_mfmapr {A B C} : forall (g : forall k, W * B -> T k C) (f : W * A -k-> B),
        mbindr F g ∘ mfmapr F f =
        mbindr F (fun k '(w, a) => g k (w, f k (w, a))).
    Proof.
      introv. unfold mbindr, mfmapr.
      reassociate -> on left.
      reassociate <- near (decorate (A:=B) F).
      rewrite <- (naturality (η := @decorate W F _)).
      reassociate <- on left.
      unfold_mfmap @Mfmap_comp_Fmap.
      reassociate <- on left.
      rewrite (mbind_mfmap F).
      reassociate -> on left.
      rewrite (drmod_read_read W F T).
      reassociate <- on left.
      rewrite (mbind_mfmap F).
      do 2 fequal. now ext k [? ?].
    Qed.

    Corollary mbindr_mfmap {A B C} : forall (g : W * B ~k~> T C) (f : A -k-> B),
        mbindr F g ∘ mfmap F f =
        mbindr F (fun k '(w, a) => g k (w, f k a)).
    Proof.
      introv. rewrite (mfmap_to_mfmapr F).
      now rewrite mbindr_mfmapr.
    Qed.

    Corollary mbind_mfmapr {A B C} : forall (g : forall k, B -> T k C) (f : W * A -k-> B),
        mbind F g ∘ mfmapr F f =
        mbindr F (fun k '(w, a) => g k (f k (w, a))).
    Proof.
      introv. rewrite (mbind_to_mbindr F).
      now rewrite mbindr_mfmapr.
    Qed.

    Corollary mbind_mbindr {A B C} : forall (g : B ~k~> T C) (f : W * A ~k~> T B),
        mbind F g ∘ mbindr F f = mbindr F (g ∗m f).
    Proof.
      intros g f.
      rewrite (mbind_to_mbindr F).
      rewrite (mbindr_mbindr F).
      f_equal. ext k [w a].
      unfold mkcompr.
      assert (RightModule (T k) T) by apply Module_MMonad.
      rewrite <- (mbind_mfmap (T k)).
      reassociate <- on left.
      (* this next reassociation is difficult to achieve with current tactic support *)
      change left ((mbind (T k) g ∘
                         (mfmap (T k) (const snd) ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f k))) (w, a)).
      now rewrite (mkcompr_discard F).
    Qed.

    Corollary mfmapr_mbindr {A B C} : forall (g : W * B -k-> C) (f : W * A ~k~> T B),
        mfmapr F g ∘ mbindr F f = mbindr F ((fun k => mret T k ∘ g k) ∗mr f).
    Proof.
      introv. rewrite (mfmapr_to_mbindr).
      now rewrite (mbindr_mbindr F).
    Qed.

    Corollary mfmap_mbindr {A B C} : forall (g : B -k-> C) (f : W * A ~k~> T B),
        mfmap F g ∘ mbindr F f = mbindr F (fun k => mfmap (T k) g ∘ f k).
    Proof.
      introv. unfold_mfmap @Mfmap_rmod.
      now rewrite (mbind_mbindr).
    Qed.

  (** Composition with [ret] *)
  Lemma mbindr_comp_mret {A B} : forall (f : forall k, W * A -> T k B) k,
      mbindr (T k) f ∘ mret T k = f k ∘ pair Ƶ.
  Proof.
    introv. unfold mbindr.
    reassociate -> on left.
    rewrite (dmmon_mret W T).
    reassociate <- on left.
    now rewrite (mmon_mbind_comp_mret T).
  Qed.

  End composition_misc_mbindr.

  (** ** Kleisli composition for [mbindr] *)
  (******************************************************************************)
  Section kleisli_mbindr.

    Context
      F `{DecoratedModule W F T}
      {A B C D : Type}.

    Theorem kcompr_id_l : forall f : W * A ~k~> T B,
        (fun k => mret T k ∘ snd) ∗mr f = f.
    Proof.
      introv. unfold mkcompr. ext k.
      assert (RightModule (T k) T) by apply Module_MMonad.
      change ((fun k => mret T k ∘ snd)) with ((fun k => mret T k ∘ const (@snd W B) k)).
      rewrite <- (mbind_mfmap (T k)).
      change left (mbind (T k) (mret T) ∘
                        (mfmap (T k) (const snd) ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f k))).
      rewrite (mkcompr_discard F).
      now rewrite (mmon_mbind_mret T).
    Qed.

    Theorem kcompr_id_r : forall f : W * A ~k~> T B,
        f ∗mr (fun k => mret T k ∘ snd) = f.
    Proof.
      introv. unfold mkcompr. ext k.
      rewrite (mkcompr_1 F).
      reassociate <- on left.
      rewrite (mmon_mbind_comp_mret T).
      now ext [? ?].
    Qed.

    Lemma kcompr_assoc :
      forall (f : W * A ~k~> T B)
        (g : W * B ~k~> T C)
        (h : W * C ~k~> T D),
      h ∗mr (g ∗mr f) = (h ∗mr g) ∗mr f.
    Proof.
      introv. unfold mkcompr. ext k.
    Admitted.

  End kleisli_mbindr.

End decorated_module_parallel_substitution.

(** * Targeted substitution in decorated modules, [bindkr] *)
(******************************************************************************)

(** ** Operations [bindkr] and [kcomprk] *)
(******************************************************************************)
(** Build a k-substitution that targets only the leaves belonging to a partition
    [k]. This must be restricted to morphisms that do not change the leaf type. *)
#[program] Definition btgr `{Index} T `{! Mreturn T} {W A} (k : K) (f : W * A -> T k A) :
  forall k, W * A -> T k A := btgd T k f (fun k' => mret T k' ∘ snd).

Definition bindkr `{Index} F {W A} `{! Mreturn T} `{! Mbind F T}
           `{Decorate W F} (k : K) (f : W * A -> T k A) : F A -> F A
  := mbindr F (btgr T k f).

Definition kcompkr `{Index} {A W} `{Monoid_op W}
           `{forall k, Decorate W (T k)} `{! Mreturn T} `{! forall k, Mbind (T k) T}
           (k : K)
           (g : W * A -> T k A)
           (f : W * A -> T k A) : W * A -> T k A
  := mbind (T k) (btgr T k g) ∘ shift ∘ cobind (prod W) (decorate (T k) ∘ f).

Lemma btgr_eq `{Index} `{! Mreturn T} {A W} (k : K) (f : W * A -> T k A) : btgr T k f k = f.
Proof.
  unfold btgr. now rewrite btgd_eq.
Qed.

Lemma btgr_neq `{Index} `{! Mreturn T} {A W} (k k' : K) (p : k <> k') (f : W * A -> T k A) :
  btgr T k f k' = mret T k' ∘ snd.
Proof.
  unfold btgr. now rewrite btgd_neq.
Qed.

Hint Rewrite @btgr_eq : tea_tgt.
Hint Rewrite @btgr_eq : tea_tgt_eq.
Hint Rewrite @btgr_neq using auto : tea_tgt.
Hint Rewrite @btgr_neq using auto : tea_tgt_neq.

Theorem kcompkr_spec `{DecoratedModule W F T} A k
        (g : W * A -> T k A) (f : W * A -> T k A) :
  kcompkr k g f =
  fun '(w, a) => (bindkr (T k) k (fun '(w', a) => g (w ● w', a)) ∘ f) (w, a).
Proof.
  intros. unfold kcompkr. ext [w a].
  unfold bindkr, mbindr, compose, shift; cbn.
  compose near (decorate (T k) (f (w, a))) on left.
  assert (RightModule (T k) T) by apply Module_MMonad.
  rewrite (mbind_mfmap (T k)).
  unfold compose at 1; cbn.
  fequal. ext k' [? ?].
  compare values k and k'; now simpl_tgt_fallback.
Qed.

Section decorated_module_targeted_substitution.

  Context
    `{ix : Index}.

  Notation "g ∗kr f" := (kcompkr _ g f) (at level 60).
  Notation "g ∗mr f" := (mkcompr _ g f) (at level 60).

  (** ** Operations [mbindr] and [kcompr] *)
  (******************************************************************************)
  Context
    (F : Type -> Type)
    `{DecoratedModule (ix:=ix) W F T}.

  Lemma btgr_btgr_eq {A} (k : K) (g f : W * A -> T k A) :
    btgr T k (g ∗kr f) = btgr T k g ∗mr btgr T k f.
  Proof.
    ext k'. destruct_eq_args k k'.
    - rewrite btgr_eq. unfold mkcompr.
      now rewrite btgr_eq.
    - rewrite btgr_neq; auto. unfold mkcompr.
      rewrite btgr_neq; auto.
      rewrite (mkcompr_1 F). reassociate <- on right.
      rewrite (mmon_mbind_comp_mret T).
      rewrite btgr_neq; auto.
      now ext [? ?].
  Qed.

  (** ** Special cases [fmapk], [fmapkr], [bindk] of [bindkr] *)
  (******************************************************************************)
  Lemma bindk_to_bindkr {A} : forall (k : K) (f : A -> T k A),
      bindk F k f = (bindkr F k (f ∘ snd) : F A -> F A).
  Proof.
    intros k ?. unfold bindk, bindkr.
    rewrite (mbind_to_mbindr F). fequal; ext k' [? ?].
    unfold compose; cbn. destruct_eq_args k k'.
    all: now autorewrite* with tea_tgt.
  Qed.

  Lemma fmapk_to_bindkr {A} : forall (k : K) (f : A -> A),
      fmapk F k f = (bindkr F k (mret T k ∘ f ∘ snd) : F A -> F A).
  Proof.
    introv. rewrite fmapk_to_bindk.
    now rewrite bindk_to_bindkr.
  Qed.

  Lemma fmapkr_to_bindkr {A} : forall (k : K) (f : W * A -> A),
      fmapkr F k f = (bindkr F k (mret T k ∘ f) : F A -> F A).
  Proof.
    intros k ?. unfold fmapkr, mfmapr, bindkr, mbindr.
    unfold_mfmap @Mfmap_rmod. do 2 f_equal.
    ext k'. destruct_eq_args k k'.
    all: now autorewrite* with tea_tgt.
  Qed.

  (** ** Interaction between [decorate] and [bindkr] *)
  (******************************************************************************)
  Lemma dec_bindkr {k A} : forall (f : W * A -> T k A),
      decorate F ∘ bindkr F k f =
      mbindr F (btgd T k (shift ∘ cobind (prod W) (decorate (T k) ∘ f)) (fun k => mret T k)).
  Proof.
    intros f. unfold bindkr. rewrite (dec_mbindr F).
    fequal. ext k'. destruct_eq_args k k'.
    - now autorewrite* with tea_tgt.
    - autorewrite* with tea_tgt.
      rewrite (mkcompr_1 F). now ext [? ?].
  Qed.

  (** ** Kleisli composition for [bindkr] *)
  (******************************************************************************)
  Theorem kcompkr_id_l {k A} : forall f : W * A -> T k A,
      (mret T k ∘ snd) ∗kr f = f.
  Proof.
    introv. unfold kcompkr.
    unfold btgr.
    change (btgd T k (mret T k ∘ snd) (fun k0 : K => mret T k0 ∘ snd))
      with (btgd T k (((fun k0 : K => mret T k0 ∘ @snd W A) k)) (fun k0 : K => mret T k0 ∘ snd)).
    rewrite btgd_same.
    assert (RightModule (T k) T) by apply Module_MMonad.
    rewrite <- (mbind_mfmap (T k)).
    change (fun _ => snd) with (@const K _ (@snd W A)).
    rewrite (mmon_mbind_mret T).
    now rewrite <- (mkcompr_discard F).
  Qed.

  Theorem kcompkr_id_r {k A} : forall f : W * A -> T k A,
      f ∗kr (mret T k ∘ snd) = f.
  Proof.
    introv. unfold kcompkr.
    reassociate -> on left.
    rewrite (mkcompr_1 F).
    reassociate <- on left.
    rewrite (mmon_mbind_comp_mret T).
    ext [? ?]. now rewrite btgr_eq.
  Qed.

  Theorem bindkr_id : forall {A k},
      bindkr F k (mret T k ∘ snd) = @id (F A).
  Proof.
    intros A k. unfold bindkr.
    replace (btgr T k (mret T k ∘ snd))
      with (fun k : K => mret T k ∘ const (@snd W A) k).
    { apply (mbindr_id F). }
    ext k'. destruct_eq_args k k'.
    all: now autorewrite* with tea_tgt.
  Qed.

  Theorem bindkr_bindkr_eq : forall A k (g : W * A -> T k A) (f :  W * A -> T k A),
      bindkr F k g ∘ bindkr F k f =
      bindkr F k (g ∗kr f).
  Proof.
    introv. unfold bindkr.
    rewrite (mbindr_mbindr F).
    now rewrite (btgr_btgr_eq).
  Qed.

  (** *** Composition laws in special cases *)
  (******************************************************************************)
  Corollary bindkr_bindk {A} : forall k (g : W * A -> T k A) (f : A -> T k A),
      bindkr F k g ∘ bindk F k f = bindkr F k (g ∗kr f ∘ snd).
  Proof.
    introv. rewrite bindk_to_bindkr.
    now rewrite bindkr_bindkr_eq.
  Qed.

  Corollary bindkr_fmapkr {A} : forall k (g : W * A -> T k A) (f : W * A -> A),
      bindkr F k g ∘ fmapkr F k f =
      bindkr F k (g ∘ cobind (prod W) f).
  Proof.
    introv. rewrite fmapkr_to_bindkr.
    rewrite bindkr_bindkr_eq. f_equal.
    unfold kcompkr. reassociate -> on left.
    rewrite (mkcompr_1 F).
    reassociate <- on left.
    rewrite (mmon_mbind_comp_mret T).
    now rewrite btgr_eq.
  Qed.

  Corollary bindkr_fmapk {A} : forall k (g : W * A -> T k A) (f : A -> A),
      bindkr F k g ∘ fmapk F k f =
      bindkr F k (g ∘ map_snd f).
  Proof.
    introv. rewrite (fmapk_to_fmapkr F).
    rewrite bindkr_fmapkr.
    fequal. ext [? ?]. easy.
  Qed.

  Corollary bindk_bindkr {A} : forall k (g : A -> T k A) (f : W * A -> T k A),
      bindk F k g ∘ bindkr F k f =
      bindkr F k (bindk (T k) k g ∘ f).
  Proof.
    intros k ? ?. unfold bindkr, mbindr, bindk.
    reassociate <- on left.
    rewrite (mbind_mbind F).
    do 2 f_equal. ext k' [? a]. compare values k and k'.
    - unfold mkcomp, compose. now simpl_tgt_fallback.
    - unfold mkcomp, compose. simpl_tgt_fallback.
      unfold compose; cbn.
      compose near a on left.
      rewrite (mmon_mbind_comp_mret T).
      now simpl_tgt_fallback.
  Qed.

  Corollary fmapkr_bindkr {A} : forall k (g : W * A -> A) (f : W * A -> T k A),
      fmapkr F k g ∘ bindkr F k f =
      bindkr F k (mret T k ∘ g ∗kr f).
  Proof.
    intros. rewrite fmapkr_to_bindkr.
    now rewrite bindkr_bindkr_eq.
  Qed.

  Corollary fmapk_bindkr {A} : forall k (g : A -> A) (f : W * A -> T k A),
      fmapk F k g ∘ bindkr F k f =
      bindkr F k (fmapk (T k) k g ∘ f).
  Proof.
    introv. unfold bindkr, fmapk. rewrite (mfmap_mbindr F).
    fequal. ext j. compare values k and j.
    - now simpl_tgt_fallback.
    - simpl_tgt_fallback.
      reassociate <- on left. rewrite (Natural_mret).
      fequal. unfold mfmap, Mfmap_id_k.
      now simpl_tgt_fallback.
  Qed.

  Corollary bindk_fmapkr {A} : forall k (g : A -> T k A) (f : W * A -> A),
      bindk F k g ∘ fmapkr F k f =
      bindkr F k (g ∘ f).
  Proof.
    introv. rewrite bindk_to_bindkr.
    rewrite bindkr_fmapkr.
    reassociate -> on left.
    do 2 f_equal. now rewrite cobind_discard.
  Qed.

  Lemma bindkr_comp_mret_eq {A} : forall k (f : W * A -> T k A) (a : A),
      bindkr (T k) k f (mret T k a) = f (Ƶ, a).
  Proof.
    introv. unfold bindkr.
    compose near a. rewrite (mbindr_comp_mret F).
    now simpl_tgt.
  Qed.

  Lemma bindkr_comp_mret_neq {A} : forall k1 k2 (f : W * A -> T k2 A) (a : A),
      k1 <> k2 ->
      bindkr (T k1) k2 f (mret T k1 a) = mret T k1 a.
  Proof.
    introv neq. unfold bindkr.
    compose near a on left. rewrite (mbindr_comp_mret F).
    now simpl_tgt.
  Qed.

End decorated_module_targeted_substitution.

(** ** Rewrite Hint registration *)
Hint Rewrite @btgr_eq : tea_tgt.
Hint Rewrite @btgr_eq : tea_tgt_eq.
Hint Rewrite @btgr_neq using auto : tea_tgt.
Hint Rewrite @btgr_neq using auto : tea_tgt_neq.

Module Notations.
  Notation "g ∗mr f" := (mkcompr _ g f) (at level 60) : tealeaves_multi_scope.
  Notation "g ∗kr f" := (kcompkr _ g f) (at level 60) : tealeaves_multi_scope.
End Notations.
