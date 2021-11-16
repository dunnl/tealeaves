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

(** * The <<shift>> operation *)
(******************************************************************************)
Section shift.

  Context
    {W : Type}
    `{MultisortedFunctor F}
    `{Monoid W}.

  Definition shift {A} : W * F (W * A) -> F (W * A) :=
    fun '(w, t) => mfmap F (fun k '(w', a) => (w ● w',  a)) t.

  Definition shift_spec : forall (A : Type),
      shift (A:=A) = mfmap F (fun k => join (W ×)) ∘ multistrength F.
  Proof.
    intros. ext [w t].
    unfold shift, join, Join_writer, compose.
    cbn. compose near t on right.
    rewrite (mfun_mfmap_mfmap F). fequal.
    ext k [w' a]. cbn. reflexivity.
  Qed.

  Lemma shift_extract {A} :
    mfmap F (const (extract (W ×))) ∘ shift (A:=A) = mfmap F (const (extract (W ×))) ∘ extract (W ×).
  Proof.
    ext [w t]. unfold shift, compose. cbn.
    compose near t on left.
    rewrite (mfun_mfmap_mfmap F). fequal.
    now ext k [? ?].
  Qed.

End shift.

(** * Multisorted decorated functors *)
(******************************************************************************)
Section typeclasses.

  Context
    `{ix : Index}.

  (** ** Decorated functors *)
  (******************************************************************************)
  Section MultisortedDecoratedFunctor_operation.

    Context
      (W : Type)
      (F : Type -> Type).

    Class Decorate :=
      decorate : F ⇒ (F ○ (W ×)).

  End MultisortedDecoratedFunctor_operation.

  Section MultisortedDecoratedFunctor.

    Context
      (W : Type)
      (F : Type -> Type)
      `{Decorate W F}
      `{MFmap (ix:=ix) F}.

    Class DecoratedMultisortedFunctor :=
      { decf_functor :> MultisortedFunctor F;
        decf_natural :> MultisortedNatural (@decorate W F _);
        decf_dec_dec : forall {A},
            decorate W F (W * A) ∘ decorate W F A =
            mfmap F (const (cojoin (W ×))) ∘ decorate W F A;
        decf_dec_extract : forall {A},
            mfmap F (const (extract (W ×))) ∘ decorate W F A = @id (F A);
      }.

  End MultisortedDecoratedFunctor.

  #[global] Arguments decorate {W} F%function_scope {Decorate} {A}%type_scope.

  Class DecoratedTransformation
        {W : Type}
        {F G : Type -> Type}
        `{MFmap (ix:=ix) F} `{Decorate W F}
        `{MFmap (ix:=ix) G} `{Decorate W G}
        (η : F ⇒ G) :=
    { dectrans_natural : MultisortedNatural η;
      dectrans_commute : forall A,
          η (W * A) ∘ decorate F = decorate G ∘ η A;
    }.

End typeclasses.

(** * Context-sensitive parallel maps, [mfmapd] *)
(******************************************************************************)
Definition mfmapd F {A B} `{MFmap F} `{Decorate W F}
           (f : W * A -k-> B) : F A -> F B := mfmap F f ∘ decorate F.

Section decorated_functor_parallel.

  Context
    {W : Type}
    (F : Type -> Type)
    `{DecoratedMultisortedFunctor W F}.

  (** ** [fmap] as a special case *)
  (******************************************************************************)
  Lemma mfmap_to_mfmapd {A B} (f : K -> A -> B) :
    mfmap F f = mfmapd F (f ⊙ const snd).
  Proof.
    unfold mfmapd. rewrite <- (mfun_mfmap_mfmap F).
    reassociate -> on right. now rewrite (decf_dec_extract W).
  Qed.

  (** ** Interaction between [dec] and [mfmapd] *)
  (******************************************************************************)
  Theorem dec_mfmapd {A B}: forall (f : W * A -k-> B),
      decorate F ∘ mfmapd F f = mfmapd F (cobind (prod W) ∘ f).
  Proof.
    introv. unfold mfmapd.
    reassociate <- on left.
    rewrite <- (mnaturality (η := @decorate W F _)).
    reassociate -> on left.
    rewrite (decf_dec_dec W F).
    reassociate <- on left.
    unfold_ops @MFmap_compose_Fmap. rewrite (mfun_mfmap_mfmap F).
    reflexivity.
  Qed.

  (** ** Composition and identity laws for [mfmapd] *)
  (******************************************************************************)
  Theorem mfmapd_id {A} :
    mfmapd F (const snd) = @id (F A).
  Proof.
    introv. unfold mfmapd.
    now rewrite (decf_dec_extract).
  Qed.

  Theorem mfmapd_mfmapd {A B C} : forall (g : W * B -k-> C) (f : W * A -k-> B),
      mfmapd F g ∘ mfmapd F f = mfmapd F (fun k => g k ∘ cobind (prod W) (f k)).
  Proof.
    introv. unfold mfmapd at 1.
    reassociate -> on left.
    rewrite (dec_mfmapd). unfold mfmapd.
    reassociate <- on left.
    now rewrite (mfun_mfmap_mfmap F).
  Qed.

  (** *** Corollaries *)
  (******************************************************************************)
  Corollary mfmap_mfmapd {A B C} : forall (g : B -k-> C) (f : W * A -k-> B),
      mfmap F g ∘ mfmapd F f = mfmapd F (fun k => g k ∘ f k).
  Proof.
    introv. rewrite (mfmap_to_mfmapd), (mfmapd_mfmapd).
    fequal. now ext k [? ?].
  Qed.

End decorated_functor_parallel.

(** * Context-sensitive targeted maps, [fmapkd] *)
(******************************************************************************)
Definition fmapkd F {A} `{MFmap F} `{Decorate W F} (k : K) (f : W * A -> A)
  : F A -> F A := mfmapd F (tgtd k f snd).

Section decorated_functor_targeted.

  Context
    {W : Type}
    (F : Type -> Type)
    `{DecoratedMultisortedFunctor W F}.

  (** ** [fmapk] as a special case of [fmapkd] *)
  (******************************************************************************)
  Lemma fmapk_to_fmapkd {A} k (f : A -> A) :
    fmapk F k f = fmapkd F k (f ∘ extract (prod W)).
  Proof.
    unfold fmapk, fmapkd, mfmapd. ext t.
    replace t with ((mfmap F (const snd) ∘ (decorate F)) t) at 1.
    2: now rewrite (decf_dec_extract W).
    compose near t on left.
    reassociate <- on left.
    rewrite (mfun_mfmap_mfmap F).
    do 2 fequal. ext k' [w a].
    unfold Classes.comp, kconst_comp.
    compare values k and k'; now simpl_tgt.
  Qed.

  (** ** Composition and identity laws for [fmapkd] *)
  (******************************************************************************)
  Theorem fmapkd_id {A} (k : K) :
    fmapkd F k snd = @id (F A).
  Proof.
    unfold fmapkd. simpl_tgt.
    now rewrite (mfmapd_id F).
  Qed.

  (** *** Composing sequential maps *)
  Theorem fmapkd_fmapkd_eq {A} (k : K) (f g : W * A -> A) :
    fmapkd F k g ∘ fmapkd F k f = fmapkd F k (g ∘ cobind (prod W) f).
  Proof.
    unfold fmapkd. rewrite (mfmapd_mfmapd F).
    fequal. ext k' [? ?].  destruct_eq_args k k'.
    all: now autorewrite with tea_tgt_eq tea_tgt_neq.
  Qed.

  (** *** Composing parallel maps *)
  Theorem fmapkd_fmapkd_neq {A} (k j : K) (f g : W * A -> A) :
    k <> j ->
    fmapkd F j g ∘ fmapkd F k f = fmapkd F k f ∘ fmapkd F j g.
  Proof with auto.
    intro. unfold fmapkd. do 2 rewrite (mfmapd_mfmapd F).
    fequal. ext k' [? ?]. compare values k and k'.
    - now simpl_tgt.
    - compare values j and k';
        now simpl_tgt_fallback.
  Qed.

  (** ** Other composition laws *)
  (******************************************************************************)
  Corollary fmapk_fmapkd_eq {A} (k : K) (g : A -> A) (f : W * A -> A) :
    fmapk F k g ∘ fmapkd F k f = fmapkd F k (g ∘ f).
  Proof.
    rewrite fmapk_to_fmapkd, fmapkd_fmapkd_eq.
    fequal. now ext [? ?].
  Qed.

  Corollary fmapk_fmapkd_neq {A} (k j : K) (g : A -> A) (f : W * A -> A) :
    k <> j ->
    fmapk F j g ∘ fmapkd F k f = fmapkd F k f ∘ fmapk F j g.
  Proof with auto.
    introv neq. rewrite fmapk_to_fmapkd, fmapkd_fmapkd_neq...
  Qed.

  (** ** Interaction between [decorate] and [fmapkd] *)
  (******************************************************************************)
  Lemma dec_fmapkd {A} : forall k (f : W * A -> A),
      decorate F ∘ fmapkd F k f = mfmapd F (tgt k (cobind (prod W) f)).
  Proof.
    intros k ?. unfold fmapkd. rewrite (dec_mfmapd F).
    fequal. ext k' [? ?]. unfold compose; cbn.
    compare values k and k'; now simpl_tgt.
  Qed.

End decorated_functor_targeted.
