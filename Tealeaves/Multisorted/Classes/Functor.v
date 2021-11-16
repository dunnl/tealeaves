From Tealeaves Require Export
     Util.Prelude
     Singlesorted.Functors.Writer (* for results about tensorial strength *)
     Singlesorted.Classes.Functor
     Multisorted.Category.

Import Product.Notations.
Import Multisorted.Category.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

Section assume_some_index_type.

  Context
    `{ix : Index}.

  Implicit Type (k : K).

  (** * K-partitioned functors *)
  (******************************************************************************)
  Section MultisortedFunctor_operation.

    Context
      (F : Type -> Type).

    Class MFmap : Type :=
      mfmap : forall {A B}, (A -k-> B) -> F A -> F B.

  End MultisortedFunctor_operation.

  Section Multifunctor.

    Context
      (F : Type -> Type)
      `{MFmap F}.

    Class MultisortedFunctor :=
      { mfun_mfmap_id :
          `(mfmap F kid = @id (F A));
        mfun_mfmap_mfmap : forall `(f : A -k-> B) `(g : B -k-> C),
            mfmap F g ∘ mfmap F f = mfmap F (g ⊙ f);
      }.

  End Multifunctor.

  (** ** Natural transformations *)
  (******************************************************************************)
  Section MultisortedNatural.

    Context
      `{MultisortedFunctor F}
      `{MultisortedFunctor G}.

    Class MultisortedNatural (η : F ⇒ G) :=
      mnaturality : forall {A B} (f : K -> A -> B),
        mfmap G f ∘ η A = η B ∘ mfmap F f.

  End MultisortedNatural.

  (** ** Identity functors at some <<k : K>> *)
  (** For each <<k : K>> one obtains a K-sorted functor whose object map is the
        identity operation and whose <<mfmap>> treats values <<a : A>> as if
        tagged by <<k : K>>. *)
  (******************************************************************************)
  Section MultisortedFunctor_identity.

    Context
      (k : K).

    #[global] Instance MFmap_I_k : MFmap (fun A => A) :=
      fun `(f : A -k-> B) => f k.

    #[global, program] Instance MultisortedFunctor_I_k :
      @MultisortedFunctor (fun A => A) MFmap_I_k.

  End MultisortedFunctor_identity.

  (** ** Composition with ordinary functors *)
  (******************************************************************************)
  #[global] Instance MFmap_compose_Fmap
   `{MFmap F2} `{Fmap F1} : MFmap (F2 ∘ F1) :=
    fun A B f => mfmap F2 (fun (k : K) (a : F1 A) => fmap F1 (f k) a).

  Section MultisortedFunctor_compose_Functor.

    Context
      `{MultisortedFunctor F} `{Functor G}.

    Lemma mfmap_id_compose_fmap : forall (A : Type),
        mfmap (F ∘ G) kid = @id (F (G A)).
    Proof.
      intros. ext x. cbv in x.
      unfold_ops @MFmap_compose_Fmap.
      change (fun (k : K) (a : G A) => fmap G (kid k) a)
        with (fun (_ : K) (a : G A) => fmap G id a).
      now rewrite (fun_fmap_id G), (mfun_mfmap_id F).
    Qed.

    Lemma mfmap_mfmap_compose_fmap : forall `(f : A -k-> B) `(g : B -k-> C),
        mfmap (F ∘ G) g ∘ mfmap (F ∘ G) f = mfmap (F ∘ G) (g ⊙ f).
    Proof.
      introv. ext t. unfold compose. unfold_ops @MFmap_compose_Fmap.
      compose near t on left. rewrite (mfun_mfmap_mfmap F).
      fequal. ext k x. unfold Classes.comp, kconst_comp, compose.
      compose near x on left. now rewrite (fun_fmap_fmap G).
    Qed.

    #[global] Instance MultisortedFunctor_compose_Functor :
      MultisortedFunctor (F ∘ G) :=
      {| mfun_mfmap_id := mfmap_id_compose_fmap;
         mfun_mfmap_mfmap := @mfmap_mfmap_compose_fmap;
      |}.

  End MultisortedFunctor_compose_Functor.

  (** ** Tensorial strength *)
  (******************************************************************************)
  Section tensorial_strength.

    Context
      (F : Type -> Type)
      `{MultisortedFunctor F}.

    Definition multistrength {B A} : B * F A -> F (B * A) :=
      fun '(b, x) => mfmap F (fun k => pair b) x.

    Lemma strength_discard {W : Type} {A : Type} :
      mfmap F (const (extract (W ×))) ∘ multistrength (B:=W) (A:=A) =
      extract (prod W) (A := F A).
    Proof.
      unfold multistrength. ext [w t].
      unfold compose; cbn. compose near t on left.
      now rewrite (mfun_mfmap_mfmap F), (mfun_mfmap_id F).
    Qed.

  End tensorial_strength.

  (** * Targeted maps, [fmapk] *)
  (******************************************************************************)

  (** ** Rewriting Hints for [tgt]-like combinators *)
  (******************************************************************************)
  (** We create some hint databases for rewriting expressions involving the
    "targeting" combinators defined in this section and elsewhere. These should
    typically be used with [autorewrite*] in order to ensure the correct lemmas
    are invoked (namely, those which do not raise side-conditions that cannot be
    solved, typically because a <<XXX_neq>> lemma has been chosen when
    <<XXX_eq>> is the right one). Due to a bug involving [autorewrite*] we also
    create smaller databases that are convenient to use with [autorewrite]
    (without the <<*>>), at the cost of verbosity. *)
  (** See #<a href="https://github.com/coq/coq/issues/14344">https://github.com/coq/coq/issues/14344</a>#,
   *)
  Create HintDb tea_tgt.
  Create HintDb tea_tgt_eq.
  Create HintDb tea_tgt_neq.

  (** ** Map-building combinators: [tgt], [tgtd] *)
  (** Build a k-morphism that targets only the leaves belonging to a partition
    [k]. This must be restricted to morphisms that do not change the leaf type
    because leaves of the other partitions are left unchanged. *)
  (******************************************************************************)
  Definition tgt {A} (k : K) (f : A -> A) : A -k-> A :=
    fun j => if k == j then f else id.

  Definition tgtd {A B} (k : K) (f def : A -> B) : A -k-> B :=
    fun j => if k == j then f else def.

  (** ** Lemmas for [tgt], [tgtd] *)
  (******************************************************************************)
  Lemma tgt_id {A} (k : K) :
    tgt k (@id A) = kid.
  Proof.
    unfold tgt. ext j. compare values k and j.
  Qed.

  Lemma tgt_tgt_eq {A} (k : K) (g f : A -> A) :
    tgt k (g ∘ f) = tgt k g ◻ tgt k f.
  Proof.
    unfold tgt. ext j. compare values k and j.
  Qed.

  Lemma tgt_tgt_neq {A} (k1 k2 : K) (g f : A -> A) :
    k1 <> k2 -> tgt k2 g ⊙ tgt k1 f = tgt k1 f ⊙ tgt k2 g.
  Proof.
    introv neq. unfold tgt. ext k.
    unfold Classes.comp, kconst_comp.
    compare k to both of {k1 k2}.
  Qed.

  Lemma tgt_eq {A} (k : K) (f : A -> A) : tgt k f k = f.
  Proof.
    unfold tgt. compare values k and k.
  Qed.

  Lemma tgt_neq {A} (k j : K) (p : k <> j) (f : A -> A) : tgt k f j = id.
  Proof.
    unfold tgt. compare values k and j.
  Qed.

  (** Build a k-morphism that targets only the leaves belonging to a partition
    [k]. A default function is applied to all other partitions, so in general
    the leaf types may change to some [B]. *)
  Lemma tgtd_eq {A B} (k : K) (f def : A -> B) : tgtd k f def k = f.
  Proof.
    unfold tgtd. compare values k and k.
  Qed.

  Lemma tgtd_neq {A B} (k j : K) (p : k <> j) (f def : A -> B) : tgtd k f def j = def.
  Proof.
    unfold tgtd. compare values k and j.
  Qed.

  Lemma tgtd_tgtd_eq {A B C} (k : K) (f def1 : A -> B) (g def2 : B -> C) :
    tgtd k (g ∘ f) (def2 ∘ def1) = tgtd k g def2 ◻ tgtd k f def1.
  Proof.
    unfold tgtd. ext j. compare values k and j.
  Qed.

  Lemma tgtd_tgtd_neq {A B C} (k1 k2 : K) (f def1 : A -> B) (g def2 : B -> C)  :
    k1 <> k2 ->
    tgtd k2 g def2 ◻ tgtd k1 f def1 =
    fun k => if k == k1 then def2 ∘ f else
            if k == k2 then g ∘ def1 else def2 ∘ def1.
  Proof.
    introv neq. unfold tgtd. ext k. compare k to both of {k1 k2}.
  Qed.

  Lemma tgtd_same {A B} (k : K) (f : A -> B) : tgtd k f f = const f.
  Proof.
    unfold tgtd. ext j. compare values k and j.
  Qed.

  (** ** Identity and composition laws for [fmapk] *)
  (******************************************************************************)
  Definition fmapk {A} F `{! MFmap F} : K -> (A -> A) -> F A -> F A :=
    fun k f => mfmap F (tgt k f).

  Context
    (F : Type -> Type)
    `{MultisortedFunctor F}.

  Lemma fmapk_id k : forall A,
      fmapk F k id = @id (F A).
  Proof.
    introv. unfold fmapk.
    now rewrite tgt_id, (mfun_mfmap_id F).
  Qed.

  Lemma fmapk_fmapk_eq : forall k `(f : A -> A) `(g : A -> A),
      fmapk F k g ∘ fmapk F k f = fmapk F k (g ∘ f).
  Proof.
    introv. unfold fmapk.
    now rewrite (mfun_mfmap_mfmap F), tgt_tgt_eq.
  Qed.

  Lemma fmapk_fmapk_neq : forall k1 k2 `(f : A -> A) `(g : A -> A),
      k1 <> k2 -> fmapk F k2 g ∘ fmapk F k1 f = fmapk F k1 f ∘ fmapk F k2 g.
  Proof.
    introv p. unfold fmapk. rewrite 2(mfun_mfmap_mfmap F).
    rewrite tgt_tgt_neq; auto.
  Qed.

End assume_some_index_type.

(** ** Automation support *)
Hint Rewrite @tgt_eq @tgtd_eq @tgtd_same : tea_tgt.
Hint Rewrite @tgt_eq @tgtd_eq @tgtd_same : tea_tgt_eq.
Hint Rewrite @tgt_neq @tgtd_neq using auto : tea_tgt.
Hint Rewrite @tgt_neq @tgtd_neq using auto : tea_tgt_neq.

(** <<autorewrite>>* seems to be bit by this bug:
      https://github.com/coq/coq/issues/14344 *)
Tactic Notation "simpl_tgt" := (autorewrite* with tea_tgt).
Tactic Notation "simpl_tgt" "in" hyp(H) := (autorewrite* with tea_tgt in H).
Tactic Notation "simpl_tgt" "in" "*" := (autorewrite* with tea_tgt in *).

Ltac simpl_tgt_fallback :=
  repeat first [ let n1:= numgoals in
          autorewrite with tea_tgt_neq;
          let n2:= numgoals in guard n1 = n2 |
          let n1:= numgoals in
          autorewrite with tea_tgt_eq;
          let n2:= numgoals in guard n1 = n2 ].

Ltac simpl_tgt_fallback_all :=
  repeat first [ let n1:= numgoals in
          autorewrite with tea_tgt_neq in *;
          let n2:= numgoals in guard n1 = n2 |
          let n1:= numgoals in
          autorewrite with tea_tgt_eq in *;
          let n2:= numgoals in guard n1 = n2 ].

Ltac simpl_tgt_fallback_in H :=
  repeat first [ let n1:= numgoals in
          autorewrite with tea_tgt_neq in H;
          let n2:= numgoals in guard n1 = n2 |
          let n1:= numgoals in
          autorewrite with tea_tgt_eq in H;
          let n2:= numgoals in guard n1 = n2 ].

Tactic Notation "simpl_tgt_fallback" "in" hyp(H) := (simpl_tgt_fallback_in H).
Tactic Notation "simpl_tgt_fallback" "in" "*" := (simpl_tgt_fallback_all).
