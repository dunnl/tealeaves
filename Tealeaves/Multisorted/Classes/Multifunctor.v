From Tealeaves Require Export
  Classes.Functor
  Functors.Writer.
From Tealeaves.Categories Require Export
  TypeFamilies.

Import Product.Notations.
Import TypeFamilies.Notations.

#[local] Generalizable Variables A B C F G.

Section assume_some_index_type.

  Context
    `{ix : Index}.

  Implicit Type (k : K).

  (** * Multisorted functors *)
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

  (** ** Identity multisorted functors at some <<k : K>> *)
  (** For each <<k : K>> one obtains a K-sorted functor whose object
        map is the identity operation and whose <<mfmap>> treats
        values <<a : A>> as if tagged by <<k : K>>. *)
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
      fequal. ext k x. unfold Category.comp, kconst_comp, compose.
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

    Definition mstrength {B A} : B * F A -> F (B * A) :=
      fun '(b, x) => mfmap F (fun k => pair b) x.

    Lemma strength_extract {W : Type} {A : Type} :
      mfmap F (const (extract (W ×))) ∘ mstrength (B:=W) (A:=A) =
      extract (prod W) (A := F A).
    Proof.
      unfold mstrength. ext [w t].
      unfold compose; cbn. compose near t on left.
      now rewrite (mfun_mfmap_mfmap F), (mfun_mfmap_id F).
    Qed.

  End tensorial_strength.

  (** * Single-sorted maps, [fmapk] *)
  (******************************************************************************)

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
