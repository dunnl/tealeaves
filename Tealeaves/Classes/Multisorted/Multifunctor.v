From Tealeaves Require Export
  Classes.Functor
  Functors.Writer.
From Tealeaves.Categories Require Export
  TypeFamily.

Import Product.Notations.
Import TypeFamily.Notations.

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

    Class MMap : Type :=
      mmap : forall {A B}, (A -k-> B) -> F A -> F B.

  End MultisortedFunctor_operation.

  Section Multifunctor.

    Context
      (F : Type -> Type)
      `{MMap F}.

    Class MultisortedFunctor :=
      { mfun_mmap_id :
          `(mmap F kid = @id (F A));
        mfun_mmap_mmap : forall `(f : A -k-> B) `(g : B -k-> C),
            mmap F g ∘ mmap F f = mmap F (g ⊙ f);
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
        mmap G f ∘ η A = η B ∘ mmap F f.

  End MultisortedNatural.

  (** ** Identity multisorted functors at some <<k : K>> *)
  (** For each <<k : K>> one obtains a K-sorted functor whose object
        map is the identity operation and whose <<mmap>> treats
        values <<a : A>> as if tagged by <<k : K>>. *)
  (******************************************************************************)
  Section MultisortedFunctor_identity.

    Context
      (k : K).

    #[global] Instance MMap_I_k : MMap (fun A => A) :=
      fun `(f : A -k-> B) => f k.

    #[global, program] Instance MultisortedFunctor_I_k :
      @MultisortedFunctor (fun A => A) MMap_I_k.

  End MultisortedFunctor_identity.

  (** ** Composition with ordinary functors *)
  (******************************************************************************)
  #[global] Instance MMap_compose_Map
   `{MMap F2} `{Map F1} : MMap (F2 ∘ F1) :=
    fun A B f => mmap F2 (fun (k : K) (a : F1 A) => map (F := F1) (f k) a).

  Section MultisortedFunctor_compose_Functor.

    Context
      `{MultisortedFunctor F} `{Functor G}.

    Lemma mmap_id_compose_map : forall (A : Type),
        mmap (F ∘ G) kid = @id (F (G A)).
    Proof.
      intros. ext x. cbv in x.
      unfold_ops @MMap_compose_Map.
      change (fun (k : K) (a : G A) => map (F := G) (kid k) a)
        with (fun (_ : K) (a : G A) => map (F := G) id a).
      now rewrite (fun_map_id), (mfun_mmap_id F).
    Qed.

    Lemma mmap_mmap_compose_map : forall `(f : A -k-> B) `(g : B -k-> C),
        mmap (F ∘ G) g ∘ mmap (F ∘ G) f = mmap (F ∘ G) (g ⊙ f).
    Proof.
      introv. ext t. unfold compose. unfold_ops @MMap_compose_Map.
      compose near t on left. rewrite (mfun_mmap_mmap F).
      fequal. ext k x. unfold Category.comp, kconst_comp, compose.
      compose near x on left. now rewrite (fun_map_map).
    Qed.

    #[global] Instance MultisortedFunctor_compose_Functor :
      MultisortedFunctor (F ∘ G) :=
      {| mfun_mmap_id := mmap_id_compose_map;
         mfun_mmap_mmap := @mmap_mmap_compose_map;
      |}.

  End MultisortedFunctor_compose_Functor.

  (** ** Tensorial strength *)
  (******************************************************************************)
  Section tensorial_strength.

    Context
      (F : Type -> Type)
      `{MultisortedFunctor F}.

    Definition mstrength {B A} : B * F A -> F (B * A) :=
      fun '(b, x) => mmap F (fun k => pair b) x.

    Lemma strength_extract {W : Type} {A : Type} :
      mmap F (const (extract (W := (W ×)))) ∘ mstrength (B:=W) (A:=A) =
      extract (W := (W ×)) (A := F A).
    Proof.
      unfold mstrength. ext [w t].
      unfold compose; cbn. compose near t on left.
      now rewrite (mfun_mmap_mmap F), (mfun_mmap_id F).
    Qed.

  End tensorial_strength.

  (** * Single-sorted maps, [mapk] *)
  (******************************************************************************)

  (** ** Identity and composition laws for [mapk] *)
  (******************************************************************************)
  Definition mapk {A} F `{! MMap F} : K -> (A -> A) -> F A -> F A :=
    fun k f => mmap F (tgt k f).

  Context
    (F : Type -> Type)
    `{MultisortedFunctor F}.

  Lemma mapk_id k : forall A,
      mapk F k id = @id (F A).
  Proof.
    introv. unfold mapk.
    now rewrite tgt_id, (mfun_mmap_id F).
  Qed.

  Lemma mapk_mapk_eq : forall k `(f : A -> A) `(g : A -> A),
      mapk F k g ∘ mapk F k f = mapk F k (g ∘ f).
  Proof.
    introv. unfold mapk.
    now rewrite (mfun_mmap_mmap F), tgt_tgt_eq.
  Qed.

  Lemma mapk_mapk_neq : forall k1 k2 `(f : A -> A) `(g : A -> A),
      k1 <> k2 -> mapk F k2 g ∘ mapk F k1 f = mapk F k1 f ∘ mapk F k2 g.
  Proof.
    introv p. unfold mapk. rewrite 2(mfun_mmap_mmap F).
    rewrite tgt_tgt_neq; auto.
  Qed.

End assume_some_index_type.
