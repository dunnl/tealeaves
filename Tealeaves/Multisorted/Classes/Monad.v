From Tealeaves Require Export
     Singlesorted.Classes.Monad
     Multisorted.Classes.Functor.

(* to use [dependent destruction] for component-wise reasoning about [bind] *)
Require Import Coq.Program.Equality.

Import Multisorted.Category.Notations.
#[local] Open Scope tealeaves_multi_scope.

Section with_index.

  Context
    `{ix : Index}.

  (** * K-partitioned Monads *)
  (**************************************************************)
  Class Mreturn (G : K -> Type -> Type) : Type :=
    mret : forall {A}, A ~k~> G A.

  Class Mbind (F : Type -> Type) (G : K -> Type -> Type) : Type :=
    mbind : forall {A B : Type},  A ~k~> G B -> F A -> F B.

  #[global] Arguments mret G%function_scope {Mreturn} {A}%type_scope.

  #[global] Arguments mbind F%function_scope {G}%function_scope {Mbind}
   {A B}%type_scope (_)%tea_multi.

  (** ** Constant multisorted monads *)
  (******************************************************************************)
  Section ConstantMultisortedMonad.

    Context
      (T : Type -> Type)
      `{Mreturn (const T)}
      `{Mbind T (const T)}.

    Class ConstantMultisortedMonad : Prop :=
      { cmmon_mbind_mret : forall A,
          mbind T (mret (const T)) = @id (T A);
        cmmon_mbind_comp_mret : forall A B (f : K -> A -> T B) k,
            mbind T f ∘ mret (const T) k = f k;
        cmmon_mbind_mbind : forall A B C (f : K -> A -> T B) (g : K -> B -> T C),
            mbind T g ∘ mbind T f = mbind T (fun k => mbind T g ∘ f k);
      }.

  End ConstantMultisortedMonad.

  (** ** Multisorted monads *)
  (******************************************************************************)
  Section MultisortedMonad.

    Context
      (T : K -> Type -> Type)
      `{Mreturn T}
      `{forall k, Mbind (T k) T}.

    Class MultisortedMonad : Prop :=
      { mmon_mbind_mret :
          forall A k, mbind (T k) (mret T) = @id (T k A);
        mmon_mbind_comp_mret :
          forall A B (f : A ~k~> T B) k,
            mbind (T k) f ∘ mret T k (A:=A) = f k;
        mmon_mbind_mbind :
          forall A B C (f : A ~k~> T B) (g : B ~k~> T C) k,
            mbind (T k) g ∘ mbind (T k) f =
            mbind (T k) (fun k => mbind (T k) g ∘ f k);
      }.

  End MultisortedMonad.

  (** ** K-partitioned Modules *)
  (******************************************************************************)
  Section MultisortedModule.

    Context
      (F : Type -> Type)
      (T : K -> Type -> Type)
      `{Mbind F T}
      `{MultisortedMonad T}.

    Class MultisortedRightModule :=
      { rmod_monad :> MultisortedMonad T;
        rmod_mret : forall A,
            mbind F (mret T) = @id (F A);
        rmod_mbind_mbind : forall A B C (f : A ~k~> T B) (g : B ~k~> T C),
            mbind F g ∘ mbind F f = mbind F (fun k => mbind (T k) g ∘ f k);
      }.

  End MultisortedModule.

  (** ** ???? *)
  (******************************************************************************)
  Section monad_system_of_monad.

    Context
      `{ConstantMultisortedMonad T}.

    #[global] Instance CMM_MM : MultisortedMonad (const T) :=
      {| mmon_mbind_mret := fun A k => @cmmon_mbind_mret T _ _ _ A;
         mmon_mbind_mbind := fun A B C f g k => @cmmon_mbind_mbind T _ _ _ A B C f g;
         mmon_mbind_comp_mret := fun A B => @cmmon_mbind_comp_mret T _ _ _ A B;
      |}.

  End monad_system_of_monad.

  (** ** Every component of a partitioned monad system forms a module *)
  (******************************************************************************)
  Section MultisortedModule_monad_component.

    Context
      `{MultisortedMonad T}.

    Instance Module_MMonad (k : K) : MultisortedRightModule (T k) T :=
      {| rmod_mret := fun A => mmon_mbind_mret T _ k;
         rmod_mbind_mbind := fun A B C f g => mmon_mbind_mbind T A B C f g k;
      |}.

    Context
      `{ConstantMultisortedMonad U}.

    Instance Module_CMMonad : MultisortedRightModule U (const U) :=
      {| rmod_mret := cmmon_mbind_mret U;
         rmod_mbind_mbind := cmmon_mbind_mbind U;
      |}.

  End MultisortedModule_monad_component.

  (** ** The carrier of a module is a functor *)
  (******************************************************************************)
  Section MultisortedFunctor_module_carrier.

    #[global] Instance Mfmap_rmod `{Mreturn T} `{Mbind F T} : Mfmap F :=
      fun A B f => mbind F (mret T ◻ f).

    Context
      `{MultisortedRightModule F T}.

    Lemma fmap_id_rmod : forall A,
        mfmap F kid = @id (F A).
    Proof.
      introv. unfold_ops @Mfmap_rmod.
      unfold compose. now rewrite (rmod_mret F T).
    Qed.

    Lemma fmap_fmap_rmod : forall `(f : A -k-> B) `(g : B -k-> C),
        mfmap F g ∘ mfmap F f = mfmap F (g ⊙ f).
    Proof.
      introv. unfold_ops @Mfmap_rmod.
      rewrite (rmod_mbind_mbind F T).
      f_equal. ext k.
      reassociate <- on left.
      now rewrite (mmon_mbind_comp_mret T).
    Qed.

    #[global] Instance MFunctor_rmod : MultisortedFunctor F :=
      {| mfmap_id := @fmap_id_rmod;
         mfmap_mfmap := @fmap_fmap_rmod;
      |}.

  End MultisortedFunctor_module_carrier.

  (** ** [ret] is a natural transformation *)
  (******************************************************************************)
  Section naturality.

    Context
      `{MultisortedMonad T}.

    #[global] Instance Natural_mret {k} :
      Natural (fun A => @mret T _ A k) (H := Mfmap_id_k k).
    Proof.
      introv. unfold_ops @Mfmap_rmod.
      now rewrite (mmon_mbind_comp_mret T).
    Qed.

  End naturality.

  (** * Properties of right modules *)
  (******************************************************************************)


  (** ** Parallel substitution, [mbind] and [mkcomp] *)
  (******************************************************************************)
  Definition mkcomp  {A B C : Type} (T : K -> Type -> Type)
             `{forall k, Mbind (T k) T} `{Mreturn T}
             (g : B ~k~> T C) (f : forall k, A -> T k B)
    : forall k, A -> T k C := fun k => mbind (T k) g ∘ f k.

  #[local] Notation "g ⋆m f" := (mkcomp _ g f) (at level 60) : tealeaves_multi_scope.

  Section MultisortedModule_theory.

    Context
      (F : Type -> Type)
      `{MultisortedRightModule F T}.

    (** ** Identity and composition laws for [mbind] *)
    (******************************************************************************)
    (** The next two theorems state that the [mbind] operation represents the
      morphism part of a functor from the Kleisli category to the category of
      F-morphisms (i.e., arrows of the form [F A -> F B].)*)
    Theorem mbind_id : forall {A},
        mbind F (mret T) = @id (F A).
    Proof.
      exact (rmod_mret F T).
    Qed.

    Theorem mbind_mbind :
      forall A B C (g : B ~k~> T C) (f : A ~k~> T B),
        mbind F g ∘ mbind F f = mbind F (g ⋆m f).
    Proof.
      introv. now rewrite (rmod_mbind_mbind F T).
    Qed.

    Corollary mbind_mfmap {A B C} : forall (g : B ~k~> T C) (f : K -> A -> B),
        mbind F g ∘ mfmap F f = mbind F (fun k => g k ∘ f k).
    Proof.
      introv. unfold_ops @Mfmap_rmod.
      rewrite mbind_mbind. f_equal.
      unfold mkcomp. ext k.
      rewrite Prelude.compose_assoc.
      now rewrite (mmon_mbind_comp_mret T).
    Qed.

    Corollary mfmap_mbind {A B C} : forall (g : K -> B -> C) (f : A ~k~> T B),
        mfmap F g ∘ mbind F f = mbind F (fun k => mfmap (T k) g ∘ f k).
    Proof.
      introv. unfold_ops @Mfmap_rmod.
      now rewrite mbind_mbind.
    Qed.

    (** ** Kleisli laws for [mbind] *)
    (******************************************************************************)
    (** The next three theorems are the left and right identity laws and the
      associativity law for Kleisli composition. *)
    Theorem kcomp_id_l {A B} : forall f : A ~k~> T B,
        (fun k => mret T k) ⋆m f = f.
    Proof.
      introv. unfold mkcomp. ext k. now rewrite (mmon_mbind_mret T).
    Qed.

    Theorem kcomp_id_r {A B} : forall f : A ~k~> T B,
        f ⋆m (fun k => mret T k) = f.
    Proof.
      introv. unfold mkcomp. ext k. now rewrite (mmon_mbind_comp_mret T).
    Qed.

    Lemma kcomp_assoc :
      forall A B C D (h : C ~k~> T D)
        (g : B ~k~> T C) (f : A ~k~> T B),
        h ⋆m (g ⋆m f) = h ⋆m (g ⋆m f).
    Proof.
      reflexivity.
    Qed.

  End MultisortedModule_theory.

  (** * Targeted substitution, [bindk] and [kcompk] *)
  (******************************************************************************)

  (** ** Substitution-building combinators: [btg], [btgd]. *)
  (******************************************************************************)
  (** Build a k-substitution that targets only the leaves belonging to a partition
    [k]. This must be restricted to morphisms that do not change the leaf type. *)
  #[program] Definition btg T `{! Mreturn T} {A} (k : K) (f : A -> T k A) :
    A ~k~> T A := fun j => if k == j then f else mret T j.

  #[program] Definition btgd T `{! Mreturn T} {A B} (k : K) (f : A -> T k B)
   (def : A ~k~> T B) : A ~k~> T B :=
    fun j => if k == j then f else def j.

  (** ** Operations [bindk] and [kcompk] *)
  (******************************************************************************)
  Definition bindk F `{! Mbind F T} `{! Mreturn T} k {A} : (A -> T k A) -> F A -> F A :=
    fun f => mbind F (btg T k f).

  Definition kcompk {A} k `{forall k, Mbind (T k) T} `{! Mreturn T}
             (g : A -> T k A) (f : A -> T k A) :
    A -> T k A := bindk (T k) k g ∘ f.

  Notation "g ⋆k f" := (kcompk _ g f) (at level 60).

  (** ** Lemmas for [btg], [btgd] *)
  (******************************************************************************)
  Section btg_lemmas.

    Context
      (F : Type -> Type)
      `{MultisortedRightModule F T}.

    Lemma btg_eq {A} : forall k (f : A -> T k A),
        btg T k f k = f.
    Proof.
      introv. unfold btg. compare values k and k.
      dependent destruction DESTR_EQ.
      cbn. reflexivity.
    Qed.

    Lemma btg_neq {A} : forall {k j} (f : A -> T k A),
        k <> j -> btg T k f j = mret T j.
    Proof.
      introv. unfold btg. compare values k and j.
    Qed.

    Lemma btg_id {A} (k : K) :
      btg T k (mret T k) = mret T (A:=A).
    Proof.
      unfold btg. ext j. compare values k and j.
    Qed.

    Lemma btgd_eq {A B} (k : K) (f : A -> T k B) (def : A ~k~> T B) :
      btgd T k f def k = f.
    Proof.
      unfold btgd. compare values k and k. dependent destruction DESTR_EQ.
      cbn. reflexivity.
    Qed.

    Lemma btgd_neq  {A B} (k j : K) (p : k <> j) (f : A -> T k B)
          (def : A ~k~> T B) : btgd T k f def j = def j.
    Proof.
      unfold btgd. compare values k and j.
    Qed.

    Lemma btgd_same {A B} (k : K) (f : A ~k~> T B) :
      btgd T k (f k) f = f.
    Proof.
      unfold btgd. ext j. compare values k and j.
    Qed.

    Lemma btgd_mret {A} (k : K) (f : A -> T k A) :
      btgd T k f (mret T) = btg T k f.
    Proof.
      ext j. compare values k and j.
    Qed.

    (** *** Composing [btg] *)
    (******************************************************************************)
    Theorem btg_btg_eq {A} (k : K) (f g : A -> T k A) :
      (btg T k g ⋆m btg T k f) = (btg T k (g ⋆k f)).
    Proof.
      unfold mkcomp, kcompk. ext j. compare values k and j.
      - subst. now do 2 rewrite btg_eq.
      - do 2 (rewrite btg_neq; auto).
        rewrite (mmon_mbind_comp_mret T).
        now rewrite btg_neq.
    Qed.

    Theorem btg_btg_neq {A} (k j : K) (f : A -> T k A) (g : A -> T j A) :
      k <> j ->
      (forall a, mbind (T k) (btg T j g) (f a) = f a) ->
      (forall a, mbind (T j) (btg T k f) (g a) = g a) ->
      (btg T j g ⋆m btg T k f) =
      (btg T k f ⋆m btg T j g).
    Proof.
      intros neq hyp1 hyp2.
      unfold mkcomp, kcompk. ext i. compare i to both of {k j}.
      - rewrite btg_eq. rewrite btg_neq; [| assumption].
        rewrite (mmon_mbind_comp_mret T). rewrite btg_eq.
        ext a. unfold compose. now rewrite hyp1.
      - rewrite btg_eq. rewrite btg_neq; [| assumption].
        rewrite (mmon_mbind_comp_mret T). rewrite btg_eq.
        ext a. unfold compose. now rewrite hyp2.
      - rewrite btg_neq; [| assumption].
        rewrite btg_neq; [| assumption].
        rewrite (mmon_mbind_comp_mret T).
        rewrite (mmon_mbind_comp_mret T).
        rewrite btg_neq; [| assumption].
        rewrite btg_neq; [| assumption].
        trivial.
    Qed.

  End btg_lemmas.

  (** ** [fmapk] as a special case of [bindk] *)
  (******************************************************************************)
  Section bindk_lemmas.

    Context
      (F : Type -> Type)
      `{MultisortedRightModule F T}.

    Lemma fmapk_to_bindk {A} : forall (f : A -> A) k,
        fmapk F k f = bindk F k (mret T k ∘ f).
    Proof.
      intros. unfold fmapk, bindk.
      unfold_ops @Mfmap_rmod. fequal.
      ext j. destruct_eq_args k j.
      all : now repeat first
                [ rewrite tgt_eq | rewrite tgt_neq |
                  rewrite btg_eq | rewrite btg_neq ].
    Qed.

  End bindk_lemmas.

  (** ** Composition and identity laws for [bindk] *)
  (******************************************************************************)
  Section bindk_lemmas.

    Context
      (F : Type -> Type)
      `{MultisortedRightModule F T}.

    Lemma bindk_mret k {A} :
      bindk F k (mret T k) = @id (F A).
    Proof.
      introv. unfold bindk.
      rewrite btg_id.
      now rewrite (rmod_mret F T).
    Qed.

    Lemma bindk_comp_mret_eq k {A} : forall (f : A -> T k A),
        bindk (T k) k f ∘ mret T k = f.
    Proof.
      introv. unfold bindk.
      rewrite (mmon_mbind_comp_mret T).
      ext a. now rewrite btg_eq.
    Qed.

    Lemma bindk_comp_mret_neq k2 k1 {A} : forall (f : A -> T k2 A),
        k2 <> k1 ->
        bindk (T k1) k2 f ∘ mret T k1 = mret T k1.
    Proof.
      introv neq. unfold bindk.
      rewrite (mmon_mbind_comp_mret T).
      now rewrite btg_neq.
    Qed.

    Lemma bindk_bindk_eq k {A}: forall (f : A -> T k A) (g : A -> T k A),
        bindk F k g ∘ bindk F k f = bindk F k (g ⋆k f).
    Proof.
      intros. unfold bindk. rewrite (rmod_mbind_mbind F T).
      fequal. ext j a. unfold compose.
      destruct_eq_args k j.
      all: repeat first [rewrite btg_eq | rewrite btg_neq ]; auto.
      change left ((bindk (T j) k g ∘ mret T j) a).
      now rewrite bindk_comp_mret_neq.
    Qed.

    Theorem bindk_bindk_neq_simple {A} (k j : K) (f : A -> T k A) (g : A -> T j A) :
      k <> j ->
      bindk (T k) j g ∘ f = f ->
      bindk (T j) k f ∘ g = g ->
      bindk F j g ∘ bindk F k f =
      bindk F k f ∘ bindk F j g.
    Proof.
      intros neq hyp1 hyp2. unfold bindk.
      do 2 rewrite (rmod_mbind_mbind F T).
      f_equal. ext i. compare i to both of {k j}.
      - rewrite btg_eq. rewrite btg_neq; [| assumption].
        rewrite (mmon_mbind_comp_mret T).
        rewrite btg_eq. apply hyp1.
      - rewrite btg_eq. rewrite btg_neq; [| assumption].
        rewrite (mmon_mbind_comp_mret T).
        rewrite btg_eq. symmetry. apply hyp2.
      - rewrite btg_neq; [| assumption].
        rewrite btg_neq; [| assumption].
        rewrite (mmon_mbind_comp_mret T).
        rewrite (mmon_mbind_comp_mret T).
        rewrite btg_neq; [| assumption].
        rewrite btg_neq; [| assumption].
        trivial.
    Qed.

    Lemma bindk_fmapk_eq k {A} : forall (g : A -> T k A) (f : A -> A),
        bindk F k g ∘ fmapk F k f = bindk F k (g ∘ f).
    Proof.
      introv. unfold bindk. unfold fmapk.
      rewrite (mbind_mfmap F). fequal. ext j a.
      destruct_eq_args k j.
      - do 2 rewrite btg_eq.
        now rewrite tgt_eq.
      - do 2 (rewrite btg_neq; auto).
        now rewrite tgt_neq.
    Qed.

  End bindk_lemmas.

  (** ** Kleisli laws for [bindk] *)
  (******************************************************************************)
  Section bindk_kleisli.

    Context
      (F : Type -> Type)
      `{MultisortedRightModule F T}.

    Existing Instance Module_MMonad.

    (** The next three theorems are the left and right identity laws and the
      associativity law for Kleisli composition. *)
    Theorem kcompk_id_l {A k} : forall f : A -> T k A,
        mret T k ⋆k f = f.
    Proof.
      introv. unfold kcompk. now rewrite (bindk_mret (T k)).
    Qed.

    Theorem kcompk_id_r {A k} : forall f : A -> T k A,
        f ⋆k mret T k = f.
    Proof.
      introv. unfold kcompk. now rewrite (bindk_comp_mret_eq (T k)).
    Qed.

    Lemma kcompk_assoc :
      forall A k (h : A -> T k A)
             (g : A -> T k A) (f : A -> T k A),
        h ⋆k (g ⋆k f) = h ⋆k (g ⋆k f).
    Proof.
      introv. unfold kcompk. reflexivity.
    Qed.

  End bindk_kleisli.

End with_index.

(** ** Rewrite Hint registration *)
Hint Rewrite @btg_eq @btgd_eq @btg_id @btgd_same : tea_tgt.
Hint Rewrite @btg_eq @btgd_eq @btg_id @btgd_same : tea_tgt_eq.
Hint Rewrite @btg_neq @btgd_neq using auto : tea_tgt.
Hint Rewrite @btg_neq @btgd_neq using auto : tea_tgt_neq.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "g ⋆m f" := (mkcomp _ g f) (at level 60) : tealeaves_multi_scope.
  Notation "g ⋆k f" := (kcompk _ g f) (at level 60) : tealeaves_multi_scope.
End Notations.
