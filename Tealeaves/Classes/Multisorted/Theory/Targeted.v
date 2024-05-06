From Tealeaves Require Import
  Classes.Multisorted.DecoratedTraversableMonad
  Classes.Multisorted.Theory.Container
  Categories.TypeFamily
  Functors.List
  Functors.Constant.

Import TypeFamily.Notations.
Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables A B C F G W S T K.

(** * Targeted substitution-building combinators: [btg] and [btgd] *)
(******************************************************************************)
(* TODO : Define a version that works for applicative effects. *)
(*
#[program] Definition btga `{ix : Index} `{Map F} `{Pure F} `{Mult F}
 {A W : Type} (T : K -> Type -> Type) `{! MReturn T}
 (j : K) (f : W * A -> F (T j A)) : forall (k : K), W * A -> F (T k A) :=
  fun k '(w, a) => if k == j then f (w, a) else pure ∘ mret T k a.
 *)

Require Import Coq.Program.Equality.

#[program] Definition btgd `{ix : Index} {A W : Type}
  {T : K -> Type -> Type} `{! MReturn T}
  (j : K) (f : W * A -> T j A) : forall (k : K), W * A -> T k A :=
  fun k '(w, a) => if k == j then f (w, a) else mret T k a.

#[program] Definition btg `{ix : Index} {A : Type}
  {T : K -> Type -> Type} `{! MReturn T}
  (j : K) (f : A -> T j A) : forall (k : K), A -> T k A :=
  fun k => if k == j then f else mret T k.

Require Import Coq.Program.Equality.

Section btg_lemmas.

  Context
    `{ix : Index}.

  Context
    `{MReturn T}
      {W A : Type}.

  Lemma btgd_eq : forall k (f : W * A -> T k A),
      btgd k f k = f.
  Proof.
    introv. unfold btgd. ext [w a].
    compare values k and k.
    dependent destruction DESTR_EQ.
    cbn. reflexivity.
  Qed.

  Lemma btgd_neq : forall {k j} (f : W * A -> T j A),
      k <> j -> btgd j f k = mret T k ∘ extract (W := (W ×)).
  Proof.
    introv. unfold btgd. intro hyp. ext [w a].
    compare values k and j.
  Qed.

  Lemma btgd_id (j : K) :
    btgd (A := A) j (mret T j ∘ extract (W := (W ×))) = mret T ◻ allK extract.
  Proof.
    unfold btgd. ext k [w a]. compare values k and j.
  Qed.

  Lemma btg_eq : forall k (f : A -> T k A),
      btg k f k = f.
  Proof.
    introv. unfold btg.
    compare values k and k.
    dependent destruction DESTR_EQ.
    cbn. reflexivity.
  Qed.

  Lemma btg_neq : forall {k j} (f : A -> T j A),
      k <> j -> btg j f k = mret T k.
  Proof.
    introv. unfold btg. intro hyp.
    compare values k and j.
  Qed.

  Lemma btg_id (j : K) :
    btg (A := A) j (mret T j) = mret T.
  Proof.
    unfold btg. ext k. compare values k and j.
  Qed.

End btg_lemmas.

(** ** Rewrite Hint registration *)
(******************************************************************************)
#[export] Hint Rewrite @btg_eq @btg_id @btgd_eq @btgd_id: tea_tgt.
#[export] Hint Rewrite @tgtd_eq @tgtd_eq @tgtd_id: tea_tgt.
#[export] Hint Rewrite @btgd_neq @btg_neq using auto : tea_tgt.

#[export] Hint Rewrite @btgd_eq @btg_eq @btg_id @btgd_id : tea_tgt_eq.
#[export] Hint Rewrite @tgtd_eq @tgt_eq @tgt_id : tea_tgt_eq.
#[export] Hint Rewrite @btgd_neq @btg_neq using auto : tea_tgt_neq.
#[export] Hint Rewrite @tgtd_neq : tea_tgt_neq.

(** ** Derived targeted DTM operations *)
(******************************************************************************)
Section DTM_targeted.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    (j : K).

  (** *** Definitions *)
  (* For now we ignore traversals because we don't need them for System F. *)
  (******************************************************************************)
  Definition kbindd {A} `(f : W * A -> T j A) : U A -> U A
    := mbindd U (btgd j f).

  Definition kbind `(f : A -> T j A) : U A -> U A
    := mbind U (btg j f).

  Definition kmapd `(f : W * A -> A) : U A -> U A :=
    mmapd U (tgtd j f).

  Definition kmap `(f : A -> A) : U A -> U A :=
    mmap U (tgt j f).

  Section special_cases.

    Context
      {A : Type}.

    (** *** Rewriting rules for special cases of <<kbindd>> *)
    (******************************************************************************)
    Lemma kbind_to_kbindd (f : A -> T j A) :
      kbind f = kbindd (f ∘ extract (W := (W ×))).
    Proof.
      unfold kbind, kbindd. rewrite mbind_to_mbindd.
      fequal. ext k [w a].
      unfold vec_compose, compose; cbn.
      compare values k and j.
      - autorewrite  with tea_tgt_eq. easy.
      - autorewrite  with tea_tgt_neq. easy.
    Qed.

    Lemma kmapd_to_kbindd (f : W * A -> A) :
      kmapd f = kbindd (mret T j ∘ f).
    Proof.
      unfold kmapd, kbindd. rewrite mmapd_to_mbindd.
      fequal. ext k [w a].
      unfold vec_compose, compose.
      cbn. compare values k and j.
    Qed.

    Lemma kmap_to_kbindd (f : A -> A) :
      kmap f = kbindd (mret T j ∘ f ∘ extract (W := (W ×))).
    Proof.
      unfold kmap, kbindd. rewrite mmap_to_mbindd.
      fequal. ext k [w a].
      unfold vec_compose, compose. cbn.
      compare values k and j. cbn.
      now autorewrite with tea_tgt_eq.
      now autorewrite with tea_tgt_neq.
    Qed.

    (** *** Rewriting rules for special cases of <<kmapd>> *)
    (******************************************************************************)
    Lemma kmap_to_kmapd (f : A -> A) :
      kmap f = kmapd (f ∘ extract (W := (W ×))).
    Proof.
      unfold kmap, kbind.
      unfold kmapd. rewrite mmap_to_mmapd.
      fequal. ext k.
      unfold vec_compose.
      compare values j and k.
      now autorewrite with tea_tgt_eq.
      now autorewrite with tea_tgt_neq.
    Qed.

    (** *** Rewriting rules for special cases of <<kbind>> *)
    (******************************************************************************)
    Lemma kmap_to_kbind (f : A -> A) :
      kmap f = kbind (mret T j ∘ f).
    Proof.
      unfold kmap, kbind.
      rewrite mmap_to_mbind.
      fequal. ext k.
      unfold vec_compose.
      compare values j and k.
      now autorewrite with tea_tgt_eq.
      now autorewrite with tea_tgt_neq.
    Qed.

  End special_cases.

End DTM_targeted.

(** ** Decorated monad (<<kbindd>>) *)
(******************************************************************************)

Definition compose_kdm
           `{ix : Index}
           {W : Type}
           {T : K -> Type -> Type}
           `{mn_op : Monoid_op W}
           `{mn_unit : Monoid_unit W}
           `{forall k, MBind W T (T k)}
           `{! MReturn T}
           {j : K}
           {A : Type}
           (g : W * A -> T j A)
           (f : W * A -> T j A) : W * A -> T j A :=
  fun '(w, a) => kbindd (T j) j (g ∘ incr w) (f (w, a)).

Infix "⋆kdm" := compose_kdm (at level 40).

Section DecoratedMonad.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}
    {j : K}
    {A : Type}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem kbindd_id :
    kbindd U j (mret T j ∘ extract) = @id (U A).
  Proof.
    intros. unfold kbindd. rewrite <- (mbindd_id U).
    fequal. ext k [w a]. cbn. compare values k and j.
  Qed.

  Theorem kbindd_kbindd_eq : forall (g : W * A -> T j A) (f : W * A -> T j A),
      kbindd U j g ∘ kbindd U j f =
      kbindd U j (g ⋆kdm f).
  Proof.
    intros. unfold kbindd. rewrite (mbindd_mbindd U).
    fequal. ext k [w a]. cbn. compare values k and j.
    - cbn. unfold kbindd. fequal. ext k [w' a'].
      compare values k and j.
    - compose near a on left. rewrite mbindd_comp_mret.
      cbn. compare values k and j.
  Qed.

  Theorem kbindd_kbindd_neq :
    forall {i : K} (Hneq : j <> i)
      (g : W * A -> T i A) (f : W * A -> T j A),
      kbindd U i g ∘ kbindd U j f =
      mbindd U (btgd i g ⋆dm btgd j f).
  Proof.
    intros. unfold kbindd. now rewrite (mbindd_mbindd U).
  Qed.

  (** *** Right unit law for monads *)
  (******************************************************************************)
  Theorem kbindd_comp_mret_eq : forall (f : W * A -> T j A) (a : A),
      kbindd (T j) j f (mret T j a) = f (Ƶ, a).
  Proof.
    intros. unfold kbindd. compose near a on left.
    rewrite (mbindd_comp_mret).
    now autorewrite with tea_tgt_eq.
  Qed.

  Theorem kbindd_comp_mret_neq :
    forall (i : K) (Hneq : j <> i)
      (f : W * A -> T j A) (a : A),
      kbindd (T i) j f (mret T i a) = mret T i a.
  Proof.
    intros. unfold kbindd. compose near a on left.
    rewrite (mbindd_comp_mret).
    now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Composition with special cases *)
  (******************************************************************************)
  Lemma kmapd_kbindd : forall
      (g : W * A -> A) (f : W * A -> T j A),
      kmapd U j g ∘ kbindd U j f = kbindd U j (fun '(w, a) => kmapd (T j) j (g ∘ incr w) (f (w, a))).
  Proof.
    intros. rewrite kmapd_to_kbindd.
    rewrite kbindd_kbindd_eq. fequal.
    unfold compose_kdm. ext [w a].
    now rewrite kmapd_to_kbindd.
  Qed.

  Lemma kbind_kbindd : forall
      (g : A -> T j A) (f : W * A -> T j A),
      kbind U j g ∘ kbindd U j f = kbindd U j (kbind (T j) j g ∘ f).
  Proof.
    intros. rewrite kbind_to_kbindd. rewrite kbindd_kbindd_eq.
    fequal. unfold compose_kdm. ext [w a].
    reassociate ->. rewrite extract_incr. now rewrite kbind_to_kbindd.
  Qed.

  Lemma kmap_kbindd : forall
      (g : A -> A) (f : W * A -> T j A),
      kmap U j g ∘ kbindd U j f = kbindd U j (fun '(w, a) => kmap (T j) j g (f (w, a))).
  Proof.
    intros. unfold kmap, kbindd. rewrite mmap_to_mbindd.
    rewrite (mbindd_mbindd U). fequal. ext k [w a].
    compare values j and k.
    - autorewrite with tea_tgt_eq.
      rewrite mmap_to_mbindd. fequal.
      ext k' [w' a']. unfold compose; cbn. reflexivity.
    - autorewrite with tea_tgt_neq.
      unfold vec_compose, compose; cbn.
      compose near a on left.
      rewrite (mbindd_comp_mret).
      rewrite tgt_neq; auto.
  Qed.

  Lemma kbindd_kmapd : forall
      (g : W * A -> T j A) (f : W * A -> A),
      kbindd U j g ∘ kmapd U j f = kbindd U j (fun '(w, a) => g (w, f (w, a))).
  Proof.
    intros. rewrite kmapd_to_kbindd.
    rewrite kbindd_kbindd_eq. fequal.
    ext (w, a). unfold compose; cbn.
    rewrite kbindd_comp_mret_eq. unfold compose; cbn.
    now simpl_monoid.
  Qed.

  Lemma kbindd_kbind : forall
      (g : W * A -> T j A) (f : A -> T j A),
      kbindd U j g ∘ kbind U j f = kbindd U j (fun '(w, a) => kbindd (T j) j (g ∘ incr w) (f a)).
  Proof.
    intros. rewrite kbind_to_kbindd. now rewrite kbindd_kbindd_eq.
  Qed.

  (* TODO <<kbindd_kmap>> *)

End DecoratedMonad.

(** ** Mixed structure composition laws *)
(** Composition laws involving <<kbind>> and <<kmapd>> *)
(******************************************************************************)

(* TODO <<kbind_kmapd>> *)

(* TODO <<kmapd_kbind>> *)

(** ** Decorated functors (<<kmapd>>) *)
(******************************************************************************)
Section DecoratedFunctor.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}
    {j : K}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem kmapd_id : forall A,
      kmapd U j extract = @id (U A).
  Proof.
    intros. unfold kmapd.
    rewrite <- (mmapd_id U).
    fequal. ext k. compare values j and k.
    - now autorewrite with tea_tgt.
    - now autorewrite with tea_tgt.
  Qed.

  Theorem kmapd_kmapd : forall A,
      forall (g : W * A -> A) (f : W * A -> A),
        kmapd U j g ∘ kmapd U j f =
        kmapd U j (fun '(w, a) => g (w, f (w, a))).
  Proof.
    intros. unfold kmapd.
    rewrite (mmapd_mmapd U). fequal.
    ext k [w a]. compare values j and k.
    - now autorewrite with tea_tgt.
    - now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma kmapd_comp_mret_eq : forall A,
      forall (f : W * A -> A) (a : A),
        kmapd (T j) j f (mret T j a) = mret T j (f (Ƶ, a)).
  Proof.
    intros. unfold kmapd. rewrite mmapd_comp_mret.
    now autorewrite with tea_tgt.
  Qed.

  Lemma kmapd_comp_mret_neq : forall A,
      forall (k : K) (neq : k <> j) (f : W * A -> A) (a : A),
        kmapd (T k) j f (mret T k a) = mret T k a.
  Proof.
    intros. unfold kmapd. rewrite mmapd_comp_mret.
    now autorewrite with tea_tgt_neq.
  Qed.

  (* TODO <<kmap_kmapd>> *)

  (* TODO <<kmapd_kmap>> *)

End DecoratedFunctor.

(** ** Monads (<<kbind>>) *)
(******************************************************************************)
Definition compose_km
           `{ix : Index}
           {W : Type}
           {T : K -> Type -> Type}
           `{forall k, MBind W T (T k)}
           `{! MReturn T}
           {j : K}
           {A : Type}
           (g : A -> T j A)
           (f : A -> T j A) : A -> T j A :=
  (kbind (T j) j g ∘ f).

Infix "⋆km" := compose_km (at level 40).

Section Monad.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}
    {j : K}.

  (** *** Composition and identity law *)
  (******************************************************************************)
    Theorem kbind_id : forall A,
      kbind U j (mret T j) = @id (U A).
  Proof.
    intros. unfold kbind.
    rewrite <- (mbind_id U). fequal.
    ext k. compare values j and k.
    - now autorewrite with tea_tgt_eq.
    - now autorewrite with tea_tgt_neq.
  Qed.

  Theorem kbind_kbind : forall A,
      forall (g f : A -> T j A),
        kbind U j g ∘ kbind U j f =
        kbind U j (g ⋆km f).
  Proof.
    intros. unfold kbind.
    rewrite (mbind_mbind U). fequal.
    ext k a. compare values j and k.
    - now autorewrite with tea_tgt_eq.
    - autorewrite with tea_tgt_neq.
      rewrite (mbind_comp_mret k).
      now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma kbind_comp_mret_eq : forall A,
    forall (f : A -> T j A) (a : A),
      kbind (T j) j f (mret T j a) = f a.
  Proof.
    intros. unfold kbind. rewrite mbind_comp_mret.
    now autorewrite with tea_tgt_eq.
  Qed.

  Lemma kbind_comp_mret_neq : forall A,
    forall (i : K) (Hneq : j <> i) (f : A -> T j A) (a : A),
      kbind (T i) j f (mret T i a) = mret T i a.
  Proof.
    intros. unfold kbind. rewrite mbind_comp_mret.
    now autorewrite with tea_tgt_neq.
  Qed.

  (* TODO <<kmap_kbind>> *)

  (* TODO <<kbind_kmap>> *)

End Monad.

(** ** Functors (<<kmap>>) *)
(******************************************************************************)
Section Functor.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}
    {j : K}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem kmap_id : forall A,
      kmap U j (@id A) = @id (U A).
  Proof.
    intros. unfold kmap.
    rewrite <- (mmap_id U).
    fequal. ext k. compare values k and j.
    now autorewrite with tea_tgt_eq.
    now autorewrite with tea_tgt_neq.
  Qed.

  Theorem kmap_kmap : forall (A : Type) (g f : A -> A),
      kmap U j g ∘ kmap U j f = kmap U j (g ∘ f).
  Proof.
    intros. unfold kmap.
    rewrite (mmap_mmap U). fequal.
    ext k.
    rewrite vec_compose_k.
    compare values j and k.
    - now autorewrite with tea_tgt_eq.
    - now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Naturality w.r.t. <<mret>> *)
  (******************************************************************************)
  Lemma kmap_comp_kret_eq {A} :
    forall (f : A -> A) (a : A),
      kmap (T j) j f (mret T j a) = mret T j (f a).
  Proof.
    intros. unfold kmap. rewrite mmap_comp_mret.
    now rewrite tgt_eq.
  Qed.

  Lemma kmap_comp_kret_neq {A} :
    forall (i : K) (Hneq : j <> i) (f : A -> A) (a : A),
      kmap (T i) j f (mret T i a) = mret T i a.
  Proof.
    intros. unfold kmap. rewrite mmap_comp_mret.
    rewrite tgt_neq; auto.
  Qed.

End Functor.

(** ** Notations **)
(******************************************************************************)
Module Notations.
  Infix "⋆dtm" := compose_dtm (at level 40) : tealeaves_scope.
  Infix "⋆kdm" := compose_kdm (at level 40) : tealeaves_scope.
  Infix "⋆km" := compose_km (at level 40) : tealeaves_scope.
End Notations.

Import Container.Notations.

(** * Characterizing occurrences post-operation (targetted operations) *)
(******************************************************************************)
Section DTM_membership_targetted.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Context
    (j : K)
    {A : Type}.

  (** *** Occurrences in <<kbindd>> with context *)
  (******************************************************************************)
  Lemma ind_kbindd_eq_iff1 :
    forall `(f : W * A -> T j A) (t : U A) (wtotal : W) (a2 : A),
      (wtotal, (j, a2)) ∈md kbindd U j f t ->
      exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (j, a2)) ∈md f (w1, a1)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold kbindd in hyp.
    apply (ind_mbindd_iff1 U) in hyp.
    destruct hyp as [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]. subst.
    compare values j and k1.
    + exists w1 w2 a. splits.
      { auto. }
      { rewrite btgd_eq in hyp2. auto. }
      { reflexivity. }
    + rewrite btgd_neq in hyp2; auto.
      unfold compose in hyp2; cbn in hyp2.
      rewrite ind_mret_iff in hyp2. destructs hyp2.
      subst. contradiction.
  Qed.

  Lemma ind_kbindd_eq_iff2 :
    forall `(f : W * A -> T j A) (t : U A) (wtotal : W) (a2 : A),
      (exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (j, a2)) ∈md f (w1, a1)
        /\ wtotal = w1 ● w2) ->
      (wtotal, (j, a2)) ∈md kbindd U j f t.
  Proof.
    introv [w1 [w2 [a1 hyp]]]. destructs hyp. unfold kbindd.
    apply (ind_mbindd_iff2 U).
    exists j w1 w2 a1. rewrite btgd_eq. auto.
  Qed.

  Theorem ind_kbindd_eq_iff :
    forall `(f : W * A -> T j A) (t : U A) (wtotal : W) (a2 : A),
      (wtotal, (j, a2)) ∈md kbindd U j f t <->
      exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (j, a2)) ∈md f (w1, a1)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using ind_kbindd_eq_iff1, ind_kbindd_eq_iff2.
  Qed.

  Lemma ind_kbindd_neq_iff1 :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> T j A) (t : U A) (wtotal : W) (a2 : A),
      (wtotal, (i, a2)) ∈md kbindd U j f t ->
      (wtotal, (i, a2)) ∈md t \/
      (exists (w1 w2 : W) (a1 : A), (w1, (j, a1)) ∈md t /\ (w2, (i, a2)) ∈md f (w1, a1) /\ wtotal = w1 ● w2).
  Proof.
    introv ? hyp. unfold kbindd in hyp.
    apply (ind_mbindd_iff1 U) in hyp.
    destruct hyp as [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]. subst.
    compare values j and k1.
    + right. exists w1 w2 a. rewrite btgd_eq in hyp2. splits; auto.
    + left. rewrite btgd_neq in hyp2; auto.
      unfold compose in hyp2. cbn in hyp2.
      rewrite ind_mret_iff in hyp2. destructs hyp2; subst.
      simpl_monoid. auto.
  Qed.

  Lemma ind_kbindd_neq_iff2 :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> T j A) (t : U A) (wtotal : W) (a2 : A),
      (wtotal, (i, a2)) ∈md t \/
      (exists (w1 w2 : W) (a1 : A), (w1, (j, a1)) ∈md t /\ (w2, (i, a2)) ∈md f (w1, a1) /\ wtotal = w1 ● w2) ->
      (wtotal, (i, a2)) ∈md kbindd U j f t.
  Proof.
    introv ? hyp. destruct hyp as [hyp | hyp].
    - apply (ind_mbindd_iff2 U). exists i wtotal Ƶ a2.
      splits.
      { auto. }
      { rewrite btgd_neq; auto. unfold compose; cbn.
        rewrite ind_mret_iff; auto. }
      { now simpl_monoid. }
    - destruct hyp as [w1 [w2 [a1 [hyp1 [hyp2 hyp3]]]]]. subst.
      apply (ind_mbindd_iff2 U).
      exists j w1 w2 a1. rewrite btgd_eq. auto.
  Qed.

  Theorem ind_kbindd_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> T j A) (t : U A) (wtotal : W) (a2 : A),
      (wtotal, (i, a2)) ∈md kbindd U j f t <->
      (wtotal, (i, a2)) ∈md t \/
      (exists (w1 w2 : W) (a1 : A), (w1, (j, a1)) ∈md t /\ (w2, (i, a2)) ∈md f (w1, a1) /\ wtotal = w1 ● w2).
  Proof.
    split; auto using ind_kbindd_neq_iff1, ind_kbindd_neq_iff2.
  Qed.

  (** *** Corollaries for <<kbind>>, <<kmapd>>, and <<kmap>>*)
  (******************************************************************************)
  Corollary ind_kbind_eq_iff :
    forall `(f : A -> T j A) (t : U A) (wtotal : W) (a2 : A),
      (wtotal, (j, a2)) ∈md kbind U j f t <->
      exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (j, a2)) ∈md f a1
        /\ wtotal = w1 ● w2.
  Proof.
    intros. rewrite kbind_to_kbindd. now rewrite (ind_kbindd_eq_iff).
  Qed.

  Corollary ind_kbind_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : A -> T j A) (t : U A) (wtotal : W) (a2 : A),
      (wtotal, (i, a2)) ∈md kbind U j f t <->
      (wtotal, (i, a2)) ∈md t \/
      (exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (i, a2)) ∈md f a1
        /\ wtotal = w1 ● w2).
  Proof.
    intros. rewrite kbind_to_kbindd. rewrite ind_kbindd_neq_iff; auto.
    unfold compose. cbn. easy.
  Qed.

  Corollary ind_kmapd_eq_iff :
    forall `(f : W * A -> A) (t : U A) (w : W) (a2 : A),
      (w, (j, a2)) ∈md kmapd U j f t <->
      exists (a1 : A), (w, (j, a1)) ∈md t /\ a2 = f (w, a1).
  Proof.
    intros. unfold kmapd. rewrite (ind_mmapd_iff U).
    now rewrite tgtd_eq.
  Qed.

  Corollary ind_kmapd_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> A) (t : U A) (w : W) (a2 : A),
      (w, (i, a2)) ∈md kmapd U j f t <->
      (w, (i, a2)) ∈md t.
  Proof.
    intros. unfold kmapd. rewrite (ind_mmapd_iff U).
    rewrite tgtd_neq; auto. cbn. split.
    - intros [a [hyp eq]]; subst. auto.
    - intros hyp. now (exists a2).
  Qed.

  Corollary ind_kmap_eq_iff :
    forall `(f : A -> A) (t : U A) (w : W) (a2 : A),
      (w, (j, a2)) ∈md kmap U j f t <->
      exists (a1 : A), (w, (j, a1)) ∈md t /\ a2 = f a1.
  Proof.
    intros. unfold kmap. rewrite (ind_mmap_iff U).
    now rewrite tgt_eq.
  Qed.

  Corollary ind_kmap_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : A -> A) (t : U A) (w : W) (a2 : A),
      (w, (i, a2)) ∈md kmap U j f t <->
      (w, (i, a2)) ∈md t.
  Proof.
    intros. unfold kmap. rewrite (ind_mmap_iff U).
    rewrite tgt_neq; auto. split.
    - intros [a [hyp eq]]; subst. auto.
    - intros hyp. now (exists a2).
  Qed.

  (** *** Occurrences without context *)
  (******************************************************************************)
  Theorem in_kbindd_eq_iff :
    forall `(f : W * A -> T j A) (t : U A) (a2 : A),
      (j, a2) ∈m kbindd U j f t <->
      exists (w1 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (j, a2) ∈m f (w1, a1).
  Proof.
    intros. rewrite ind_iff_in.
    setoid_rewrite ind_iff_in.
    setoid_rewrite ind_kbindd_eq_iff.
    split.
    - intros [w [w1 [w2 [a1 [hyp1 [hyp2 hyp3]]]]]].
      eexists. eexists. split; eauto.
    - intros [w [a1 [hyp1 [w2 hyp2]]]].
      repeat eexists; eauto.
  Qed.

  Theorem in_kbindd_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> T j A) (t : U A) (a2 : A),
      (i, a2) ∈m kbindd U j f t <->
      (i, a2) ∈m t \/
      (exists (w1 : W) (a1 : A), (w1, (j, a1)) ∈md t /\ (i, a2) ∈m f (w1, a1)).
  Proof.
    intros. rewrite ind_iff_in.
    setoid_rewrite ind_iff_in.
    setoid_rewrite ind_kbindd_neq_iff; auto.
    split.
    - intros [w [hyp | hyp]].
      + left. eauto.
      + right. destruct hyp as [w1 [w2 [a1 [hyp1 [hyp2 hyp3]]]]].
        repeat eexists; eauto.
    - intros [hyp | hyp].
      + destruct hyp as [w hyp]. eexists. left. eauto.
      + destruct hyp as [w1 [a1 [hyp1 [w2 hyp2]]]].
        eexists. right. repeat eexists; eauto.
  Qed.

 Corollary in_kbind_eq_iff :
    forall `(f : A -> T j A) (t : U A) (a2 : A),
      (j, a2) ∈m kbind U j f t <->
      exists (a1 : A),
        (j, a1) ∈m t /\ (j, a2) ∈m f a1.
  Proof.
    intros. rewrite kbind_to_kbindd. rewrite (in_kbindd_eq_iff).
    setoid_rewrite ind_iff_in at 2.
    unfold compose. cbn. firstorder.
  Qed.

  Corollary in_kbind_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : A -> T j A) (t : U A) (a2 : A),
      (i, a2) ∈m kbind U j f t <->
      (i, a2) ∈m t \/
      (exists (a1 : A),
        (j, a1) ∈m t /\ (i, a2) ∈m f a1).
  Proof.
    intros. rewrite kbind_to_kbindd. rewrite in_kbindd_neq_iff; auto.
    split.
    - intros [hyp|hyp].
      + now left.
      + right. unfold compose in hyp. cbn in hyp.
        destruct hyp as [? [a1 [hyp1 hyp2]]].
        apply ind_implies_in in hyp1. eauto.
    - intros [hyp|hyp].
      + now left.
      + right.
        destruct hyp as [a1 [hyp1 hyp2]].
        rewrite ind_iff_in in hyp1. destruct hyp1 as [w1 hyp1].
        exists w1 a1. auto.
  Qed.

  Corollary in_kmapd_eq_iff :
    forall `(f : W * A -> A) (t : U A) (a2 : A),
      (j, a2) ∈m kmapd U j f t <->
      exists (w : W) (a1 : A), (w, (j, a1)) ∈md t /\ a2 = f (w, a1).
  Proof.
    intros. unfold kmapd. rewrite (in_mmapd_iff U).
    now rewrite tgtd_eq.
  Qed.

  Corollary in_kmapd_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> A) (t : U A) (a2 : A),
      (i, a2) ∈m kmapd U j f t <->
      (i, a2) ∈m t.
  Proof.
    intros. unfold kmapd. rewrite (in_mmapd_iff U).
    rewrite tgtd_neq; auto. cbn. split.
    - intros [w [a [hyp eq]]]; subst.
      eapply ind_implies_in; eauto.
    - intros hyp. rewrite ind_iff_in in hyp.
      destruct hyp as [w hyp]. eauto.
  Qed.

  Corollary in_kmap_eq_iff :
    forall `(f : A -> A) (t : U A) (a2 : A),
      (j, a2) ∈m kmap U j f t <->
      exists (a1 : A), (j, a1) ∈m t /\ a2 = f a1.
  Proof.
    intros. unfold kmap. rewrite (in_mmap_iff U).
    now rewrite tgt_eq.
  Qed.

  Corollary in_kmap_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : A -> A) (t : U A) (a2 : A),
      (i, a2) ∈m kmap U j f t <->
      (i, a2) ∈m t.
  Proof.
    intros. unfold kmap. rewrite (in_mmap_iff U).
    rewrite tgt_neq; auto. split.
    - intros [a [hyp ?]]; subst. assumption.
    - intros; now (exists a2).
  Qed.

End DTM_membership_targetted.
