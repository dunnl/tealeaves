From Tealeaves Require Import
     Singlesorted.Classes.SetlikeFunctor
     Singlesorted.Functors.List
     Multisorted.Functors.Tag
     Multisorted.Classes.SetlikeMonad.

Import Sets.Notations.
Import List.Notations.
Import Multisorted.Classes.SetlikeFunctor.Notations.
Import Multisorted.Category.Notations.
#[local] Open Scope list_scope.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

(** * The monad of multisorted lists *)
(******************************************************************************)
Section mlist.

  Context
    `{ix : Index}.

  Implicit Types (k : K).

  Definition mlist : Type -> Type :=
    fun A => list (Tag A).

  #[global] Instance MReturn_mlist : MReturn (const mlist) := MReturn_T_Tag list.
  #[global] Instance MBind_mlist : MBind mlist (const mlist) := MBind_T_Tag list.
  #[global] Instance TaggedMonad_mlist : ConstantMultisortedMonad mlist := CMMonad_T_Tag list.
  #[global] Instance Modulep_mlist : MultisortedRightModule mlist (const mlist) := Module_T_Tag list.

  (** ** Rewriting lemmas for [mfmap] *)
  Lemma mfmap_mlist_nil `{f : A -k-> B} :
    mfmap mlist f (@nil (Tag A)) = @nil (Tag B).
  Proof.
    reflexivity.
  Qed.

  Lemma mfmap_mlist_cons `{f : A -k-> B} : forall (x : Tag A) (xs : mlist A),
      mfmap mlist f (x :: xs) = (fst x, f (fst x) (snd x)) :: mfmap mlist f xs.
  Proof.
    now destruct x.
  Qed.

  Lemma mfmap_mlist_one `{f : A -k-> B} : forall k a,
      mfmap mlist f [ (k, a) ] = [(k, f k a)].
  Proof.
    reflexivity.
  Qed.

  Lemma mfmap_mlist_app `{f : A -k-> B} : forall (xs ys : mlist A),
      mfmap mlist f (xs ++ ys) = mfmap mlist f xs ++ mfmap mlist f ys.
  Proof.
    intros. unfold mlist.
    unfold MReturn_mlist, MBind_mlist.
    rewrite (Monad_T_Tag_mfmap_spec list).
    now rewrite fmap_list_app.
  Qed.

  (** ** Rewriting lemmas for [mbind] *)
  Lemma mbind_mlist_nil `{f : K -> A -> mlist B} :
    mbind mlist f (@nil (Tag A)) = @nil (Tag B).
  Proof.
    reflexivity.
  Qed.

  Lemma mbind_mlist_cons {A B} : forall (f : A ~k~> (const mlist) B) (k : K) (a : A) (xs : mlist A),
      mbind mlist f ((k, a) :: xs) = f k a ++ mbind mlist f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma mbind_mlist_one {A B} : forall (f : A ~k~> (const mlist) B) (k : K) (a : A),
      mbind mlist f [(k, a)] = f k a.
  Proof.
    intros. cbn. now List.simpl_list.
  Qed.

  Lemma mbind_mlist_app {A B} : forall (f : A ~k~> (const mlist) B) (xs ys : mlist A),
      mbind mlist f (xs ++ ys) = mbind mlist f xs ++ mbind mlist f ys.
  Proof.
    introv. unfold mbind, MBind_mlist, MBind_T_Tag.
    now rewrite bind_list_app.
  Qed.

  (** ** Rewriting lemmas for [fmapk] *)
  Lemma fmapk_mlist_nil k `{f : A -> A} :
    fmapk mlist k f (@nil (Tag A)) = @nil (Tag A).
  Proof.
    reflexivity.
  Qed.

  Lemma fmapk_mlist_one_eq `{f : A -> A} : forall k a,
      fmapk mlist k f [ (k, a) ] = [(k, f a)].
  Proof.
    intros. cbn. now simpl_tgt.
  Qed.

  Lemma fmapk_mlist_one_neq `{f : A -> A} : forall k j a,
      k <> j ->
      fmapk mlist j f [ (k, a) ] = [(k, a)].
  Proof.
    intros. cbn. now simpl_tgt.
  Qed.

  Lemma fmapk_mlist_cons_eq `{f : A -> A} : forall (k : K) (a : A) (xs : mlist A),
      fmapk mlist k f ((k, a) :: xs) = (k, f a) :: fmapk mlist k f xs.
  Proof.
    intros. cbn. now simpl_tgt.
  Qed.

  Lemma fmapk_mlist_cons_neq `{f : A -> A} : forall (k : K) (j : K) (a : A) (xs : mlist A),
      k <> j ->
      fmapk mlist j f ((k, a) :: xs) = (k, a) :: fmapk mlist j f xs.
  Proof.
    intros. cbn. now simpl_tgt.
  Qed.

  Lemma fmapk_mlist_app `{f : A -> A} : forall k (xs ys : mlist A),
      fmapk mlist k f (xs ++ ys) = fmapk mlist k f xs ++ fmapk mlist k f ys.
  Proof.
    intros. unfold fmapk. now rewrite mfmap_mlist_app.
  Qed.

  (** ** Rewriting lemmas for [bindk] *)
  Lemma bindk_mlist_nil k `{f : A -> mlist A} :
    bindk mlist k f (@nil (Tag A)) = @nil (Tag A).
  Proof.
    reflexivity.
  Qed.

  Lemma bindk_mlist_cons_eq `{f : A -> mlist A} : forall (k : K) (a : A) (xs : mlist A),
      bindk mlist k f ((k, a) :: xs) = f a ++ bindk mlist k f xs.
  Proof.
    intros. unfold bindk. rewrite mbind_mlist_cons.
    now simpl_tgt_fallback.
  Qed.

  Lemma bindk_mlist_cons_neq `{f : A -> mlist A} : forall (j k : K) (a : A) (xs : mlist A),
      j <> k ->
      bindk mlist j f ((k, a) :: xs) = (k, a) :: bindk mlist j f xs.
  Proof.
    intros. unfold bindk. rewrite mbind_mlist_cons.
    now simpl_tgt_fallback.
  Qed.

  Lemma bindk_mlist_one_eq `{f : A -> mlist A} : forall (k : K) (a : A) (xs : mlist A),
      bindk mlist k f [ (k, a) ] = f a.
  Proof.
    intros. unfold bindk. rewrite mbind_mlist_one.
    now simpl_tgt_fallback.
  Qed.

  Lemma bindk_mlist_one_neq `{f : A -> mlist A} : forall (j k : K) (a : A) (xs : mlist A),
      j <> k ->
      bindk mlist j f [ (k, a) ] = [ (k, a) ].
  Proof.
    intros. unfold bindk. rewrite mbind_mlist_one.
    now simpl_tgt_fallback.
  Qed.

  Lemma bindk_mlist_app {A} : forall k (f : A -> mlist A) (xs ys : mlist A),
      bindk mlist k f (xs ++ ys) = bindk mlist k f xs ++ bindk mlist k f ys.
  Proof.
    introv. unfold bindk. now rewrite mbind_mlist_app.
  Qed.

End mlist.

Hint Rewrite @mfmap_mlist_nil @mfmap_mlist_cons
     @mfmap_mlist_one @mfmap_mlist_app : tea_list.

Hint Rewrite @fmapk_mlist_nil @fmapk_mlist_cons_eq
     @fmapk_mlist_one_eq @fmapk_mlist_app: tea_list.
Hint Rewrite @fmapk_mlist_cons_neq @fmapk_mlist_one_neq
     using (discriminate + auto) : tea_list.

Hint Rewrite @mbind_mlist_nil @mbind_mlist_cons
     @mbind_mlist_one @mbind_mlist_app : tea_list.

Hint Rewrite @bindk_mlist_nil @bindk_mlist_cons_eq
     @bindk_mlist_one_eq @bindk_mlist_app : tea_list.
Hint Rewrite @bindk_mlist_cons_neq @bindk_mlist_one_neq
     using (discriminate + auto) : tea_list.

(** * [mlist] is a quantifiable monad *)
(** This is a key step to showing that all listable (functors, monads, modules)
    are quantifiable. The idea is to prove the relevant properties for
    [mlist], and then transfer these to listables by the compatibility
    properties of [tomlist]. *)
#[global] Instance tomset_mlist `{Index} : Tomset mlist :=
  fun A => toset list.

(** ** Rewriting lemmas for [tomset] and [mlist] *)
Section tomset_mlist.

  Context
    `{ix : Index}.

  Lemma tomset_mlist_nil {A} : tomset mlist (@nil (Tag A)) = ∅.
  Proof.
    unfold tomset, tomset_mlist.
    now autorewrite with tea_list.
  Qed.

  Lemma tomset_mlist_cons {A} : forall (k : K) (a : A) (xs : mlist A),
      tomset mlist ((k, a) :: xs) = {{ (k, a) }} ∪ tomset mlist xs.
  Proof.
    intros. unfold tomset, tomset_mlist.
    now autorewrite with tea_list.
  Qed.

  Lemma tomset_mlist_one {A} (k : K) (a : A) :
    tomset mlist [ (k, a) ] = {{ (k, a) }}.
  Proof.
    intros. unfold tomset, tomset_mlist.
    now autorewrite with tea_list.
  Qed.

  Lemma tomset_mlist_app {A} : forall (xs ys : mlist A),
      tomset mlist (xs ++ ys) = tomset mlist xs ∪ tomset mlist ys.
  Proof.
    intros. unfold tomset, tomset_mlist.
    now autorewrite with tea_list.
  Qed.

  Lemma in_mlist_nil {A} : forall (p : Tag A), p ∈m @nil (Tag A) <-> False.
  Proof.
    intros. unfold tomset, tomset_mlist.
    now autorewrite with tea_list.
  Qed.

  Lemma in_mlist_cons {A} : forall (k1 k2 : K) (a1 a2 : A) (xs : mlist A),
      (k1, a1) ∈m ((k2, a2) :: xs) <-> k1 = k2 /\ a1 = a2 \/ (k1, a1) ∈m xs.
  Proof.
    intros. unfold tomset, tomset_mlist.
    autorewrite with tea_list.
    now rewrite Coq.Init.Datatypes.pair_equal_spec.
  Qed.

  Lemma in_mlist_cons_eq {A} : forall (k : K) (a1 a2 : A) (xs : mlist A),
      (k, a1) ∈m ((k, a2) :: xs) <-> a1 = a2 \/ (k, a1) ∈m xs.
  Proof.
    intros. unfold tomset, tomset_mlist.
    autorewrite with tea_list.
    rewrite Coq.Init.Datatypes.pair_equal_spec.
    tauto.
  Qed.

  Lemma in_mlist_one {A} (k1 k2 : K) (a1 a2 : A) :
    (k1, a1) ∈m [ (k2, a2) ] <-> k1 = k2 /\ a1 = a2.
  Proof.
    intros. unfold tomset, tomset_mlist.
    autorewrite with tea_list.
    now rewrite pair_equal_spec.
  Qed.

  Lemma in_mlist_one_eq {A} (k : K) (a1 a2 : A) :
    (k, a1) ∈m [ (k, a2) ] <-> a1 = a2.
  Proof.
    intros. now rewrite in_mlist_one.
  Qed.

  Lemma in_mlist_app {A} : forall (k : K) (a : A) (xs ys : mlist A),
      (k, a) ∈m (xs ++ ys) <-> (k, a) ∈m xs \/ (k, a) ∈m ys.
  Proof.
    intros. now rewrite tomset_mlist_app.
  Qed.

End tomset_mlist.

Hint Rewrite @tomset_mlist_nil @tomset_mlist_cons @tomset_mlist_one
     @tomset_mlist_app : tea_list.
Hint Rewrite @in_mlist_nil @in_mlist_cons @in_mlist_one
     @in_mlist_app : tea_list.

(** ** Quantifiable instance *)
Section mlist_is_quantifiable.

  Context
    `{ix : Index}.

  #[global] Instance: MultisortedNatural (tomset_mlist).
  Proof.
    change (@tomset_mlist _) with (@tomset _ mlist _).
    intros A B f.
    unfold mset, MReturn_mset, MBind_mset. (** TODO <-- these are hidden *)
    rewrite (Monad_T_Tag_mfmap_spec set).
    unfold mlist, MReturn_mlist, MBind_mlist. (** TODO <-- these are hidden *)
    rewrite (Monad_T_Tag_mfmap_spec list).
    unfold tomset, tomset_mlist.
    now rewrite (natural (G := set)).
  Qed.

  Theorem qmmon_mret_mlist : forall (k : K) (A : Type),
      tomset mlist ∘ mret (const mlist) k (A:=A) = mret (const mset) k.
  Proof.
    introv. ext a. ext p. destruct p as [kp ap].
    propext; firstorder.
  Qed.

  Theorem qmmon_mbind_mlist : forall `(f : forall k, A -> list (Tag B)),
      tomset mlist ∘ mbind mlist f = mbind mset (fun k => tomset mlist ∘ f k) ∘ tomset mlist.
  Proof.
    intros. ext l [k b]. unfold tomset, tomset_mlist.
    unfold mbind, MBind_mlist, MBind_mset, MBind_T_Tag.
    unfold compose. apply propositional_extensionality.
    rewrite (SetlikeMonad.in_bind_iff list).
    rewrite Sets.bind_set_spec.
    split; intros [[k' a] ?]; now exists (k', a).
  Qed.

  Theorem qmmon_respectful_mlist : forall (k : K) A B (t : (const mlist) k A) (f g : A ~k~> (const mlist) B),
      (forall k a, (k, a) ∈m t -> f k a = g k a) -> mbind ((const mlist) k) f t = mbind ((const mlist) k) g t.
  Proof.
    intros. cbv in t. induction t.
    - reflexivity.
    - change (const mlist k) with (mlist).
      destruct a as [k' a].
      rewrite (mbind_mlist_cons f).
      rewrite (mbind_mlist_cons g). fequal.
      + apply H. now left.
      + apply IHt. intros. apply H. now right.
  Qed.

  #[global] Instance: SetlikeMultisortedMonad (const mlist) :=
    {| qmmon_mret := @qmmon_mret_mlist;
       qmmon_mbind := fun A B f k => @qmmon_mbind_mlist A B f;
       qmmon_respectful := qmmon_respectful_mlist;
    |}.

End mlist_is_quantifiable.

(** ** Filtering *)
Fixpoint filterk `{Index} {A} (k : K) (l : mlist A) : list A :=
  match l with
  | nil => nil
  | cons (j, a) ts =>
    if k == j then a :: filterk k ts else filterk k ts
  end.

(** ** Rewriting lemmas for [filterk] *)
Section filterk_lemmas.

  Context
    `{Index}.

  Lemma filterk_nil : forall A k,
    filterk k (nil : mlist A) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filterk_cons : forall A k j (a : A) (l : mlist A),
      filterk j ((k, a) :: l) = if k == j then a :: filterk k l else filterk j l.
  Proof.
    intros; cbn. compare values k and j.
  Qed.

  Corollary filterk_cons_eq: forall A k (a : A) (l : mlist A),
      filterk k ((k, a) :: l) = a :: filterk k l.
  Proof.
    intros. rewrite filterk_cons. compare values k and k.
  Qed.

  Corollary filterk_cons_neq : forall A k j (a : A) (l : mlist A),
      k <> j ->
      filterk j ((k, a) :: l) = filterk j l.
  Proof.
    intros. rewrite filterk_cons. compare values k and j.
  Qed.

  Lemma filterk_one : forall A k j (a : A) (l : mlist A),
      filterk j [(k, a)] = if k == j then [ a ] else nil.
  Proof.
    intros; cbn. compare values k and j.
  Qed.

  Corollary filterk_one_eq : forall A k (a : A) (l : mlist A),
      filterk k [(k, a)] = [ a ].
  Proof.
    intros; cbn. compare values k and k.
  Qed.

  Corollary filterk_one_neq : forall A k j (a : A) (l : mlist A),
      k <> j ->
      filterk j [(k, a)] = nil.
  Proof.
    intros; cbn. compare values k and j.
  Qed.

  Lemma filterk_app : forall A k (l1 l2 : mlist A),
      filterk k (l1 ++ l2) = filterk k l1 ++ filterk k l2.
  Proof.
    intros. induction l1.
    - reflexivity.
    - cbn. destruct a. compare values k and k0.
      now rewrite IHl1.
  Qed.

  Lemma filterk_natural : forall A B k (f : A -k-> B),
    filterk k ∘ mfmap mlist f = fmap list (f k) ∘ filterk k.
  Proof.
    intros. unfold compose; ext l. induction l.
    - reflexivity.
    - destruct a as [j a].
      autorewrite with tea_list. rewrite filterk_cons.
      cbn. compare values k and j.
      now rewrite IHl.
  Qed.

  Lemma filterk_fmapk_eq : forall A k (f : A -> A),
    filterk k ∘ fmapk mlist k f = fmap list f ∘ filterk k.
  Proof.
    intros. unfold fmapk. rewrite filterk_natural.
    now rewrite tgt_eq.
  Qed.

  Lemma filterk_fmapk_neq : forall A k j (f : A -> A),
      k <> j ->
    filterk k ∘ fmapk mlist j f = filterk k.
  Proof.
    intros. unfold fmapk. rewrite filterk_natural.
    rewrite tgt_neq; auto.
    now rewrite (fun_fmap_id list).
  Qed.

  Lemma filterk_bindk_eq : forall A k (f : A -> mlist A),
    filterk k ∘ bindk mlist k f = bind list (filterk k ∘ f) ∘ filterk k.
  Proof.
    intros. unfold compose; ext l. induction l.
    - reflexivity.
    - destruct a as [j a]. compare values k and j.
      + autorewrite* with tea_list.
        rewrite ?(filterk_cons_eq).
        autorewrite* with tea_list.
        rewrite bindk_mlist_cons_eq.
        rewrite filterk_app. now rewrite IHl.
      + rewrite (bindk_mlist_cons_neq); auto.
        rewrite filterk_cons_neq; auto.
        rewrite filterk_cons_neq; auto.
  Qed.

End filterk_lemmas.

Hint Rewrite @filterk_nil @filterk_cons_eq @filterk_one_eq
     @filterk_app : tea_list.
Hint Rewrite @filterk_cons_neq @filterk_one_neq @filterk_fmapk_neq
     using (discriminate + auto) : tea_list.
