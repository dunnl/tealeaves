From Tealeaves Require Export
  Functors.Batch
  Classes.DT.Monad
  Theory.Traversable.Functor
  Theory.Traversable.Monad
  Theory.DT.Functor
  Functors.Sets.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Sets.Notations.

#[local] Generalizable Variables G A B C.

Import DT.Monad.DerivedInstances.

(** * Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}
    (M : Type)
    `{Monoid M}.

  #[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

  Lemma binddt_constant_applicative1 {A B : Type}
    `(f : W * A -> const M (T B)) :
    binddt W T T (const M) A B f =
      binddt W T T (const M) A False f.
  Proof.
    change_right (map (const M) (T False) (T B) (map T False B exfalso)
                    ∘ (binddt W T T (const M) A False (f : W * A -> const M (T False)))).
    rewrite (map_binddt W T (const M)).
    reflexivity.
  Qed.

  Lemma binddt_constant_applicative2 (fake1 fake2 : Type)
    `(f : W * A -> const M (T B)) :
    binddt W T T (const M) A fake1 f
    = binddt W T T (const M) A fake2 f.
  Proof.
    intros.
    rewrite (binddt_constant_applicative1 (B := fake1)).
    rewrite (binddt_constant_applicative1 (B := fake2)).
    easy.
  Qed.

End lemmas.

(** * Batch *)
(******************************************************************************)
Section with_functor.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Lemma runBatch_batch7 : forall `{Applicative G} (A B : Type) (f : W * A -> G (T B)),
      runBatch f ∘ (@batch (W * A) (T B)) = f.
  Proof.
    intros. apply (runBatch_batch G).
  Qed.

  Definition toBatch7 {A : Type} (B : Type) : T A -> @Batch (W * A) (T B) (T B) :=
    binddt W T T (Batch (W * A) (T B)) A B (batch (T B)).

  Lemma extract_to_runBatch : forall (A X : Type) (j : @Batch A A X),
      extract_Batch j = runBatch (@id A) j.
  Proof.
    intros. induction j.
    - reflexivity.
    - cbn. now rewrite <- IHj.
  Qed.

End with_functor.

#[local] Arguments runBatch {A}%type_scope F%function_scope {B}%type_scope ϕ%function_scope
  {H H0 H1} {X}%type_scope j.

(** ** Expressing <<binddt>> with <<runBatch>> *)
(******************************************************************************)
Section with_monad.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Theorem binddt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G (T B)) (t : T A),
      binddt W T T G A B f t = runBatch G f (toBatch7 W T B t).
  Proof.
    intros.
    unfold toBatch7.
    compose near t on right.
    rewrite (kdtm_morph W T (Batch (W * A) (T B)) G).
    now rewrite (runBatch_batch).
  Qed.

  Theorem bindd_to_runBatch :
    forall (A B : Type) (f : W * A -> T B) (t : T A),
      bindd W T T A B f t =
        runBatch (fun A => A) f (toBatch7 W T B t).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite (binddt_to_runBatch).
    reflexivity.
  Qed.

  Theorem mapdt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G B) (t : T A),
      mapdt W T G A B f t = runBatch G f (toBatch6 W T B t).
  Proof.
    intros. apply (mapdt_to_runBatch W T G).
  Qed.

  Corollary bind_to_runBatch :
    forall (A B : Type) (t : T A)
      (f : A -> T B),
      bind T T A B f t = runBatch (fun A => A) f (toBatch3 T B t).
  Proof.
    intros. rewrite bind_to_bindt.
    now rewrite (bindt_to_runBatch T).
  Qed.

  (*
  Corollary traverse_to_runBatch `{Applicative G} `(f : A -> G B) (t : T A) :
    traverse T G f t = runBatch T G (map G (ret T) ∘ f ∘ extract (W ×)) ( T B t).
  Proof.
    rewrite traverse_to_binddt. now rewrite (binddt_to_runBatch T).
  Qed.

  Theorem mapd_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> B) (t : T A),
      mapd W T A B f t = runBatch (fun A => A) f (toBatch6 W T B t).
  Proof.
    intros.
    change (@Mapd_Binddt W T _ _) with
      (@DerivedInstances.Mapd_Mapdt W T _).
    apply (mapd_to_runBatch W T).
  Qed.

  Theorem map_to_runBatch : forall (A B : Type) (f : A -> B),
      map T f = runBatch (fun A => A) f ∘ toBatch T B.
  Proof.
    intros.
    change (@Map_Binddt W T H0 H) with (@DerivedInstances.Map_Mapdt W T _).
    change (@Traverse_Binddt W T _ _) with (@DerivedInstances.Traverse_Mapdt W T _).
    apply (map_to_runBatch W T).
  Qed.
  *)

End with_monad.

Section foldMapd.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  (** *** Composition with monad operattions *)
  (******************************************************************************)
  Lemma foldMapd_ret (M : Type) `{Monoid M} : forall `(f : W * A -> M),
      foldMapd W T f ∘ ret T A = f ∘ ret (W ×) A.
  Proof.
    intros. unfold foldMapd.
    rewrite (mapdt_to_binddt).
    rewrite (kdtm_binddt0 W T (const M) A False).
    reflexivity.
  Qed.

  Lemma foldMapd_binddt (M : Type) `{Applicative G} `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> G (T B)),
      map G (foldMapd W T g) ∘ binddt W T T G A B f =
        foldMapd W T (fun '(w, a) => map G (foldMapd W T (g ⦿ w)) (f (w, a))).
  Proof.
    intros. unfold foldMapd. unfold_ops @Mapdt_Binddt.
    rewrite (kdtm_binddt2 W T G (const M) A B False).
    fequal.
    - unfold Map_compose.
      ext A' B' f'.
      enough (hyp : map G (map (const M) f') = id).
      + rewrite hyp. reflexivity.
      + ext m. rewrite <- (fun_map_id G).
        reflexivity.
    - ext A' B' [t1 t2]. reflexivity.
  Qed.

  Corollary foldMapd_binddt_I (M : Type) `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd W T g ∘ binddt W T T (fun A => A) A B f =
        foldMapd W T (fun '(w, a) => foldMapd W T (g ⦿ w) (f (w, a))).
  Proof.
    intros. change (foldMapd W T g) with (map (fun A => A) (foldMapd W T g)).
    rewrite (foldMapd_binddt M (G := fun A => A)).
    reflexivity.
  Qed.

  (** *** Composition with lessor operations *)
  (******************************************************************************)
  Lemma foldMapd_bindd (M : Type) `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd W T g ∘ bindd W T T A B f =
        foldMapd W T (fun '(w, a) => foldMapd W T (g ⦿ w) (f (w, a))).
  Proof.
    intros. unfold_ops @Bindd_Binddt.
    change (foldMapd W T g) with (map (fun A => A) (foldMapd W T g)).
    now rewrite (foldMapd_binddt M (G := fun A => A)).
  Qed.

End foldMapd.

















(*
(** * Shape and contents *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import DT.Monad.Derived.

  (** ** Relating <<tolistd>> and <<binddt>> / <<ret>> *)
  (******************************************************************************)
  Lemma tolistd_ret : forall (A : Type) (a : A),
      tolistd T (ret T a) = [ (Ƶ, a) ].
  Proof.
    unfold tolistd.
    intros. compose near a.
    now rewrite (foldMapd_ret T).
  Qed.

  Lemma tolistd_binddt : forall `{Applicative G} `{Monoid M} `(f : W * A -> G (T B)),
      map G (tolistd T) ∘ binddt T G f =
        foldMapd T (fun '(w, a) => map G (foldMapd T (preincr w (ret list))) (f (w, a))).
  Proof.
    intros. unfold tolistd. now rewrite (foldMapd_binddt T).
  Qed.

  (** ** Relating <<tolistd>> and lesser operations *)
  (******************************************************************************)
  Lemma tolistd_bindd : forall `{Monoid M} `(f : W * A -> T B),
      tolistd T ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMapd T (preincr w (ret list)) (f (w, a))).
  Proof.
    intros. unfold_ops @Bindd_Binddt.
    change (@tolistd T _ _ B) with (map (fun A => A) (@tolistd T _ _ B)).
    rewrite (tolistd_binddt (G := fun A => A)).
    reflexivity.
  Qed.

  (** ** Corollaries for the rest *)
  (******************************************************************************)
  Corollary tosetd_ret : forall (A : Type) (a : A),
      tosetd T (ret T a) = {{ (Ƶ, a) }}.
  Proof.
    intros. unfold_ops @Tosetd_Kleisli.
    compose near a.
    now rewrite (foldMapd_ret T).
  Qed.

  Corollary tolist_binddt : forall `{Applicative G} `{Monoid M} `(f : W * A -> G (T B)),
      map G (tolist T) ∘ binddt T G f =
        foldMapd T (map G (tolist T) ∘ f).
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt _ _ _).
    rewrite (tolist_to_tolistd T).
    rewrite <- (fun_map_map G).
    reassociate ->.
    rewrite tolistd_binddt.
    rewrite (foldMapd_morphism T).
    rewrite (fun_map_map G).
    fequal. unfold tolistd.
    ext [w a]. unfold compose at 1 2.
    compose near (f (w, a)) on left.
    rewrite (fun_map_map G).
    rewrite (foldMapd_morphism T).
    rewrite (foldMapd_morphism T).
    fequal. fequal.
    ext [w' b]. reflexivity.
  Qed.

  (** ** Relating <<tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma tolist_bindd : forall `{Monoid M} `(f : W * A -> T B),
      tolist T ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMap T (ret list) (f (w, a))).
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt T W _).
    rewrite (tolist_to_tolistd T).
    reassociate ->. rewrite (tolistd_bindd).
    rewrite (foldMapd_morphism T).
    fequal. ext [w a].
    cbn. compose near (f (w, a)) on left.
    rewrite (foldMapd_morphism T).
    rewrite (foldMap_to_foldMapd T).
    fequal. now ext [w' a'].
  Qed.

End DTM_tolist.

Import Setlike.Functor.Notations.

(** ** Characterizing membership in list operations *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import Derived.

  Lemma ind_iff_in_tolistd : forall (A : Type) (a : A) (w : W) (t : T A),
      (w, a) ∈d t <-> toset list (tolistd T t) (w, a).
  Proof.
    intros. unfold tolistd.
    unfold_ops @Tosetd_Kleisli.
    compose near t on right.
    rewrite (foldMapd_morphism T (ϕ := toset list)).
    replace (@ret set (Return_set) (W * A)) with (toset (A := W * A) list ∘ ret list).
    reflexivity. ext [w' a']. solve_basic_set.
  Qed.

  Lemma in_iff_in_tolist : forall (A : Type) (a : A) (t : T A),
      (a ∈ t) <-> toset list (tolist T t) a.
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt _ _ _).
    rewrite (toset_to_tolist T).
    reflexivity.
  Qed.

End DTM_tolist.





























(** * Characterizing <<∈d>> *)
(******************************************************************************)
Section section.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Existing Instance Toset_set.
  Existing Instance SetlikeFunctor_set.
  Lemma ind_iff_in : forall (A : Type) (a : A) (t : T A),
      a ∈ t <-> exists w, (w, a) ∈d t.
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt T _ _).
    now rewrite (ind_iff_in T).
  Qed.

  Lemma ind_ret_iff : forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret T a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros. unfold_ops @Tosetd_Kleisli.
    compose near a2 on left. rewrite (foldMapd_ret T).
    unfold compose. split.
    now inversion 1.
    inversion 1. subst. solve_basic_set.
  Qed.

  Lemma in_ret_iff : forall {A : Type} (a1 a2 : A),
      a1 ∈ ret T a2 <-> a1 = a2.
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Bindt T _ _).
    now rewrite (in_ret_iff T).
  Qed.

  Lemma ind_bindd_iff1 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd T f t ->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold Tosetd_Kleisli, tosetd, compose in *.
    change (foldMapd T (ret set) (bindd T f t) (wtotal, b))
      with (((foldMapd T (ret set) ∘ bindd T f) t) (wtotal, b)) in hyp.
    rewrite (foldMapd_bindd T) in hyp.
    rewrite (foldMapd_to_runBatch T) in hyp.
    rewrite (foldMapd_to_runBatch T).
    (* HACK: We want to call "rewrite (foldMapd_to_runBatch T)" but
    this fails under the binder. The following is a kludge. *)
    cut (exists (w1 w2 : W) (a : A),
               runBatch (B := False) (F := fun _ => set (W * A))
                 (@ret set Return_set (W * A)) (toBatchd T (A:=A) False t) (w1, a) /\
                 runBatch (B := False) (F := fun _ => set (W * B)) (ret set) (toBatchd T (A:=B) False (f (w1, a))) (w2, b) /\ wtotal = w1 ● w2).
    { intro. preprocess. repeat eexists; try rewrite (foldMapd_to_runBatch T B); eauto. }
    induction (toBatchd T False t).
    - cbv in hyp. inversion hyp.
    - destruct x as [wx ax].
      cbn in hyp. destruct hyp as [hyp | hyp].
      + (* (wtotal, b) in b0 *)
        specialize (IHb0 hyp).
        destruct IHb0 as [w1 [w2 [a [IH_a_in [IH_b_in IH_sum]]]]].
        exists w1 w2 a. split; [now left | auto].
      + (* (wotal, b) in f (wx,ax) *)
        clear IHb0.
        rewrite (foldMapd_to_runBatch T) in hyp.
        assert (lemma : exists w2 : W, runBatch (B := False) (F := fun _ => set (W * B)) (ret set) (toBatchd T False (f (wx, ax))) (w2, b) /\ wtotal = wx ● w2).
        { induction (toBatchd T False (f (wx, ax))).
          - cbv in hyp. inversion hyp.
          - destruct hyp as [hyp|hyp].
            + specialize (IHb1 hyp). destruct IHb1 as [w2 [IHb1' IHb1'']].
              exists w2. split. now left. assumption.
            + destruct x as [wx2 b2]. cbv in hyp. inverts hyp.
              exists wx2. split. now right. reflexivity. }
        destruct lemma as [w2 rest].
        exists wx w2 ax. split. now right. assumption.
  Qed.

  Lemma ind_bindd_iff2 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
    (exists (w1 w2 : W) (a : A),
      (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2) ->
      (wtotal, b) ∈d bindd T f t.
  Proof.
    introv [w1 [w2 [a [a_in [b_in wsum]]]]]. subst.
    unfold tosetd, Tosetd_Kleisli, compose in *.
    compose near t.
    rewrite (foldMapd_bindd T).
    rewrite (foldMapd_to_runBatch T).
    rewrite (foldMapd_to_runBatch T) in a_in.
    rewrite (foldMapd_to_runBatch T) in b_in.
    induction (toBatchd T False t).
    - cbv in a_in. inversion a_in.
    - cbn in a_in. destruct a_in as [a_in | a_in].
      + destruct x as [wx ax].
        specialize (IHb0 a_in b_in).
        left. assumption.
      + clear IHb0. destruct x as [wx ax].
        inverts a_in. right.
        { rewrite (foldMapd_to_runBatch T).
          induction (toBatchd T False (f (w1, a))).
          - inversion b_in.
          - destruct b_in.
            + left. auto.
            + right. destruct x. unfold preincr, compose. cbn.
              inverts H2. easy.
        }
  Qed.

  Theorem ind_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd T f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using ind_bindd_iff1, ind_bindd_iff2.
  Qed.

  Theorem ind_bind_iff :
    forall `(f : A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bind T f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f a
        /\ wtotal = w1 ● w2.
  Proof.
    intros. apply ind_bindd_iff.
  Qed.

  (** ** Characterizing <<∈>> with <<bindd>> *)
  (******************************************************************************)
  Corollary in_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (b : B),
      b ∈ bindd T f t <->
      exists (w1 : W) (a : A),
        (w1, a) ∈d t /\ b ∈ f (w1, a).
  Proof.
    intros.
    rewrite (ind_iff_in).
    setoid_rewrite ind_bindd_iff.
    setoid_rewrite (ind_iff_in).
    split; intros; preprocess; repeat eexists; eauto.
  Qed.

  Corollary in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T f t <-> exists (a : A), a ∈ t /\ b ∈ f a.
  Proof.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt _ _ _).
    intros. setoid_rewrite (ind_iff_in).
    setoid_rewrite (ind_bindd_iff).
    intuition.
    - preprocess. eexists; split; eauto.
    - preprocess. repeat eexists; eauto.
  Qed.

  Theorem in_mapd_iff :
    forall `(f : W * A -> B) (t : T A) (b : B),
      b ∈ mapd T f t <-> exists (w : W) (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt _ _ _).
    rewrite (ind_iff_in).
    setoid_rewrite (ind_mapd_iff T).
    reflexivity.
  Qed.

End section.

(** ** Respectfulness for <<bindd>> *)
(******************************************************************************)
Section bindd_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Theorem bindd_respectful :
    forall A B (t : T A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd T f t = bindd T g t.
  Proof.
    unfold_ops @Tosetd_Kleisli.
    unfold foldMapd in *.
    introv hyp.
    rewrite (mapdt_constant_applicative2 T False B) in hyp.
    unfold mapdt, Mapdt_Binddt in hyp.
    rewrite (binddt_to_runBatch T) in hyp.
    do 2 rewrite (bindd_to_runBatch T).
    induction (toBatchdm T B t).
    - easy.
    - destruct x. do 2 rewrite runBatch_rw2.
      rewrite runBatch_rw2 in hyp.
      fequal.
      + apply IHb. intros. apply hyp.
        cbn. now left.
      + apply hyp. now right.
  Qed.

  (** *** For equalities with special cases *)
  (** Corollaries with conclusions of the form <<bindd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary bindd_respectful_bind :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> bindd T f t = bind T g t.
  Proof.
    introv hyp. rewrite bind_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_mapd :
    forall A B (t : T A) (f : W * A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T (g (w, a)))
      -> bindd T f t = mapd T g t.
  Proof.
    introv hyp. rewrite mapd_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_map :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T (g a))
      -> bindd T f t = map T g t.
  Proof.
    introv hyp. rewrite map_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_id :
    forall A (t : T A) (f : W * A -> T A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T a)
      -> bindd T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (kmond_bindd1 T).
    eapply bindd_respectful.
    unfold compose; cbn. auto.
  Qed.

End bindd_respectful.

(** ** Respectfulness for <<bind>> *)
(******************************************************************************)
Section bind_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma bind_respectful :
    forall A B (t : T A) (f g : A -> T B),
      (forall (a : A), a ∈ t -> f a = g a)
      -> bind T f t = bind T g t.
  Proof.
    introv hyp. rewrite bind_to_bindd.
    apply (bindd_respectful T). introv premise. apply (ind_implies_in T) in premise.
    unfold compose; cbn. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<bind t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary bind_respectful_mapd :
    forall A B (t : T A) (f : A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = ret T (g (w, a)))
      -> bind T f t = mapd T g t.
  Proof.
    intros. rewrite mapd_to_bindd.
    symmetry. apply (bindd_respectful_bind T).
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary bind_respectful_map :
    forall A B (t : T A) (f : A -> T B) (g : A -> B),
      (forall (a : A), a ∈ t -> f a = ret T (g a))
      -> bind T f t = map T g t.
  Proof.
    intros. rewrite map_to_bind.
    symmetry. apply bind_respectful.
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary bind_respectful_id : forall A (t : T A) (f : A -> T A),
      (forall (a : A), a ∈ t -> f a = ret T a)
      -> bind T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (kmon_bind1 T).
    eapply bind_respectful.
    unfold compose; cbn. auto.
  Qed.

End bind_respectful.

(** ** Respectfulness for <<mapd>> *)
(******************************************************************************)
Section mapd_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma mapd_respectful :
    forall A B (t : T A) (f g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> mapd T f t = mapd T g t.
  Proof.
    introv hyp. do 2 rewrite mapd_to_bindd.
    apply (bindd_respectful T). introv premise.
    unfold compose; cbn. fequal. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mapd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mapd_respectful_map :
    forall A (t : T A) (f : W * A -> A) (g : A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> mapd T f t = map T g t.
  Proof.
    intros. rewrite map_to_mapd.
    apply (mapd_respectful). introv Hin.
    unfold compose; cbn; auto.
  Qed.

  Corollary mapd_respectful_id : forall A (t : T A) (f : W * A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = a)
      -> mapd T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (dfun_mapd1 W T).
    eapply (mapd_respectful).
    cbn. auto.
  Qed.

End mapd_respectful.

(** ** Respectfulness for <<map>> *)
(******************************************************************************)
Section map_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma map_respectful :
    forall A B (t : T A) (f g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = g a)
      -> map T f t = map T g t.
  Proof.
    introv hyp. do 2 rewrite map_to_mapd.
    now apply (mapd_respectful T).
  Qed.

  Corollary map_respectful_id :
    forall A (t : T A) (f : A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = a)
      -> map T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (fun_map_id T).
    eapply (map_respectful).
    auto.
  Qed.

End map_respectful.
*)