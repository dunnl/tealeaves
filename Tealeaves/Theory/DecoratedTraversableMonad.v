From Tealeaves Require Export
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Adapters.KleisliToCoalgebraic.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedContainerFunctor
  Theory.DecoratedTraversableFunctor.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variables M W T G A B C.

(* HACK get rid of me after making *-Full typeclass *)
Import DecoratedTraversableMonad.DerivedInstances.

#[local] Arguments binddt {W}%type_scope {U} {T}%function_scope
  {Binddt} {G}%function_scope {H H0 H1} {A B}%type_scope.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.

(** * Lemmas for particular applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}.

  (** ** <<binddt>> with constant applicative functors *)
  (******************************************************************************)
  Section constant_applicative.

    Context `{Monoid M}.

    Lemma binddt_constant_applicative1 {A B : Type}
      `(f : W * A -> const M (T B)) :
      binddt (U := T) f = binddt (U := T) (B := False) f.
    Proof.
      change_right (map (F := const M) (A := T False) (B := T B)
                      (map (F := T) (A := False) (B := B) exfalso)
                      ∘ binddt (U := T) (B := False) f).
      rewrite (map_binddt W T (G1 := const M)).
      reflexivity.
    Qed.

    Lemma binddt_constant_applicative2 (fake1 fake2 : Type)
      `(f : W * A -> const M (T B)) :
      binddt (U := T) (B := fake1) f = binddt (U := T) (B := fake2) f.
    Proof.
      intros.
      rewrite (binddt_constant_applicative1 (B := fake1)).
      rewrite (binddt_constant_applicative1 (B := fake2)).
      reflexivity.
    Qed.

  End constant_applicative.

  (** ** Expressing <<binddt>> with <<runBatch>> *)
  (******************************************************************************)
  Theorem binddt_through_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G (T B)),
      binddt f = runBatch f ∘ toBatchDM.
  Proof.
    intros.
    unfold_ops @ToBatchDM_Binddt.
    rewrite (kdtm_morph (Batch (W * A) (T B)) G).
    rewrite (runBatch_batch G). (* TODO get rid of G argument *)
    reflexivity.
  Qed.

  Theorem bindd_through_runBatch :
    forall (A B : Type) (f : W * A -> T B),
      bindd f = runBatch (F := fun A => A) f ∘ toBatchDM.
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  (*
  Corollary bind_through_runBatch :
    forall (A B : Type) (t : T A)
      (f : A -> T B),
      bind f = runBatch (F := fun A => A) f ∘ toBatchM T A B.
  Proof.
    intros.
    rewrite bind_to_bindt.
    rewrite bindt_to_runBatch. (* TODO rename *)
    reflexivity.
  Qed.

  Corollary traverse_through_runBatch `{Applicative G} `(f : A -> G B) (t : T A) :
    traverse T G A B f t = runBatch G (map G (ret T B) ∘ f ∘ extract (W ×) A) (toBatchDM W T B t).
  Proof.
    rewrite traverse_through_binddt.
    rewrite (binddt_through_runBatch).
    reflexivity.
  Qed.

  Theorem mapd_through_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> B) (t : T A),
      mapd W T A B f t = runBatch (fun A => A) f (toBatch6 W T B t).
  Proof.
    intros.
    change (@Mapd_Binddt W T _ _) with
      (@DerivedInstances.Mapd_Mapdt W T _).
    apply (mapd_through_runBatch W T).
  Qed.

  Theorem map_through_runBatch : forall (A B : Type) (f : A -> B),
      map T f = runBatch (fun A => A) f ∘ toBatch T B.
  Proof.
    intros.
    change (@Map_Binddt W T H0 H) with (@DerivedInstances.Map_Mapdt W T _).
    change (@Traverse_Binddt W T _ _) with (@DerivedInstances.Traverse_Mapdt W T _).
    apply (map_through_runBatch W T).
  Qed.
   *)

  (** ** Properties of <<foldMapd>> *)
  (******************************************************************************)
  Section foldMapd.

    (** *** Composition with monad operattions *)
    (******************************************************************************)
    Lemma foldMapd_ret `{Monoid M} : forall `(f : W * A -> M),
        foldMapd (T := T) f ∘ ret = f ∘ ret.
    Proof.
      intros.
      rewrite (foldMapd_to_mapdt1 M). (* TODO get rid of this argument *)
      rewrite mapdt_to_binddt.
      rewrite (kdtm_binddt0 (G := const M) A False). (* TODO arguments *)
      reflexivity.
    Qed.

    Lemma foldMapd_binddt (M : Type) `{Applicative G} `{Monoid M} :
      forall `(g : W * B -> M) `(f : W * A -> G (T B)),
        map (foldMapd g) ∘ binddt f =
          foldMapd (fun '(w, a) => map (foldMapd (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite (foldMapd_to_mapdt1 M).
      rewrite mapdt_to_binddt.
      rewrite (kdtm_binddt2 (G2 := const M) (G1 := G) A B False). (* TODO args *)
      rewrite (foldMapd_to_mapdt1 (G M)).
      rewrite mapdt_to_binddt.
      rewrite binddt_app_const_r.
      reflexivity.
    Qed.

    Corollary foldMapd_binddt_I (M : Type) `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
        foldMapd g ∘ binddt (T := T) (G := fun A => A) f =
          foldMapd (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      change (foldMapd g) with (map (F := fun A => A) (foldMapd (T := T) g)).
      rewrite (foldMapd_binddt M (G := fun A => A)).
      reflexivity.
    Qed.

    (** *** Composition with lessor operations *)
    (******************************************************************************)
    Lemma foldMapd_bindd (M : Type) `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
        foldMapd g ∘ bindd f =
          foldMapd (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      unfold_ops @Bindd_Binddt.
      change (foldMapd g) with (map (F := fun A => A) (foldMapd (T := T) g)).
      rewrite (foldMapd_binddt M (G := fun A => A)).
      reflexivity.
    Qed.

  End foldMapd.

  (** * Shape and contents *)
  (******************************************************************************)
  Section DTM_tolist.

  (** ** Relating <<tolistd>> and <<binddt>> / <<ret>> *)
  (******************************************************************************)
  Lemma ctx_tolist_ret : forall (A : Type) (a : A),
      ctx_tolist (ret (T := T) a) = [ (Ƶ, a) ].
  Proof.
    intros.
    unfold_ops @CtxTolist_Mapdt.
    compose near a.
    rewrite foldMapd_ret.
    reflexivity.
  Qed.

  Lemma ctx_tolist_binddt : forall `{Applicative G} `(f : W * A -> G (T B)),
      map (F := G) ctx_tolist ∘ binddt (G := G) f =
        foldMapd (T := T) (fun '(w, a) => map (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
  Proof.
    intros.
    unfold_ops @CtxTolist_Mapdt.
    rewrite (foldMapd_binddt (list (W * B))).
    reflexivity.
  Qed.

  (** ** Relating <<ctx_tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma ctx_tolist_bindd : forall `(f : W * A -> T B),
      ctx_tolist ∘ bindd f =
        foldMapd (T := T) (fun '(w, a) => (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    change (ctx_tolist (E := W) (A := ?A)) with
      (map (F := fun A => A) (ctx_tolist (F := T) (A := A))).
    rewrite (ctx_tolist_binddt (G := fun A => A)).
    reflexivity.
  Qed.

  (** ** Corollaries for the rest *)
  (******************************************************************************)
  Corollary tosetd_ret : forall (A : Type) (a : A),
      ctx_element_of (ret (T := T) a) = {{ (Ƶ, a) }}.
  Proof.
    intros.
    unfold_ops @CtxElements_CtxTolist.
    unfold compose.
    rewrite ctx_tolist_ret.
    cbv. solve_basic_subset.
  Qed.

  Corollary tolist_binddt : forall `{Applicative G} `(f : W * A -> G (T B)),
      map G (tolist T B) ∘ binddt W T T G A B f =
        foldMapd W T (map G (tolist T B) ∘ f).
  Proof.
    intros.
    change (@Traverse_Binddt W T _ _)
      with (@DerivedInstances.Traverse_Mapdt _ _ _).
    rewrite (tolist_to_ctx_tolist W T).
    rewrite <- (fun_map_map G).
    reassociate ->.
    rewrite tolistd_binddt.
    rewrite (foldMapd_morphism W T).
    rewrite (fun_map_map G).
    fequal. unfold tolistd.
    ext [w a]. unfold compose at 1 2.
    compose near (f (w, a)) on left.
    rewrite (fun_map_map G).
    rewrite (foldMapd_morphism W T).
    rewrite (foldMapd_morphism W T).
    fequal. fequal.
    ext [w' b]. reflexivity.
  Qed.

  (** ** Relating <<tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma tolist_bindd : forall `(f : W * A -> T B),
      tolist T B ∘ bindd W T T A B f =
        foldMapd W T (fun '(w, a) => foldMap T (ret list B) (f (w, a))).
  Proof.
    intros.
    change (@Traverse_Binddt W T _ _)
      with (@DerivedInstances.Traverse_Mapdt W T _).
    rewrite (tolist_to_tolistd W T).
    reassociate ->. rewrite (tolistd_bindd).
    rewrite (foldMapd_morphism W T).
    fequal. ext [w a].
    cbn. compose near (f (w, a)) on left.
    rewrite (foldMapd_morphism W T).
    rewrite (foldMap_to_foldMapd W T).
    fequal. now ext [w' a'].
  Qed.

End DTM_tolist.

(** ** Characterizing membership in list operations *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Import DerivedInstances.

  Lemma ind_iff_in_tolistd : forall (A : Type) (a : A) (w : W) (t : T A),
      (w, a) ∈d t <-> el list (W * A) (tolistd W T t) (w, a).
  Proof.
    intros. unfold tolistd.
    unfold_ops @Tosetd_DTF.
    compose near t on right.
    rewrite (foldMapd_morphism W T (ϕ := el list _)).
    replace (@ret set (Return_set) (W * A)) with (el list _ ∘ ret list (W * A)).
    reflexivity. ext [w' a']. solve_basic_set.
  Qed.

  Lemma in_iff_in_tolist : forall (A : Type) (a : A) (t : T A),
      (a ∈ t) <-> el list A (tolist T A t) a.
  Proof.
    intros.
    change (@Traverse_Binddt W T _ _)
      with (@DerivedInstances.Traverse_Mapdt _ _ _).
    rewrite (toset_to_tolist T).
    reflexivity.
  Qed.

End DTM_tolist.

(** * Characterizing <<∈d>> *)
(******************************************************************************)
Section section.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Import DT.Monad.DerivedInstances.

  Lemma ind_iff_in : forall (A : Type) (a : A) (t : T A),
      a ∈ t <-> exists w, (w, a) ∈d t.
  Proof.
    intros.
    change (@Traverse_Binddt W T _ _)
      with (@DerivedInstances.Traverse_Mapdt W T _).
    rewrite (ind_iff_in W T).
    reflexivity.
  Qed.

  Lemma ind_ret_iff : forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret T A a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros. unfold_ops @Tosetd_DTF.
    compose near a2 on left. rewrite (foldMapd_ret W T _).
    unfold compose. split.
    now inversion 1.
    inversion 1. subst. solve_basic_set.
  Qed.

  Lemma in_ret_iff : forall {A : Type} (a1 a2 : A),
      a1 ∈ ret T A a2 <-> a1 = a2.
  Proof.
    intros.
    change (@Traverse_Binddt W T _ _)
      with (@DerivedInstances.Traverse_Bindt T _ _).
    now rewrite (in_ret_iff T).
  Qed.

  Lemma ind_bindd_iff1 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd W T T A B f t ->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold Tosetd_DTF, el_ctx, compose in *.
    change (foldMapd W T (ret set (W * B)) (bindd W T T A B f t) (wtotal, b))
      with (((foldMapd W T (ret set _) ∘ bindd W T T A B f) t) (wtotal, b)) in hyp.
    rewrite (foldMapd_bindd W T _) in hyp.
    rewrite (foldMapd_to_runBatch W T _) in hyp.
    rewrite (foldMapd_to_runBatch W T _).
    (* HACK: We want to call "rewrite (foldMapd_to_runBatch T)" but
    this fails under the binder. The following is a kludge. *)
    cut (exists (w1 w2 : W) (a : A),
               runBatch (B := False) (fun _ => set (W * A))
                 (@ret set Return_set (W * A)) (toBatch6 W T False t) (w1, a) /\
                 runBatch (B := False) (fun _ => set (W * B)) (ret set _) (toBatch6 W T False (f (w1, a))) (w2, b) /\ wtotal = w1 ● w2).
    { intro. preprocess. repeat eexists; try rewrite (foldMapd_to_runBatch W T B _); eauto. }
    induction (toBatch6 W T False t).
    - cbv in hyp. inversion hyp.
    - destruct x as [wx ax].
      cbn in hyp. destruct hyp as [hyp | hyp].
      + (* (wtotal, b) in b0 *)
        specialize (IHb0 hyp).
        destruct IHb0 as [w1 [w2 [a [IH_a_in [IH_b_in IH_sum]]]]].
        exists w1 w2 a. split; [now left | auto].
      + (* (wotal, b) in f (wx,ax) *)
        clear IHb0.
        rewrite (foldMapd_to_runBatch W T) in hyp.
        assert (lemma : exists w2 : W, runBatch (B := False) (fun _ => set (W * B)) (ret set _) (toBatch6 W T False (f (wx, ax))) (w2, b) /\ wtotal = wx ● w2).
        { induction (toBatch6 W T False (f (wx, ax))).
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
      (wtotal, b) ∈d bindd W T T A B f t.
  Proof.
    introv [w1 [w2 [a [a_in [b_in wsum]]]]]. subst.
    unfold el_ctx, Tosetd_DTF, compose in *.
    compose near t.
    rewrite (foldMapd_bindd W T _).
    rewrite (foldMapd_to_runBatch W T _).
    rewrite (foldMapd_to_runBatch W T _) in a_in.
    rewrite (foldMapd_to_runBatch W T _) in b_in.
    induction (toBatch6 W T False t).
    - cbv in a_in. inversion a_in.
    - cbn in a_in. destruct a_in as [a_in | a_in].
      + destruct x as [wx ax].
        specialize (IHb0 a_in b_in).
        left. assumption.
      + clear IHb0. destruct x as [wx ax].
        inverts a_in. right.
        { rewrite (foldMapd_to_runBatch W T).
          induction (toBatch6 W T False (f (w1, a))).
          - inversion b_in.
          - destruct b_in.
            + left. auto.
            + right. destruct x. unfold preincr, compose. cbn.
              inverts H2. easy.
        }
  Qed.

  Theorem ind_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd W T T A B f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using ind_bindd_iff1, ind_bindd_iff2.
  Qed.

  Corollary ind_bind_iff :
    forall `(f : A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bind T T A B f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f a
        /\ wtotal = w1 ● w2.
  Proof.
    intros. apply ind_bindd_iff.
  Qed.

  (** ** Characterizing <<∈d>> *)
  (******************************************************************************)
  Theorem ind_mapd_iff :
    forall `(f : W * A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d mapd W T A B f t <-> exists (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros.
    rewrite (mapd_to_bindd W T).
    unfold compose.
    rewrite ind_bindd_iff.
    setoid_rewrite (ind_ret_iff).
    split.
    - intros [w1 [w2 [a [h1 [h2 h3]]]]].
      destruct h2 as [hz heq].
      subst. simpl_monoid.
      eauto.
    - intros [a [h1 h2]].
      subst.
      exists w Ƶ a. simpl_monoid. auto.
  Qed.

  Corollary ind_map_iff :
    forall `(f : A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d map T f t <-> exists (a : A), (w, a) ∈d t /\ f a = b.
  Proof.
    intros. change_left ((w, b) ∈d mapd W T A B (f ∘ extract (prod W) A) t).
    rewrite ind_mapd_iff.
    unfold compose. cbn. splits; eauto.
  Qed.

  (** ** Characterizing <<∈>> with <<bindd>> *)
  (******************************************************************************)
  Corollary in_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (b : B),
      b ∈ bindd W T T A B f t <->
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
      b ∈ bind T T A B f t <-> exists (a : A), a ∈ t /\ b ∈ f a.
  Proof.
    change (@Traverse_Binddt W T _ _)
      with (@DerivedInstances.Traverse_Mapdt _ _ _).
    intros. setoid_rewrite (ind_iff_in).
    setoid_rewrite (ind_bindd_iff).
    intuition.
    - preprocess. eexists; split; eauto.
    - preprocess. repeat eexists; eauto.
  Qed.

  Theorem in_mapd_iff :
    forall `(f : W * A -> B) (t : T A) (b : B),
      b ∈ mapd W T A B f t <-> exists (w : W) (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros.
    change (@Traverse_Binddt W T _ _)
      with (@DerivedInstances.Traverse_Mapdt _ _ _).
    rewrite (ind_iff_in).
    change (@Mapd_Binddt W T _ _)
      with (@DerivedInstances.Mapd_Mapdt _ _ _).
    setoid_rewrite (ind_mapd_iff).
    reflexivity.
  Qed.

End section.

(** ** Respectfulness for <<bindd>> *)
(******************************************************************************)
Section bindd_respectful.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Import DT.Monad.DerivedInstances.

  Theorem bindd_respectful :
    forall A B (t : T A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd W T T A B f t = bindd W T T A B g t.
  Proof.
    unfold_ops @Tosetd_DTF.
    unfold foldMapd in *.
    introv hyp.
    rewrite (mapdt_constant_applicative2 W T False B) in hyp.
    unfold mapdt, Mapdt_Binddt in hyp.
    rewrite (binddt_to_runBatch W T) in hyp.
    do 2 rewrite (bindd_to_runBatch W T).
    induction (toBatchDM W T B t).
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
      -> bindd W T T A B f t = bind T T A B g t.
  Proof.
    introv hyp. rewrite bind_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_mapd :
    forall A B (t : T A) (f : W * A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T _ (g (w, a)))
      -> bindd W T T A B f t = mapd W T A B g t.
  Proof.
    introv hyp. rewrite mapd_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_map :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T _ (g a))
      -> bindd W T T A B f t = map T g t.
  Proof.
    introv hyp. rewrite map_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_id :
    forall A (t : T A) (f : W * A -> T A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T _ a)
      -> bindd W T T A A f t = t.
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
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Import DT.Monad.DerivedInstances.

  Lemma bind_respectful :
    forall A B (t : T A) (f g : A -> T B),
      (forall (a : A), a ∈ t -> f a = g a)
      -> bind T T A B f t = bind T T A B g t.
  Proof.
    introv hyp.
    rewrite (bind_to_bindd W T).
    apply (bindd_respectful W T). introv premise. apply (ind_implies_in W T) in premise.
    unfold compose; cbn. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<bind t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary bind_respectful_mapd :
    forall A B (t : T A) (f : A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = ret T _ (g (w, a)))
      -> bind T T A B f t = mapd W T A B g t.
  Proof.
    intros. rewrite mapd_to_bindd.
    symmetry. apply (bindd_respectful_bind W T).
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary bind_respectful_map :
    forall A B (t : T A) (f : A -> T B) (g : A -> B),
      (forall (a : A), a ∈ t -> f a = ret T _ (g a))
      -> bind T T A B f t = map T g t.
  Proof.
    intros. rewrite map_to_bind.
    symmetry. apply bind_respectful.
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary bind_respectful_id : forall A (t : T A) (f : A -> T A),
      (forall (a : A), a ∈ t -> f a = ret T _ a)
      -> bind T T A A f t = t.
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
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Import DT.Monad.DerivedInstances.

  Lemma mapd_respectful :
    forall A B (t : T A) (f g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> mapd W T A B f t = mapd W T A B g t.
  Proof.
    introv hyp. do 2 rewrite mapd_to_bindd.
    apply (bindd_respectful W T). introv premise.
    unfold compose; cbn. fequal. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mapd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mapd_respectful_map :
    forall A B (t : T A) (f : W * A -> B) (g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> mapd W T A B f t = map T g t.
  Proof.
    intros. rewrite map_to_mapd.
    apply (mapd_respectful). introv Hin.
    unfold compose; cbn; auto.
  Qed.

  Corollary mapd_respectful_id : forall A (t : T A) (f : W * A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = a)
      -> mapd W T A A f t = t.
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
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Import DT.Monad.DerivedInstances.

  Lemma map_respectful :
    forall A B (t : T A) (f g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = g a)
      -> map T f t = map T g t.
  Proof.
    introv hyp. do 2 rewrite map_to_mapd.
    now apply (mapd_respectful W T).
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
