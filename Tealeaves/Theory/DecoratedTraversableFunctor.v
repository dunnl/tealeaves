From Tealeaves Require Export
  Functors.Batch
  Classes.Kleisli.DecoratedTraversableFunctor
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Theory.TraversableFunctor.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.

#[local] Generalizable Variables M E T G A B C ϕ.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.

(** * Theory of decorated traversable functors *)
(******************************************************************************)
Section traversable_functor_theory.

  Context
    `{DecoratedTraversableFunctorFull E T}.

  (** ** Constant applicative functors *)
  (******************************************************************************)
  Section constant.

    Context
      `{Monoid M}.

    Lemma mapdt_constant_applicative1 {A B : Type}
      `(f : E * A -> const M B) :
      mapdt (G := const M) f =
        mapdt (G := const M) (B := False) f.
    Proof.
      change_right (map (F := const M) (A := T False) (B := T B)
                      (map (F := T) (@exfalso B))
                      ∘ mapdt (G := const M) (B := False) f).
      rewrite map_mapdt.
      reflexivity.
    Qed.

    Lemma mapdt_constant_applicative2 (B fake1 fake2 : Type)
      `(f : E * A -> const M B) :
      mapdt (G := const M) (B := fake1) f =
        mapdt (G := const M) (B := fake2) f.
    Proof.
      intros.
      rewrite (mapdt_constant_applicative1 (B := fake1)).
      rewrite (mapdt_constant_applicative1 (B := fake2)).
      easy.
    Qed.

  End constant.

  (** ** Expressing <<binddt>> with <<runBatch>> *)
  (******************************************************************************)
  Theorem mapdt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : E * A -> G B),
      mapdt f = runBatch f ∘ toBatch6.
  Proof.
    intros. unfold_ops @ToBatch6_Mapdt.
    rewrite <- (kdtfun_morph).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse f = runBatch (f ∘ extract (W := (E ×))) ∘ toBatch6.
  Proof.
    rewrite kdtfunf_traverse_to_mapdt.
    rewrite (mapdt_to_runBatch).
    reflexivity.
  Qed.

  Corollary mapd_to_runBatch `(f : E * A -> B) :
      mapd f = runBatch (F := fun A => A) f ∘ toBatch6.
  Proof.
    intros.
    rewrite (kdtfunf_mapd_to_mapdt).
    rewrite (mapdt_to_runBatch).
    reflexivity.
  Qed.

  Corollary map_to_runBatch : forall `(f : A -> B),
      map f = runBatch (F := fun A => A) (f ∘ extract) ∘ toBatch6.
  Proof.
    intros.
    rewrite (kdtfunf_map_to_mapdt).
    rewrite (mapdt_to_runBatch).
    reflexivity.
  Qed.

  (** ** The <<foldmapd>> operation *)
  (******************************************************************************)
  Definition foldMapd {T : Type -> Type} `{Mapdt E T} `{op : Monoid_op M} `{unit : Monoid_unit M}
    {A : Type} (f : E * A -> M) : T A -> M := mapdt (G := const M) (B := False) f.

  (** *** As a generalization of <<foldMap>> *)
  (******************************************************************************)
  Lemma foldMap_to_foldMapd :  forall `{Monoid M} `(f : A -> M),
      foldMap (T := T) f = foldMapd (T := T) (f ∘ extract).
  Proof.
    intros.
    rewrite (foldMap_to_traverse1 M).
    rewrite (kdtfunf_traverse_to_mapdt).
    reflexivity.
  Qed.

  (** *** As a special case of <<traverse>> *)
  (******************************************************************************)
  Lemma foldMapd_to_mapdt1 (M : Type) `{Monoid M} : forall `(f : E * A -> M),
      foldMapd (T := T) f = mapdt (G := const M) (B := False) f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_to_mapdt2 (M : Type) `{Monoid M} : forall (fake : Type) `(f : E * A -> M),
      foldMapd f = mapdt (G := const M) (B := fake) f.
  Proof.
    intros.
    rewrite (foldMapd_to_mapdt1 M).
    rewrite (mapdt_constant_applicative1 (B := fake) f).
    reflexivity.
  Qed.

  (** *** As a special case of <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMapd_to_runBatch1 (A : Type) `{Monoid M} : forall `(f : E * A -> M),
      foldMapd f = runBatch (F := const M) f (C := T False) ∘ toBatch6 (B := False).
  Proof.
    intros.
    rewrite (foldMapd_to_mapdt1 M).
    rewrite (mapdt_to_runBatch (G := const M)).
    reflexivity.
  Qed.

  Lemma foldMapd_to_runBatch2 `{Monoid M} : forall (A fake : Type) `(f : E * A -> M),
      foldMapd f = runBatch (F := const M) f (C := T fake) ∘ toBatch6 (B := fake).
  Proof.
    intros.
    rewrite (foldMapd_to_mapdt1 M).
    rewrite (mapdt_constant_applicative2 False False fake).
    rewrite (mapdt_to_runBatch).
    reflexivity.
  Qed.

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma foldMapd_mapd `{Monoid M} {B : Type} :
    forall `(g : E * B -> M) `(f : E * A -> B),
      foldMapd g ∘ mapd f = foldMapd (g ∘ cobind f).
  Proof.
    intros.
    rewrite (foldMapd_to_mapdt1 M).
    rewrite (mapdt_mapd (E := E) (T := T) g f).
    reflexivity.
  Qed.

  (** *** Composition with <<map>> *)
  (******************************************************************************)
  Corollary foldMapd_map `{Monoid M} : forall `(g : E * B -> M) `(f : A -> B),
      foldMapd g ∘ map f = foldMapd (g ∘ map (F := prod E) f).
  Proof.
    intros.
    rewrite (kdtfunf_map_to_mapdt).
    replace (mapdt (G := fun A => A) (f ∘ extract)) with (mapd (f ∘ extract)).
    - rewrite (foldMapd_mapd).
      reflexivity.
    - rewrite (kdtfunf_mapd_to_mapdt).
      reflexivity.
  Qed.

  (** *** Homomorphism law *)
  (******************************************************************************)
  Lemma foldMapd_morphism (M1 M2 : Type) `{morphism : Monoid_Morphism M1 M2 ϕ} : forall `(f : E * A -> M1),
      ϕ ∘ foldMapd f = foldMapd (ϕ ∘ f).
  Proof.
    intros.
    inversion morphism.
    rewrite (foldMapd_to_mapdt1 M1).
    change ϕ with (const ϕ (T False)).
    rewrite <- (kdtfun_morph (G1 := const M1) (G2 := const M2)).
    reflexivity.
  Qed.

  (** ** The <<tolistd>> operation *)
  (******************************************************************************)
  Section tolist.

    Class Tolistd (E : Type) (F : Type -> Type) :=
      tolistd : forall A : Type, F A -> list (E * A).

    #[global] Arguments tolistd {E}%type_scope {F}%function_scope
      {Tolistd} {A}%type_scope _.

    #[export] Instance Tolistd_Mapdt : Tolistd E T :=
    fun A => foldMapd (ret (T := list)).

    #[export] Instance Natural_Tolistd_Mapdt : Natural (@tolistd E T _).
    Proof.
      constructor; try typeclasses eauto.
      intros. unfold_ops @Tolistd_Mapdt.
      rewrite (foldMapd_morphism (list (E * A)) (list (E * B))).
      rewrite foldMapd_map.
      unfold_ops @Map_compose.
      rewrite (natural (ϕ := @ret list _)).
      reflexivity.
    Qed.

    Lemma foldMapd_list_eq `{Monoid M} : forall (A : Type) (f : E * A -> M),
        foldMapd f = List.foldMap f ∘ tolistd.
    Proof.
      intros. unfold_ops @Tolistd_Mapdt. unfold foldMapd.
      rewrite <- (kdtfun_morph (ϕ := fun A => List.foldMap f)).
      rewrite foldMap_list_ret.
      reflexivity.
    Qed.

    Lemma tolistd_to_foldMapd : forall (A : Type),
        tolistd (F := T) = foldMapd (ret (T := list) (A := E * A)).
    Proof.
      reflexivity.
    Qed.

    Corollary tolistd_to_mapdt1 : forall (A : Type),
        tolistd = mapdt (G := const (list (E * A))) (B := False) (ret (T := list)).
    Proof.
      reflexivity.
    Qed.

    Corollary tolistd_to_mapdt2 : forall (A fake : Type),
        tolistd = mapdt (G := const (list (E * A))) (B := fake) (ret (T := list)).
    Proof.
      intros.
      rewrite tolistd_to_mapdt1.
      rewrite (mapdt_constant_applicative1 (B := fake)).
      reflexivity.
    Qed.

    Corollary tolistd_to_runBatch6 {A : Type} (tag : Type) :
      tolistd = runBatch (B := tag) (F := const (list (E * A)))
                  (ret (T := list)) ∘ toBatch6.
    Proof.
      rewrite (tolistd_to_mapdt2 A tag).
      now rewrite (mapdt_to_runBatch).
    Qed.

  End tolist.

  (** ** Relating <<tolistd>> and lesser operations *)
  (******************************************************************************)
  Lemma tolistd_mapd : forall `(f : E * A -> B),
      tolistd (F := T) ∘ mapd f = foldMapd (ret (T := list) ∘ cobind f).
  Proof.
    intros.
    rewrite tolistd_to_foldMapd.
    rewrite foldMapd_mapd.
    reflexivity.
  Qed.

  Lemma tolistd_map : forall `(f : A -> B),
      tolistd (F := T) ∘ map f = foldMapd (ret (T := list) ∘ map (F := (E ×)) f).
  Proof.
    intros.
    rewrite tolistd_to_foldMapd.
    rewrite foldMapd_map.
    reflexivity.
  Qed.

  (** ** Relating <<tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma tolist_mapd : forall `(f : E * A -> B),
      tolist ∘ mapd f = foldMapd (ret (T := list) ∘ f).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_mapd.
    reassociate -> on left.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  (** ** The <<∈d>> operation *)
  (******************************************************************************)
  Section toset.

    Class Elementsd (E : Type) (F : Type -> Type) :=
      elementsd : forall A : Type, F A -> subset (E * A).

    #[global] Arguments elementsd {E}%type_scope {F}%function_scope
      {Elementsd} {A}%type_scope _.

    #[export] Instance Elementd_Mapdt : Elementsd E T :=
      fun A => foldMapd (ret (T := subset)).

    #[export] Instance Elementd_Mapdt : Elementsd E T :=
      fun A => foldMapd (ret (T := subset)).

    #[export] Instance Natural_Tolistd_Mapdt : Natural (@tolistd E T _).
    Proof.
      constructor; try typeclasses eauto.
      intros. unfold_ops @Tolistd_Mapdt.
      rewrite (foldMapd_morphism (list (E * A)) (list (E * B))).
      rewrite foldMapd_map.
      unfold_ops @Map_compose.
      rewrite (natural (ϕ := @ret list _)).
      reflexivity.
    Qed.

    Lemma foldMapd_list_eq `{Monoid M} : forall (A : Type) (f : E * A -> M),
        foldMapd f = List.foldMap f ∘ tolistd.
    Proof.
      intros. unfold_ops @Tolistd_Mapdt. unfold foldMapd.
      rewrite <- (kdtfun_morph (ϕ := fun A => List.foldMap f)).
      rewrite foldMap_list_ret.
      reflexivity.
    Qed.

    Lemma tolistd_to_foldMapd : forall (A : Type),
        tolistd (F := T) = foldMapd (ret (T := list) (A := E * A)).
    Proof.
      reflexivity.
    Qed.

    Corollary tolistd_to_mapdt1 : forall (A : Type),
        tolistd = mapdt (G := const (list (E * A))) (B := False) (ret (T := list)).
    Proof.
      reflexivity.
    Qed.

    Corollary tolistd_to_mapdt2 : forall (A fake : Type),
        tolistd = mapdt (G := const (list (E * A))) (B := fake) (ret (T := list)).
    Proof.
      intros.
      rewrite tolistd_to_mapdt1.
      rewrite (mapdt_constant_applicative1 (B := fake)).
      reflexivity.
    Qed.

    Corollary tolistd_to_runBatch6 {A : Type} (tag : Type) :
      tolistd = runBatch (B := tag) (F := const (list (E * A)))
                  (ret (T := list)) ∘ toBatch6.
    Proof.
      rewrite (tolistd_to_mapdt2 A tag).
      now rewrite (mapdt_to_runBatch).
    Qed.

  End tolist.

  (** ** Relating <<tolistd>> and lesser operations *)
  (******************************************************************************)
  Lemma tolistd_mapd : forall `(f : E * A -> B),
      tolistd (F := T) ∘ mapd f = foldMapd (ret (T := list) ∘ cobind f).
  Proof.
    intros.
    rewrite tolistd_to_foldMapd.
    rewrite foldMapd_mapd.
    reflexivity.
  Qed.

  Lemma tolistd_map : forall `(f : A -> B),
      tolistd (F := T) ∘ map f = foldMapd (ret (T := list) ∘ map (F := (E ×)) f).
  Proof.
    intros.
    rewrite tolistd_to_foldMapd.
    rewrite foldMapd_map.
    reflexivity.
  Qed.

  (** ** Relating <<tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma tolist_mapd : forall `(f : E * A -> B),
      tolist ∘ mapd f = foldMapd (ret (T := list) ∘ f).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_mapd.
    reassociate -> on left.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

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
      replace (@ret set Return_set (W * A)) with (el list _ ∘ ret list (W * A)).
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
    setoid_rewrite ind_ret_iff.
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
    rewrite ind_iff_in.
    setoid_rewrite ind_bindd_iff.
    setoid_rewrite ind_iff_in.
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
    induction (toBatch7 W T B t).
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
