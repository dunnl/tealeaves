From Tealeaves Require Export
  Classes.DT.Functor
  Theory.Traversable.Functor
  Functors.Sets.

#[local] Generalizable Variables T G A B C ϕ M.

Import Strength.Notations.
Import Product.Notations.
Import Traversable.Functor.Notations.
Import Sets.Notations.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments traverse T%function_scope {Traverse} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments bind (T)%function_scope {U}%function_scope {Bind} {A B}%type_scope _%function_scope _.
#[local] Arguments mapdt  {M}%type_scope T%function_scope   {Mapdt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

Import DT.Functor.DerivedInstances.

(** * Batch *)
(******************************************************************************)
Section with_functor.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}.

  Lemma runBatch_batch3 : forall `{Applicative G} (A B : Type) (f : W * A -> G B),
      runBatch f ∘ (@batch (W * A) B) = f.
  Proof.
    intros. apply (runBatch_batch G).
  Qed.

  Definition toBatch6 {A : Type} (B : Type) : T A -> @Batch (W * A) B (T B) :=
    mapdt T (Batch (W * A) B) A B (batch B).

  (** ** Expressing operations with <<runBatch>> *)
  (******************************************************************************)

  (** *** <<mapdt>> *)
  (******************************************************************************)
  Theorem mapdt_to_runBatch :
    forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : W * A -> G B) (t : T A),
      mapdt T G A B f t = runBatch f (toBatch6 B t).
  Proof.
    intros. unfold toBatch6.
    compose near t on right.
    rewrite <- (kdtfun_morph W T).
    now rewrite runBatch_batch.
  Qed.

  (** *** <<mapd>> *)
  (******************************************************************************)
  Theorem mapd_to_runBatch :
    forall (A B : Type) (f : W * A -> B) (t : T A),
      mapd W T A B f t = runBatch (F := fun A => A) f (toBatch6 B t).
  Proof.
    intros. unfold toBatch6.
    compose near t on right.
    rewrite <- (kdtfun_morph W T (G1 := Batch (prod W A) B) (G2 := fun A => A)).
    reflexivity.
  Qed.

  (** *** <<mapd>> *)
  (******************************************************************************)
  Theorem traverse_to_runBatch :
    forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G B) (t : T A),
      traverse T G f t = runBatch f (toBatch T B t).
  Proof.
    intros. now rewrite (traverse_to_runBatch T G).
  Qed.

  (** *** <<map>> *)
  (******************************************************************************)
  Theorem map_to_runBatch :
    forall (A B : Type) (f : A -> B),
      map T f = runBatch f ∘ toBatch T B.
  Proof.
    intros. ext t. unfold compose.
    unfold toBatch.
    compose near t on right.
    rewrite (traverse_to_mapdt W T).
    rewrite <- (kdtfun_morph W T (G1 := Batch A B) (G2 := fun A => A)).
    reassociate <-.
    rewrite (runBatch_batch (fun A => A)).
    reflexivity.
  Qed.

End with_functor.

(** * <<foldMapd>> *)
(******************************************************************************)
Section foldMapd.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Monoid_op M} `{Monoid_unit M}
    `{Mapdt W T}.

  Definition foldMapd : forall {A : Type}, (W * A -> M) -> T A -> M :=
    fun A f => mapdt T (const M) A False f.

End foldMapd.

(** ** Basic properties *)
(******************************************************************************)
Section with_functor.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}.

  (** *** Lemmas for <<mapdt>> with constant applicative functors *)
  (******************************************************************************)
  Section constant_applicatives.

    Context
      `{Monoid M}
      `{f : W * A -> M}.

    #[local] Arguments mapdt  {M}%type_scope (T)%function_scope   {Mapdt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
    #[local] Arguments mapd   {M}%type_scope (T)%function_scope   {Mapd}                                (A B)%type_scope _%function_scope _.
    #[local] Arguments traverse              (T)%function_scope   {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
    #[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.


    Lemma mapdt_constant_applicative1: forall (B : Type),
        mapdt T (const M) A B f = mapdt T (const M) A False f.
    Proof.
      intros.
      change_right (map (const M) (T False) (T B) (map T False B exfalso)
                      ∘ mapdt T (const M) A False f).
      rewrite (map_mapdt T (const M) (A := A) (B := False) (C := B)).
      reflexivity.
    Qed.

    Lemma mapdt_constant_applicative2 : forall (fake1 fake2 : Type),
        mapdt T (const M) A fake1 f = mapdt T (const M) A fake2 f.
    Proof.
      intros. rewrite (mapdt_constant_applicative1 fake1).
      rewrite (mapdt_constant_applicative1 fake2).
      reflexivity.
    Qed.

  End constant_applicatives.

  (** *** Expressing <<foldMapd>> in terms of <<runBatch>> *)
  (******************************************************************************)
  Theorem foldMapd_to_runBatch :
    forall `{Monoid M} (A : Type) (f : W * A -> M) (t : T A),
      foldMapd W T f t = runBatch f (toBatch6 W T False t).
  Proof.
    intros. unfold foldMapd.
    rewrite (mapdt_to_runBatch W T (const M)).
    reflexivity.
  Qed.

  (** *** Rewriting the "tag" parameter *)
  (******************************************************************************)
  Lemma foldMapd_equiv1 `{Monoid M} : forall (fake : Type) `(f : W * A -> M),
      foldMapd W T f = mapdt T (const M) A fake f.
  Proof.
    intros. unfold foldMapd.
    now rewrite (mapdt_constant_applicative2 fake False).
  Qed.

  (** *** Homomorphism law *)
  (******************************************************************************)
  Lemma foldMapd_morphism `{Monoid_Morphism M1 M2 ϕ} : forall `(f : W * A -> M1),
      ϕ ∘ foldMapd W T f = foldMapd W T (ϕ ∘ f).
  Proof.
    intros.
    unfold foldMapd. inversion H5.
    change ϕ with (const (ϕ) (T False)).
    rewrite (mapdt_constant_applicative2 (f := const ϕ (T False) ∘ f) False (T False)).
    rewrite (kdtfun_morph W T f (G1 := const M1) (G2 := const M2) (ϕ := const ϕ) (B := T False) (A := A)).
    rewrite (mapdt_constant_applicative2 (T False) False).
    reflexivity.
  Qed.

  (** *** Composition with <<mapdt>> *)
  (******************************************************************************)
  Lemma foldMapd_mapdt : forall `{Monoid M} `{Applicative G} `(g : W * B -> M) `(f : W * A -> G B),
      map G (foldMapd W T g) ∘ mapdt T G A B f =
        foldMapd W T (M := G M) (map G g ∘ σ G ∘ cobind (W ×) A (G B) f).
  Proof.
    intros. unfold foldMapd.
    rewrite (kdtfun_mapdt2 W T G (const M) A B False).
    fequal. (* TODO abstract this step *)
    - ext A' B' f' t. unfold Map_compose, Map_const.
      change t with (id t) at 2. rewrite (fun_map_id G).
      reflexivity.
    - ext A' B' [a b]. reflexivity.
  Qed.

  (** *** Composition with <<mapd>>, <<traverse>>, <<map>> *)
  (******************************************************************************)
  Lemma foldMapd_mapd : forall `{Monoid M} `(g : W * B -> M) `(f : W * A -> B),
      foldMapd W T g ∘ mapd W T A B f =
        foldMapd W T (M := M) (g ∘ cobind (W ×) A B f).
  Proof.
    intros. unfold foldMapd.
    rewrite (mapd_to_mapdt).
    change (mapdt T (const M) B False g) with (map (fun A => A) (A := T B) (B := M) (mapdt T (const M) B False g)).
    rewrite (kdtfun_mapdt2 W T (fun A => A) (const M) A B False).
    rewrite (kc6_64).
    fequal.
    - ext A' B' [a b]. reflexivity.
  Qed.

  Lemma foldMapd_traverse : forall `{Monoid M} `{Applicative G} `(g : W * B -> M) `(f : A -> G B),
      map G (foldMapd W T g) ∘ traverse T G f =
        foldMapd W T (M := G M) (map G g ∘ σ G ∘ map (W ×) f).
  Proof.
    intros.
    rewrite (traverse_to_mapdt).
    rewrite (foldMapd_mapdt g (f ∘ extract (W ×) A)).
    reflexivity.
  Qed.

  Lemma foldMap_map : forall `{Monoid M} `(g : W * B -> M) `(f : A -> B),
      foldMapd W T g ∘ map T f =
        foldMapd W T (M := M) (g ∘ map (W ×) f).
  Proof.
    intros.
    rewrite (map_to_mapdt).
    change (mapdt T (fun A => A) ?f) with (mapd W T f).
    rewrite foldMapd_mapd.
    reflexivity.
  Qed.

End with_functor.

Import Sets.ElNotations.

(** * <<tolistd>> and <<tosetd>> *)
(******************************************************************************)
Section tolistd.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}.

  Definition tolistd {A} : T A -> list (W * A) :=
    foldMapd W T (ret list (W * A)).

  #[export] Instance Tosetd_DTF : El_ctx T W :=
    fun A => foldMapd W T (ret set (W * A)).

  (** ** Relating <<tosetd>> and <<tolistd>> *)
  (******************************************************************************)
  Lemma tosetd_to_tolistd : forall (A : Type),
      @el_ctx T W _ A = el list (W * A) ∘ tolistd.
  Proof.
    intros. unfold_ops @Tosetd_DTF. unfold tolistd.
    rewrite (foldMapd_morphism W T).
    fequal. ext [w a]. unfold compose.
    solve_basic_set.
  Qed.

  (** ** Characterizing <<∈d>> *)
  (******************************************************************************)
  Theorem ind_mapd_iff :
    forall `(f : W * A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d mapd W T A B f t <-> exists (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros. unfold_ops @Tosetd_DTF.
    compose near t on left.
    rewrite (foldMapd_mapd);
      try typeclasses eauto.
    rewrite foldMapd_to_runBatch;
      try typeclasses eauto.
    rewrite foldMapd_to_runBatch;
      try typeclasses eauto.
    induction (toBatch6 W T False t).
    - splits.
      + introv hyp. inverts hyp.
      + introv [a' hyp]. inverts hyp.
        solve_basic_set.
    - splits.
      + intros [hyp | hyp].
        { rewrite IHb0 in hyp. preprocess.
          eexists. split; [| reflexivity]. now left. }
        { destruct x as [w' a]. inverts hyp.
          eexists. split; [| reflexivity]. now right. }
      + introv [a [rest1 rest2]]. subst.
        inverts rest1.
        { left. rewrite IHb0.
          exists a. split; auto. }
        { right. destruct x.
          unfold compose; cbn.
          inverts H1. easy. }
  Qed.

  Corollary ind_map_iff :
    forall `(f : A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d map T f t <-> exists (a : A), (w, a) ∈d t /\ f a = b.
  Proof.
    intros. change_left ((w, b) ∈d mapd W T A B (f ∘ extract (prod W) A) t).
    rewrite ind_mapd_iff.
    unfold compose. cbn. splits; eauto.
  Qed.

End tolistd.

(** * Relating <<foldMapd>> and <<foldMap>> *)
(******************************************************************************)
Section new.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}.

  (** ** Expressing <<foldMap>> with <<foldMapd>> *)
  (******************************************************************************)
  Lemma foldMap_to_foldMapd : forall `{Monoid M} `(f : A -> M),
      foldMap T f = foldMapd W T (f ∘ extract (W ×) A).
  Proof.
    intros. unfold foldMapd, foldMap.
    unfold_ops @Traverse_Mapdt.
    reflexivity.
  Qed.

  (* for naturality of <<ret list>> *)
  Import Tealeaves.Classes.Traversable.Monad.DerivedInstances.

  (** ** Relating <<tolist>> to <<tolistd>>*)
  (******************************************************************************)
  Lemma tolist_to_tolistd : forall (A : Type),
      @tolist T _ A = map list (extract (W ×) A) ∘ tolistd W T.
  Proof.
    intros. unfold_ops Tolist_Traverse.
    rewrite (foldMap_to_foldMapd).
    unfold tolistd.
    rewrite (foldMapd_morphism W T).
    rewrite (natural (ϕ := @ret list _)).
    reflexivity.
  Qed.

  (* for naturality of <<ret set>> *)
  Import Tealeaves.Classes.Monad.DerivedInstances.

  (** ** Relating <<toset>> to <<tosetd>>*)
  (******************************************************************************)
  Lemma toset_to_tosetd : forall (A : Type),
      @el T _ A = map set (extract (W ×) A) ∘ el_ctx T A.
  Proof.
    intros. unfold_ops @Toset_Traverse @Tolist_Traverse.
    unfold_ops @Tosetd_DTF.
    rewrite (foldMap_to_foldMapd).
    rewrite (foldMapd_morphism W T).
    rewrite (natural (ϕ := @ret set _)).
    reflexivity.
  Qed.

  (** ** Relating <<∈>> to <<∈d>> *)
  (******************************************************************************)
  Lemma ind_iff_in : forall (A : Type) (a : A) (t : T A),
      a ∈ t <-> exists w, (w, a) ∈d t.
  Proof.
    intros. unfold_ops @Toset_Traverse.
    rewrite (foldMap_to_foldMapd).
    change (extract (prod W) A) with (map (fun A => A) (@extract (prod W) _ A)).
    rewrite <- (natural (ϕ := @ret set _)).
    rewrite <- (foldMapd_morphism W T).
    unfold el_ctx.
    unfold compose.
    unfold_ops @Map_set. split.
    - intros [[w a'] [rest1 rest2]]. exists w.
      inverts rest2.
      assumption.
    - intros [w rest]. exists (w, a). split.
      + assumption.
      + cbv. reflexivity.
  Qed.

  Corollary ind_implies_in : forall (A : Type) (a : A) (w : W) (t : T A),
      (w, a) ∈d t -> a ∈ t.
  Proof.
    intros. rewrite ind_iff_in. eauto.
  Qed.

  (** ** Characterizing <<∈>> to with <<mapdt>> *)
  (******************************************************************************)
  Theorem in_mapd_iff :
    forall `(f : W * A -> B) (t : T A) (b : B),
      b ∈ mapd W T A B f t <-> exists (w : W) (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros. rewrite ind_iff_in.
    setoid_rewrite (ind_mapd_iff W T).
    reflexivity.
  Qed.

End new.

(** * Respectfulness *)
(******************************************************************************)
Section decorated_setlike_respectfulness.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DecoratedTraversableFunctor W T}.

  Lemma mapd_respectful {A B} : forall (t : T A) (f g : W * A -> B),
      (forall w a, (w, a) ∈d t -> f (w, a) = g (w, a)) ->
      mapd W T A B f t = mapd W T A B g t.
  Proof.
    unfold_ops @Tosetd_DTF.
    introv hyp.
    unfold foldMapd in hyp.
    rewrite (mapdt_constant_applicative2 W T False B) in hyp.
    rewrite (mapdt_to_runBatch W T _) in hyp.
    do 2 rewrite (mapd_to_mapdt W T).
    do 2 rewrite (mapdt_to_runBatch W T (fun A => A)).
    induction (toBatch6 W T B t).
    - reflexivity.
    - destruct x as [w a]. cbn. rewrite IHb. fequal.
      apply hyp. now right.
      intros. apply hyp. now left.
  Qed.

  Corollary mapd_respectful_id {A} : forall (t : T A) (f : W * A -> A),
      (forall w a, (w, a) ∈d t -> f (w, a) = a) ->
      mapd W T A A f t = t.
  Proof.
    intros. replace t with (mapd W T _ _ (extract (prod W) A) t) at 2
      by (now rewrite (dfun_mapd1 W T)).
    now apply mapd_respectful.
  Qed.

End decorated_setlike_respectfulness.
