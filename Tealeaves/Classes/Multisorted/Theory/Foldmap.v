 From Tealeaves Require Import
   Classes.Multisorted.DecoratedTraversableMonad
   Classes.Multisorted.Theory.Container
   Classes.Multisorted.Theory.Targeted
   Functors.List
   Functors.Subset
   Functors.Constant.

Import TypeFamily.Notations.
Import Monoid.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import Multisorted.Theory.Container.Notations.
Import ContainerFunctor.Notations.
#[local] Open Scope list_scope.

#[local] Generalizable Variables A B C F G W T U K M.

(** * Foldmap *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section foldmap.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}
    `{M_mn_op: Monoid_op M}
    `{M_mn_unit: Monoid_unit M}.

  Definition mapReducemd_gen {A} (fake: Type) (f : K -> (W * A) -> M): U A -> M :=
    mmapdt (B := fake) U (const M) f.

  Definition mapReducemd {A} (f : K -> (W * A) -> M): U A -> M :=
    mapReducemd_gen False f.

  Definition mapReducem {A} (f : K -> A -> M) : U A -> M :=
    mapReducemd (f ◻ allK (extract (W := (prod W)))).

  Definition mapReducekd {A} (k: K) (f : W * A -> M): U A -> M :=
    mapReducemd (tgt_def k f (const Ƶ)).

  Definition mapReducek {A} (k: K) (f : A -> M): U A -> M :=
    mapReducem (tgt_def k f (const Ƶ)).

  Lemma mapReducemd_to_mmapdt {A} (f : K -> (W * A) -> M):
    mapReducemd f = mmapdt (B := False) U (const M) f.
  Proof.
    reflexivity.
  Qed.

  Lemma mapReducem_to_mapReducemd {A} (f : K -> A -> M):
    mapReducem f = mapReducemd (f ◻ allK (extract (W := (prod W)))).
  Proof.
    reflexivity.
  Qed.

  Lemma mapReducemd_fake `{! Monoid M}: forall {A} (fake1 fake2: Type),
      mapReducemd_gen (A := A) fake1 = mapReducemd_gen fake2.
  Proof.
    intros.
    ext f.
    unfold mapReducemd_gen.
    unfold mmapdt.
    rewrite (mbinddt_constant_applicative2 U fake1 fake2).
    reflexivity.
  Qed.

  Lemma mapReducekd_to_kmapdt `{! Monoid M} {A} (f : W * A -> M) {k: K}:
    mapReducekd k f = kmapdt U k (G := const M) f.
  Proof.
    unfold kmapdt.
    unfold mapReducekd, mapReducemd.
    rewrite (mapReducemd_fake False A).
    unfold mapReducemd_gen.
    fequal.
    ext j [w a].
    unfold tgt_def, tgtdt.
    destruct_eq_args k j.
  Qed.

  Lemma mapReducek_to_kmapt `{! Monoid M} {A} (f : A -> M) {k: K}:
    mapReducek k f = ktraverse U k (G := const M) f.
  Proof.
    unfold mapReducek, mapReducem, mapReducemd.
    rewrite (mapReducemd_fake False A).
    reflexivity.
  Qed.

  Lemma mapReducekd_to_mapReducemd `{! Monoid M} {A} (f : W * A -> M) {k: K}:
    mapReducekd k f = mapReducemd (tgt_def (A := W * A) k f (const Ƶ)).
  Proof.
    intros.
    rewrite mapReducekd_to_kmapdt.
    rewrite kmapdt_to_mmapdt.
    rewrite mapReducemd_to_mmapdt.
    unfold mmapdt.
    rewrite (mbinddt_constant_applicative2 U A False).
    fequal. fequal. ext j [w a].
    unfold tgtdt, tgt_def.
    destruct_eq_args k j.
  Qed.

  Lemma mapReducek_to_mapReducekd `{! Monoid M} {A} (f : A -> M) {k: K}:
    mapReducek k f = mapReducekd k (f ∘ extract (W := prod W)).
  Proof.
    intros.
    rewrite mapReducek_to_kmapt.
    unfold ktraverse.
    rewrite mapReducekd_to_kmapdt.
    unfold mmapt.
    unfold kmapdt.
    fequal. (ext j [w a]).
    unfold tgtt, tgtdt, vec_compose, compose.
    destruct_eq_args k j.
  Qed.

End foldmap.

Section tolist_and_tosubset.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma tolistmd_gen_to_mapReducemd_gen : forall {A} {fake:Type} (t: U A),
      tolistmd_gen U fake t = mapReducemd_gen U fake tolistmd_gen_loc t.
  Proof.
    reflexivity.
  Qed.

  Lemma tolistmd_to_mapReducemd : forall {A},
      tolistmd (A := A) (T := T) U = mapReducemd U tolistmd_gen_loc.
  Proof.
    reflexivity.
  Qed.

  Definition tosetmd_gen_loc {A}: K -> W * A -> subset (W * (K * A)) :=
    fun k '(w, a) => {{ (w, (k, a)) }}.

  Lemma tosetmd_to_mapReducemd : forall {A},
      tosetmd (A := A) (T := T) U = mapReducemd U tosetmd_gen_loc.
  Proof.
    intros.
    unfold tosetmd.
    rewrite tolistmd_to_mapReducemd.
    unfold mapReducemd, mapReducemd_gen, mmapdt.
    change (ContainerFunctor.tosubset (A := (W * (K * A))))
      with (const (ContainerFunctor.tosubset (A := (W * (K * A))))
              (list (W * (K * A)))).
    Set Keyed Unification.
    rewrite (dtp_mbinddt_morphism W T U
                 (const (list (W * (K * A))))
                 (const (subset (W * (K * A))))
                 (H6 := ApplicativeMorphism_monoid_morphism)).
    Unset Keyed Unification.
    fequal.
    ext j (w, a).
    ext (j', (w', a')).
    unfold vec_compose, compose, mapMret, vec_apply, const.
    unfold_ops @Map_const.
    unfold tosetmd_gen_loc,
      tolistmd_gen_loc.
    propext; intuition.
  Qed.

  #[global] Instance ApplicativeMorphism_filterk : forall {A} (k: K),
      ApplicativeMorphism (const (list (W * (K * A))))
                          (const (list (W * A)))
                          (const (filterk k)).
  Proof.
    intros. eapply ApplicativeMorphism_monoid_morphism.
    Unshelve. constructor; try typeclasses eauto.
    - easy.
    - intros. apply filterk_app.
  Qed.

  Lemma toklistd_to_mapReducekd : forall {A} (k: K),
      toklistd (T := T) (A := A) U k = mapReducekd U k (fun p => [p]).
    Proof.
      intros.
      unfold toklistd.
      rewrite tolistmd_to_mapReducemd.
      unfold mapReducemd, mapReducemd_gen, mmapdt.
      rewrite (dtp_mbinddt_morphism W T U
                 (const (list (W * (K * A))))
                 (const (list (W * A)))
                 (H6 := ApplicativeMorphism_filterk k)).
      unfold mapReducekd, mapReducemd, mapReducemd_gen, mmapdt.
      fequal. ext j (w, a).
      unfold vec_compose, compose, mapMret, vec_apply, tgt_def.
      cbn. destruct_eq_args k j.
    Qed.

  Lemma toksetd_to_mapReducekd : forall {A} (t: U A) (k : K),
      toksetd U k t = mapReducekd U k (fun p => {{p}}) t.
  Proof.
    intros.
    unfold toksetd.
    rewrite toklistd_to_mapReducekd.
    unfold mapReducemd, mapReducemd_gen, mmapdt.
    change (ContainerFunctor.tosubset (A := (W * A)))
      with (const (ContainerFunctor.tosubset (A := (W * A)))
              (list (W * A))).
    Set Keyed Unification.
    rewrite (dtp_mbinddt_morphism W T U
               (const (list (W * A)))
               (const (subset (W * A)))
               (H6 := ApplicativeMorphism_monoid_morphism)).
    Unset Keyed Unification.
    unfold mapReducekd, mapReducemd, mapReducemd_gen, mmapdt.
    fequal.
    ext j (w, a).
    ext (w', a').
    unfold vec_compose, compose, mapMret, vec_apply, const.
    unfold_ops @Map_const.
    unfold tgt_def.
    propext; destruct_eq_args k j; intuition.
  Qed.

End tolist_and_tosubset.

Section morphisms.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Generalizable Variables ϕ.

  Lemma mapReducemd_morphism:
    forall {A}
      `{Monoid M1} `{Monoid M2}
      `{! Monoid_Morphism M1 M2 ϕ} (f: K -> W * A -> M1),
      ϕ ∘ mapReducemd U f = mapReducemd U (fun k => ϕ ∘ f k).
  Proof.
    intros.
    change ϕ with (const ϕ (U False)).
    unfold mapReducemd, mapReducemd_gen, mmapdt.
    rewrite (dtp_mbinddt_morphism W T U
               (A := A)
               (B := False)
               (ix := ix)
               (ϕ := const ϕ)
               (const M1)
               (const M2)
               (H6 := ApplicativeMorphism_monoid_morphism)).
    reflexivity.
  Qed.

  Lemma mapReducemd_through_tolist {A} `{Monoid M} (f : K -> (W * A) -> M):
    mapReducemd U f = mapReduce_list (fun '(w, (k, a)) => f k (w, a)) ∘ tolistmd U.
  Proof.
    rewrite tolistmd_to_mapReducemd.
    rewrite mapReducemd_morphism.
    fequal. ext k [w a]. cbn.
    now simpl_monoid.
  Qed.

End morphisms.

Section forall_and_exists.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Definition Forallmd {A} (P: K -> W * A -> Prop) :=
    mapReducemd U (T := T)
      (M_mn_op := Monoid_op_and) (M_mn_unit := Monoid_unit_true) P.

  Definition Forallkd {A} (k: K) (P: W * A -> Prop) :=
    mapReducekd U k (T := T)
      (M_mn_op := Monoid_op_and) (M_mn_unit := Monoid_unit_true) P.

  Lemma Forallmd_to_mapReducemd {A} (P: K -> W * A -> Prop ):
    Forallmd P =
    mapReducemd U (T := T)
      (M_mn_op := Monoid_op_and) (M_mn_unit := Monoid_unit_true) P.
  Proof.
    reflexivity.
  Qed.

  Lemma Forallkd_to_mapReducekd {A} (k: K) (P: W * A -> Prop):
    Forallkd k P =
    mapReducekd U k (T := T)
      (M_mn_op := Monoid_op_and) (M_mn_unit := Monoid_unit_true) P.
  Proof.
    reflexivity.
  Qed.

  Lemma Forallkd_to_Forallmd {A} (k: K) (P: W * A -> Prop):
    Forallkd k P =
      Forallmd (tgt_def k P (const True)).
  Proof.
    unfold Forallkd, Forallmd.
    unfold mapReducekd.
    reflexivity.
  Qed.

  Definition Forallmd_spec : forall {A} (P: W * (K * A) -> Prop) (t: U A),
      (forall w k a, (w, (k, a)) ∈md t -> P (w, (k, a))) =
        Forallmd (fun k '(w, a) => P (w, (k, a))) t.
  Proof.
    intros.
    unfold Forallmd.
    unfold tosetmd.
    rewrite (mapReducemd_through_tolist U).
    unfold compose.
    apply propositional_extensionality.
    induction (tolistmd U t).
    - cbv; intuition.
    - destruct a as [w [k a]]. cbn.
      split.
      + introv hyp. split.
        * apply hyp. now left.
        * apply IHl. auto.
      + introv [case1 case2] [Heq | Hin].
        * inversion Heq; subst. cbv in *; tauto.
        * unfold mapReduce_list, compose in IHl.
          rewrite <- IHl in case2. auto.
  Qed.

  Definition Forallkd_spec : forall {A} {k: K} (P: W * A -> Prop) (t: U A),
      (forall w a, (w, (k, a)) ∈md t -> P (w, a)) =
        Forallkd k (fun '(w, a) => P (w, a)) t.
  Proof.
    intros.
    unfold Forallkd, Forallmd, tosetmd.
    rewrite (mapReducekd_to_mapReducemd U).
    rewrite (mapReducemd_through_tolist U).
    unfold compose.
    apply propositional_extensionality.
    induction (tolistmd U t).
    - cbv; intuition.
    - destruct a as [w [j a]].
      cbn. unfold tgt_def.
      destruct_eq_args k j.
      { split.
        + introv hyp. split.
          * cbn. apply hyp. now left.
          * apply IHl. auto.
        + introv [case1 case2] [Heq | Hin].
          * inversion Heq; subst. cbv in *; tauto.
          * unfold mapReduce_list, compose in IHl.
            rewrite <- IHl in case2. auto. }
      { split.
        + introv hyp. split.
          * cbv. easy.
          * apply IHl. auto.
        + introv [case1 case2] [Heq | Hin].
          * inversion Heq; subst. cbv in *; tauto.
          * unfold mapReduce_list, compose in IHl.
            rewrite <- IHl in case2. auto. }
  Qed.

End forall_and_exists.
