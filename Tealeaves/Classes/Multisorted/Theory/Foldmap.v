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

  Definition foldMapmd_gen {A} (fake: Type) (f : K -> (W * A) -> M): U A -> M :=
    mmapdt (B := fake) U (const M) f.

  Definition foldMapmd {A} (f : K -> (W * A) -> M): U A -> M :=
    foldMapmd_gen False f.

  Definition foldMapm {A} (f : K -> A -> M) : U A -> M :=
    foldMapmd (f ◻ allK (extract (W := (prod W)))).

  Definition foldMapkd {A} (k: K) (f : W * A -> M): U A -> M :=
    foldMapmd (tgt_def k f (const Ƶ)).

  Definition foldMapk {A} (k: K) (f : A -> M): U A -> M :=
    foldMapm (tgt_def k f (const Ƶ)).

  Lemma foldMapmd_to_mmapdt {A} (f : K -> (W * A) -> M):
    foldMapmd f = mmapdt (B := False) U (const M) f.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMapm_to_foldMapmd {A} (f : K -> A -> M):
    foldMapm f = foldMapmd (f ◻ allK (extract (W := (prod W)))).
  Proof.
    reflexivity.
  Qed.

  Lemma foldMapmd_fake `{! Monoid M}: forall {A} (fake1 fake2: Type),
      foldMapmd_gen (A := A) fake1 = foldMapmd_gen fake2.
  Proof.
    intros.
    ext f.
    unfold foldMapmd_gen.
    unfold mmapdt.
    rewrite (mbinddt_constant_applicative2 U fake1 fake2).
    reflexivity.
  Qed.

  Lemma foldMapkd_to_kmapdt `{! Monoid M} {A} (f : W * A -> M) {k: K}:
    foldMapkd k f = kmapdt U k (G := const M) f.
  Proof.
    unfold kmapdt.
    unfold foldMapkd, foldMapmd.
    rewrite (foldMapmd_fake False A).
    unfold foldMapmd_gen.
    fequal.
    ext j [w a].
    unfold tgt_def, tgtdt.
    destruct_eq_args k j.
  Qed.

  Lemma foldMapk_to_kmapt `{! Monoid M} {A} (f : A -> M) {k: K}:
    foldMapk k f = ktraverse U k (G := const M) f.
  Proof.
    unfold foldMapk, foldMapm, foldMapmd.
    rewrite (foldMapmd_fake False A).
    reflexivity.
  Qed.

  Lemma foldMapkd_to_foldMapmd `{! Monoid M} {A} (f : W * A -> M) {k: K}:
    foldMapkd k f = foldMapmd (tgt_def (A := W * A) k f (const Ƶ)).
  Proof.
    intros.
    rewrite foldMapkd_to_kmapdt.
    rewrite kmapdt_to_mmapdt.
    rewrite foldMapmd_to_mmapdt.
    unfold mmapdt.
    rewrite (mbinddt_constant_applicative2 U A False).
    fequal. fequal. ext j [w a].
    unfold tgtdt, tgt_def.
    destruct_eq_args k j.
  Qed.

  Lemma foldMapk_to_foldMapkd `{! Monoid M} {A} (f : A -> M) {k: K}:
    foldMapk k f = foldMapkd k (f ∘ extract (W := prod W)).
  Proof.
    intros.
    rewrite foldMapk_to_kmapt.
    unfold ktraverse.
    rewrite foldMapkd_to_kmapdt.
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

  Lemma tolistmd_gen_to_foldMapmd_gen : forall {A} {fake:Type} (t: U A),
      tolistmd_gen U fake t = foldMapmd_gen U fake tolistmd_gen_loc t.
  Proof.
    reflexivity.
  Qed.

  Lemma tolistmd_to_foldMapmd : forall {A},
      tolistmd (A := A) (T := T) U = foldMapmd U tolistmd_gen_loc.
  Proof.
    reflexivity.
  Qed.

  Definition tosetmd_gen_loc {A}: K -> W * A -> subset (W * (K * A)) :=
    fun k '(w, a) => {{ (w, (k, a)) }}.

  Lemma tosetmd_to_foldMapmd : forall {A},
      tosetmd (A := A) (T := T) U = foldMapmd U tosetmd_gen_loc.
  Proof.
    intros.
    unfold tosetmd.
    rewrite tolistmd_to_foldMapmd.
    unfold foldMapmd, foldMapmd_gen, mmapdt.
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

  Lemma toklistd_to_foldMapkd : forall {A} (k: K),
      toklistd (T := T) (A := A) U k = foldMapkd U k (fun p => [p]).
    Proof.
      intros.
      unfold toklistd.
      rewrite tolistmd_to_foldMapmd.
      unfold foldMapmd, foldMapmd_gen, mmapdt.
      rewrite (dtp_mbinddt_morphism W T U
                 (const (list (W * (K * A))))
                 (const (list (W * A)))
                 (H6 := ApplicativeMorphism_filterk k)).
      unfold foldMapkd, foldMapmd, foldMapmd_gen, mmapdt.
      fequal. ext j (w, a).
      unfold vec_compose, compose, mapMret, vec_apply, tgt_def.
      cbn. destruct_eq_args k j.
    Qed.

  Lemma toksetd_to_foldMapkd : forall {A} (t: U A) (k : K),
      toksetd U k t = foldMapkd U k (fun p => {{p}}) t.
  Proof.
    intros.
    unfold toksetd.
    rewrite toklistd_to_foldMapkd.
    unfold foldMapmd, foldMapmd_gen, mmapdt.
    change (ContainerFunctor.tosubset (A := (W * A)))
      with (const (ContainerFunctor.tosubset (A := (W * A)))
              (list (W * A))).
    Set Keyed Unification.
    rewrite (dtp_mbinddt_morphism W T U
               (const (list (W * A)))
               (const (subset (W * A)))
               (H6 := ApplicativeMorphism_monoid_morphism)).
    Unset Keyed Unification.
    unfold foldMapkd, foldMapmd, foldMapmd_gen, mmapdt.
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

  Lemma foldMapmd_morphism:
    forall {A}
      `{Monoid M1} `{Monoid M2}
      `{! Monoid_Morphism M1 M2 ϕ} (f: K -> W * A -> M1),
      ϕ ∘ foldMapmd U f = foldMapmd U (fun k => ϕ ∘ f k).
  Proof.
    intros.
    change ϕ with (const ϕ (U False)).
    unfold foldMapmd, foldMapmd_gen, mmapdt.
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

  Lemma foldMapmd_through_tolist {A} `{Monoid M} (f : K -> (W * A) -> M):
    foldMapmd U f = foldMap_list (fun '(w, (k, a)) => f k (w, a)) ∘ tolistmd U.
  Proof.
    rewrite tolistmd_to_foldMapmd.
    rewrite foldMapmd_morphism.
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
    foldMapmd U (T := T)
      (M_mn_op := Monoid_op_and) (M_mn_unit := Monoid_unit_true) P.

  Definition Forallkd {A} (k: K) (P: W * A -> Prop) :=
    foldMapkd U k (T := T)
      (M_mn_op := Monoid_op_and) (M_mn_unit := Monoid_unit_true) P.

  Lemma Forallmd_to_foldMapmd {A} (P: K -> W * A -> Prop ):
    Forallmd P =
    foldMapmd U (T := T)
      (M_mn_op := Monoid_op_and) (M_mn_unit := Monoid_unit_true) P.
  Proof.
    reflexivity.
  Qed.

  Lemma Forallkd_to_foldMapkd {A} (k: K) (P: W * A -> Prop):
    Forallkd k P =
    foldMapkd U k (T := T)
      (M_mn_op := Monoid_op_and) (M_mn_unit := Monoid_unit_true) P.
  Proof.
    reflexivity.
  Qed.

  Lemma Forallkd_to_Forallmd {A} (k: K) (P: W * A -> Prop):
    Forallkd k P =
      Forallmd (tgt_def k P (const True)).
  Proof.
    unfold Forallkd, Forallmd.
    unfold foldMapkd.
    reflexivity.
  Qed.

  Definition Forallmd_spec : forall {A} (P: W * (K * A) -> Prop) (t: U A),
      (forall w k a, (w, (k, a)) ∈md t -> P (w, (k, a))) =
        Forallmd (fun k '(w, a) => P (w, (k, a))) t.
  Proof.
    intros.
    unfold Forallmd.
    unfold tosetmd.
    rewrite (foldMapmd_through_tolist U).
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
        * unfold foldMap_list, compose in IHl.
          rewrite <- IHl in case2. auto.
  Qed.

  Definition Forallkd_spec : forall {A} {k: K} (P: W * A -> Prop) (t: U A),
      (forall w a, (w, (k, a)) ∈md t -> P (w, a)) =
        Forallkd k (fun '(w, a) => P (w, a)) t.
  Proof.
    intros.
    unfold Forallkd, Forallmd, tosetmd.
    rewrite (foldMapkd_to_foldMapmd U).
    rewrite (foldMapmd_through_tolist U).
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
          * unfold foldMap_list, compose in IHl.
            rewrite <- IHl in case2. auto. }
      { split.
        + introv hyp. split.
          * cbv. easy.
          * apply IHl. auto.
        + introv [case1 case2] [Heq | Hin].
          * inversion Heq; subst. cbv in *; tauto.
          * unfold foldMap_list, compose in IHl.
            rewrite <- IHl in case2. auto. }
  Qed.

End forall_and_exists.
