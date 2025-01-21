From Tealeaves Require Export
  Functors.Batch
  Functors.VectorRefinement
  Functors.Backwards.

Import Batch.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables G T.

  (** ** Lens-like laws *)
  (******************************************************************************)
  Section lens_laws.

    Context {A A' A'' B C: Type}.

    Lemma Batch_make_contents:
      forall (b: Batch A A C),
        Batch_make b (Batch_contents b) = extract_Batch b.
    Proof.
      intros.
      induction b.
      - reflexivity.
      - rewrite Batch_make_rw2.
        rewrite Batch_contents_rw2.
        rewrite Vector_tl_vcons.
        rewrite Vector_hd_vcons.
        rewrite IHb.
        reflexivity.
    Qed.

    Lemma Batch_get_put:
      forall (b: Batch A B C),
        Batch_replace_contents b (Batch_contents b) = b.
    Proof.
      intros.
      induction b.
      - reflexivity.
      - cbn.
        rewrite Vector_tl_vcons.
        rewrite Vector_hd_vcons.
        rewrite IHb.
        reflexivity.
    Qed.

    Lemma Batch_put_get:
      forall (b: Batch A B C) (v: Vector (length_Batch b) A'),
        Batch_contents (Batch_replace_contents b v) =
          coerce length_replace_contents b v in v.
    Proof.
      intros.
      generalize (length_replace_contents b v).
      intros Heq.
      induction b.
      - cbn. symmetry.
        apply Vector_nil_eq.
      - cbn in *.
        rewrite Vector_surjective_pairing2.
        rewrite <- (Vector_hd_coerce_eq (Heq := Heq) (v := v)).
        specialize (IHb (Vector_tl v) (S_uncons Heq)).
        fold (@length_Batch A B).
        (* ^^ I have no idea why this got expanded but it blocks rewriting *)
        rewrite IHb.
        fequal.
        apply Vector_sim_eq.
        vector_sim.
    Qed.

    Lemma Batch_put_put:
      forall (b: Batch A B C)
        (v1: Vector (length_Batch b) A')
        (v2: Vector (length_Batch b) A''),
        Batch_replace_contents
          (Batch_replace_contents b v1)
          (coerce (length_replace_contents b v1) in v2) =
          Batch_replace_contents b v2.
    Proof.
      intros.
      apply Batch_replace_sim3.
      symmetry.
      apply Batch_shape_replace_contents.
      vector_sim.
    Qed.

    Lemma Batch_replace_spec:
      forall (b: Batch A B C),
        Batch_replace_contents b =
          precoerce (length_cojoin_Batch b)
                   in Batch_make (cojoin_Batch b (B := A')).
    Proof.
      intros b. ext v.
      generalize (length_cojoin_Batch (A' := A') b).
      intros Heq.
      induction b.
      - reflexivity.
      - rewrite Batch_replace_rw2.
        cbn.
        rewrite Batch_make_compose_rw2.
        rewrite <- (Vector_hd_coerce_eq (Heq := Heq)).
        fequal.
        specialize (IHb (Vector_tl v) (length_cojoin_Batch b)).
        rewrite IHb.
        apply Batch_make_sim1.
        vector_sim.
    Qed.

    Lemma Batch_make_replace_contents:
      forall (b: Batch A B C) (v: Vector (length_Batch b) A'),
        Batch_make (Batch_replace_contents b v) =
          precoerce (eq_sym (length_replace_contents b v))
        in (Batch_make (B := B) b).
    Proof.
      intros.
      ext v'.
      generalize (eq_sym (length_replace_contents b v)).
      intro e.
      induction b.
      - reflexivity.
      - cbn.
        specialize (IHb (Vector_tl v) (Vector_tl v')).
        specialize (IHb (eq_sym (length_replace_contents b (Vector_tl v)))).
        replace (Vector_hd (coerce_Vector_length e v'))
          with (Vector_hd v') at 1.
        Set Keyed Unification.
        rewrite IHb.
        Unset Keyed Unification.
        fequal.
        { apply Vector_eq.
          rewrite <- coerce_Vector_contents.
          apply Vector_tl_coerce_sim.
        }
        apply Vector_hd_coerce_eq.
    Qed.

  End lens_laws.


  (** ** Misc *)
  (******************************************************************************)
  Section spec.

    Lemma runBatch_const_contents:
      forall `{Applicative G} `(b: Batch A B C)
        (x: G B) `(v: Vector _ A'),
        runBatch G (const x) C b =
          runBatch G (const x) C
                   (Batch_replace_contents b v).
    Proof.
      intros.
      induction b.
      - reflexivity.
      - cbn. fequal. apply IHb.
    Qed.

    Lemma Batch_eq_iff:
      forall `(b1: Batch A B C) `(b2: Batch A B C),
        b1 = b2 <->
          Batch_make b1 ~!~ Batch_make b2 /\
            Batch_contents b1 ~~ Batch_contents b2.
    Proof.
      intros. split.
      - intros; subst. split.
        2: reflexivity.
        unfold Vector_fun_sim.
        split; try reflexivity.
        introv Hsim.
        auto using Batch_make_sim1.
      - intros [Hmake Hcontents].
        rewrite <- (Batch_get_put b1).
        rewrite <- (Batch_get_put b2).
        apply Batch_replace_sim3.
        now apply Batch_make_shape_rev.
        assumption.
    Qed.

  End spec.

  (** ** Representation theorems *)
  (******************************************************************************)
  Lemma runBatch_repr1 `{Applicative G}:
    forall `(b: Batch A B C) (f: A -> G B),
      map (F := G) (Batch_make b)
          (traverse (T := Vector (length_Batch b)) f (Batch_contents b)) =
        forwards (runBatch (Backwards G) (mkBackwards ∘ f) _ b).
  Proof.
    intros.
    induction b.
    - cbn.
      rewrite app_pure_natural.
      reflexivity.
    - rewrite Batch_contents_rw2.
      unfold length_Batch at 2. (* hidden *)
      rewrite traverse_Vector_vcons.
      rewrite runBatch_rw2.
      rewrite forwards_ap.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite <- IHb.
      rewrite map_to_ap.
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      fequal.
      fequal.
      fequal.
      ext b' v'.
      unfold compose, precompose, evalAt.
      cbn.
      rewrite Vector_tl_vcons.
      rewrite Vector_hd_vcons.
      reflexivity.
  Qed.

  Lemma runBatch_repr2 `{Applicative G}:
    forall `(b: Batch A B C) (f: A -> G B),
      runBatch G f _ b =
        map (F := G) (Batch_make b)
            (forwards (traverse (G := (Backwards G))
                                (T := Vector (length_Batch b))
                                (mkBackwards ∘ f)
                                (Batch_contents b))).
  Proof.
    intros.
    symmetry.
    change_left
      (forwards
         (map (F := Backwards G) (Batch_make b)
              (traverse (G := Backwards G) (mkBackwards ∘ f) (Batch_contents b)))).
    rewrite runBatch_repr1.
    rewrite runBatch_spec.
    rewrite runBatch_spec.
    change_left
      (map (F := G) extract_Batch
           (forwards (
                forwards (
                    traverse (G := Backwards (Backwards G))
                             (mkBackwards ∘ (mkBackwards ∘ f)) b)))).
    rewrite traverse_double_backwards.
    reflexivity.
  Qed.

End deconstruction.

(** * Deconstructing <<Batch A B C>> with an extrinsic approach *)
(******************************************************************************)
Require Import Functors.Option.

Section deconstruction_extrinsic.

  Fixpoint Batch_to_makeFn {A B C} (b: Batch A B C) (l: list B): option C :=
    match b with
    | Done c =>
        match l with
        | nil => Some c
        | _ => None
        end
    | Step rest a =>
        match (List.rev l) with
        | (b' :: bs) =>
            map (evalAt  b') (Batch_to_makeFn rest bs)
        | _ => None
        end
    end.

  Lemma basic0 {A B C C'} (b: Batch A B C) (l: list B) (f: C -> C'):
    map f (Batch_to_makeFn b l) = Batch_to_makeFn (map f b) l.
  Proof.
    induction b; induction l.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn in *.
      rename a0 into b'.
      specialize (IHb (f ∘ evalAt b')).
      destruct b.
  Abort.

  Lemma Batch_to_makeFn_rw11 {A B C}: forall c,
      Batch_to_makeFn (@Done A B C c) nil = Some c.
  Proof.
    reflexivity.
  Qed.

  Lemma Batch_to_makeFn_rw12 {A B C} b' l: forall c,
      Batch_to_makeFn (@Done A B C c) (b' :: l) = None.
  Proof.
    reflexivity.
  Qed.

  Lemma Batch_to_makeFn_rw21 {A B C}:
    forall (b: Batch A B (B -> C)) (a: A),
       Batch_to_makeFn (b ⧆ a) nil = None.
  Proof.
    reflexivity.
  Qed.

  Lemma Batch_to_makeFn_rw22 {A B C}:
    forall (b: Batch A B (B -> C)) (a: A) (l : list B) (b' : B),
       Batch_to_makeFn (b ⧆ a) (l ++ b' :: nil) =
        Batch_to_makeFn b (List.rev l) <⋆> pure b'.
  Proof.
    intros.
    cbn.
    rewrite List.rev_unit.
    rewrite map_to_ap.
    rewrite ap3.
    reflexivity.
  Qed.

  Lemma basic1 {A B C} (b: Batch A B C) (l: list B):
    length l = length_Batch b ->
    {c | Batch_to_makeFn b l = Some c}.
  Proof.
    intros.
    generalize dependent l.
    induction b; intros l.
    - destruct l.
      + cbn. exists c. reflexivity.
      + cbn. inversion 1.
    - destruct l.
      + inversion 1.
      + intro Heq.
        specialize (IHb (List.rev l)).
        assert (length (List.rev l) = length_Batch b).
        { rewrite List.rev_length.
          apply S_uncons.
          assumption. }
        specialize (IHb H).
        destruct IHb as [c pf].
        rewrite <- (List.rev_involutive l).
        rewrite <- List.rev_unit.
        rewrite List.rev_app_distr.
        destruct l.
        { cbn. exists (c b0).
          cbn in pf. rewrite pf.
          reflexivity. }
  Abort.

  (*
  Lemma Batch_repr {A C}:
    forall (b: Batch A A C),
      Batch_to_makeFn b (List.rev (Batch_to_list b)) = Some (extract_Batch b).
  Proof.
    intros.
    induction b.
    - reflexivity.
    - rewrite Batch_to_list_rw2.
      assert (forall {A B C} (b: Batch A B (B -> C)) (a: A) (l : list B) (b': B),
      Batch_to_makeFn (b ⧆ a) (l ++ b' :: nil) =
        Batch_to_makeFn b (List.rev l) <⋆> pure b').
      { intros.
        rewrite Batch_to_makeFn_rw22.
        reflexivity. }
      rewrite List.rev_app_distr.
      cbn.
  Qed.
  *)

End deconstruction_extrinsic.
