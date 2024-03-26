From Tealeaves Require Export
  Functors.Batch
  Functors.VectorRefinement
  Functors.Backwards.

Import Batch.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables G.

(** * Deconstructing <<Batch A B C>> via <<Vector>> *)
(******************************************************************************)
Module Deconstruction1.

  Section deconstruction.

    #[local] Arguments Done {A B C}%type_scope _.
    #[local] Arguments Step {A B C}%type_scope _.

    Fixpoint Batch_to_contents {A B C} (b: Batch A B C):
      Vector.t A (length_Batch b) :=
      match b return (Vector.t A (length_Batch b)) with
      | Done c => Vector.nil A
      | Step rest a =>
          Vector.cons A a (length_Batch rest) (Batch_to_contents rest)
      end.

    Fixpoint Batch_to_makeFn {A B C} (b: Batch A B C):
      Vector.t B (length_Batch b) -> C :=
      match b return (Vector.t B (length_Batch b) -> C) with
      | Done c =>
          const c
      | Step rest a =>
          fun (v: Vector.t B (S (length_Batch rest))) =>
            match (Vector.uncons v) with
            | (b, v_rest) => Batch_to_makeFn rest v_rest b
            end
      end.

    Lemma Batch_to_contents_rw2: forall {A B C} (b: Batch A B (B -> C)) (a: A),
        Batch_to_contents (b ⧆ a) =
          Vector.cons A a (length_Batch b) (Batch_to_contents b).
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_to_makeFn_rw2: forall {A B C} (a: A) (b: Batch A B (B -> C)),
        Batch_to_makeFn (b ⧆ a) =
          fun (v:Vector.t B (S (length_Batch b))) =>
            match (Vector.uncons v) with
            | (b', v') => Batch_to_makeFn b v' b'
            end.
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_repr {A C}:
      forall (b: Batch A A C),
        Batch_to_makeFn b (Batch_to_contents b) = extract_Batch b.
    Proof.
      intros.
      induction b.
      - reflexivity.
      - cbn.
        rewrite IHb.
        reflexivity.
    Qed.

  (*
  Lemma runBatch_repr `{Applicative G} {A B C}:
    forall (f: A -> G B) (b: Batch A B C),
      runBatch G f C b =
        pure (F := G)
             (Batch_to_makeFn b) <⋆>
                traverse (T := VEC (length_Batch b)) f (Batch_to_contents b).
  Proof.
    intros.
    induction b.
    - cbn.
      rewrite ap2.
      reflexivity.
    - rewrite runBatch_rw2.
      rewrite Batch_to_contents_rw2.
      rewrite Batch_to_makeFn_rw2.
      cbn.
      rewrite <- ap4.
      rewrite ap2.
      rewrite <- ap4.
      rewrite ap2.
      rewrite ap2.
      rewrite IHb.
      reflexivity.
  Qed.
  *)

  End deconstruction.

End Deconstruction1.

(** * Deconstructing <<Batch A B C>> into shape and contents via
    refinement-style <<Vector>> *)
(******************************************************************************)
Section deconstruction.

  #[local] Arguments Done {A B C}%type_scope _.
  #[local] Arguments Step {A B C}%type_scope _.

  Generalizable Variables A B C D n v a.

  (** Extract the contents of <<Batch>> as a vector *)
  Fixpoint Batch_contents `(b: Batch A B C):
    Vector (length_Batch b) A :=
    match b with
    | Done c => vnil
    | Step b a => vcons (length_Batch b) a (Batch_contents b)
    end.

  (** Obtain the build function of <<Batch>>. Note that
 <<Batch_make b v>> in general has type <<C>>, not another <<Batch>>.
 That is, this is not <<make>> in the sense of <<put>> *)
  Fixpoint Batch_make `(b: Batch A B C):
    Vector (length_Batch b) B -> C :=
    match b return Vector (length_Batch b) B -> C with
    | Done c => fun v => c
    | Step b a => fun v =>
                   Batch_make b (Vector_tl v) (Vector_hd v)
    end.

  (** This is <<make>> in the sense of <<put>>. *)
  Fixpoint Batch_replace_contents
             `(b: Batch A B C)
             `(v: Vector (length_Batch b) A')
    : Batch A' B C :=
    match b return (Vector (length_Batch b) A' -> Batch A' B C) with
    | Done c =>
        fun v => Done c
    | Step rest a =>
        fun v =>
          Step (Batch_replace_contents rest (Vector_tl v))
               (Vector_hd v)
    end v.

  (** ** Rewriting rules *)
  (******************************************************************************)
  Section rw.

    Context {A B C: Type}.

    Implicit Types (a: A) (b: Batch A B (B -> C)) (c: C).

    Lemma Batch_contents_rw1 {c}:
      Batch_contents (@Done A B C c) = vnil.
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_contents_rw2 {b a}:
      Batch_contents (Step b a) =
        vcons (length_Batch b) a (Batch_contents b).
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_make_rw1 {c}:
      Batch_make (@Done A B C c) = const c.
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_make_rw2 {b a}:
      Batch_make (Step b a) =
        fun v => Batch_make b (Vector_tl v) (Vector_hd v).
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_replace_rw1 {c} `{v: Vector _ A'}:
      Batch_replace_contents (@Done A B C c) v = Done c.
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_replace_rw2 {b a} `{v: Vector _ A'}:
      Batch_replace_contents (Step b a) v =
        Step (Batch_replace_contents b (Vector_tl v)) (Vector_hd v).
    Proof.
      reflexivity.
    Qed.

  End rw.

  (** ** Lemmas regarding <<shape>> *)
  (******************************************************************************)
  Section shape_lemmas.

    Section shape_induction.

      Context
        {A1 A2 B C : Type}
          {b1: Batch A1 B C}
          {b2: Batch A2 B C}
          (Hshape: shape b1 = shape b2)
          (P : forall C : Type,
              Batch A1 B C ->
              Batch A2 B C ->
              Prop)
          (IHdone:
            forall (C : Type) (c : C), P C (Done c) (Done c))
          (IHstep:
            forall (C : Type)
              (b1 : Batch A1 B (B -> C))
              (b2 : Batch A2 B (B -> C)),
              P (B -> C) b1 b2 ->
              forall (a1 : A1) (a2: A2)
                (Hshape: shape (Step b1 a1) = shape (Step b2 a2)),
                P C (Step b1 a1) (Step b2 a2)).

      Lemma Batch_shape_ind: P C b1 b2.
      Proof.
        induction b1 as [C c | C rest IHrest a].
        - destruct b2.
          + now inversion Hshape.
          + false.
        - destruct b2 as [c' | rest' a'].
          + false.
          + apply IHstep.
            * apply IHrest.
              auto.
              now inversion Hshape.
            * apply Hshape.
      Qed.

    End shape_induction.

    Lemma length_Batch_shape:
      forall `(b1: Batch A1 B C)
        `(b2: Batch A2 B C),
        shape b1 = shape b2 ->
        length_Batch b1 = length_Batch b2.
    Proof.
      introv Hshape.
      induction b1.
      - destruct b2.
        + now inversion Hshape.
        + false.
      - destruct b2.
        + false.
        + cbn. fequal.
          apply IHb1.
          now inversion Hshape.
    Qed.

    Lemma Batch_make_shape:
      forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
        shape b1 = shape b2 ->
        Batch_make b1 ~!~ Batch_make b2.
    Proof.
      introv Hshape.
      apply (Batch_shape_ind Hshape).
      - split; auto.
      - clear.
        introv Hsim; introv Hshape.
        split.
        + auto using length_Batch_shape.
        + introv Hsim'.
          do 2 rewrite Batch_make_rw2.
          rewrite (Vector_hd_sim Hsim').
          enough
            (cut: Batch_make b1 (Vector_tl v1) =
                    Batch_make b2 (Vector_tl v2))
            by now rewrite cut.
          auto using Vector_fun_sim_eq, Vector_tl_sim.
    Qed.

    (* This is true, but to prove it we need more lemmas *)
    Lemma Batch_make_shape_rev:
      forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
        Batch_make b1 ~!~ Batch_make b2 ->
        shape b1 = shape b2.
    Proof.
    Abort.

    Lemma Batch_replace_shape:
      forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
        shape b1 = shape b2 ->
        forall (A': Type),
          Batch_replace_contents
            (A' := A') b1
            ~!~ Batch_replace_contents
            (A' := A') b2.
    Proof.
      introv Hshape.
      apply (Batch_shape_ind Hshape).
      - clear. intros. now split.
      - intros. split.
        + auto using length_Batch_shape.
        + introv Hsim.
          do 2 rewrite Batch_replace_rw2.
          rewrite (Vector_hd_sim Hsim).
          fequal.
          apply H.
          auto using Vector_tl_sim.
    Qed.

    Lemma Batch_shape_spec:
      forall `(b: Batch A B C),
        shape b =
          Batch_replace_contents b (Vector_tt (length_Batch b)).
    Proof.
      intros.
      induction b.
      - reflexivity.
      - cbn.
        rewrite Vector_tl_vcons.
        rewrite Vector_hd_vcons.
        fequal.
        apply IHb.
    Qed.

  End shape_lemmas.

  (** ** Lemmas regarding <<Batch_make>> *)
  (******************************************************************************)
  Section Batch_make.

    Lemma Batch_make_sim1
            `(b: Batch A B C)
            `{v1: Vector (length_Batch b) B}
            `{v2: Vector (length_Batch b) B}
            (Hsim: v1 ~~ v2):
      Batch_make b v1 = Batch_make b v2.
    Proof.
      induction b.
      - reflexivity.
      - rewrite Batch_make_rw2.
        rewrite (IHb _ _ (Vector_tl_sim Hsim)).
        rewrite (Vector_hd_sim Hsim).
        reflexivity.
    Qed.

    (* This sort of lemma is very useful when the complexity of expression
     <<v1>> and <<v2>> obstructs tactics like <<rewrite>> *)
    Lemma Batch_make_sim2
            `(b1: Batch A B C)
            `(b2: Batch A B C)
            `{v1: Vector (length_Batch b1) B}
            `{v2: Vector (length_Batch b2) B}
            (Heq: b1 = b2)
            (Hsim: v1 ~~ v2):
      Batch_make b1 v1 = Batch_make b2 v2.
    Proof.
      now (subst; apply Batch_make_sim1).
    Qed.

    Lemma Batch_make_sim3
            `(b1: Batch A1 B C)
            `(b2: Batch A2 B C)
            `{v1: Vector (length_Batch b1) B}
            `{v2: Vector (length_Batch b2) B}
            (Heq: shape b1 = shape b2)
            (Hsim: v1 ~~ v2):
      Batch_make b1 v1 = Batch_make b2 v2.
    Proof.
      apply Vector_fun_sim_eq.
      apply Batch_make_shape.
      auto. assumption.
    Qed.

    Lemma Batch_make_coerce
            `(b: Batch A B C)
            `{v1: Vector (length_Batch b) B}
            `{v2: Vector n B}
            (Heq: n = length_Batch b):
      v1 ~~ v2 ->
      Batch_make b v1 = Batch_make b (coerce Heq in v2).
    Proof.
      subst.
      intros.
      apply Batch_make_sim1.
      rewrite coerce_Vector_eq_refl.
      assumption.
    Qed.

    (** Rewrite the <<Batch>> argument to an equal one by
      coercing the length proof in the vector. *)
    Lemma Batch_make_rw
            `(b1: Batch A B C)
            `(b2: Batch A B C)
            `{v: Vector (length_Batch b1) B}
            (Heq: b1 = b2):
      Batch_make b1 v =
        Batch_make b2 (rew [fun b => Vector (length_Batch b) B]
                           Heq in v).
    Proof.
      now (subst; apply Batch_make_sim1).
    Qed.

    Lemma Batch_make_compose
            `(b: Batch A B C)
            `(f: C -> D)
            `(Hsim: v1 ~~ v2):
      f (Batch_make b v1) =
        Batch_make (map (F := Batch A B) f b) v2.
    Proof.
      generalize dependent v2.
      generalize dependent v1.
      generalize dependent D.
      induction b as [C c | C rest IHrest].
      - reflexivity.
      - intros D f v1 v2 Hsim.
        change (map f (Step rest a)) with
          (Step (map (compose f) rest) a) in *.
        cbn in v2, v1.
        do 2 rewrite Batch_make_rw2.
        rewrite <- (Vector_hd_sim Hsim).
        change_left ((f ∘ Batch_make rest (Vector_tl v1)) (Vector_hd v1)).
        specialize (IHrest _ (compose f)).
        rewrite (IHrest (Vector_tl v1) (Vector_tl v2) (Vector_tl_sim Hsim)).
        reflexivity.
    Qed.

    Lemma Batch_make_compose_rw1
            `(b: Batch A B C)
            `(f: C -> D)
            (v: Vector (length_Batch b) B):
      f (Batch_make b v) =
        Batch_make (map (F := Batch A B) f b)
                   (coerce (batch_length_map _ _) in v).
    Proof.
      now rewrite (
              Batch_make_compose
                b f
                (v1 := v)
                (v2 :=coerce_Vector_length (batch_length_map _ _) v)
            ) by vector_sim.
    Qed.

    Lemma Batch_make_compose_rw2 `(b: Batch A B C) `(f: C -> D) v:
      Batch_make (map (F := Batch A B) f b) v =
        f (Batch_make b (coerce_Vector_length (eq_sym (batch_length_map _ _)) v)).
    Proof.
      rewrite (Batch_make_compose_rw1 b f).
      apply Batch_make_sim1.
      vector_sim.
    Qed.

  End Batch_make.

  (** ** Lemmas regarding <<Batch_make>> *)
  (******************************************************************************)
  Section Batch_replace.

    Lemma Batch_replace_sim1
            `(b: Batch A B C)
            `{v1: Vector (length_Batch b) A'}
            `{v2: Vector (length_Batch b) A'}
            (Hsim: v1 ~~ v2):
      Batch_replace_contents b v1 = Batch_replace_contents b v2.
    Proof.
      induction b.
      - reflexivity.
      - do 2 rewrite Batch_replace_rw2.
        rewrite (IHb _ _ (Vector_tl_sim Hsim)).
        rewrite (Vector_hd_sim Hsim).
        reflexivity.
    Qed.

    Lemma Batch_replace_sim2
            `(b1: Batch A B C)
            `(b2: Batch A B C)
            `{v1: Vector (length_Batch b1) A'}
            `{v2: Vector (length_Batch b2) A'}
            (Heq: b1 = b2)
            (Hsim: Vector_sim v1 v2):
      Batch_replace_contents b1 v1 = Batch_replace_contents b2 v2.
    Proof.
      now (subst; apply Batch_replace_sim1).
    Qed.

    Lemma Batch_replace_sim3
            `(b1: Batch A1 B C)
            `(b2: Batch A2 B C)
            `{v1: Vector (length_Batch b1) A'}
            `{v2: Vector (length_Batch b2) A'}
            (Heq: shape b1 = shape b2)
            (Hsim: v1 ~~ v2):
      Batch_replace_contents b1 v1 = Batch_replace_contents b2 v2.
    Proof.
      apply Vector_fun_sim_eq;
        auto using Batch_replace_shape.
    Qed.

    Lemma length_replace_contents:
      forall {A B C: Type} (b: Batch A B C) `(v: Vector _ A'),
        length_Batch b = length_Batch (Batch_replace_contents b v).
    Proof.
      intros.
      induction b.
      - reflexivity.
      - cbn. fequal.
        apply (IHb (Vector_tl v)).
    Qed.

    Lemma Batch_shape_replace_contents:
      forall {A A' B C: Type} (b: Batch A B C) `(v: Vector _ A'),
        shape b = shape (Batch_replace_contents b v).
    Proof.
      intros.
      induction b.
      - reflexivity.
      - cbn. fequal.
        apply (IHb (Vector_tl v)).
    Qed.

  End Batch_replace.

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

  (** ** Relating make and shape *)
  (******************************************************************************)
  Section make_shape.

    Lemma Batch_make_shape_rev:
      forall `(b1: Batch A B C) `(b2: Batch A2 B C),
        Batch_make b1 ~!~ Batch_make b2 ->
        shape b1 = shape b2.
    Proof.
      intros.
      unfold Vector_fun_sim in *.
      destruct H as [Hlen Hsim].
      induction b1.
      - destruct b2.
        * cbn in *.
          specialize (Hsim vnil vnil ltac:(reflexivity)).
          now inversion Hsim.
        * false.
      - destruct b2.
        + false.
        + cbn. fequal. apply IHb1.
          * now inversion Hlen.
          * intros v1 v2 Vsim.
            ext b.
            assert (Vsim': vcons _ b v1 ~~ vcons _ b v2).
            now apply vcons_sim.
            specialize (Hsim _ _ Vsim').
            cbn in Hsim.
            do 2 rewrite Vector_tl_vcons in Hsim.
            do 2 rewrite Vector_hd_vcons in Hsim.
            assumption.
    Qed.

    Corollary Batch_make_shape_iff:
      forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
        shape b1 = shape b2 <->
          Batch_make b1 ~!~ Batch_make b2.
    Proof.
      intros.
      split; auto using Batch_make_shape,
        Batch_make_shape_rev.
    Qed.

    Lemma Batch_replace_sim_if_make:
      forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
      Batch_make b1 ~!~ Batch_make b2 ->
      forall A',
        Batch_replace_contents (A' := A') b1 ~!~ Batch_replace_contents b2.
    Proof.
      introv Hshape.
      rewrite <- Batch_make_shape_iff in Hshape.
      intro.
      apply (Batch_shape_ind Hshape).
      - intros. split.
        + reflexivity.
        + intros v1 v2 Hsim.
          reflexivity.
      - intros. split.
        + auto using length_Batch_shape.
        + intros. cbn.
          fequal.
          * destruct H as [Hlen Hsim].
            apply Hsim.
            now apply Vector_tl_sim.
          * now apply Vector_hd_sim.
    Qed.

  End make_shape.

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
