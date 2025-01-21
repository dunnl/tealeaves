From Tealeaves.Classes Require Export
  Monoid
  Categorical.Applicative
  Categorical.Monad
  Categorical.ShapelyFunctor
  Kleisli.TraversableFunctor.

From Tealeaves.Functors Require Import
  Early.Batch
  Constant.


Import Early.Batch.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import Kleisli.TraversableFunctor.Notations.

#[local] Generalizable Variables ψ ϕ W F G M A B C D X Y O.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.
#[local] Arguments pure F%function_scope {Pure} {A}%type_scope _.
#[local] Arguments mult F%function_scope {Mult} {A B}%type_scope _.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.

(** * Miscellaneous *)
(******************************************************************************)
(*
Instance: forall B, Pure (BATCH1 B B).
Proof.
  unfold Pure.
  intros B A.
  apply batch.
Defined.

Instance: forall B, Mult (BATCH1 B B).
Proof.
  unfold Mult.
  intros B A A'.
  apply batch.
Defined.
 *)

(** * <<runBatch>> specialized to monoids *)
(******************************************************************************)
Section runBatch_monoid.

  Context
    `{Monoid M}.

  Fixpoint runBatch_monoid
    {A B: Type} `(ϕ: A -> M) `(b: Batch A B C): M :=
    match b with
    | Done c => monoid_unit M
    | Step rest a => runBatch_monoid (ϕ: A -> M) rest ● ϕ a
    end.

  Lemma runBatch_monoid1
    {A B: Type}:
    forall (ϕ: A -> M) `(b: Batch A B C),
      runBatch_monoid ϕ b =
        unconst (runBatch (F := Const M)
                   (mkConst (tag := B) ∘ ϕ) b).
  Proof.
    intros. induction b.
    - easy.
    - cbn. now rewrite IHb.
  Qed.

  Lemma runBatch_monoid2 {A B}:
    forall (ϕ: A -> M)
      `(b: Batch A B C),
      runBatch_monoid ϕ b =
        runBatch (F := const M) (ϕ: A -> const M B) b.
  Proof.
    intros. induction b.
    - easy.
    - cbn. now rewrite IHb.
  Qed.

  Lemma runBatch_monoid_map
          {A B C C'}: forall (ϕ: A -> M) `(f: C -> C') (b: Batch A B C),
      runBatch_monoid ϕ b =
        runBatch_monoid ϕ (map (Batch A B) f b).
  Proof.
    intros.
    generalize dependent C'.
    induction b; intros.
    - reflexivity.
    - cbn.
      rewrite <- IHb.
      reflexivity.
  Qed.

  Lemma runBatch_monoid_mapsnd
          {A B B'}: forall (ϕ: A -> M) `(f: B' -> B) `(b: Batch A B C),
      runBatch_monoid ϕ b =
        runBatch_monoid ϕ (mapsnd_Batch B' B f b).
  Proof.
    intros.
    rewrite runBatch_monoid2.
    rewrite runBatch_monoid2.
    rewrite <- runBatch_mapsnd.
    intros. induction b.
    - easy.
    - cbn. now rewrite IHb.
  Qed.

End runBatch_monoid.

(** * Length of <<Batch>> *)
(******************************************************************************)
From Tealeaves Require Import Misc.NaturalNumbers.

Section length.

  Fixpoint length_Batch {A B C: Type} (b: Batch A B C): nat :=
    match b with
    | Done _  => 0
    | Step rest a => S (length_Batch (C := B -> C) rest)
    end.

  Lemma length_Batch_spec {A B C: Type} (b: Batch A B C):
    length_Batch b =
      runBatch (F := @const Type Type nat) (fun _ => 1) b.
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn. rewrite IHb.
      unfold_ops @Monoid_op_plus.
      lia.
  Qed.

 (* The length of a batch is the same as the length of the
    list we can extract from it *)
  Lemma batch_length1:
    forall {A B C: Type} (b: Batch A B C),
      length_Batch b =
        length (runBatch (F := const (list A))
                  (ret list A) b).
  Proof.
    intros.
    induction b as [C c | C b IHb a].
    - reflexivity.
    - cbn. rewrite IHb.
      unfold_ops @Monoid_op_list.
      rewrite List.app_length.
      cbn. lia.
  Qed.

  (** *** Length commutes with maps *)
  (******************************************************************************)
  Lemma batch_length_map:
    forall {A B C C': Type}
      (f: C -> C') (b: Batch A B C),
      length_Batch b =
        length_Batch (map (Batch A B) f b).
  Proof.
    intros.
    generalize dependent C'.
    induction b as [C c | C b IHb a]; intros.
    - reflexivity.
    - cbn.
      fequal.
      specialize (IHb _ (compose f)).
      auto.
  Qed.

  Lemma batch_length_mapfst:
    forall {A A' B C: Type}
      (f: A -> A') (b: Batch A B C),
      length_Batch b =
        length_Batch (mapfst_Batch A A' f b).
  Proof.
    intros.
    induction b as [C c | C b IHb a].
    - reflexivity.
    - cbn. rewrite IHb.
      reflexivity.
  Qed.

  Lemma batch_length_mapsnd:
    forall {A B B' C: Type}
      (f: B' -> B) (b: Batch A B C),
      length_Batch b =
        length_Batch (mapsnd_Batch B' B f b).
  Proof.
    intros.
    induction b as [C c | C b IHb a]; intros.
    - reflexivity.
    - cbn.
      fequal.
      rewrite IHb.
      rewrite (batch_length_map ((precompose f))).
      reflexivity.
  Qed.

  (** *** Length of <<cojoin_Batch>> *)
  (******************************************************************************)
  Lemma length_cojoin_Batch:
    forall {A A' B C} (b: Batch A B C),
      length_Batch b = length_Batch (cojoin_Batch (B := A') b).
  Proof.
    induction b.
    - reflexivity.
    - cbn. fequal.
      rewrite IHb.
      rewrite <- batch_length_map.
      reflexivity.
  Qed.

End length.


(** * Partial Contents Replacement Operation *)
(******************************************************************************)
Section traversal_reassemble.

  Context
    (T: Type -> Type)
    `{TraversableFunctor T}.

  Fixpoint add_elements `(b: Batch A B C) `(l: list A'):
    Batch (option A') B C :=
    match b with
    | Done c => Done c
    | Step rest a =>
      match l with
      | nil => Step (add_elements rest nil) None
      | cons a l' => Step (add_elements rest l') (Some a)
      end
    end.

End traversal_reassemble.

(** * Specification for <<traverse>> via <<runBatch>> *)
(******************************************************************************)
Lemma traverse_via_runBatch
  (G: Type -> Type) `{Map G} `{Mult G} `{Pure G} `{! Applicative G}
  `(ϕ: A -> G A') (B C: Type) :
  traverse (T := BATCH1 B C) (G := G) ϕ =
    runBatch (F := G ∘ Batch A' B) (map G (batch A' B) ∘ ϕ).
Proof.
  intros.
  ext b.
  induction b as [C c | C rest IHrest].
  - rewrite runBatch_rw1.
    rewrite traverse_Batch_rw1.
    reflexivity.
  - rewrite runBatch_rw2.
    rewrite traverse_Batch_rw2'.
    rewrite IHrest.
    unfold compose at 6.
    rewrite (ap_compose2 (Batch A' B) G).
    rewrite <- ap_map.
    compose near (runBatch (F := G ∘ Batch A' B)
                    (map G (batch A' B) ∘ ϕ) rest) on right.
    rewrite (fun_map_map (F := G)).
    repeat fequal.
    ext b.
    unfold precompose, ap, compose.
    cbn.
    compose near b on right.
    rewrite (fun_map_map (F := Batch A' B)).
    compose near b on right.
    rewrite (fun_map_map (F := Batch A' B)).
    unfold compose. cbn.
    fequal.
    change (?f ○ id) with f.
    rewrite (fun_map_id).
    reflexivity.
Qed.

(** * <<Batch _ B C>> is a traversable monad *)
(******************************************************************************)

(** ** Operation *)
(******************************************************************************)
Definition bindt_Batch (B C: Type) (G: Type -> Type)
  `{Map G} `{Pure G} `{Mult G} (A A': Type) (f: A -> G (Batch A' B B))
  (b: Batch A B B): G (Batch A' B B) :=
  map G join_Batch (traverse (T := BATCH1 B B) f b).




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

From Tealeaves Require Import
  Functors.VectorRefinement.

(** * Deconstructing <<Batch A B C>> into Shape and Contents *)
(******************************************************************************)
Section deconstruction.

  #[local] Generalizable Variables n v a.

  (** * <<Batch_make>> and <<Batch_contents>> *)
  (******************************************************************************)
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

    Lemma Batch_make_rw_alt
      `(b1: Batch A B C)
      `(b2: Batch A B C)
      `{v: Vector (length_Batch b1) B}
      (Heq: b1 = b2):
      Batch_make b1 v =
        Batch_make b2
          (coerce
             (eq_ind_r
                (fun z => length_Batch z = length_Batch b2) eq_refl Heq)
            in v).
    Proof.
      subst. cbn.
      now rewrite coerce_Vector_eq_refl.
    Qed.

    Lemma Batch_make_compose
            `(b: Batch A B C)
            `(f: C -> D)
            `(Hsim: v1 ~~ v2):
      f (Batch_make b v1) =
        Batch_make (map (Batch A B) f b) v2.
    Proof.
      generalize dependent v2.
      generalize dependent v1.
      generalize dependent D.
      induction b as [C c | C rest IHrest].
      - reflexivity.
      - intros D f v1 v2 Hsim.
        change (map (Batch A B) f (Step rest a)) with
          (Step (map (Batch A B) (compose f) rest) a) in *.
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
        Batch_make (map (Batch A B) f b)
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
      Batch_make (map (Batch A B) f b) v =
        f (Batch_make b (coerce_Vector_length (eq_sym (batch_length_map _ _)) v)).
    Proof.
      rewrite (Batch_make_compose_rw1 b f).
      apply Batch_make_sim1.
      vector_sim.
    Qed.

  End Batch_make.

  (** ** Lemmas regarding <<Batch_contents>> *)
  (******************************************************************************)
  Lemma Batch_contents_natural: forall `(b: Batch A B C) `(f: A -> A'),
      map (Vector (length_Batch b)) f (Batch_contents b)
             ~~ Batch_contents (mapfst_Batch _ _ f b).
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn.
      rewrite map_Vector_vcons.
      apply vcons_sim.
      assumption.
  Qed.

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

End deconstruction.

(** * Theory About Batch *)
(******************************************************************************)
Section Batch_theory.

  Lemma Batch_make_precompose1:
    forall {A B C' C D: Type} (b: Batch A B (C -> D)) (f: C' -> C)
      (v: Vector (length_Batch b) B)
      (v': Vector (length_Batch (map _ (precompose f) b)) B)
      (Hsim: v ~~ v')
      (c: C'),
      Batch_make (map (Batch A B) (precompose f) b) v' c =
        Batch_make b v (f c).
  Proof.
    intros.
    rewrite (Batch_make_compose_rw2 b (precompose f) v').
    unfold precompose.
    fequal.
    apply Vector_sim_eq.
    apply Vector_coerce_sim_l'.
    symmetry.
    assumption.
  Qed.

  Lemma Batch_make_precompose2:
    forall {A B C' C D: Type} (b: Batch A B (C -> D)) (f: C' -> C)
      (v: Vector (length_Batch (map _ (precompose f) b)) B)
      (c: C'),
      Batch_make (map _ (precompose f) b) v c =
        Batch_make b (coerce eq_sym (batch_length_map (precompose f) b) in v) (f c).
  Proof.
    intros.
    apply Batch_make_precompose1.
    apply Vector_coerce_sim_l.
  Qed.

  Ltac hide_lhs :=
    match goal with
    | |- ?lhs = ?rhs =>
        let name := fresh "lhs" in
        remember lhs as name
    end.

  Lemma Batch_make_natural1:
    forall {A B B' C: Type} (b: Batch A B' C) (f: B -> B')
      (v: Vector (length_Batch b) B)
      (v': Vector (length_Batch (mapsnd_Batch B B' f b)) B),
      v ~~ v' ->
      Batch_make b (map _ f v) =
        Batch_make (mapsnd_Batch _ _ f b) v'.
  Proof.
    introv Hsim.
    induction b.
    - cbn in v, v'.
      rewrite (Vector_nil_eq v).
      rewrite (Vector_nil_eq v').
      reflexivity.
    - cbn in v, v'.
      (* LHS *)
      rewrite Batch_make_rw2.
      rewrite (Vector_surjective_pairing2 (v := v)).
      rewrite (map_Vector_vcons f (length_Batch b) _ (Vector_hd v)).
      rewrite Vector_tl_vcons.
      rewrite Vector_hd_vcons.
      (* RHS *)
      try rewrite (mapsnd_Batch_rw2 (B := B) f a b).
      (* ^^^ fails for some reason *)
      cbn.
      rewrite (Batch_make_precompose2 (mapsnd_Batch B B' f b) _).
      assert (cut: f (Vector_hd v) = f (Vector_hd v')).
      { inversion Hsim.
        fequal.
        apply (Vector_hd_sim Hsim). }
      rewrite cut.
      specialize (IHb (Vector_tl v)).
      specialize (IHb
                    (coerce eq_sym (batch_length_map (precompose f)
                                      (mapsnd_Batch B B' f b))
                      in Vector_tl v')).
      rewrite IHb.
      + reflexivity.
      + apply Vector_coerce_sim_r'.
        apply Vector_tl_sim.
        assumption.
  Qed.

  Lemma map_coerce_Vector:
    forall (n m: nat) (Heq: n = m)
      (A B: Type) (f: A -> B) (v: Vector n A),
      coerce Heq in (map _ f v) = map _ f (coerce Heq in v).
  Proof.
    intros.
    apply Vector_sim_eq.
    apply (transitive_Vector_sim (v2 := map _ f v)).
    - apply symmetric_Vector_sim.
      apply Vector_coerce_sim_r.
    - apply map_coerce_Vector.
  Qed.

  Lemma Batch_make_natural2:
    forall {A B B' C: Type} (b: Batch A B' C) (f: B -> B')
      (v: Vector (length_Batch (mapsnd_Batch B B' f b)) B),
      Batch_make (mapsnd_Batch _ _ f b) v =
        Batch_make b (coerce (eq_sym (batch_length_mapsnd f b)) in (map _ f v)).
  Proof.
    intros.
    symmetry.
    rewrite map_coerce_Vector.
    apply (Batch_make_natural1 b f _ v).
    apply Vector_coerce_sim_l.
  Qed.

End Batch_theory.
