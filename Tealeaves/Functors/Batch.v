From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.Applicative
  Classes.Categorical.Monad
  Classes.Categorical.ShapelyFunctor
  Classes.Kleisli.TraversableFunctor
  Functors.Early.Batch.

From Tealeaves.Functors Require Import
  List
  Constant
  VectorRefinement.

Import Early.Batch.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import VectorRefinement.Notations.

#[local] Generalizable Variables ψ ϕ W F G M A B C D X Y O.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.
#[local] Arguments pure F%function_scope {Pure} {A}%type_scope _.
#[local] Arguments mult F%function_scope {Mult} {A B}%type_scope _.

(** * <<foldMap>> Rewriting Lemmas *)
(******************************************************************************)
Section Batch_foldMap_rewriting.

  Context {A B C: Type}.

  Lemma foldMap_Batch_rw2:
    forall `{Monoid M}
      (f: A -> M) (a: A) (rest: Batch A B (B -> C)),
      foldMap (T := BATCH1 B C) f (rest ⧆ a) =
        foldMap f rest ● f a.
  Proof.
    intros.
    unfold foldMap.
    rewrite traverse_Batch_rw2.
    reflexivity.
  Qed.

End Batch_foldMap_rewriting.

(** ** <<foldMap>> Rewriting for << <⋆> >> *)
(******************************************************************************)
Lemma foldMap_Batch_map {A B C C': Type}:
  forall `{Monoid M}
    (f: A -> M)
    (g: C -> C')
    (b: Batch A B C),
    foldMap (T := BATCH1 B C) f b =
      foldMap (T := BATCH1 B C') f (map (Batch A B) g b).
Proof.
  intros.
  generalize dependent C'.
  induction b; intros.
  - reflexivity.
  - rewrite foldMap_Batch_rw2.
    rewrite map_Batch_rw2.
    rewrite foldMap_Batch_rw2.
    specialize (IHb _ (compose g)).
    rewrite IHb.
    reflexivity.
Qed.

Lemma foldMap_Batch_mult_Done {A B C D: Type}
  `{Monoid M}(f: A -> M):
  forall (c: C) (b2: Batch A B D),
    foldMap (T := BATCH1 B (C * D))
      f (Done c ⊗ b2) = foldMap f b2.
Proof.
  intros.
  induction b2.
  - reflexivity.
  - rewrite foldMap_Batch_rw2.
    rewrite <- IHb2.
    cbn.
    unfold_ops @Pure_const.
    rewrite monoid_id_r.
    change (Traverse_Batch1 B (B -> C * C0) (const M) Map_const
              (fun (X : Type) (_ : X) => Ƶ) Mult_const A False f)
      with (foldMap (T := BATCH1 B (B -> C * C0)) f).
    rewrite <- foldMap_Batch_map.
    reflexivity.
Qed.

Lemma foldMap_Batch_mult {A B C D: Type}
  `{Monoid M}(f: A -> M):
  forall (b1: Batch A B C) (b2: Batch A B D),
    foldMap (T := BATCH1 B (C * D))
      f (b1 ⊗ b2) =
      foldMap f b1 ● foldMap f b2.
Proof.
  intros.
  induction b2.
  - cbn.
    rewrite <- foldMap_Batch_map.
    unfold_ops @Pure_const.
    rewrite monoid_id_l.
    reflexivity.
  - rewrite foldMap_Batch_rw2.
    rewrite <- monoid_assoc.
    rewrite <- IHb2; clear IHb2.
    induction b1.
    + rewrite foldMap_Batch_mult_Done.
      rewrite foldMap_Batch_mult_Done.
      rewrite foldMap_Batch_rw2.
      reflexivity.
    + cbn.
      unfold_ops @Pure_const.
      rewrite monoid_id_r.
      change (Traverse_Batch1 B (B -> C * C0) (const M) Map_const
                (fun (X : Type) (_ : X) => Ƶ) Mult_const A False f)
        with (foldMap (T := BATCH1 B (B -> C * C0)) f).
      rewrite <- foldMap_Batch_map.
      reflexivity.
Qed.

Lemma foldMap_Batch_ap_rw2 {A B: Type}:
  forall `{Monoid M}
    (f: A -> M)
    {X Y: Type}
    (lhs: Batch A B (X -> Y))
    (rhs: Batch A B X),
    foldMap (T := BATCH1 B Y) f (lhs <⋆> rhs) =
      foldMap (T := BATCH1 B (X -> Y)) f lhs
        ● foldMap (T := BATCH1 B X) f rhs.
Proof.
  intros.
  unfold ap.
  rewrite <- foldMap_Batch_map.
  rewrite foldMap_Batch_mult.
  reflexivity.
Qed.

Section Batch_foldMap_rewriting_derived.

  Context {A B C: Type}.

  (** ** <<tolist>> *)
  (******************************************************************************)
  Import List.ListNotations.

  Lemma tolist_Batch_rw2: forall (b: Batch A B (B -> C)) (a: A),
      tolist (b ⧆ a) = tolist b ++ [a].
  Proof.
    intros.
    reflexivity.
  Qed.

  (** ** <<tosubset>> *)
  (******************************************************************************)
  Import Subset.Notations.
  #[export] Instance ToSubset_Batch1 {B C}: ToSubset (BATCH1 B C) :=
    ToSubset_Traverse.

  Lemma tosubset_Batch_rw2: forall (b: Batch A B (B -> C)) (a: A),
      tosubset (b ⧆ a) = tosubset b ∪ {{a}}.
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_Batch_rw2.
    reflexivity.
  Qed.

  (** ** <<a ∈ _>> *)
  (******************************************************************************)
  Import ContainerFunctor.Notations.

  Lemma element_of_Batch_rw2: forall `(b: Batch A B (B -> C)) a a',
      a' ∈ (b ⧆ a) = (a' ∈ b \/ a' = a).
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite element_of_to_foldMap.
    rewrite foldMap_Batch_rw2.
    reflexivity.
  Qed.

End Batch_foldMap_rewriting_derived.

(** * Simultaneous Induction on Two <<Batch>>es of the Same Shape *)
(******************************************************************************)
Section shape_induction.

  Context
    {A1 A2 B C : Type}
      {b1: Batch A1 B C}
      {b2: Batch A2 B C}
      (Hshape: shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2)
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
            (Hshape: shape (F := BATCH1 B C)  (Step b1 a1) =
                       shape (F := BATCH1 B C) (Step b2 a2)),
            P C (Step b1 a1) (Step b2 a2)).

  Lemma Batch_simultaneous_ind: P C b1 b2.
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

(*
(** * Miscellaneous *)
(******************************************************************************)

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
        unconst (runBatch (G := Const M)
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
        runBatch (G := const M) (ϕ: A -> const M B) b.
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

(** * The <<length_Batch>> Operation *)
(** This function is introduced because using <<plength>> has less desirable
    simplification behavior, which makes programming functions like <<Batch_make>>  difficult *)
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
      plength (T := BATCH1 B C) b.
  Proof.
    induction b.
    - reflexivity.
    - cbn. rewrite IHb.
      unfold_all_transparent_tcs.
      rewrite PeanoNat.Nat.add_1_r.
      reflexivity.
  Qed.

  Lemma length_Batch_spec2 {A B C: Type} (b: Batch A B C):
    length_Batch b =
      runBatch (G := @const Type Type nat) (fun _ => 1) b.
  Proof.
    rewrite length_Batch_spec.
    induction b.
    - reflexivity.
    - cbn. rewrite <- IHb.
      reflexivity.
  Qed.

  (** ** Rewriting Rules *)
  (** TODO *)
  (******************************************************************************)
  Lemma length_Batch_rw2 {A B C: Type}:
    forall (b: Batch A B (B -> C)) (a: A),
      length_Batch (b ⧆ a) = S (length_Batch b).
  Proof.
    reflexivity.
  Qed.

  (** ** Length is the Same as the Underlying <<list>> *)
  (* The length of a <<Batch>> is the same as the length of the
    list we can extract from it *)
  (******************************************************************************)
  Lemma batch_length1:
    forall {A B C: Type} (b: Batch A B C),
      length_Batch b =
        length (runBatch (G := const (list A))
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

  (** ** Length is Preserved By <<map>> *)
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

  (** ** Length is Preserved by <<cojoin_Batch>> *)
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

  (** ** Two Same-Shaped <<Batch>>es Have the Same Length*)
  (******************************************************************************)
  Lemma length_Batch_shape:
    forall `(b1: Batch A1 B C)
      `(b2: Batch A2 B C),
      shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2 ->
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

End length.

(** * Specification for <<traverse>> via <<runBatch>> *)
(******************************************************************************)
Lemma traverse_via_runBatch
  (G: Type -> Type) `{Map G} `{Mult G} `{Pure G} `{! Applicative G}
  `(ϕ: A -> G A') (B C: Type) :
  traverse (T := BATCH1 B C) (G := G) ϕ =
    runBatch (G := G ∘ Batch A' B) (map G (batch A' B) ∘ ϕ).
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
    compose near (runBatch (G := G ∘ Batch A' B)
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

(** ** Traversable Monad Laws *)
(** TODO *)


(** * Deconstructing <<Batch A B C>> into Shape and Contents *)
(******************************************************************************)
Section deconstruction.

  #[local] Generalizable Variables n v a.

  (** ** <<Batch_make>> and <<Batch_contents>> *)
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

  (** ** <<Batch_replace_contents>> *)
  (** This is <<make>> in the sense of <<put>>. *)
  (******************************************************************************)
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

  (** ** Relating <<tolist>> and <<Batch_contents>> *)
  (******************************************************************************)
  Ltac hide_rhs :=
    match goal with
    | |- ?lhs = ?rhs =>
        let name := fresh "rhs" in
        remember rhs as name
    end.

  Lemma tolist_Batch_contents {A B C}: forall (b: Batch A B C),
      proj1_sig (Batch_contents b) = List.rev (tolist b).
  Proof.
    intros.
    induction b.
    - reflexivity.
    - rewrite Batch_contents_rw2.
      hide_rhs; cbn; rewrite Heqrhs; clear Heqrhs.
      (* ^^ Simplify a hidden (length_Batch (b ⧆ a) without affecting RHS. *)
      (* ^^ rewrite Batch_contents_rw2 fails due to binders *)
      rewrite proj_vcons.
      rewrite tolist_Batch_rw2.
      rewrite List.rev_unit.
      rewrite <- IHb.
      reflexivity.
  Qed.

  (** ** Rewriting Rules for << <⋆> >> *)
  (******************************************************************************)
  Section rewrite_Batch_contents.

    Context {A B: Type}.

    Lemma Batch_contents_rw_pure:
      forall X (x: X), Batch_contents (pure (Batch A B) x) = vnil.
    Proof.
      intros.
      reflexivity.
    Qed.

    Lemma Batch_contents_rw_mult:
      forall {C D} (x: Batch A B C) (y: Batch A B D),
        Batch_contents (x ⊗ y) ~~
          Vector_append (Batch_contents y)
          (Batch_contents x).
    Proof.
      intros.
      unfold Vector_sim.
      rewrite tolist_Batch_contents.
      rewrite tolist_to_foldMap.
      rewrite foldMap_Batch_mult.
      unfold_ops @Monoid_op_list.
      rewrite List.rev_app_distr.
      rewrite proj_Vector_append.
      rewrite tolist_Batch_contents.
      rewrite tolist_Batch_contents.
      reflexivity.
    Qed.

    Lemma Batch_contents_rw_app:
      forall X Y (f: Batch A B (X -> Y)) (x: Batch A B X),
        Batch_contents (f <⋆> x) ~~
          Vector_append (Batch_contents x) (Batch_contents f).
    Proof.
      intros.
      unfold Vector_sim.
      rewrite tolist_Batch_contents.
      rewrite tolist_to_foldMap.
      rewrite proj_Vector_append.
      rewrite foldMap_Batch_ap_rw2.
      unfold_ops @Monoid_op_list.
      rewrite List.rev_app_distr.
      rewrite tolist_Batch_contents.
      rewrite tolist_Batch_contents.
      reflexivity.
    Qed.

  End rewrite_Batch_contents.

  (** ** Same Shape Iff Same <<Batch_make>> *)
  (******************************************************************************)
  Lemma Batch_make_shape:
    forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
      shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2 ->
      Batch_make b1 ~!~ Batch_make b2.
  Proof.
    introv Hshape.
    apply (Batch_simultaneous_ind Hshape).
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

  Lemma Batch_make_shape_rev:
    forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
      Batch_make b1 ~!~ Batch_make b2 ->
      shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2.
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
      shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2 <->
        Batch_make b1 ~!~ Batch_make b2.
  Proof.
    intros.
    split; auto using Batch_make_shape,
      Batch_make_shape_rev.
  Qed.

  (** ** Two Lemmas for <<shape>> and <<length_Batch>> *)
  (******************************************************************************)
  Lemma Batch_shape_spec:
    forall `(b: Batch A B C),
      shape (F := BATCH1 B C) b =
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

  Corollary Batch_make_sim_length:
    forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
      (forall (A': Type),
          Batch_make b1
            ~!~ Batch_make b2) ->
      length_Batch b1 = length_Batch b2.
  Proof.
    intros.
    eapply Vector_fun_sim_length.
    apply (H False).
  Qed.

  Corollary Batch_replace_contents_sim_length:
    forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
      (forall (A': Type),
          Batch_replace_contents
            (A' := A') b1
            ~!~ Batch_replace_contents
            (A' := A') b2) ->
      length_Batch b1 = length_Batch b2.
  Proof.
    intros.
    eapply Vector_fun_sim_length.
    apply (H False).
  Qed.

  (** ** Same Shape Implies Same <<Batch_replace_contents>> *)
  (******************************************************************************)
  Lemma Batch_replace_contents_shape:
    forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
      shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2 ->
      forall (A': Type),
        Batch_replace_contents
          (A' := A') b1
          ~!~ Batch_replace_contents
          (A' := A') b2.
  Proof.
    introv Hshape.
    apply (Batch_simultaneous_ind Hshape).
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

  Corollary Batch_replace_contents_shape_rev:
    forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
    (forall (A': Type),
      Batch_replace_contents
        (A' := A') b1
        ~!~ Batch_replace_contents
        (A' := A') b2) ->
    shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2.
  Proof.
    introv Hsim.
    rewrite Batch_shape_spec.
    rewrite Batch_shape_spec.
    apply Hsim.
    enough (length_Batch b1 = length_Batch b2).
    { rewrite H. reflexivity. }
    now apply Batch_replace_contents_sim_length.
  Qed.

  Corollary Batch_replace_contents_shape_iff:
    forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
    (forall (A': Type),
      Batch_replace_contents
        (A' := A') b1
        ~!~ Batch_replace_contents
        (A' := A') b2) <->
      shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2.
  Proof.
    intros. split.
    - intros. now apply Batch_replace_contents_shape_rev.
    - intros. now apply Batch_replace_contents_shape.
  Qed.

  (** ** <<Batch_make>> Equal Iff <<Batch_replace_contents>> Equal *)
  (******************************************************************************)
  Lemma Batch_replace_sim_iff_make_sim:
    forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
      Batch_make b1 ~!~ Batch_make b2 <->
      forall A', Batch_replace_contents (A' := A') b1 ~!~
              Batch_replace_contents b2.
  Proof.
    intros.
    rewrite <- Batch_make_shape_iff.
    rewrite <- Batch_replace_contents_shape_iff.
    reflexivity.
  Qed.

  (** ** Similarity Lemmas for <<Batch_make>> *)
  (******************************************************************************)
  Lemma Batch_make_sim1
    `(b: Batch A B C)
    `{v1: Vector (length_Batch b) B}
    `{v2: Vector (length_Batch b) B}
    (Hsim: v1 ~~ v2):
    Batch_make b v1 = Batch_make b v2.
  Proof.
    apply Vector_sim_eq in Hsim.
    now subst.
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
    subst.
    now (subst; apply Batch_make_sim1).
  Qed.

  Lemma Batch_make_sim3
    `(b1: Batch A1 B C)
    `(b2: Batch A2 B C)
    `{v1: Vector (length_Batch b1) B}
    `{v2: Vector (length_Batch b2) B}
    (Heq: shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2)
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
    rewrite coerce_Vector_eq_refl.
    apply Batch_make_sim1.
    assumption.
  Qed.

  (** Rewrite the <<Batch>> argument to an equal one by
      coercing the length proof in the vector. *)
  Lemma Batch_make_rw_alt
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

  Lemma Batch_make_rw
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

  (** ** Similarity Laws for <<Batch_replace_contents>> *)
  (******************************************************************************)
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
    (Heq: shape (F := BATCH1 B C) b1 = shape (F := BATCH1 B C) b2)
    (Hsim: v1 ~~ v2):
    Batch_replace_contents b1 v1 = Batch_replace_contents b2 v2.
  Proof.
    apply Vector_fun_sim_eq; auto.
    now apply Batch_replace_contents_shape_iff.
  Qed.

  (** ** Naturality of <<Batch_make>> *)
  (******************************************************************************)
  Lemma Batch_make_natural
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

  Lemma Batch_make_natural_rw1
    `(b: Batch A B C)
    `(f: C -> D)
    (v: Vector (length_Batch b) B):
    f (Batch_make b v) =
      Batch_make (map (Batch A B) f b)
        (coerce (batch_length_map _ _) in v).
  Proof.
    now rewrite (
        Batch_make_natural
          b f
          (v1 := v)
          (v2 :=coerce_Vector_length (batch_length_map _ _) v)
      ) by vector_sim.
  Qed.

  Lemma Batch_make_natural_rw2 `(b: Batch A B C) `(f: C -> D) v:
    Batch_make (map (Batch A B) f b) v =
      f (Batch_make b (coerce_Vector_length (eq_sym (batch_length_map _ _)) v)).
  Proof.
    rewrite (Batch_make_natural_rw1 b f).
    apply Batch_make_sim1.
    vector_sim.
  Qed.

  (** ** Naturality of <<Batch_contents>> *)
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

  (** ** Specification for <<Batch_replace_contents>> *)
  (*******************************************************************************)
  Lemma Batch_replace_contents_spec {A A' B C}:
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
      rewrite Batch_make_natural_rw2.
      rewrite <- (Vector_hd_coerce_eq (Heq := Heq)).
      fequal.
      specialize (IHb (Vector_tl v) (length_cojoin_Batch b)).
      rewrite IHb.
      apply Batch_make_sim1.
      vector_sim.
  Qed.

  (** ** Replacing Contents Does Not Change <<length_Batch>>, <<shape>>, or <<Batch_make>> *)
  (*******************************************************************************)
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

  Lemma Batch_make_replace_contents {A A' B C}:
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

  Lemma Batch_shape_replace_contents:
    forall {A A' B C: Type} (b: Batch A B C) `(v: Vector _ A'),
      shape (F := BATCH1 B C) b =
        shape (F := BATCH1 B C) (Batch_replace_contents b v).
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn. fequal.
      apply (IHb (Vector_tl v)).
  Qed.

  (** * Lens-like laws *)
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

  End lens_laws.

  (** ** Batch is Shapely *)
  (******************************************************************************)
  Section Batch_shapely.

    Context {A B C: Type}.

    Lemma Batch_shapeliness: forall (b1 b2: Batch A B C),
        (shape (F := BATCH1 B C) b1 =
           shape (F := BATCH1 B C) b2) ->
        tolist (F := BATCH1 B C) b1 = tolist b2 ->
        b1 = b2.
    Proof.
      introv Hshape.
      apply (Batch_simultaneous_ind Hshape).
      - intros; reflexivity.
      - intros X b1' b2' Heq a1 a2 Hshape' Hlist.
        rewrite tolist_Batch_rw2 in Hlist.
        rewrite tolist_Batch_rw2 in Hlist.
        do 2 change (?x::nil) with (ret list _ x) in Hlist.
        assert (a1 = a2).
        { eapply list_app_inv_r2; eauto. }
        assert (b1' = b2').
        { apply Heq. eapply list_app_inv_l2.
          eauto. }
        subst.
        reflexivity.
    Qed.

  End Batch_shapely.

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
    rewrite (Batch_make_natural_rw2 b (precompose f) v').
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

(** ** Misc *)
(******************************************************************************)
Section spec.

  Lemma runBatch_const_contents:
    forall `{Applicative G} `(b: Batch A B C)
      (x: G B) `(v: Vector _ A'),
      runBatch (G := G) (const x) b =
        runBatch (G := G) (const x)
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

(** * Representation theorems *)
(******************************************************************************)
Lemma runBatch_repr1 `{Applicative G}:
  forall `(b: Batch A B C) (f: A -> G B),
    map G (Batch_make b)
      (traverse (T := Vector (length_Batch b)) f (Batch_contents b)) =
      forwards (runBatch (G := Backwards G) (mkBackwards ∘ f) b).
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
    runBatch f b =
      map G (Batch_make b)
        (forwards (traverse (G := (Backwards G))
                     (T := Vector (length_Batch b))
                     (mkBackwards ∘ f)
                     (Batch_contents b))).
Proof.
  intros.
  symmetry.
  change_left
    (forwards
       (map (Backwards G) (Batch_make b)
          (traverse (G := Backwards G) (mkBackwards ∘ f) (Batch_contents b)))).
  rewrite runBatch_repr1.
  rewrite runBatch_via_traverse.
  rewrite runBatch_via_traverse.
  change_left
    (map G extract_Batch
       (forwards (
            forwards (
                traverse (G := Backwards (Backwards G))
                  (mkBackwards ∘ (mkBackwards ∘ f)) b)))).
  rewrite traverse_double_backwards.
  reflexivity.
Qed.


(** * Annotating <<Batch>> with Proofs of Occurrence *)
(******************************************************************************)
Require Import ContainerFunctor.

Import ContainerFunctor.Notations.
Import Applicative.Notations.
Import Functors.Subset.
Import Subset.Notations.

Section annotate_Batch_elements.

  (** ** Lemmas regarding <<tosubset>> *)
  (******************************************************************************)
  Definition tosubset_Step1 {A B C:Type}:
    forall (a': A) (rest: Batch A B (B -> C)),
      forall (a: A),
        tosubset (F := BATCH1 B (B -> C)) rest a ->
        tosubset (F := BATCH1 B C) (Step rest a') a.
  Proof.
    introv.
    rewrite tosubset_Batch_rw2.
    simpl_subset.
    tauto.
  Defined.

  Definition tosubset_Step2 {A B C:Type}:
    forall (rest: Batch A B (B -> C)) (a: A),
      tosubset (F := BATCH1 B C) (Step rest a) a.
  Proof.
    intros.
    rewrite tosubset_Batch_rw2.
    simpl_subset.
    tauto.
  Qed.

  Definition element_of_Step1 {A B C:Type}:
    forall (a': A) (rest: Batch A B (B -> C)),
    forall (a: A),
      a ∈ rest ->
      a ∈ (Step rest a').
  Proof.
    introv.
    rewrite element_of_Batch_rw2.
    tauto.
  Defined.

  Definition element_of_Step2 {A B C:Type}:
    forall (rest: Batch A B (B -> C)) (a: A),
      a ∈ (Step rest a).
  Proof.
    intros.
    rewrite element_of_Batch_rw2.
    tauto.
  Qed.

  (** ** Annotation Operation *)
  (******************************************************************************)
  Definition sigMap {A: Type} (P Q: A -> Prop) (Himpl: forall a, P a -> Q a):
    sig P -> sig Q :=
    fun σ => match σ with
          | exist _ a h => exist Q a (Himpl a h)
          end.

  Lemma annotate_occurrence_helper {A B C: Type}:
    forall (a: A) (b_orig: Batch A B (B -> C))
      (b_recc: Batch {a'| element_of (F := BATCH1 B (B -> C))
                           a' b_orig} B (B -> C)),
      Batch {a'| element_of (F := BATCH1 B C) a' (b_orig ⧆ a)} B (B -> C).
  Proof.
    intros a b_orig b_recc.
    apply (map (BATCH1 B (B -> C))
             (sigMap (fun a0 : A => a0 ∈ b_orig)
                (fun a0 : A => a0 ∈ (b_orig ⧆ a))
                (element_of_Step1 a b_orig)) b_recc).
  Defined.

  Fixpoint annotate_occurrence
   {A B C: Type}
   (b: Batch A B C):
    Batch {a| element_of (F := BATCH1 B C) a b} B C :=
    match b with
    | Done c => Done c
    | Step rest a =>
        Step (annotate_occurrence_helper a rest (annotate_occurrence rest))
          (exist (tosubset (rest ⧆ a))
          a (element_of_Step2 rest a))
    end.

  (** * <<runBatch>> Assuming Proofs of Occurrence *)
  (******************************************************************************)
  Definition runBatch_with_occurrence
    {A B C} (G: Type -> Type)
    `{Applicative G}:
    forall (b: Batch A B C)
      `(f: {a | element_of (F := BATCH1 B C) a b} -> G B), G C :=
    fun b f => runBatch f (annotate_occurrence b).

End annotate_Batch_elements.
