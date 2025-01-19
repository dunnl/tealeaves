From Tealeaves.Classes Require Export
  Monoid
  Categorical.Applicative
  Categorical.Monad
  Categorical.ShapelyFunctor
  Kleisli.TraversableFunctor
  Kleisli.Theory.TraversableFunctor.

From Tealeaves.Functors Require Import
  Constant
  List
  VectorRefinement.

Import Monoid.Notations.
Import Applicative.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import Theory.TraversableFunctor.Notations.

#[local] Generalizable Variables ψ ϕ W F G M A B C D X Y O.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.
#[local] Arguments pure F%function_scope {Pure} {A}%type_scope _.
#[local] Arguments mult F%function_scope {Mult} {A B}%type_scope _.

(** ** <<runBatch>> specialized to monoids *)
(******************************************************************************)
Section runBatch_monoid.

  Context
    `{Monoid M}.

  Fixpoint runBatch_monoid
             {A B: Type} `(ϕ : A -> M) `(b : Batch A B C) : M :=
    match b with
    | Done _ _ _ c => monoid_unit M
    | Step _ _ _ rest a => runBatch_monoid (ϕ : A -> M) rest ● ϕ a
    end.

  Lemma runBatch_monoid1
          {A B: Type} : forall (ϕ : A -> M) `(b : Batch A B C),
      runBatch_monoid ϕ b = unconst (runBatch (Const M) (mkConst (tag := B) ∘ ϕ) _ b).
  Proof.
    intros. induction b.
    - easy.
    - cbn. now rewrite IHb.
  Qed.

  Lemma runBatch_monoid2 {A B} : forall (ϕ : A -> M) `(b : Batch A B C),
      runBatch_monoid ϕ b = runBatch (const M) (ϕ : A -> const M B) _ b.
  Proof.
    intros. induction b.
    - easy.
    - cbn. now rewrite IHb.
  Qed.

  Lemma runBatch_monoid_map
          {A B C C'} : forall (ϕ : A -> M) `(f : C -> C') (b : Batch A B C),
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
          {A B B'} : forall (ϕ : A -> M) `(f : B' -> B) `(b : Batch A B C),
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

(** * Length *)
(******************************************************************************)
From Tealeaves Require Import Misc.NaturalNumbers.

Section length.

  Fixpoint length_Batch {A B C : Type} (b : Batch A B C) : nat :=
    match b with
    | Done _ _ _ _ => 0
    | Step _ _ _ rest a => S (length_Batch (C := B -> C) rest)
    end.

  Lemma length_Batch_spec {A B C : Type} (b : Batch A B C):
    length_Batch b = runBatch (@const Type Type nat) (fun _ => 1) _ b.
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn. rewrite IHb.
      unfold_ops @Monoid_op_plus.
      lia.
  Qed.

 (* The length of a batch is the same as the length of the list we can extract from it *)
  Lemma batch_length1 : forall {A B C : Type} (b : Batch A B C),
      length_Batch b =
        length (runBatch (const (list A)) (ret list A) _ b).
  Proof.
    intros.
    induction b as [C c | C b IHb a].
    - reflexivity.
    - cbn. rewrite IHb.
      unfold_ops @Monoid_op_list.
      rewrite List.app_length.
      cbn. lia.
  Qed.

  Lemma batch_length_map:
    forall {A B C C': Type}
      (f : C -> C') (b : Batch A B C),
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
      (f : A -> A') (b : Batch A B C),
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
      (f : B' -> B) (b : Batch A B C),
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

  (** ** Misc *)
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


(** ** Reassembly operation *)
(******************************************************************************)
Section traversal_reassemble.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Fixpoint add_elements `(b : Batch A B C) `(l : list A') : Batch (option A') B C :=
    match b with
    | Done _ _ _ c => Done _ _ _ c
    | Step _ _ _ rest a =>
      match l with
      | nil => Step _ _ _ (add_elements rest nil) None
      | cons a l' => Step _ _ _ (add_elements rest l') (Some a)
      end
    end.

End traversal_reassemble.


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

Arguments extract_Batch (A B)%type_scope b : clear implicits.
Arguments traverse T%function_scope {Traverse} (G)%function_scope
  {H H0 H1} (A B)%type_scope _%function_scope _.
*)

(** ** Specification for <<traverse>> *)
(******************************************************************************)
Lemma traverse_spec
  (F : Type -> Type) `{Map F} `{Mult F} `{Pure F} `{! Applicative F}
  `(ϕ : A -> F A') (B C : Type) :
  traverse (T := BATCH1 B C) (G := F) ϕ =
    runBatch (F ∘ Batch A' B) (map F (batch A' B) ∘ ϕ) (A := A) (B := B) C.
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
    rewrite (ap_compose2 (Batch A' B) F).
    rewrite <- ap_map.
    compose near (runBatch (F ∘ Batch A' B) (map F (batch A' B) ∘ ϕ) (B -> C) rest) on right.
    rewrite (fun_map_map (F := F)).
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
Definition bindt_Batch (B C : Type) (G : Type -> Type)
  `{Map G} `{Pure G} `{Mult G} (A A' : Type) (f : A -> G (Batch A' B B))
  (b : Batch A B B) : G (Batch A' B B) :=
  map G join_Batch (traverse (T := BATCH1 B B) f b).
