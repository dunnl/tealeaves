From Tealeaves Require Import
  Classes.Categorical.Applicative.

Import Applicative.Notations.

(** * Batch of Two Parameters *)
(**********************************************************************)
Inductive Batch2 (B1 B2 A1 A2 C: Type): Type :=
| Done2: C -> Batch2 B1 B2 A1 A2 C
| StepB: Batch2 B1 B2 A1 A2 (B2 -> C) -> B1 -> Batch2 B1 B2 A1 A2 C
| StepA: Batch2 B1 B2 A1 A2 (A2 -> C) -> A1 -> Batch2 B1 B2 A1 A2 C.

#[global] Arguments Done2 {B1 B2 A1 A2 C}%type_scope _.
#[global] Arguments StepA {B1 B2 A1 A2 C}%type_scope _ _.
#[global] Arguments StepB {B1 B2 A1 A2 C}%type_scope _ _.

(** ** Functor Instance *)
(**********************************************************************)

(** *** Map Operations *)
(**********************************************************************)
Fixpoint map_Batch2 {B1 B2 A1 A2: Type} {C1 C2: Type} (f: C1 -> C2)
  (b: Batch2 B1 B2 A1 A2 C1): Batch2 B1 B2 A1 A2 C2 :=
  match b with
  | Done2 c => Done2 (f c)
  | StepB mk a => StepB (map_Batch2 (compose f) mk) a
  | StepA mk b => StepA (map_Batch2 (compose f) mk) b
  end.

#[export] Instance Map_Batch2 {B1 B2 A1 A2: Type}:
  Map (Batch2 B1 B2 A1 A2) :=
  @map_Batch2 B1 B2 A1 A2.

(** ** Applicative Instance *)
(**********************************************************************)

(** *** Operations *)
(**********************************************************************)
#[export] Instance Pure_Batch2 {B1 B2 A1 A2}:
  Pure (@Batch2 B1 B2 A1 A2) :=
  @Done2 B1 B2 A1 A2.

#[program] Fixpoint mult_Batch {B1 B2 A1 A2} {C1 C2: Type}
  (b1: Batch2 B1 B2 A1 A2 C1)
  (b2: Batch2 B1 B2 A1 A2 C2):
  Batch2 B1 B2 A1 A2 (C1 * C2) :=
  match b2 with
  | Done2 c2 =>
      map (F := Batch2 B1 B2 A1 A2) (fun (c1: C1) => (c1, c2)) b1
  | StepB mk a =>
      StepB
        (map (F := Batch2 B1 B2 A1 A2)
           strength_arrow (mult_Batch b1 mk))
        a
  | StepA mk b =>
      StepA
        (map (F := Batch2 B1 B2 A1 A2)
           strength_arrow (mult_Batch b1 mk))
        b
  end.

#[export] Instance Mult_Batch2 {B1 B2 A1 A2: Type}:
  Mult (Batch2 B1 B2 A1 A2) :=
  fun C1 C2 => uncurry (@mult_Batch B1 B2 A1 A2 C1 C2).

(** ** Operation <<runBatch2>> *)
(**********************************************************************)
Fixpoint runBatch2 {B1 B2 A1 A2: Type}
  (F: Type -> Type) `{Map F} `{Mult F} `{Pure F}
  (ϕB: B1 -> F B2)
  (ϕA: A1 -> F A2)
  {C: Type} (b: Batch2 B1 B2 A1 A2 C): F C :=
  match b with
  | Done2 c => pure c
  | StepB mk b => runBatch2 F ϕB ϕA (C := B2 -> C) mk <⋆> ϕB b
  | StepA mk a => runBatch2 F ϕB ϕA (C := A2 -> C) mk <⋆> ϕA a
  end.

#[export] Instance ApplicativeMorphism_runBatch
  (B B' A A': Type) (G: Type-> Type) `{Applicative G}
  (ϕB: B -> G B') (ϕA: A -> G A'):
  ApplicativeMorphism (Batch2 B B' A A') G (fun C => runBatch2 G ϕB ϕA).
Proof.
  constructor; try typeclasses eauto.
  - intros. now rewrite natural_runBatch.
  - intros. easy.
  - intros. apply appmor_mult_runBatch.
Qed.


(** * <<Batch>> as a Parameterized Comonad *)
(**********************************************************************)
Section parameterized.

  #[local] Unset Implicit Arguments.

  (** ** Operations <<extract_Batch>> and <<cojoin_Batch>> *)
  (********************************************************************)
  Fixpoint extract_Batch2 {B A C: Type} (b: Batch2 B B A A C): C :=
    match b with
    | Done2 c => c
    | StepA mk a => extract_Batch2 mk a
    | StepB mk b => extract_Batch2 mk b
    end.

  Fixpoint cojoin_Batch2 {B B' A A' X Y C: Type}
    (b: Batch2 B B' A A' C):
    Batch2 B X A Y (Batch2 X B' Y A' C) :=
    match b with
    | Done2 c => Done2 (Done2 c)
    | StepA rest a =>
        StepA (map (StepA) (cojoin_Batch2 (Y := Y) (X := X) rest)) a
    | StepB rest a =>
        StepB (map (StepB) (cojoin_Batch2 (Y := Y) (X := X) rest)) a
    end.

  (** ** Rewriting Principles *)
  (********************************************************************)
  Lemma extract_Batch_rw0:
    forall (A B C: Type) (c: C),
      extract_Batch2 (B := B) (A := A) (Done2 c) = c.
  Proof.
    reflexivity.
  Qed.

  Lemma extract_Batch_rw1:
    forall (B A C: Type) (rest: Batch2 B B A A (A -> C)) (a: A),
      extract_Batch2 (StepA rest a) = extract_Batch2 rest a.
  Proof.
    reflexivity.
  Qed.

  Lemma extract_Batch_rw2:
    forall (B A C: Type) (rest: Batch2 B B A A (B -> C)) (b: B),
      extract_Batch2 (StepB rest b) = extract_Batch2 rest b.
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_rw0:
    forall (B A C X Y: Type) (c: C),
      cojoin_Batch2 (X := X) (Y := Y)
        (Done2 (B1 := B) (B2 := B) (A1 := A) (A2 := A) c) =
        Done2 (Done2 c).
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_rw1:
    forall (B B' A A' C X Y: Type) (rest: Batch2 B B' A A' (A' -> C)) (a: A),
      cojoin_Batch2 (StepA rest a) =
        StepA (map (F := Batch2 B B' A A') StepA (cojoin_Batch2 rest)) a.
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_rw2:
    forall (B B' A A' C X Y: Type) (rest: Batch2 B B' A A' (B' -> C)) (b: B),
      cojoin_Batch2 (StepB rest b) =
        StepB (map (F := Batch2 B B' A A') StepB (cojoin_Batch2 rest)) b.
  Proof.
    reflexivity.
  Qed.

  (** ** <<extract_Batch2>> as <<runBatch (fun A => A) id>> *)
  (********************************************************************)
  Lemma extract_Batch_to_runBatch2: forall (A B: Type),
      @extract_Batch2 B A =
        (fun C => runBatch2 (fun A => A) (@id B) (@id A) (C := C)).
  Proof.
    intros.
    ext C.
    ext b.
    induction b.
    - reflexivity.
    - cbn. rewrite IHb.
      reflexivity.
    - cbn. rewrite IHb.
      reflexivity.
  Qed.

  (*
  (** ** <<cojoin_Batch2>> as <<runBatch double_batch>> *)
  (********************************************************************)
  Definition double_batch {B B' A A' C: Type}:
    A -> Batch2 B B' A A' (Batch B C C) :=
    map (Batch A B) (batch B C) ∘ (batch A B).

  Lemma double_batch_rw {A B C: Type} (a: A):
    double_batch (B := B) (C := C) a =
      Done A B (B -> Batch B C C) (batch B C) ⧆ a.
  Proof.
    reflexivity.
  Qed.

  Lemma double_batch_spec: forall (A B C: Type),
      double_batch = batch B C ⋆2 batch A B.
  Proof.
    reflexivity.
  Qed.
  Lemma cojoin_Batch_to_runBatch: forall (A B C: Type),
      @cojoin_Batch2 A B C =
        runBatch (Batch A B ∘ Batch B C) double_batch.
  Proof.
    intros. ext D.
    ext b.
    induction b as [D d | D rest IHrest a].
    - reflexivity.
    - cbn.
      compose near (runBatch (Batch A B ∘ Batch B C) double_batch (C -> D) rest).
      rewrite (fun_map_map (F := Batch A B)).
      compose near (runBatch (Batch A B ∘ Batch B C) double_batch (C -> D) rest).
      rewrite (fun_map_map (F := Batch A B)).
      compose near (runBatch (Batch A B ∘ Batch B C) double_batch (C -> D) rest).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite <- IHrest.
      fequal.
      fequal.
      clear.
      ext rest b. cbn.
      unfold compose, id.
      fequal.
      compose near rest.
      rewrite fun_map_map.
      compose near rest.
      rewrite fun_map_map.
      rewrite fun_map_id.
      reflexivity.
  Qed.
  *)

  (** ** <<extract_Batch>> and <<cojoin_Batch2>> as Applicative Homomorphisms *)
  (********************************************************************)
  #[export] Instance ApplicativeMorphism_extract_Batch2:
    forall (B A: Type),
      ApplicativeMorphism (Batch2 B B A A) (fun A => A) (@extract_Batch2 B A).
  Proof.
    intros.
    rewrite extract_Batch_to_runBatch2.
    apply ApplicativeMorphism_runBatch2.
  Qed.

  #[export] Instance ApplicativeMorphism_cojoin_Batch2:
    forall (A B C: Type),
      ApplicativeMorphism (Batch A C) (Batch A B ∘ Batch B C)
        (@cojoin_Batch2 A B C).
  Proof.
    intros.
    rewrite cojoin_Batch_to_runBatch.
    apply ApplicativeMorphism_runBatch.
  Qed.
