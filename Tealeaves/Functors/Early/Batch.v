From Tealeaves.Classes Require Import
  Categorical.Applicative
  Categorical.Monad
  Kleisli.TraversableFunctor.

Import Applicative.Notations.
Import TraversableFunctor.Notations.

#[local] Generalizable Variables ψ ϕ W F G M A B C D X Y O.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments pure F%function_scope {Pure} {A}%type_scope _.
#[local] Arguments mult F%function_scope {Mult} {A B}%type_scope _.

(** * The [Batch] Functor *)
(******************************************************************************)
Inductive Batch (A B C: Type): Type :=
| Done: C -> Batch A B C
| Step: Batch A B (B -> C) -> A -> Batch A B C.

#[global] Arguments Done {A B C}%type_scope _.
#[global] Arguments Step {A B C}%type_scope _ _.

#[local] Arguments Done: clear implicits.
#[local] Arguments Step: clear implicits.

#[local] Infix "⧆" := (Step _ _ _) (at level 51, left associativity): tealeaves_scope.

#[global] Notation "'BATCH1' B C" := (fun A => Batch A B C) (at level 0, B at level 0, C at level 0).
#[global] Notation "'BATCH2' A C" := (fun B => Batch A B C) (at level 3).

(** ** Map Operations *)
(******************************************************************************)
Fixpoint map_Batch {A B: Type} (C1 C2: Type) (f: C1 -> C2) (b: Batch A B C1): Batch A B C2 :=
  match b with
  | Done _ _ _ c =>
      Done A B C2 (f c)
  | Step _ _ _ rest a =>
      Step A B C2 (@map_Batch A B (B -> C1) (B -> C2) (compose f) rest) a
  end.

#[export] Instance Map_Batch {A B: Type}: Map (Batch A B) := @map_Batch A B.

Fixpoint mapfst_Batch {B C: Type} (A1 A2: Type) (f: A1 -> A2) (b: Batch A1 B C): Batch A2 B C :=
  match b with
  | Done _ _ _  c => Done A2 B C c
  | Step _ _ _ rest a => Step A2 B C (mapfst_Batch A1 A2 f rest) (f a)
  end.

#[export] Instance Map_Batch1 {B C: Type}: Map (BATCH1 B C) := @mapfst_Batch B C.

Fixpoint mapsnd_Batch {A: Type} (B1 B2: Type) {C: Type} (f: B1 -> B2) (b: Batch A B2 C): Batch A B1 C :=
  match b with
  | Done _ _ _ c => Done A B1 C c
  | Step _ _ _ rest c => Step A B1 C
                          (map (Batch A B1) (precompose f)
                             (mapsnd_Batch B1 B2 f rest)) c
  end.

(** ** Rewriting Principles *)
(******************************************************************************)
Lemma map_Batch_rw1 {A B C1 C2: Type} `(f: C1 -> C2) (c: C1) :
  map (Batch A B) f (Done A B C1 c) = Done A B C2 (f c).
Proof.
  reflexivity.
Qed.

Lemma map_Batch_rw2 {A B C1 C2: Type} `(f: C1 -> C2) (a: A) (rest: Batch A B (B -> C1)) :
  map (Batch A B) f (rest ⧆ a) = map (Batch A B) (compose f) rest ⧆ a.
Proof.
  reflexivity.
Qed.

Lemma mapfst_Batch_rw1 {A1 A2 B C: Type} `(f: A1 -> A2) (c: C) :
  mapfst_Batch A1 A2 f (Done A1 B C c) = Done A2 B C c.
Proof.
  reflexivity.
Qed.

Lemma mapfst_Batch_rw2 {A1 A2 B C: Type} (f: A1 -> A2) (a: A1) (b: Batch A1 B (B -> C)) :
  mapfst_Batch A1 A2 f (b ⧆ a) = mapfst_Batch A1 A2 f b ⧆ f a.
Proof.
  reflexivity.
Qed.

Lemma mapsnd_Batch_rw1 {A B B' C: Type} `(f: B' -> B) (c: C) :
  mapsnd_Batch B' B f (Done A B C c) = Done A B' C c.
Proof.
  reflexivity.
Qed.

Lemma mapsnd_Batch_rw2 {A B B' C: Type} `(f: B -> B')
                       (a: A) (b: Batch A B' (B' -> C)) :
  mapsnd_Batch B B' f (b ⧆ a) =
    map (Batch A B) (precompose f) (mapsnd_Batch B B' f b) ⧆ a.
Proof.
  reflexivity.
Qed.

(** ** Functor Laws *)
(******************************************************************************)

(** *** In the <<A>> Argument *)
(******************************************************************************)
Lemma mapfst_id_Batch: forall (B C A: Type),
    mapfst_Batch A A (@id A) = @id (Batch A B C).
Proof.
  intros. ext b. induction b as [C c|C rest IHrest a].
  - reflexivity.
  - cbn. rewrite IHrest. reflexivity.
Qed.

Lemma mapfst_mapfst_Batch: forall (B C A1 A2 A3: Type) (f: A1 -> A2) (g: A2 -> A3),
    mapfst_Batch _ _ g ∘ mapfst_Batch _ _ f =
      mapfst_Batch (B := B) (C := C) _ _ (g ∘ f).
Proof.
  intros.
  ext b. unfold compose. induction b as [C c|C rest IHrest a].
  - reflexivity.
  - cbn. fequal.
    apply IHrest.
Qed.

#[export, program] Instance Functor_Batch1 {B C: Type}: Functor (BATCH1 B C) :=
  {| fun_map_id := @mapfst_id_Batch B C;
    fun_map_map := @mapfst_mapfst_Batch B C;
  |}.

(** *** In the <<B>> Argument *)
(** TODO *)
(******************************************************************************)

(** *** In the <<C>> Argument *)
(******************************************************************************)
Lemma map_id_Batch: forall (A B C: Type),
    map (Batch A B) (@id C) = @id (Batch A B C).
Proof.
  intros. ext b. induction b as [C c|C rest IHrest a].
  - reflexivity.
  - cbn.
    assert (lemma: compose (@id C) = @id (B -> C)).
    { reflexivity. } rewrite lemma.
    now rewrite IHrest.
Qed.

Lemma map_map_Batch: forall (A B C1 C2 C3: Type) (f: C1 -> C2) (g: C2 -> C3),
    map (Batch A B) g ∘ map (Batch A B) f = map (Batch A B) (g ∘ f).
Proof.
  intros.
  ext b. unfold compose.
  generalize dependent C3.
  generalize dependent C2.
  induction b; intros.
  - reflexivity.
  - cbn. fequal.
    specialize (IHb (B -> C2) (compose f)
                    (B -> C3) (compose g)).
    rewrite IHb.
    reflexivity.
Qed.

#[export, program] Instance Functor_Batch {A B: Type}: Functor (Batch A B) :=
  {| fun_map_id := @map_id_Batch A B;
     fun_map_map := @map_map_Batch A B;
  |}.

(** ** Commuting Independent <<map>>s *)
(******************************************************************************)
Lemma mapfst_map_Batch {B: Type} `(f: A1 -> A2) `(g: C1 -> C2) (b: Batch A1 B C1) :
  mapfst_Batch A1 A2 f (map (Batch A1 B) g b) = map (Batch A2 B) g (mapfst_Batch A1 A2 f b).
Proof.
  generalize dependent C2.
  generalize dependent B.
  induction b.
  - reflexivity.
  - intros.
    cbn. fequal.
    specialize (IHb (B -> C2) (compose g)).
    rewrite IHb.
    reflexivity.
Qed.

Lemma mapsnd_map_Batch {A: Type} `(f: B1 -> B2) `(g: C1 -> C2) (b: Batch A B2 C1) :
  mapsnd_Batch B1 B2 f (map (Batch A B2) g b) = map (Batch A B1) g (mapsnd_Batch B1 B2 f b).
Proof.
  generalize dependent C2.
  induction b.
  - reflexivity.
  - intros. cbn. fequal.
    rewrite IHb.
    compose near (mapsnd_Batch _ _ f b).
    do 2 rewrite (fun_map_map (F := Batch A B1)).
    do 2 rewrite <- IHb.
    reflexivity.
Qed.

Lemma mapfst_mapsnd_Batch: forall {C: Type} `(f: A1 -> A2) `(g: B1 -> B2) (b: Batch A1 B2 C),
    mapfst_Batch A1 A2 f (mapsnd_Batch B1 B2 g b) = mapsnd_Batch B1 B2 g (mapfst_Batch A1 A2 f b).
Proof.
  intros.
  generalize dependent f.
  generalize dependent g.
  induction b.
  - reflexivity.
  - intros. cbn. fequal. rewrite mapfst_map_Batch.
    now rewrite IHb.
Qed.

(** * Applicative Functor Instance *)
(******************************************************************************)
Section Applicative_Batch.

  Context
    {A B: Type}.

  (** ** Operations *)
  (******************************************************************************)
  #[export] Instance Pure_Batch: Pure (@Batch A B) :=
    fun (C: Type) (c: C) => Done A B C c.

  Fixpoint mult_Batch `(b1: Batch A B C) `(b2: Batch A B D): @Batch A B (C * D) :=
    match b2 with
    | Done _ _ _ d => map (Batch A B) (fun (c: C) => (c, d)) b1
    | Step _ _ _ rest a =>
        Step A B (C * D) (map (Batch A B) strength_arrow (mult_Batch b1 rest)) a
    end.

  #[export] Instance Mult_Batch: Mult (@Batch A B) :=
    fun C D '(b1, b2) => mult_Batch b1 b2.

  (** *** Examples of operations *)
  (******************************************************************************)
  (*
  Section demo.
    Context
      (A B C D: Type)
        (a1 a2 a3: A)
        (c1 c2 c3: C)
        (d1 d2 d3: D)
        (mk1: B -> C)
        (mk1': B -> D)
        (mk2: B -> B -> C).

    Compute Done A B C c1 ⊗ Done A B D d1.
    Compute Done A B C c1 ⊗ (Done A B (B -> D) mk1' ⧆ a1).
    Compute (Done A B _ mk1 ⧆ a1) ⊗ Done A B D d2.
    Compute (Done A B _ mk1 ⧆ a1) ⊗ (Done A B _ mk1' ⧆ a2).
    Compute (Done A B _ mk2 ⧆ a1 ⧆ a2) ⊗ (Done A B _ mk1' ⧆ a3).
  End demo.
  *)

  (** ** Rewriting Principles *)
  (******************************************************************************)
  Lemma mult_Batch_rw1: forall `(c: C) `(d: D),
      Done A B C c ⊗ Done A B D d = Done A B (C * D) (c, d).
  Proof.
    reflexivity.
  Qed.

  Lemma mult_Batch_rw2: forall `(d: D) `(b1: Batch A B C),
      b1 ⊗ Done A B D d = map (Batch A B) (pair_right d) b1.
  Proof.
    intros. induction b1; easy.
  Qed.

  Lemma mult_Batch_rw3: forall (D: Type) (b2: Batch A B (B -> D)) (a: A) `(b1: Batch A B C),
      b1 ⊗ (b2 ⧆ a) =
        map (Batch A B) strength_arrow (b1 ⊗ b2) ⧆ a.
  Proof.
    reflexivity.
  Qed.


  Lemma mult_Batch_rw4: forall `(b2: Batch A B D) `(c: C),
      Done A B C c ⊗ b2 = map (Batch A B) (pair c) b2.
  Proof.
    induction b2.
    - reflexivity.
    - intros. cbn; change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. rewrite IHb2.
      compose near b2 on left.
      now rewrite (fun_map_map (F := Batch A B)).
  Qed.

  Lemma mult_Batch_rw5: forall (a: A) `(b1: @Batch A B (B -> C)) `(d: D),
      (b1 ⧆ a) ⊗ Done A B D d =
        map (Batch A B) (costrength_arrow ∘ pair_right d) b1 ⧆ a.
  Proof.
    reflexivity.
  Qed.

  Lemma mult_Batch_rw6: forall `(b2: @Batch A B (B -> D)) `(c: C) (a: A),
      Done A B C c ⊗ (b2 ⧆ a) = map (Batch A B) (strength_arrow ∘ pair c) b2 ⧆ a.
  Proof.
    intros.
    rewrite mult_Batch_rw3.
    rewrite mult_Batch_rw4.
    compose near b2 on left.
    now rewrite (fun_map_map (F := Batch A B)).
  Qed.

  Lemma mult_Batch_rw7: forall (a1 a2: A) `(b1: Batch A B (B -> C)) `(b2: Batch A B (B -> D)),
      (b1 ⧆ a1) ⊗ (b2 ⧆ a2) =
        (map (Batch A B) strength_arrow ((b1 ⧆ a1) ⊗ b2)) ⧆ a2.
  Proof.
    reflexivity.
  Qed.

  (** ** Applicative Laws *)
  (******************************************************************************)
  Lemma app_pure_natural_Batch: forall `(f: C1 -> C2) (c: C1),
      map (Batch A B) f (pure (Batch A B) c) = pure (Batch A B) (f c).
  Proof.
    reflexivity.
  Qed.

  Lemma app_mult_natural_Batch1: forall (C1 C2 D: Type) (f: C1 -> C2) (b1: Batch A B C1) (b2: Batch A B D),
      map (Batch A B) f b1 ⊗ b2 = map (Batch A B) (map_fst f) (b1 ⊗ b2).
  Proof.
    intros. generalize dependent C1. induction b2.
    - intros; cbn. compose near b1.
      now do 2 rewrite (fun_map_map (F := Batch A B)).
    - intros; cbn.
      change (mult_Batch ?x ?y) with (x ⊗ y) in *.
      rewrite IHb2. compose near (b1 ⊗ b2).
      do 2 rewrite (fun_map_map (F := Batch A B)).
      do 2 fequal.
      now ext [? ?].
  Qed.

  Lemma app_mult_natural_Batch2: forall (C D1 D2: Type) (g: D1 -> D2) (b1: Batch A B C) (b2: Batch A B D1),
      b1 ⊗ map (Batch A B) g b2 = map (Batch A B) (map_snd g) (b1 ⊗ b2).
  Proof.
    intros. generalize dependent D2. induction b2 as [ANY any | ANY rest IH x'].
    - intros; cbn. compose near b1 on right. now rewrite (fun_map_map (F := Batch A B)).
    - intros; cbn. fequal.
      change (mult_Batch ?x ?y) with (x ⊗ y).
      compose near (b1 ⊗ rest).
      rewrite (fun_map_map (F := Batch A B)).
      specialize (IH (B -> D2) (compose g)).
      rewrite IH.
      compose near (b1 ⊗ rest) on left.
      rewrite (fun_map_map (F := Batch A B)).
      fequal.
      now ext [c mk].
  Qed.

  Lemma app_mult_natural_Batch: forall (C1 C2 D1 D2: Type) (f: C1 -> C2) (g: D1 -> D2) (b1: Batch A B C1) (b2: Batch A B D1),
      map (Batch A B) f b1 ⊗ map (Batch A B) g b2 = map (Batch A B) (map_tensor f g) (b1 ⊗ b2).
  Proof.
    intros. rewrite app_mult_natural_Batch1, app_mult_natural_Batch2.
    compose near (b1 ⊗ b2) on left. rewrite (fun_map_map (F := Batch A B)).
    fequal.
    now ext [c1 d1].
  Qed.

  Lemma app_assoc_Batch: forall (C D E: Type) (b1: Batch A B C) (b2: Batch A B D) (b3: Batch A B E),
      map (Batch A B) associator ((b1 ⊗ b2) ⊗ b3) = b1 ⊗ (b2 ⊗ b3).
  Proof.
    intros. induction b3.
    - do 2 rewrite mult_Batch_rw2.
      rewrite app_mult_natural_Batch2.
      compose near (b1 ⊗ b2) on left.
      now rewrite (fun_map_map (F := Batch A B)).
    - cbn. repeat change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal.
      rewrite app_mult_natural_Batch2.
      rewrite <- IHb3.
      compose near (b1 ⊗ b2 ⊗ b3).
      do 2 rewrite (fun_map_map (F := Batch A B)).
      compose near (b1 ⊗ b2 ⊗ b3) on right.
      rewrite (fun_map_map (F := Batch A B)).
      fequal.
      now ext [[c d] mk].
  Qed.

  Lemma app_unital_l_Batch: forall (C: Type) (b: Batch A B C),
      map (Batch A B) left_unitor (pure (Batch A B) tt ⊗ b) = b.
  Proof.
    intros. induction b.
    - reflexivity.
    - cbn. change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. compose near (pure (Batch A B) tt ⊗ b).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite <- IHb.
      do 3 fequal.
      assumption.
  Qed.

  Lemma app_unital_r_Batch: forall (C: Type) (b: Batch A B C),
      map (Batch A B) right_unitor (b ⊗ pure (Batch A B) tt) = b.
  Proof.
    intros. induction b.
    - reflexivity.
    - cbn in *. fequal. rewrite <- IHb at 2.
      compose near b.
      now do 2 rewrite (fun_map_map (F := Batch A B)).
  Qed.

  Lemma app_mult_pure_Batch: forall (C D: Type) (c: C) (d: D),
      pure (Batch A B) c ⊗ pure (Batch A B) d = pure (Batch A B) (c, d).
  Proof.
    intros. reflexivity.
  Qed.

  (** ** Typeclass Instance *)
  (******************************************************************************)
  #[export] Instance App_Path: Applicative (Batch A B).
  Proof.
    constructor; intros.
    - typeclasses eauto.
    - reflexivity.
    - apply app_mult_natural_Batch.
    - apply app_assoc_Batch.
    - apply app_unital_l_Batch.
    - apply app_unital_r_Batch.
    - reflexivity.
  Qed.

End Applicative_Batch.

(** ** <<mapfst>> and <<mapsnd>> are Applicative Homomorphisms *)
(******************************************************************************)
Lemma mapfst_Batch1 {B C D: Type} `(f: A1 -> A2)
  (b1: Batch A1 B C) (b2: Batch A1 B D):
  mapfst_Batch A1 A2 f (b1 ⊗ b2) =
    mapfst_Batch A1 A2 f b1 ⊗ mapfst_Batch A1 A2 f b2.
Proof.
  generalize dependent b1. induction b2.
  - intros. cbn. now rewrite mapfst_map_Batch.
  - cbn. fequal.
    change (mult_Batch ?x ?y) with (x ⊗ y) in *; intros.
    rewrite <- IHb2.
    now rewrite mapfst_map_Batch.
Qed.

Lemma mapfst_Batch2 {B C D: Type} `(f: A1 -> A2)
  (b1: Batch A1 B (C -> D)) (b2: Batch A1 B C):
  mapfst_Batch A1 A2 f (b1 <⋆> b2) =
    mapfst_Batch A1 A2 f b1 <⋆> mapfst_Batch A1 A2 f b2.
Proof.
  unfold ap. rewrite mapfst_map_Batch.
  now rewrite mapfst_Batch1.
Qed.

#[export] Instance mapfst_Batch1_Hom {B: Type} `(f: A1 -> A2):
  ApplicativeMorphism (Batch A1 B) (Batch A2 B) (fun C => mapfst_Batch _ _ f).
Proof.
  intros.
  constructor; try typeclasses eauto.
  - intros. now rewrite mapfst_map_Batch.
  - intros. reflexivity.
  - intros. apply mapfst_Batch1.
Qed.

Lemma mapsnd_Batch1 {A C D: Type} `(f: B1 -> B2)
  (b1: Batch A B2 C) (b2: Batch A B2 D):
  mapsnd_Batch B1 B2 f (b1 ⊗ b2) =
    mapsnd_Batch B1 B2 f b1 ⊗ mapsnd_Batch B1 B2 f b2.
Proof.
  generalize dependent b1. induction b2.
  - intros. cbn. now rewrite mapsnd_map_Batch.
  - cbn. fequal.
    change (mult_Batch ?x ?y) with (x ⊗ y) in *; intros.
    rewrite mapsnd_map_Batch.
    compose near (mapsnd_Batch B1 B2 f (b1 ⊗ b2)).
    rewrite (fun_map_map (F := Batch A B1)).
    rewrite app_mult_natural_Batch2.
    compose near (mapsnd_Batch B1 B2 f b1 ⊗ mapsnd_Batch B1 B2 f b2).
    rewrite (fun_map_map (F := Batch A B1)).
    rewrite IHb2. do 2 fequal; ext [c rest].
    reflexivity.
Qed.

Lemma mapsnd_Batch2 {A C D: Type} `(f: B1 -> B2)
  (b1: Batch A B2 (C -> D)) (b2: Batch A B2 C):
  mapsnd_Batch B1 B2 f (b1 <⋆> b2) =
    mapsnd_Batch B1 B2 f b1 <⋆> mapsnd_Batch B1 B2 f b2.
Proof.
  unfold ap. rewrite mapsnd_map_Batch.
  now rewrite mapsnd_Batch1.
Qed.

#[export] Instance mapsnd_Batch2_Hom {A B1 B2: Type} `(f: B1 -> B2):
  ApplicativeMorphism (Batch A B2) (Batch A B1) (fun C => mapsnd_Batch B1 B2 f).
Proof.
  intros.
  constructor; try typeclasses eauto.
  - intros. now rewrite mapsnd_map_Batch.
  - intros. reflexivity.
  - intros. apply mapsnd_Batch1.
Qed.

(** * The <<runBatch>> Operation *)
(******************************************************************************)

Fixpoint runBatch {A B: Type}
  (F: Type -> Type) `{Map F} `{Mult F} `{Pure F}
   (ϕ: A -> F B) (C: Type) (b: Batch A B C): F C :=
  match b with
  | Done _ _ _ c => pure F c
  | Step _ _ _ rest a => runBatch F ϕ (B -> C) rest <⋆> ϕ a
  end.

(** ** Rewriting Principles *)
(******************************************************************************)
Lemma runBatch_rw1 `{Applicative F} `(ϕ: A -> F B) (C: Type) (c: C) :
  runBatch F ϕ C (Done A B C c) = pure F c.
Proof.
  reflexivity.
Qed.

Lemma runBatch_rw2 `{Applicative F} `(ϕ: A -> F B)
  (a: A) (C: Type) (rest: Batch A B (B -> C)) :
  runBatch F ϕ C (rest ⧆ a) = runBatch F ϕ (B -> C) rest <⋆> ϕ a.
Proof.
  reflexivity.
Qed.

(** ** Naturality of <<runBatch>> *)
(******************************************************************************)
Section runBatch_naturality.

  Context
    `{Applicative F}.

  Lemma natural_runBatch {A B C1 C2: Type} (ϕ: A -> F B) (f: C1 -> C2) (b: Batch A B C1) :
    map F f (runBatch F ϕ C1 b) = runBatch F ϕ C2 (map (Batch A B) f b).
  Proof.
    generalize dependent C2.
    induction b; intros.
    - cbn. now rewrite app_pure_natural.
    - cbn. rewrite map_ap. fequal. now rewrite IHb.
  Qed.

  #[export] Instance Natural_runBatch `(ϕ: A -> F B) :
    Natural (runBatch F ϕ).
    constructor; try typeclasses eauto.
    intros C D f. ext b. unfold compose.
    rewrite natural_runBatch.
    reflexivity.
  Qed.

  Lemma runBatch_mapfst: forall `(s: Batch A1 B C) `(ϕ: A2 -> F B) (f: A1 -> A2),
      runBatch F (ϕ ∘ f) C s = runBatch F ϕ C (mapfst_Batch A1 A2 f s).
  Proof.
    intros; induction s.
    - easy.
    - cbn. now rewrite IHs.
  Qed.

  Lemma runBatch_mapfst': forall `(ϕ: A2 -> F B) `(f: A1 -> A2) C,
      runBatch F (ϕ ∘ f) C = runBatch F ϕ C ∘ mapfst_Batch A1 A2 f.
  Proof.
    intros. ext s.
    apply runBatch_mapfst.
  Qed.

  Lemma runBatch_mapsnd: forall `(s: @Batch A B2 C) `(ϕ: A -> F B1) (f: B1 -> B2),
      runBatch F (map F f ∘ ϕ) C s = runBatch F ϕ C (mapsnd_Batch B1 B2 f s).
  Proof.
    intros. induction s.
    - easy.
    - intros. cbn. unfold compose at 2.
      rewrite <- ap_map. fequal.
      rewrite IHs.
      now rewrite natural_runBatch.
  Qed.

  Context
    `{homomorphism: ApplicativeMorphism F G ψ}.

  Lemma runBatch_morphism `(ϕ: A -> F B) `(b: Batch A B C) :
    ψ C (runBatch F ϕ C b) = runBatch G (ψ B ∘ ϕ) C b.
  Proof.
    induction b.
    - cbn. now rewrite appmor_pure.
    - cbn. rewrite ap_morphism_1.
      now rewrite IHb.
  Qed.

  Lemma runBatch_morphism' `(ϕ: A -> F B) :
    forall C, ψ C ∘ runBatch F ϕ C = runBatch G (ψ B ∘ ϕ) C.
  Proof.
    intros. ext b. unfold compose. rewrite runBatch_morphism.
    reflexivity.
  Qed.

End runBatch_naturality.

(** ** <<runBatch>> as an Applicative Homomorphism **)
(******************************************************************************)
Section runBatch_morphism.

  Context
    `{Applicative F}
    `{ϕ: A -> F B}.

  Lemma appmor_pure_runBatch: forall (a: A),
      runBatch F ϕ A (pure (Batch A B) a) = pure F a.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runBatch: forall {C D} (x: Batch A B C) (y: Batch A B D),
      runBatch F ϕ (C * D) (x ⊗ y) = runBatch F ϕ C x ⊗ runBatch F ϕ D y.
  Proof.
    intros. generalize dependent x. induction y as [ANY any | ANY rest IH x'].
    - intros. rewrite mult_Batch_rw2.
      rewrite runBatch_rw1. rewrite triangle_4.
      now rewrite natural_runBatch.
    - intros.  rewrite runBatch_rw2.
      unfold ap. rewrite (app_mult_natural_r F).
      rewrite <- app_assoc.
      rewrite <- IH. clear IH.
      compose near (runBatch F ϕ _ (x ⊗ rest) ⊗ ϕ x').
      rewrite fun_map_map.
      cbn. unfold ap. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch. rewrite (app_mult_natural_l F).
      compose near (runBatch F ϕ _ (x ⊗ rest) ⊗ ϕ x') on left.
      rewrite fun_map_map. fequal. now ext [[? ?] ?].
  Qed.

  #[export] Instance ApplicativeMorphism_runBatch:
    ApplicativeMorphism (Batch A B) F (runBatch F ϕ).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatch.
    - intros. easy.
    - intros. apply appmor_mult_runBatch.
  Qed.

End runBatch_morphism.

(** * <<Batch>> as a Parameterized Monad *)
(******************************************************************************)
Section parameterised_monad.

  (** ** Operations <<batch>> and <<join_Batch>> *)
  (******************************************************************************)
  Definition batch (A B: Type): A -> Batch A B B :=
    Step A B B (Done A B (B -> B) (@id B)).

  Fixpoint join_Batch {A B C D: Type}
    (b: Batch (Batch A B C) C D): Batch A B D :=
    match b with
    | Done _ _ _ d => Done _ _ _ d
    | Step _ _ _ rest a => ap (Batch A B) (@join_Batch A B C (C -> D) rest) a
    end.

  Lemma join_Batch_rw1 {A B C D: Type}: forall (rest: Batch (Batch A B C) C (C -> D)) (b: Batch A B C),
      join_Batch (rest ⧆ b) = join_Batch rest <⋆> b.
  Proof.
    reflexivity.
  Qed.

  (** ** <<join>> as <<runBatch id>> *)
  (******************************************************************************)
  Lemma join_Batch_rw0: forall (A B C: Type),
      @join_Batch A B C = runBatch (Batch A B) (@id (Batch A B C)).
  Proof.
    intros. ext D b.
    induction b as [D d | D rest IHrest a].
    - reflexivity.
    - rewrite join_Batch_rw1.
      rewrite IHrest.
      reflexivity.
  Qed.

  (** ** Naturality *)
  (******************************************************************************)
  Lemma ret_natural (A1 A2 B: Type) (f: A1 -> A2) :
    mapfst_Batch A1 A2 f ∘ batch A1 B = batch A2 B ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma ret_dinatural (A B1 B2: Type) (f: B1 -> B2) :
    mapsnd_Batch B1 B2 f ∘ batch A B2 = map (Batch A B1) f ∘ batch A B1.
  Proof.
    reflexivity.
  Qed.

  (** ** <<join>> as an Applicative Homomorphism *)
  (******************************************************************************)
  #[export] Instance ApplicativeMorphism_join_Batch: forall (A B C: Type),
      ApplicativeMorphism (Batch (Batch A B C) C) (Batch A B) (@join_Batch A B C).
  Proof.
    intros.
    rewrite (@join_Batch_rw0 A B C).
    apply ApplicativeMorphism_runBatch.
  Qed.

  (** ** Other Laws *)
  (******************************************************************************)
  Lemma runBatch_batch: forall (G: Type -> Type) `{Applicative G} (A B: Type) (f: A -> G B),
      runBatch G f B ∘ batch A B = f.
  Proof.
    intros. ext a. cbn.
    now rewrite ap1.
  Qed.


  (** ** Monad Laws *)
  (******************************************************************************)
  Lemma ret_join: forall (A B C: Type),
      (@join_Batch A B C C) ∘ batch (Batch A B C) C = @id (Batch A B C).
  Proof.
    intros. ext b. unfold compose, id.
    induction b as [C c | C rest IHrest a].
    - reflexivity.
    - unfold batch.
      unfold join_Batch.
      change (Done A B (C -> C) id) with (pure (Batch A B) (@id C)).
      rewrite ap1.
      reflexivity.
  Qed.

  Lemma join_map_ret: forall (A B C: Type),
      (@join_Batch A B B C) ∘ mapfst_Batch A (Batch A B B) (batch A B) = @id (Batch A B C).
  Proof.
    intros. ext b. unfold compose, id.
    induction b as [C c | C rest IHrest a].
    - reflexivity.
    - cbn. rewrite IHrest. fequal.
      compose near rest on left.
      rewrite (fun_map_map).
      compose near rest on left.
      rewrite (fun_map_map).
      replace (compose (fun '(f, a0) => f a0)
                 ∘ (strength_arrow ∘ (fun c : B -> C => (c, id))))
        with (@id (B -> C)).
      2:{ symmetry.
          ext f b.
          unfold compose, strength_arrow, id.
          reflexivity. }
      rewrite fun_map_id.
      reflexivity.
  Qed.

  (*
  #[local] Notation "'BMONAD' B" := (fun A => Batch A B B) (at level 3).
  *)

  #[local] Instance Map_Batch_Fst (B: Type): Map (fun A => Batch A B B) :=
    fun A B f => mapfst_Batch _ _ f.

  #[local] Instance Return_Batch (B: Type): Return (fun A => Batch A B B) :=
    (fun A => batch A B).

  #[local] Instance Join_Batch (B: Type): Join (fun A => Batch A B B) :=
    fun A => @join_Batch A B B B.

  Goal forall B, Categorical.Monad.Monad (fun A => Batch A B B).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - constructor.
      + typeclasses eauto.
      + typeclasses eauto.
      + unfold_ops @Map_Batch_Fst.
        unfold_ops @Return_Batch.
        unfold_ops @Map_I.
        reflexivity.
    - admit.
    - unfold_ops @Join_Batch Return_Batch.
      intros A. ext b.
      induction b.
      + reflexivity.
      + cbn.
  Abort.

End parameterised_monad.

(** * <<Batch>> as a Parameterized Comonad *)
(******************************************************************************)
Section parameterized.

  #[local] Unset Implicit Arguments.

  (** ** Operations <<extract_Batch>> and <<cojoin_Batch>> *)
  (******************************************************************************)
  Fixpoint extract_Batch {A B: Type} (b: Batch A A B): B :=
    match b with
    | Done _ _ _ b => b
    | Step _ _ _ rest a => extract_Batch rest a
    end.

  Fixpoint cojoin_Batch {A B C D: Type} (b: Batch A C D) :
    Batch A B (Batch B C D) :=
    match b with
    | Done _ _ _ d => Done A B (Batch B C D) (Done B C D d)
    | Step _ _ _ rest a => Step A B (Batch B C D)
                            (map (Batch A B) (Step B C D) (cojoin_Batch rest)) a
    end.

  (** ** Rewriting rules *)
  (******************************************************************************)
  Lemma extract_Batch_rw0: forall (A C: Type) (c: C),
      extract_Batch (Done A A C c) = c.
  Proof.
    reflexivity.
  Qed.

  Lemma extract_Batch_rw1: forall (A B: Type) (rest: Batch A A (A -> B)) (a: A),
      extract_Batch (rest ⧆ a) = extract_Batch rest a.
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_rw0: forall (A B C D: Type) (d: D),
      @cojoin_Batch A B C D (Done A C D d) = Done A B (Batch B C D) (Done B C D d).
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_rw1: forall (A B C D: Type) (rest: Batch A C (C -> D)) (a: A),
      @cojoin_Batch A B C D (rest ⧆ a) =
        map (Batch A B) (Step B C D) (cojoin_Batch rest) ⧆ a.
  Proof.
    reflexivity.
  Qed.

  (** ** Specification via <<runBatch>>, <<batch>>, and <<double_batch>> *)
  (******************************************************************************)
  Lemma extract_Batch_to_runBatch: forall (A: Type),
      @extract_Batch A = runBatch (fun A => A) (@id A).
  Proof.
    intros. ext B b.
    induction b.
    - reflexivity.
    - cbn. rewrite IHb.
      reflexivity.
  Qed.

  Definition double_batch {A B C: Type} :
    A -> Batch A B (Batch B C C) :=
    map (Batch A B) (batch B C) ∘ (batch A B).

  Lemma double_batch_rw {A B C: Type} (a: A) :
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
      @cojoin_Batch A B C = runBatch (Batch A B ∘ Batch B C) double_batch.
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

  (** ** <<extract_Batch>> and <<cojoin_Batch>> as Applicative Homomorphisms *)
  (******************************************************************************)  #[export] Instance ApplicativeMorphism_extract_Batch: forall (A: Type),
      ApplicativeMorphism (Batch A A) (fun A => A) (@extract_Batch A).
  Proof.
    intros.
    rewrite extract_Batch_to_runBatch.
    apply ApplicativeMorphism_runBatch.
  Qed.

  #[export] Instance ApplicativeMorphism_cojoin_Batch: forall (A B C: Type),
      ApplicativeMorphism (Batch A C) (Batch A B ∘ Batch B C) (@cojoin_Batch A B C).
  Proof.
    intros.
    rewrite cojoin_Batch_to_runBatch.
    apply ApplicativeMorphism_runBatch.
  Qed.

  (* Direct Proof for <<extract>>
  #[export] Instance AppMor_extract: forall (A: Type),
      ApplicativeMorphism (Batch A A) (fun A => A) (@extract_Batch A).
  Proof.
    intros. constructor; try typeclasses eauto;
    unfold_ops @Mult_I.
    - intros B C f b.
      generalize dependent C.
      induction b as [B b | B rest IHrest a]; intros C f.
      + cbn.
        reflexivity.
      + cbn.
        rewrite IHrest.
        reflexivity.
    - intros B b.
      reflexivity.
    - intros B C b c.
      induction c as [C c | C rest IHrest a].
      + rewrite mult_Batch_rw2.
        rewrite extract_natural.
        reflexivity.
      + rewrite mult_Batch_rw3.
        rewrite extract_Batch_rw1.
        rewrite extract_natural.
        rewrite IHrest.
        reflexivity.
  Qed.
   *)

  (** ** Composition with <<ret>>/<<batch>> *)
  (******************************************************************************)
  Lemma extract_Batch_batch: forall (A: Type),
      extract_Batch ∘ batch A A = @id A.
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_batch: forall (A B C: Type),
      @cojoin_Batch A B C C ∘ batch A C =
        double_batch.
  Proof.
    intros.
    rewrite cojoin_Batch_to_runBatch.
    rewrite (runBatch_batch (Batch A B ∘ Batch B C) A C).
    reflexivity.
  Qed.

  (** ** Naturality properties *)
  (******************************************************************************)
  Lemma extract_natural (A C D: Type) (f: C -> D) :
    forall (b: Batch A A C),
      @extract_Batch A D (map (Batch A A) f b) =
        f (@extract_Batch A C b).
  Proof.
    intros.
    generalize dependent D.
    induction b as [C c | C rest IHrest a]; intros D f.
    - reflexivity.
    - cbn.
      now rewrite IHrest.
  Qed.

  Lemma extract_dinatural (A B C: Type) (f: A -> B) :
    forall (b: Batch A B C),
      @extract_Batch B C (mapfst_Batch A B f b) =
        @extract_Batch A C (mapsnd_Batch A B f b).
  Proof.
    intros.
    induction b as [C c | C rest IHrest a].
    - reflexivity.
    - cbn.
      rewrite IHrest.
      rewrite extract_natural.
      reflexivity.
  Qed.

  Lemma cojoin_natural (A B C D E: Type) (f: D -> E) :
    forall (b: Batch A C D),
      @cojoin_Batch A B C E (map (Batch A C) f b) =
        map (Batch A B) (map (Batch B C) f) (@cojoin_Batch A B C D b).
  Proof.
    intros.
    generalize dependent E.
    induction b as [D d | D rest IHrest a]; intros E f.
    - reflexivity.
    - cbn.
      rewrite IHrest.
      compose near (cojoin_Batch (B := B) rest).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite (fun_map_map (F := Batch A B)).
      reflexivity.
  Qed.

  Lemma cojoin_natural1 (A A' B C D: Type) (f: A -> A') :
    forall (b: Batch A C D),
      @cojoin_Batch A' B C D (mapfst_Batch _ _ f b) =
        mapfst_Batch _ _ f (@cojoin_Batch A B C D b).
  Proof.
    intros.
    induction b as [D d | D rest IHrest a].
    - reflexivity.
    - cbn.
      rewrite IHrest.
      rewrite <- mapfst_map_Batch.
      reflexivity.
  Qed.

  Lemma cojoin_natural2 (A B C C' D: Type) (f: C -> C') :
    forall (b: Batch A C' D),
      @cojoin_Batch A B C D (mapsnd_Batch _ _ f b) =
        map (Batch A B) (mapsnd_Batch _ _ f) (@cojoin_Batch A B C' D b).
  Proof.
    intros.
    generalize dependent C.
    induction b as [D d | D rest IHrest a]; intros C f.
    - reflexivity.
    - cbn.
      rewrite cojoin_natural.
      change (map (Batch A B) ?g (map (Batch A B) ?f ?b))
        with ((map (Batch A B) g ∘ map (Batch A B) f) b).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite IHrest.
      change (map (Batch A B) ?g (map (Batch A B) ?f ?b))
        with ((map (Batch A B) g ∘ map (Batch A B) f) b).
      rewrite (fun_map_map (F := Batch A B)).
      reflexivity.
  Qed.

  Lemma cojoin_dinatural (A B B' C D: Type) (f: B -> B') :
    forall (b: Batch A C D),
      map (Batch A B) (mapfst_Batch _ _ f) (@cojoin_Batch A B C D b) =
        (mapsnd_Batch _ _ f) (@cojoin_Batch A B' C D b).
  Proof.
    intros.
    induction b as [D d | D rest IHrest a].
    - reflexivity.
    - cbn.
      compose near (cojoin_Batch (B := B) rest).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite mapsnd_map_Batch.
      compose near (mapsnd_Batch B B' f (cojoin_Batch (B := B') rest)).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite <- IHrest.
      compose near (cojoin_Batch (B := B) rest).
      rewrite (fun_map_map (F := Batch A B)).
      reflexivity.
  Qed.

  (** ** Comonad Laws *)
  (******************************************************************************)
  Lemma extr_cojoin_Batch: `(extract_Batch ∘ cojoin_Batch = @id (Batch A B C)).
  Proof.
    intros. ext b. unfold id.
    induction b as [C c | C rest IHrest a].
    - unfold compose. cbn. reflexivity.
    - unfold compose in *.
      cbn.
      rewrite extract_natural.
      rewrite IHrest.
      reflexivity.
  Qed.

  (* TODO Finish rest of the parameterized comonad structure. *)

End parameterized.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⧆" := (Step _ _ _) (at level 51, left associativity) : tealeaves_scope.
End Notations.
