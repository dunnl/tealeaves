From Tealeaves Require Import
  Classes.Categorical.Applicative.

Import Applicative.Notations.

Generalizable Variables G A B C D ϕ ψ.

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

(** *** Rewriting Principles *)
(**********************************************************************)
Section rewriting.

  Context {B1 B2 A1 A2 C1 C2: Type}.

  Lemma map3_Batch2_rw1 `(f: C1 -> C2) (c: C1):
    map (F := Batch2 B1 B2 A1 A2) f (Done2 c) = Done2 (f c).
  Proof.
    reflexivity.
  Qed.

  Lemma map3_Batch2_rw2
    `(f: C1 -> C2) (rest: Batch2 B1 B2 A1 A2 (A2 -> C1)) (a: A1):
    map (F := Batch2 B1 B2 A1 A2) f (StepA rest a) =
      StepA (map (compose f) rest) a.
  Proof.
    reflexivity.
  Qed.

End rewriting.

#[export] Instance Functor_Batch2 {B1 B2 A1 A2: Type}: Functor (Batch2 B1 B2 A1 A2).
Proof.
  constructor; intros; ext b.
  - induction b; intros.
    + reflexivity.
    + cbn.
      assert (lemma: compose (@id C) = @id (B2 -> C)).
      { reflexivity. }
      rewrite lemma.
      rewrite IHb.
      reflexivity.
    + cbn.
      assert (lemma: compose (@id C) = @id (A2 -> C)).
      { reflexivity. }
      rewrite lemma.
      rewrite IHb.
      reflexivity.
  - generalize dependent B.
    generalize dependent C.
    unfold compose.
    induction b; intros.
    + reflexivity.
    + cbn.
      fequal.
      rewrite IHb.
      reflexivity.
    + cbn.
      fequal.
      rewrite IHb.
      reflexivity.
Qed.

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

(** ** Rewriting Principles *)
(********************************************************************)
Section rewriting_laws.

  Context
    {B1 B2 A1 A2: Type}
    {C D: Type}.

  Lemma mult_Batch_rw1:
    forall `(c: C) `(d: D),
      Done2 c ⊗ Done2 d = Done2 (B1 := B1) (B2 := B2) (A1 := A1) (A2 := A2) (c, d).
  Proof.
    reflexivity.
  Qed.

  Lemma mult_Batch_rw2:
    forall `(d: D) `(b1: Batch2 B1 B2 A1 A2 C),
      b1 ⊗ Done2 d = map (F := Batch2 B1 B2 A1 A2) (pair_right d) b1.
  Proof.
    intros. induction b1; easy.
  Qed.

  Lemma mult_Batch_rw3:
    forall `(b1: Batch2 B1 B2 A1 A2 C) `(b2: Batch2 B1 B2 A1 A2 (A2 -> D)) `(a: A1),
      b1 ⊗ (StepA b2 a) =
        StepA (map (F := Batch2 B1 B2 A1 A2) strength_arrow (b1 ⊗ b2)) a.
  Proof.
    intros. induction b1; easy.
  Qed.

  Lemma mult_Batch_rw4:
    forall `(b1: Batch2 B1 B2 A1 A2 C) `(b2: Batch2 B1 B2 A1 A2 (B2 -> D)) `(b: B1),
      b1 ⊗ (StepB b2 b) =
        StepB (map (F := Batch2 B1 B2 A1 A2) strength_arrow (b1 ⊗ b2)) b.
  Proof.
    intros. induction b1; easy.
  Qed.

  Lemma mult_Batch_rw5:
    forall `(c: C) `(b: Batch2 B1 B2 A1 A2 D),
      Done2 c ⊗ b = map (F:= Batch2 B1 B2 A1 A2) (pair c) b.
  Proof.
    induction b.
    - reflexivity.
    - intros. cbn. change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. rewrite IHb.
      compose near b on left.
      now rewrite (fun_map_map).
    - intros. cbn. change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. rewrite IHb.
      compose near b on left.
      now rewrite (fun_map_map).
  Qed.

  Lemma mult_Batch_rw6:
    forall (a: A1) `(b1: Batch2 B1 B2 A1 A2 (A2 -> C)) `(d: D),
      (StepA b1 a) ⊗ Done2 d =
        StepA (map (F := Batch2 B1 B2 A1 A2) (costrength_arrow ∘ pair_right d) b1) a.
  Proof.
    reflexivity.
  Qed.

  Lemma mult_Batch_rw7:
    forall (b: B1) `(b1: Batch2 B1 B2 A1 A2 (B2 -> C)) `(d: D),
      (StepB b1 b) ⊗ Done2 d =
        StepB (map (F := Batch2 B1 B2 A1 A2) (costrength_arrow ∘ pair_right d) b1) b.
  Proof.
    reflexivity.
  Qed.

End rewriting_laws.


(** ** Applicative Laws *)
(********************************************************************)
Section Applicative_Batch2.

  Context
    {B1 B2 A1 A2: Type}.

  Section basics.

    Context
      {C C1 C2 D D1 D2: Type}.

    Lemma app_pure_natural_Batch:
      forall `(f: C1 -> C2) (c: C1),
        map (F := Batch2 B1 B2 A1 A2) f (pure (F := Batch2 B1 B2 A1 A2) c) =
          pure (F := Batch2 B1 B2 A1 A2) (f c).
    Proof.
      reflexivity.
    Qed.

    Lemma app_mult_natural_Batch1:
      forall (f: C1 -> C2) (b1: Batch2 B1 B2 A1 A2 C1)
        (b2: Batch2 B1 B2 A1 A2 D),
        map (F := Batch2 B1 B2 A1 A2) f b1 ⊗ b2 = map (F := Batch2 B1 B2 A1 A2) (map_fst f) (b1 ⊗ b2).
    Proof.
      intros. generalize dependent C1. induction b2.
      - intros; cbn. compose near b1.
        now do 2 rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
      - intros; cbn.
        change (mult_Batch ?x ?y) with (x ⊗ y) in *.
        rewrite IHb2. compose near (b1 ⊗ b2).
        do 2 rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
        do 2 fequal.
        now ext [? ?].
      - intros; cbn.
        change (mult_Batch ?x ?y) with (x ⊗ y) in *.
        rewrite IHb2. compose near (b1 ⊗ b2).
        do 2 rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
        do 2 fequal.
        now ext [? ?].
    Qed.

    Lemma app_mult_natural_Batch2:
      forall (g: D1 -> D2)
        (b1: Batch2 B1 B2 A1 A2 C) (b2: Batch2 B1 B2 A1 A2 D1),
        b1 ⊗ map (F := Batch2 B1 B2 A1 A2) g b2 =
          map (F := Batch2 B1 B2 A1 A2) (map_snd g) (b1 ⊗ b2).
    Proof.
      intros. generalize dependent D2.
      induction b2 as [ANY any | ANY rest IH x' | ANY rest IH x'].
      - intros; cbn. compose near b1 on right.
        rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
        reflexivity.
      - intros; cbn. fequal.
        change (mult_Batch ?x ?y) with (x ⊗ y).
        compose near (b1 ⊗ rest).
        rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
        specialize (IH _ (compose g)).
        rewrite IH.
        compose near (b1 ⊗ rest) on left.
        rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
        fequal.
        now ext [c mk].
      - intros; cbn. fequal.
        change (mult_Batch ?x ?y) with (x ⊗ y).
        compose near (b1 ⊗ rest).
        rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
        specialize (IH _ (compose g)).
        rewrite IH.
        compose near (b1 ⊗ rest) on left.
        rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
        fequal.
        now ext [c mk].
    Qed.

  End basics.

  Lemma app_mult_natural_Batch {C1 C2 D1 D2}:
    forall (f: C1 -> C2) (g: D1 -> D2)
      (b1: Batch2 B1 B2 A1 A2 C1) (b2: Batch2 B1 B2 A1 A2 D1),
      map (F := Batch2 B1 B2 A1 A2) f b1 ⊗ map (F := Batch2 B1 B2 A1 A2) g b2 =
        map (F := Batch2 B1 B2 A1 A2) (map_tensor f g) (b1 ⊗ b2).
  Proof.
    intros.
    rewrite app_mult_natural_Batch1.
    rewrite app_mult_natural_Batch2.
    compose near (b1 ⊗ b2) on left.
    rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
    fequal.
    now ext [c1 d1].
  Qed.

  Lemma app_assoc_Batch {C D E}:
    forall (b1: Batch2 B1 B2 A1 A2 C) (b2: Batch2 B1 B2 A1 A2 D) (b3: Batch2 B1 B2 A1 A2 E),
      map (F := Batch2 B1 B2 A1 A2) associator ((b1 ⊗ b2) ⊗ b3) = b1 ⊗ (b2 ⊗ b3).
  Proof.
    intros. induction b3.
    - do 2 rewrite mult_Batch_rw2.
      rewrite app_mult_natural_Batch2.
      compose near (b1 ⊗ b2) on left.
      now rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
    - cbn. repeat change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal.
      rewrite app_mult_natural_Batch2.
      rewrite <- IHb3.
      compose near (b1 ⊗ b2 ⊗ b3).
      do 2 rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
      compose near (b1 ⊗ b2 ⊗ b3) on right.
      rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
      fequal.
      now ext [[c d] mk].
    - cbn. repeat change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal.
      rewrite app_mult_natural_Batch2.
      rewrite <- IHb3.
      compose near (b1 ⊗ b2 ⊗ b3).
      do 2 rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
      compose near (b1 ⊗ b2 ⊗ b3) on right.
      rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
      fequal.
      now ext [[c d] mk].
  Qed.

  Lemma app_unital_l_Batch:
    forall (C: Type) (b: Batch2 B1 B2 A1 A2 C),
      map (F := Batch2 B1 B2 A1 A2) left_unitor
        (pure (F := Batch2 B1 B2 A1 A2) tt ⊗ b) = b.
  Proof.
    intros. induction b.
    - reflexivity.
    - cbn. change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. compose near (pure (F := Batch2 B1 B2 A1 A2) tt ⊗ b).
      rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
      rewrite <- IHb.
      do 3 fequal.
      assumption.
    - cbn. change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. compose near (pure (F := Batch2 B1 B2 A1 A2) tt ⊗ b).
      rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
      rewrite <- IHb.
      do 3 fequal.
      assumption.
  Qed.

  Lemma app_unital_r_Batch:
    forall (C: Type) (b: Batch2 B1 B2 A1 A2 C),
      map (F := Batch2 B1 B2 A1 A2) right_unitor (b ⊗ pure (F := Batch2 B1 B2 A1 A2) tt) = b.
  Proof.
    intros. induction b.
    - reflexivity.
    - cbn in *. fequal. rewrite <- IHb at 2.
      compose near b.
      now do 2 rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
    - cbn in *. fequal. rewrite <- IHb at 2.
      compose near b.
      now do 2 rewrite (fun_map_map (F := Batch2 B1 B2 A1 A2)).
  Qed.

  Lemma app_mult_pure_Batch:
    forall (C D: Type) (c: C) (d: D),
      pure (F := Batch2 B1 B2 A1 A2) c ⊗ pure (F := Batch2 B1 B2 A1 A2) d =
        pure (F := Batch2 B1 B2 A1 A2) (c, d).
  Proof.
    intros. reflexivity.
  Qed.

  (** ** Typeclass Instance *)
  (********************************************************************)
  #[export] Instance Applicative_Batch: Applicative (Batch2 B1 B2 A1 A2).
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

End Applicative_Batch2.

(** ** Operation <<runBatch2>> *)
(**********************************************************************)
Fixpoint runBatch2 {B1 B2 A1 A2: Type}
  (G: Type -> Type) `{Map G} `{Mult G} `{Pure G}
  (ϕB: B1 -> G B2)
  (ϕA: A1 -> G A2)
  {C: Type} (b: Batch2 B1 B2 A1 A2 C): G C :=
  match b with
  | Done2 c => pure c
  | StepB mk b => runBatch2 G ϕB ϕA (C := B2 -> C) mk <⋆> ϕB b
  | StepA mk a => runBatch2 G ϕB ϕA (C := A2 -> C) mk <⋆> ϕA a
  end.

(** ** Rewriting rules for <<runBatch>> *)
(**********************************************************************)
Section rw.

  Context
    {A1 A2 B1 B2 C: Type}
      {G: Type -> Type}
      `{Applicative G}
      `(ϕB: B1 -> G B2)
      `(ϕA: A1 -> G A2).

  Lemma runBatch2_rw1 (c: C):
    runBatch2 G ϕB ϕA (Done2 c) = pure c.
  Proof.
    reflexivity.
  Qed.

  Lemma runBatch2_rw2
    (rest: Batch2 B1 B2 A1 A2 (A2 -> C)) (a: A1):
    runBatch2 G ϕB ϕA (StepA rest a) = runBatch2 G ϕB ϕA rest <⋆> ϕA a.
  Proof.
    reflexivity.
  Qed.

  Lemma runBatch2_rw3
    (rest: Batch2 B1 B2 A1 A2 (B2 -> C)) (b: B1):
    runBatch2 G ϕB ϕA (StepB rest b) = runBatch2 G ϕB ϕA rest <⋆> ϕB b.
  Proof.
    reflexivity.
  Qed.

End rw.

(** ** Naturality of <<runBatch>> *)
(**********************************************************************)
Section runBatch2_naturality.

  Section basic.

  Context
    `{Applicative G}
      {B1 B2 A1 A2: Type}
      {ϕB: B1 -> G B2}
      {ϕA: A1 -> G A2}.

  Lemma natural_runBatch
    {C1 C2: Type} (f: C1 -> C2) (b: Batch2 B1 B2 A1 A2 C1):
    map f (runBatch2 G ϕB ϕA b) = runBatch2 G ϕB ϕA (map f b).
  Proof.
    generalize dependent C2.
    induction b; intros.
    - cbn. now rewrite app_pure_natural.
    - cbn. rewrite map_ap. fequal. now rewrite IHb.
    - cbn. rewrite map_ap. fequal. now rewrite IHb.
  Qed.

  #[export] Instance Natural_runBatch `(ϕ: A -> G B):
    Natural (fun C => runBatch2 G ϕB ϕA (C := C)).
  Proof.
    constructor; try typeclasses eauto.
    intros C D f. ext b. unfold compose.
    rewrite natural_runBatch.
    reflexivity.
  Qed.

  (*
  Lemma runBatch2_mapfst:
    forall `(s: Batch2 B1 B2 A B C) `(ϕ: A2 -> F B) (f: A1 -> A2),
      runBatch F (ϕ ∘ f) C s = runBatch G ϕB ϕA C (mapfst_Batch A1 A2 f s).
  Proof.
    intros; induction s.
    - easy.
    - cbn. now rewrite IHs.
  Qed.

  Lemma runBatch2_mapfst':
    forall `(ϕ: A2 -> F B) `(f: A1 -> A2) C,
      runBatch F (ϕ ∘ f) C = runBatch G ϕB ϕA C ∘ mapfst_Batch A1 A2 f.
  Proof.
    intros. ext s.
    apply runBatch2_mapfst.
  Qed.

  Lemma runBatch2_mapsnd:
    forall `(s: @Batch A B2 C) `(ϕ: A -> F B1) (f: B1 -> B2),
      runBatch F (map F f ∘ ϕ) C s =
        runBatch G ϕB ϕA C (mapsnd_Batch B1 B2 f s).
  Proof.
    intros. induction s.
    - easy.
    - intros. cbn. unfold compose at 2.
      rewrite <- ap_map. fequal.
      rewrite IHs.
      now rewrite natural_runBatch.
  Qed.
  *)

  End basic.

  Context
    `{homomorphism: ApplicativeMorphism G1 G2 ψ}.

  Lemma runBatch2_morphism `(b: Batch2 B1 B2 A1 A2 C) ϕB ϕA :
    ψ C (runBatch2 G1 ϕB ϕA b) = runBatch2 G2 (ψ B2 ∘ ϕB) (ψ A2 ∘ ϕA) b.
  Proof.
    induction b.
    - cbn. now rewrite appmor_pure.
    - cbn. rewrite ap_morphism_1.
      now rewrite IHb.
    - cbn. rewrite ap_morphism_1.
      now rewrite IHb.
  Qed.

  Lemma runBatch2_morphism' {B1 B2 A1 A2 C: Type} ϕB ϕA :
    ψ C ∘ runBatch2 G1 ϕB ϕA = runBatch2 (B1:=B1) (A1:=A1) G2 (ψ B2 ∘ ϕB) (ψ A2 ∘ ϕA).
  Proof.
    intros. ext b. unfold compose. rewrite runBatch2_morphism.
    reflexivity.
  Qed.

End runBatch2_naturality.

(** ** <<runBatch>> as an Applicative Homomorphism **)
(**********************************************************************)
Section runBatch2_morphism.

  Context
    `{Applicative G}
      {B1 B2 A1 A2: Type}
      {ϕB: B1 -> G B2}
      {ϕA: A1 -> G A2}.

  Lemma appmor_pure_runBatch: forall `(c: C),
      runBatch2 G ϕB ϕA (pure (F := Batch2 B1 B2 A1 A2) c) = pure c.
  Proof.
    reflexivity.
  Qed.

  Lemma appmor_mult_runBatch:
    forall {C D: Type}
      (b1: Batch2 B1 B2 A1 A2 C)
      (b2: Batch2 B1 B2 A1 A2 D),
      runBatch2 G ϕB ϕA (b1 ⊗ b2) =
        runBatch2 G ϕB ϕA b1 ⊗ runBatch2 G ϕB ϕA b2.
  Proof.
    intros. generalize dependent b1.
    induction b2 as [ANY any | ANY rest IH x' | ANY rest IH x'].
    - intros.
      rewrite mult_Batch_rw2.
      rewrite runBatch2_rw1.
      rewrite triangle_4.
      rewrite natural_runBatch.
      reflexivity.
    - intros.
      rewrite runBatch2_rw3.
      unfold ap.
      rewrite (app_mult_natural_r G).
      rewrite <- app_assoc.
      rewrite <- IH. clear IH.
      compose near (runBatch2 G ϕB ϕA (b1 ⊗ rest) ⊗ ϕB x').
      rewrite fun_map_map.
      cbn. unfold ap. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch.
      rewrite (app_mult_natural_l G).
      compose near (runBatch2 G ϕB ϕA (b1 ⊗ rest) ⊗ ϕB x') on left.
      rewrite fun_map_map. fequal. now ext [[? ?] ?].
    - intros.
      rewrite runBatch2_rw2.
      unfold ap.
      rewrite (app_mult_natural_r G).
      rewrite <- app_assoc.
      rewrite <- IH. clear IH.
      compose near (runBatch2 G ϕB ϕA (b1 ⊗ rest) ⊗ ϕA x').
      rewrite fun_map_map.
      cbn. unfold ap. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch.
      rewrite (app_mult_natural_l G).
      compose near (runBatch2 G ϕB ϕA (b1 ⊗ rest) ⊗ ϕA x') on left.
      rewrite fun_map_map. fequal. now ext [[? ?] ?].
  Qed.

  #[export] Instance ApplicativeMorphism_runBatch2:
    ApplicativeMorphism (Batch2 B1 B2 A1 A2) G (fun C => runBatch2 G ϕB ϕA (C := C)).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatch.
    - intros. easy.
    - intros. apply appmor_mult_runBatch.
  Qed.

End runBatch2_morphism.


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
    try apply ApplicativeMorphism_runBatch2.
  Abort.

  (*
  #[export] Instance ApplicativeMorphism_cojoin_Batch2:
    forall (A B C: Type),
      ApplicativeMorphism (Batch A C) (Batch A B ∘ Batch B C)
        (@cojoin_Batch2 A B C).
  Proof.
    intros.
    rewrite cojoin_Batch_to_runBatch.
    apply ApplicativeMorphism_runBatch.
  Qed.
   *)
End parameterized.


(** * <<Batch>> as a Parameterized Monad *)
(**********************************************************************)
Section parameterised_monad.

  (** ** Operations <<batch>> and <<join_Batch>> *)
  (********************************************************************)
  Definition batch2A {B1 B2 A1 A2: Type}: A1 -> Batch2 B1 B2 A1 A2 A2 :=
    StepA (Done2 (@id A2)).

  Definition batch2B {B1 B2 A1 A2: Type}: B1 -> Batch2 B1 B2 A1 A2 B2 :=
    StepB (Done2 (@id B2)).

End parameterised_monad.
