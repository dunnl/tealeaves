From Tealeaves.Classes Require Export
  Monoid
  Categorical.Applicative
  Categorical.Monad
  Kleisli.TraversableFunctor.

From Tealeaves.Functors Require Export
  Constant
  List.

Import Monoid.Notations.
Import Applicative.Notations.
Import TraversableFunctor.Notations.

#[local] Generalizable Variables ψ ϕ W F G M A B C D X Y O.

(** * The [Batch] idiom *)
(******************************************************************************)
Inductive Batch (A B C : Type) : Type :=
| Done : C -> Batch A B C
| Step : Batch A B (B -> C) -> A -> Batch A B C.

#[global] Arguments Done {A B C}%type_scope _.
#[global] Arguments Step {A B C}%type_scope _ _.

#[local] Arguments Done : clear implicits.
#[local] Arguments Step : clear implicits.

#[local] Infix "⧆" := (Step _ _ _) (at level 51, left associativity) : tealeaves_scope.

#[global] Notation "'BATCH1' B C" := (fun A => Batch A B C) (at level 0, B at level 0, C at level 0).
#[global] Notation "'BATCH2' A" := (fun B => Batch A B) (at level 3).

(** ** Functor instances *)
(******************************************************************************)

(** *** Map operations *)
(******************************************************************************)
Fixpoint map_Batch {A B : Type} (C1 C2 : Type) (f : C1 -> C2) (b : Batch A B C1) : Batch A B C2 :=
  match b with
  | Done _ _ _ c =>
      Done A B C2 (f c)
  | Step _ _ _ rest a =>
      Step A B C2 (@map_Batch A B (B -> C1) (B -> C2) (compose f) rest) a
  end.

#[export] Instance Map_Batch {A B : Type} : Map (Batch A B) := @map_Batch A B.

Fixpoint mapfst_Batch {B C : Type} (A1 A2 : Type) (f : A1 -> A2) (b : Batch A1 B C) : Batch A2 B C :=
  match b with
  | Done _ _ _  c => Done A2 B C c
  | Step _ _ _ rest a => Step A2 B C (mapfst_Batch A1 A2 f rest) (f a)
  end.

#[export] Instance Map_Batch1 {B C : Type} : Map (BATCH1 B C) := @mapfst_Batch B C.

Fixpoint mapsnd_Batch {A : Type} (B1 B2 : Type) {C : Type} (f : B1 -> B2) (b : Batch A B2 C) : Batch A B1 C :=
  match b with
  | Done _ _ _ c => Done A B1 C c
  | Step _ _ _ rest c => Step A B1 C (map (Batch A B1) (precompose f) (mapsnd_Batch B1 B2 f rest)) c
  end.


(** *** Rewriting principles *)
(******************************************************************************)
Lemma map_Batch_rw1 {A B C1 C2 : Type} `(f : C1 -> C2) (c : C1) :
  map (Batch A B) f (Done A B C1 c) = Done A B C2 (f c).
Proof.
  reflexivity.
Qed.

Lemma map_Batch_rw2 {A B C1 C2 : Type} `(f : C1 -> C2) (a : A) (rest : Batch A B (B -> C1)) :
  map (Batch A B) f (rest ⧆ a) = map (Batch A B) (compose f) rest ⧆ a.
Proof.
  reflexivity.
Qed.

Lemma mapfst_Batch_rw1 {A1 A2 B C : Type} `(f : A1 -> A2) (c : C) :
  mapfst_Batch A1 A2 f (Done A1 B C c) = Done A2 B C c.
Proof.
  reflexivity.
Qed.

Lemma mapfst_Batch_rw2 {A1 A2 B C : Type} (f : A1 -> A2) (a : A1) (b : Batch A1 B (B -> C)) :
  mapfst_Batch A1 A2 f (b ⧆ a) = mapfst_Batch A1 A2 f b ⧆ f a.
Proof.
  reflexivity.
Qed.

(** *** Functor laws *)
(******************************************************************************)
Lemma map_id_Batch : forall (A B C : Type),
    map (Batch A B) (@id C) = @id (Batch A B C).
Proof.
  intros. ext b. induction b as [C c|C rest IHrest a].
  - reflexivity.
  - cbn.
    assert (lemma : compose (@id C) = @id (B -> C)).
    { reflexivity. } rewrite lemma.
    now rewrite IHrest.
Qed.

Lemma map_map_Batch : forall (A B C1 C2 C3 : Type) (f : C1 -> C2) (g : C2 -> C3),
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

#[export, program] Instance Functor_Batch {A B : Type} : Functor (Batch A B) :=
  {| fun_map_id := @map_id_Batch A B;
    fun_map_map := @map_map_Batch A B;
  |}.

(** *** Commuting independent maps *)
(******************************************************************************)
Lemma mapfst_map_Batch {B : Type} `(f : A1 -> A2) `(g : C1 -> C2) (b : Batch A1 B C1) :
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

Lemma mapsnd_map_Batch {A : Type} `(f : B1 -> B2) `(g : C1 -> C2) (b : Batch A B2 C1) :
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

Lemma mapfst_mapsnd_Batch : forall {C : Type} `(f : A1 -> A2) `(g : B1 -> B2) (b : Batch A1 B2 C),
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

(** ** Applicative instance *)
(******************************************************************************)
Section Applicative_Batch.

  Context
    {A B : Type}.

  (** *** Operations *)
  (******************************************************************************)
  #[export] Instance Pure_Batch : Pure (@Batch A B) :=
    fun (C : Type) (c : C) => Done A B C c.

  Fixpoint mult_Batch `(b1 : Batch A B C) `(b2 : Batch A B D) : @Batch A B (C * D) :=
    match b2 with
    | Done _ _ _ d => map (Batch A B) (fun (c : C) => (c, d)) b1
    | Step _ _ _ rest a =>
        Step A B (C * D) (map (Batch A B) strength_arrow (mult_Batch b1 rest)) a
    end.

  #[export] Instance Mult_Batch : Mult (@Batch A B) :=
    fun C D '(b1, b2) => mult_Batch b1 b2.

  (** *** Examples of operations *)
  (******************************************************************************)
  (*
  Section demo.
    Context
      (A B C D : Type)
        (a1 a2 a3 : A)
        (c1 c2 c3 : C)
        (d1 d2 d3 : D)
        (mk1 : B -> C)
        (mk1' : B -> D)
        (mk2 : B -> B -> C).

    Compute Done A B C c1 ⊗ Done A B D d1.
    Compute Done A B C c1 ⊗ (Done A B (B -> D) mk1' ⧆ a1).
    Compute (Done A B _ mk1 ⧆ a1) ⊗ Done A B D d2.
    Compute (Done A B _ mk1 ⧆ a1) ⊗ (Done A B _ mk1' ⧆ a2).
    Compute (Done A B _ mk2 ⧆ a1 ⧆ a2) ⊗ (Done A B _ mk1' ⧆ a3).
  End demo.
  *)

  (** *** Rewriting principles *)
  (******************************************************************************)
  Lemma mult_Batch_rw1 : forall `(c : C) `(d : D),
      Done A B C c ⊗ Done A B D d = Done A B (C * D) (c, d).
  Proof.
    reflexivity.
  Qed.

  Lemma mult_Batch_rw2 : forall `(d : D) `(b1 : Batch A B C),
      b1 ⊗ Done A B D d = map (Batch A B) (pair_right d) b1.
  Proof.
    intros. induction b1; easy.
  Qed.

  Lemma mult_Batch_rw3 : forall (D : Type) (b2 : Batch A B (B -> D)) (a : A) `(b1 : Batch A B C),
      b1 ⊗ (b2 ⧆ a) =
        map (Batch A B) strength_arrow (b1 ⊗ b2) ⧆ a.
  Proof.
    reflexivity.
  Qed.


  Lemma mult_Batch_rw4 : forall `(b2 : Batch A B D) `(c : C),
      Done A B C c ⊗ b2 = map (Batch A B) (pair c) b2.
  Proof.
    induction b2.
    - reflexivity.
    - intros. cbn; change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. rewrite IHb2.
      compose near b2 on left.
      now rewrite (fun_map_map (F := Batch A B)).
  Qed.

  Lemma mult_Batch_rw5 : forall (a : A) `(b1 : @Batch A B (B -> C)) `(d : D),
      (b1 ⧆ a) ⊗ Done A B D d =
        map (Batch A B) (costrength_arrow ∘ pair_right d) b1 ⧆ a.
  Proof.
    reflexivity.
  Qed.

  Lemma mult_Batch_rw6 : forall `(b2 : @Batch A B (B -> D)) `(c : C) (a : A),
      Done A B C c ⊗ (b2 ⧆ a) = map (Batch A B) (strength_arrow ∘ pair c) b2 ⧆ a.
  Proof.
    intros.
    rewrite mult_Batch_rw3.
    rewrite mult_Batch_rw4.
    compose near b2 on left.
    now rewrite (fun_map_map (F := Batch A B)).
  Qed.

  Lemma mult_Batch_rw7 : forall (a1 a2 : A) `(b1 : Batch A B (B -> C)) `(b2 : Batch A B (B -> D)),
      (b1 ⧆ a1) ⊗ (b2 ⧆ a2) =
        (map (Batch A B) strength_arrow ((b1 ⧆ a1) ⊗ b2)) ⧆ a2.
  Proof.
    reflexivity.
  Qed.

  (** *** Applicative laws *)
  (******************************************************************************)
  Lemma app_pure_natural_Batch : forall `(f : C1 -> C2) (c : C1),
      map (Batch A B) f (pure (Batch A B) c) = pure (Batch A B) (f c).
  Proof.
    reflexivity.
  Qed.

  Lemma app_mult_natural_Batch1 : forall (C1 C2 D : Type) (f : C1 -> C2) (b1 : Batch A B C1) (b2 : Batch A B D),
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

  Lemma app_mult_natural_Batch2 : forall (C D1 D2 : Type) (g : D1 -> D2) (b1 : Batch A B C) (b2 : Batch A B D1),
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

  Lemma app_mult_natural_Batch : forall (C1 C2 D1 D2 : Type) (f : C1 -> C2) (g : D1 -> D2) (b1 : Batch A B C1) (b2 : Batch A B D1),
      map (Batch A B) f b1 ⊗ map (Batch A B) g b2 = map (Batch A B) (map_tensor f g) (b1 ⊗ b2).
  Proof.
    intros. rewrite app_mult_natural_Batch1, app_mult_natural_Batch2.
    compose near (b1 ⊗ b2) on left. rewrite (fun_map_map (F := Batch A B)).
    fequal.
    now ext [c1 d1].
  Qed.

  Lemma app_assoc_Batch : forall (C D E : Type) (b1 : Batch A B C) (b2 : Batch A B D) (b3 : Batch A B E),
      map (Batch A B) associator ((b1 ⊗ b2) ⊗ b3) = b1 ⊗ (b2 ⊗ b3).
  Proof.
    intros. induction b3.
    - do 2 rewrite mult_Batch_rw2.
      rewrite (app_mult_natural_Batch2).
      compose near (b1 ⊗ b2) on left.
      now rewrite (fun_map_map (F := Batch A B)).
    - cbn. repeat change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal.
      rewrite (app_mult_natural_Batch2).
      rewrite <- IHb3.
      compose near (b1 ⊗ b2 ⊗ b3).
      do 2 rewrite (fun_map_map (F := Batch A B)).
      compose near (b1 ⊗ b2 ⊗ b3) on right.
      rewrite (fun_map_map (F := Batch A B)).
      fequal.
      now ext [[c d] mk].
  Qed.

  Lemma app_unital_l_Batch : forall (C : Type) (b : Batch A B C),
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

  Lemma app_unital_r_Batch : forall (C : Type) (b : Batch A B C),
      map (Batch A B) right_unitor (b ⊗ pure (Batch A B) tt) = b.
  Proof.
    intros. induction b.
    - reflexivity.
    - cbn in *. fequal. rewrite <- IHb at 2.
      compose near b.
      now do 2 rewrite (fun_map_map (F := Batch A B)).
  Qed.

  Lemma app_mult_pure_Batch : forall (C D : Type) (c : C) (d : D),
      pure (Batch A B) c ⊗ pure (Batch A B) d = pure (Batch A B) (c, d).
  Proof.
    intros. reflexivity.
  Qed.

  (** *** Typeclass instance *)
  (******************************************************************************)
  #[export, program] Instance App_Path : Applicative (Batch A B).

  Next Obligation. apply app_mult_natural_Batch. Qed.
  Next Obligation. apply app_assoc_Batch. Qed.
  Next Obligation. apply app_unital_l_Batch. Qed.
  Next Obligation. apply app_unital_r_Batch. Qed.

End Applicative_Batch.

(** *** <<mapfst>> is a homomorphism *)
(******************************************************************************)
Lemma mapfst_Batch1 {B C D : Type} `(f : A1 -> A2) (b1 : Batch A1 B C) (b2 : Batch A1 B D) :
  mapfst_Batch A1 A2 f (b1 ⊗ b2) = mapfst_Batch A1 A2 f b1 ⊗ mapfst_Batch A1 A2 f b2.
Proof.
  generalize dependent b1. induction b2.
  - intros. cbn. now rewrite mapfst_map_Batch.
  - cbn. fequal.
    change (mult_Batch ?x ?y) with (x ⊗ y) in *; intros.
    rewrite <- IHb2.
    now rewrite mapfst_map_Batch.
Qed.

Lemma mapfst_Batch2 {B C D : Type} `(f : A1 -> A2) (b1 : Batch A1 B (C -> D)) (b2 : Batch A1 B C) :
  mapfst_Batch A1 A2 f (b1 <⋆> b2) = mapfst_Batch A1 A2 f b1 <⋆> mapfst_Batch A1 A2 f b2.
Proof.
  unfold ap. rewrite mapfst_map_Batch.
  now rewrite mapfst_Batch1.
Qed.

(** * <<runBatch>> *)
(******************************************************************************)

(** ** The <<runBatch>> operation *)
(******************************************************************************)
Fixpoint runBatch {A B : Type}
  (F : Type -> Type) `{Map F} `{Mult F} `{Pure F}
   (ϕ : A -> F B) (C : Type) (b : Batch A B C) : F C :=
  match b with
  | Done _ _ _ c => pure F c
  | Step _ _ _ rest a => runBatch F ϕ (B -> C) rest <⋆> ϕ a
  end.

(** *** Rewriting principles *)
(******************************************************************************)
Lemma runBatch_rw1 `{Applicative F} `(ϕ : A -> F B) (C : Type) (c : C) :
  runBatch F ϕ C (Done A B C c) = pure F c.
Proof.
  reflexivity.
Qed.

Lemma runBatch_rw2 `{Applicative F} `(ϕ : A -> F B)
  (a : A) (C : Type) (rest : Batch A B (B -> C)) :
  runBatch F ϕ C (rest ⧆ a) = runBatch F ϕ (B -> C) rest <⋆> ϕ a.
Proof.
  reflexivity.
Qed.

(** *** Naturality of of <<runBatch>> *)
(******************************************************************************)
Section runBatch_naturality.

  Context
    `{Applicative F}.

  Lemma natural_runBatch {A B C1 C2 : Type} (ϕ : A -> F B) (f : C1 -> C2) (b : Batch A B C1) :
    map F f (runBatch F ϕ C1 b) = runBatch F ϕ C2 (map (Batch A B) f b).
  Proof.
    generalize dependent C2.
    induction b; intros.
    - cbn. now rewrite (app_pure_natural F).
    - cbn. rewrite map_ap. fequal. now rewrite IHb.
  Qed.

  #[export] Instance Natural_runBatch `(ϕ : A -> F B) :
    Natural (runBatch F ϕ).
    constructor; try typeclasses eauto.
    intros C D f. ext b. unfold compose.
    rewrite natural_runBatch.
    reflexivity.
  Qed.

  Lemma runBatch_mapfst : forall `(s : Batch A1 B C) `(ϕ : A2 -> F B) (f : A1 -> A2),
      runBatch F (ϕ ∘ f) C s = runBatch F ϕ C (mapfst_Batch A1 A2 f s).
  Proof.
    intros; induction s.
    - easy.
    - cbn. now rewrite IHs.
  Qed.

  Lemma runBatch_mapsnd : forall `(s : @Batch A B2 C) `(ϕ : A -> F B1) (f : B1 -> B2),
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
    `{ApplicativeMorphism F G ψ}.

  Lemma runBatch_morphism `(ϕ : A -> F B) `(b : Batch A B C) :
    ψ C (runBatch F ϕ C b) = runBatch G (ψ B ∘ ϕ) C b.
  Proof.
    induction b.
    - cbn. now rewrite (appmor_pure F G).
    - cbn. rewrite ap_morphism_1.
      now rewrite IHb.
  Qed.

  Lemma runBatch_morphism' `(ϕ : A -> F B) :
    forall C, ψ C ∘ runBatch F ϕ C = runBatch G (ψ B ∘ ϕ) C.
  Proof.
    intros. ext b. unfold compose. rewrite runBatch_morphism.
    reflexivity.
  Qed.

End runBatch_naturality.

(** ** <<runBatch>> as an applicative transformation **)
(******************************************************************************)
Section runBatch_morphism.

  Context
    `{Applicative F}
    `{ϕ : A -> F B}.

  Lemma appmor_pure_runBatch : forall (a : A),
      runBatch F ϕ A (pure (Batch A B) a) = pure F a.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runBatch : forall {C D} (x : Batch A B C) (y : Batch A B D),
      runBatch F ϕ (C * D) (x ⊗ y) = runBatch F ϕ C x ⊗ runBatch F ϕ D y.
  Proof.
    intros. generalize dependent x. induction y as [ANY any | ANY rest IH x'].
    - intros. rewrite mult_Batch_rw2.
      rewrite runBatch_rw1. rewrite triangle_4.
      now rewrite natural_runBatch.
    - intros.  rewrite runBatch_rw2.
      unfold ap. rewrite (app_mult_natural_r F).
      rewrite <- (app_assoc F).
      rewrite <- IH. clear IH.
      compose near (runBatch F ϕ _ (x ⊗ rest) ⊗ ϕ x').
      rewrite (fun_map_map).
      cbn. unfold ap. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch. rewrite (app_mult_natural_l F).
      compose near (runBatch F ϕ _ (x ⊗ rest) ⊗ ϕ x') on left.
      rewrite (fun_map_map). fequal. now ext [[? ?] ?].
  Qed.

  #[export] Instance ApplicativeMorphism_runBatch: ApplicativeMorphism (Batch A B) F (runBatch F ϕ).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatch.
    - intros. easy.
    - intros. apply appmor_mult_runBatch.
  Qed.

End runBatch_morphism.

(** ** <<runBatch>> specialized to monoids *)
(******************************************************************************)
Section runBatch_monoid.

  Context
    `{Monoid M}
    {A B : Type}.

  Fixpoint runBatch_monoid `(ϕ : A -> M) `(b : Batch A B C) : M :=
    match b with
    | Done _ _ _ c => monoid_unit M
    | Step _ _ _ rest a => runBatch_monoid (ϕ : A -> M) rest ● ϕ a
    end.

  Lemma runBatch_monoid1 : forall (ϕ : A -> M) `(b : Batch A B C),
      runBatch_monoid ϕ b = unconst (runBatch (Const M) (mkConst (tag := B) ∘ ϕ) _ b).
  Proof.
    intros. induction b.
    - easy.
    - cbn. now rewrite IHb.
  Qed.

  Lemma runBatch_monoid2 : forall (ϕ : A -> M) `(b : Batch A B C),
      runBatch_monoid ϕ b = runBatch (const M) (ϕ : A -> const M B) _ b.
  Proof.
    intros. induction b.
    - easy.
    - cbn. now rewrite IHb.
  Qed.

End runBatch_monoid.

(** * Length *)
(******************************************************************************)
Section length.

  Context (A B : Type).

  #[local] Unset Implicit Arguments.

  Fixpoint length_Batch (C : Type) (b : Batch A B C) : nat :=
    match b with
    | Done _ _ _ _ => 0
    | Step _ _ _ rest a => S (length_Batch (B -> C) rest)
    end.

 (* The length of a batch is the same as the length of the list we can extract from it *)
  Lemma batch_length1 : forall (C : Type) (b : Batch A B C),
      length_Batch C b =
        length (runBatch (const (list A)) (ret list A) _ b).
  Proof.
    intros C b.
    induction b as [C c | C b IHb a].
    - reflexivity.
    - cbn. rewrite IHb.
      unfold_ops @Monoid_op_list.
      rewrite List.app_length.
      cbn. lia.
  Qed.

End length.

(** * <<Batch>> as a parameterized monad *)
(******************************************************************************)
Section parameterised_monad.

  (** ** Operations *)
  (******************************************************************************)
  Definition batch (A B : Type) : A -> Batch A B B :=
    Step A B B (Done A B (B -> B) (@id B)).

  Fixpoint join_Batch {A B C D : Type}
    (b : Batch (Batch A B C) C D) : Batch A B D :=
    match b with
    | Done _ _ _ d => Done _ _ _ d
    | Step _ _ _ rest a => ap (Batch A B) (@join_Batch A B C (C -> D) rest) a
    end.

  Lemma join_Batch_rw1 {A B C D : Type} : forall (rest : Batch (Batch A B C) C (C -> D)) (b : Batch A B C),
      join_Batch (rest ⧆ b) = join_Batch rest <⋆> b.
  Proof.
    reflexivity.
  Qed.

  (** ** <<join>> as <<runBatch id>> *)
  (******************************************************************************)
  Lemma join_Batch_rw0 : forall (A B C : Type),
      @join_Batch A B C = runBatch (Batch A B) (@id (Batch A B C)).
  Proof.
    intros. ext D b.
    induction b as [D d | D rest IHrest a].
    - reflexivity.
    - rewrite join_Batch_rw1.
      rewrite IHrest.
      reflexivity.
  Qed.

  (** *** Naturality *)
  (******************************************************************************)
  Lemma ret_natural (A1 A2 B : Type) (f : A1 -> A2) :
    mapfst_Batch A1 A2 f ∘ batch A1 B = batch A2 B ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma ret_dinatural (A B1 B2 : Type) (f : B1 -> B2) :
    mapsnd_Batch B1 B2 f ∘ batch A B2 = map (Batch A B1) f ∘ batch A B1.
  Proof.
    reflexivity.
  Qed.

  (** ** Other laws *)
  (******************************************************************************)
  Lemma runBatch_batch : forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G B),
      runBatch G f B ∘ batch A B = f.
  Proof.
    intros. ext a. cbn.
    now rewrite ap1.
  Qed.


  (** ** Monad laws *)
  (******************************************************************************)
  Lemma ret_join : forall (A B C : Type),
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

  Lemma join_map_ret : forall (A B C : Type),
      (@join_Batch A B B C) ∘ mapfst_Batch A (Batch A B B) (batch A B) = @id (Batch A B C).
  Proof.
    intros. ext b. unfold compose, id.
    induction b as [C c | C rest IHrest a].
    - reflexivity.
    - admit.
  Abort.

  #[local] Notation "'BMONAD' B" := (fun A => Batch A B B) (at level 3).

  #[local] Instance Map_Batch_Fst (B : Type) : Map (BMONAD B) :=
    fun A B f => mapfst_Batch _ _ f.

  #[local] Instance Return_Batch (B : Type) : Return (BMONAD B) :=
    (fun A => batch A B).

  #[local] Instance Join_Batch (B : Type) : Join (BMONAD B) :=
    fun A => @join_Batch A B B B.

  Goal forall B, Categorical.Monad.Monad (BMONAD B).
  Proof.
    intros. constructor; unfold compose, id.
    - admit.
    - admit.
    - admit.
    - intros. ext b.
  Abort.

End parameterised_monad.

(** * <<Batch>> as a parameterized comonad *)
(******************************************************************************)
Section parameterized.

  #[local] Unset Implicit Arguments.

  (** ** Operations *)
  (******************************************************************************)
  Fixpoint extract_Batch {A B : Type} (b : Batch A A B) : B :=
    match b with
    | Done _ _ _ b => b
    | Step _ _ _ rest a => extract_Batch rest a
    end.

  Fixpoint cojoin_Batch {A B C D : Type} (b : Batch A C D) :
    Batch A B (Batch B C D) :=
    match b with
    | Done _ _ _ d => Done A B (Batch B C D) (Done B C D d)
    | Step _ _ _ rest a => Step A B (Batch B C D)
                            (map (Batch A B) (Step B C D) (cojoin_Batch rest)) a
    end.

  (** *** Specification via <<runBatch>>, <<batch>>, and <<double_batch>> *)
  (******************************************************************************)
  Lemma extract_Batch_to_runBatch : forall (A : Type),
      @extract_Batch A = runBatch (fun A => A) (@id A).
  Proof.
    intros. ext B b.
    induction b.
    - reflexivity.
    - cbn. rewrite IHb.
      reflexivity.
  Qed.

  Definition double_batch {A B C : Type} :
    A -> Batch A B (Batch B C C) :=
    map (Batch A B) (batch B C) ∘ (batch A B).

  Lemma double_batch_spec : forall (A B C : Type),
      double_batch = batch B C ⋆2 batch A B.
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_to_runBatch : forall (A B C : Type),
      @cojoin_Batch A B C = runBatch (Batch A B ∘ Batch B C) (double_batch).
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
      rewrite (fun_map_map).
      compose near rest.
      rewrite (fun_map_map).
      rewrite (fun_map_id).
      reflexivity.
  Qed.

  (** *** Composition with <<ret>>/<<batch>> *)
  (******************************************************************************)
  Lemma extract_Batch_batch : forall (A : Type),
      extract_Batch ∘ batch A A = @id A.
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_batch : forall (A B C : Type),
      @cojoin_Batch A B C C ∘ batch A C =
        double_batch.
  Proof.
    intros.
    rewrite (cojoin_Batch_to_runBatch).
    rewrite (runBatch_batch (Batch A B ∘ Batch B C) A C).
    reflexivity.
  Qed.

  (** *** Rewriting rules *)
  (******************************************************************************)
  Lemma extract_Batch_rw0 : forall (A C : Type) (c : C),
      extract_Batch (Done A A C c) = c.
  Proof.
    reflexivity.
  Qed.

  Lemma extract_Batch_rw1 : forall (A B : Type) (rest : Batch A A (A -> B)) (a : A),
      extract_Batch (rest ⧆ a) = extract_Batch rest a.
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_rw0 : forall (A B C D : Type) (d : D),
      @cojoin_Batch A B C D (Done A C D d) = Done A B (Batch B C D) (Done B C D d).
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Batch_rw1 : forall (A B C D : Type) (rest : Batch A C (C -> D)) (a : A),
      @cojoin_Batch A B C D (rest ⧆ a) =
        map (Batch A B) (Step B C D) (cojoin_Batch rest) ⧆ a.
  Proof.
    reflexivity.
  Qed.

  (** *** Naturality properties *)
  (******************************************************************************)
  Lemma extract_natural (A C D : Type) (f : C -> D) :
    forall (b : Batch A A C),
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

  Lemma extract_dinatural (A B C : Type) (f : A -> B) :
    forall (b : Batch A B C),
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

  Lemma cojoin_natural (A B C D E : Type) (f : D -> E) :
    forall (b : Batch A C D),
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

  Lemma cojoin_natural1 (A A' B C D : Type) (f : A -> A') :
    forall (b : Batch A C D),
      @cojoin_Batch A' B C D (mapfst_Batch _ _ f b) =
        mapfst_Batch _ _ f (@cojoin_Batch A B C D b).
  Proof.
    intros.
    induction b as [D d | D rest IHrest a].
    - reflexivity.
    - cbn.
      rewrite IHrest.
      rewrite <- (mapfst_map_Batch).
      reflexivity.
  Qed.

  Lemma cojoin_natural2 (A B C C' D : Type) (f : C -> C') :
    forall (b : Batch A C' D),
      @cojoin_Batch A B C D (mapsnd_Batch _ _ f b) =
        map (Batch A B) (mapsnd_Batch _ _ f) (@cojoin_Batch A B C' D b).
  Proof.
    intros.
    generalize dependent C.
    induction b as [D d | D rest IHrest a]; intros C f.
    - reflexivity.
    - cbn.
      rewrite (cojoin_natural).
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

  Lemma cojoin_dinatural (A B B' C D : Type) (f : B -> B') :
    forall (b : Batch A C D),
      map (Batch A B) (mapfst_Batch _ _ f) (@cojoin_Batch A B C D b) =
        (mapsnd_Batch _ _ f) (@cojoin_Batch A B' C D b).
  Proof.
    intros.
    induction b as [D d | D rest IHrest a].
    - reflexivity.
    - cbn.
      compose near (cojoin_Batch (B := B) rest).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite (mapsnd_map_Batch).
      compose near (mapsnd_Batch B B' f (cojoin_Batch (B := B') rest)).
      rewrite (fun_map_map (F := Batch A B)).
      rewrite <- IHrest.
      compose near (cojoin_Batch (B := B) rest).
      rewrite (fun_map_map (F := Batch A B)).
      reflexivity.
  Qed.

  (** ** <<extract>> as an applicative morphism *)
  (******************************************************************************)
  #[export] Instance AppMor_extract : forall (A : Type),
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

  (** ** Comonad laws *)
  (******************************************************************************)
  Lemma extr_cojoin_Batch : `(extract_Batch ∘ cojoin_Batch = @id (Batch A B C)).
  Proof.
    intros. ext b. unfold id.
    induction b as [C c | C rest IHrest a].
    - unfold compose. cbn. reflexivity.
    - unfold compose in *.
      cbn.
      rewrite (extract_natural).
      rewrite IHrest.
      reflexivity.
  Qed.

  (* TODO Finish rest of the parameterized comonad structure. *)

End parameterized.

(** ** <<cojoin>> as <<runBatch (double_batch)>> *)
(******************************************************************************)


(*
Lemma double_batch_spec {A B C : Type} :
  @double_batch A B C = @cojoin_Batch A B C C ∘ batch C A.
Proof.
  reflexivity.
Qed.
*)

#[export] Instance AppMor_cojoin : forall (A B C : Type),
    ApplicativeMorphism (Batch A C) (Batch A B ∘ Batch B C) (@cojoin_Batch A B C).
Proof.
  intros.
  rewrite cojoin_Batch_to_runBatch.
  apply ApplicativeMorphism_runBatch.
Qed.

#[export] Instance AppMor_join : forall (A B C : Type),
    ApplicativeMorphism (Batch (Batch A B C) C) (Batch A B) (@join_Batch A B C).
Proof.
  intros.
  rewrite (@join_Batch_rw0 A B C).
  apply ApplicativeMorphism_runBatch.
Qed.

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

(** * <<Batch _ B C>> is a traversable functor *)
(******************************************************************************)
Fixpoint traverse_Batch (B C : Type) (G : Type -> Type)
  `{Map G} `{Pure G} `{Mult G} (A A' : Type) (f : A -> G A')
  (b : Batch A B C) : G (Batch A' B C) :=
  match b with
  | Done _ _ _ c => pure G (Done A' B C c)
  | Step _ _ _ rest a =>
      pure G (Step A' B C) <⋆>
        traverse_Batch B (B -> C) G A A' f rest <⋆>
        f a
  end.

#[export] Instance Traverse_Batch1 :
  forall (B C : Type), Traverse (BATCH1 B C) := traverse_Batch.

Lemma trf_traverse_id_Batch :
  forall B C A : Type, traverse (BATCH1 B C) (fun X : Type => X) (@id A) = id.
Proof.
  intros. ext b.
  unfold id.
  induction b as [C c | C rest IHrest].
  - cbn. reflexivity.
  - cbn. fold (traverse (BATCH1 B (B -> C))).
    rewrite IHrest.
    reflexivity.
Qed.

Lemma trf_traverse_traverse_Batch :
  forall (B C : Type) (G1 G2 : Type -> Type) (H0 : Map G1) (H1 : Pure G1) (H2 : Mult G1),
    Applicative G1 ->
    forall (H4 : Map G2) (H5 : Pure G2) (H6 : Mult G2),
      Applicative G2 ->
      forall (A A' A'' : Type) (g : A' -> G2 A'') (f : A -> G1 A'),
        map G1 (traverse (BATCH1 B C) G2 g) ∘ traverse (BATCH1 B C) G1 f = traverse (BATCH1 B C) (G1 ∘ G2) (g ⋆2 f).
Proof.
  intros. ext b.
  unfold id.
  induction b as [C c | C rest IHrest].
  - cbn. unfold compose.
    cbn. rewrite (app_pure_natural G1).
    reflexivity.
  - cbn.
    (* RHS *)
    fold (traverse (BATCH1 B (B -> C))).
    (* cleanup *)
    rewrite (ap_compose1 G2 G1).
    rewrite (ap_compose1 G2 G1).
    rewrite <- map_to_ap.
    rewrite (map_ap).
    rewrite (map_ap).
    rewrite (app_pure_natural G1).
    (* <<unfold_ops Pure_compose>> prevents << rewrite <- IHrest>> *)
    unfold pure at 2; unfold Pure_compose at 1.
    rewrite (ap2).
    (* deal with <<rest>> *)
    rewrite <- IHrest.
    unfold compose at 4.
    rewrite <- ap_map.
    rewrite (app_pure_natural G1).
    unfold kc2.
    unfold compose at 4.
    rewrite <- ap_map.
    rewrite (map_ap).
    rewrite (app_pure_natural G1).
    (* LHS *)
    unfold compose; cbn.
    fold (traverse (BATCH1 B (B -> C))).
    rewrite (map_ap).
    rewrite (map_ap).
    rewrite (app_pure_natural G1).
    reflexivity.
Qed.

Lemma trf_traverse_morphism_Batch :
  forall (B C : Type) (G1 G2 : Type -> Type) (H0 : Map G1) (H1 : Pure G1) (H2 : Mult G1)
    (H3 : Map G2) (H4 : Pure G2) (H5 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ ->
    forall (A A' : Type) (f : A -> G1 A'),
      ϕ (BATCH1 B C A') ∘ traverse (BATCH1 B C) G1 f = traverse (BATCH1 B C) G2 (ϕ A' ∘ f).
Proof.
  intros. ext b.
  pose H as H'; inversion H'.
  induction b as [C c | C rest IHrest].
  - unfold compose; cbn.
    now rewrite appmor_pure.
  - cbn.
    unfold compose at 1. cbn.
    fold (traverse (BATCH1 B (B -> C))).
    rewrite <- IHrest.
    rewrite <- appmor_pure.
    rewrite (ap_morphism_1 (ϕ := ϕ)).
    rewrite (ap_morphism_1 (ϕ := ϕ)).
    reflexivity.
Qed.

#[export] Instance TraversableFunctor_Batch : forall (B C : Type),
    TraversableFunctor (BATCH1 B C) := fun B C =>
  {| trf_traverse_id := trf_traverse_id_Batch B C;
      trf_traverse_traverse := trf_traverse_traverse_Batch B C;
      trf_traverse_morphism := trf_traverse_morphism_Batch B C;
  |}.

Lemma map_compat_traverse_Batch1 : forall (B C : Type),
    @map (BATCH1 B C) _ = Map_Traverse (BATCH1 B C).
Proof.
  intros. unfold Map_Traverse.
  ext A A' f b. induction b as [C c | C rest IHrest a].
  - reflexivity.
  - cbn. fold (traverse (BATCH1 B (B -> C))).
    rewrite <- IHrest.
    reflexivity.
Qed.

#[export] Instance TraversableFunctorFull_Batch (B C : Type) :
    TraversableFunctorFull (BATCH1 B C) :=
  {| trff_map_to_traverse := map_compat_traverse_Batch1 B C;
  |}.

(** ** Specification for <<runBatch>> *)
(******************************************************************************)
Lemma runBatch_spec {A B : Type}
  (F : Type -> Type) `{Map F} `{Mult F} `{Pure F} `{! Applicative F}
  (ϕ : A -> F B) (C : Type) :
  runBatch F ϕ C = map F (extract_Batch) ∘ traverse (BATCH1 B C) F ϕ.
Proof.
  intros. ext b.
  induction b as [C c | C rest IHrest].
  - unfold compose; cbn.
    rewrite (app_pure_natural F).
    reflexivity.
  - cbn.
    rewrite IHrest.
    unfold compose; cbn.
    fold (traverse (BATCH1 B (B -> C))).
    rewrite map_ap.
    rewrite map_ap.
    rewrite (app_pure_natural F).
    rewrite (map_to_ap).
    reflexivity.
Qed.

(** * <<Batch _ B C>> is a traversable monad *)
(******************************************************************************)
Definition bindt_Batch (B C : Type) (G : Type -> Type)
  `{Map G} `{Pure G} `{Mult G} (A A' : Type) (f : A -> G (Batch A' B B))
  (b : Batch A B B) : G (Batch A' B B) :=
  map G (join_Batch) (traverse (BATCH1 B B) G f b).

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⧆" := (Step _ _ _) (at level 51, left associativity) : tealeaves_scope.
End Notations.
