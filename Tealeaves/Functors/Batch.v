From Tealeaves.Classes Require Export
  Monoid
  Categorical.Applicative.
From Tealeaves.Functors Require Export
  Store
  Constant
  List.

Import Monoid.Notations.
Import Applicative.Notations.

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

(** ** Functor instance *)
(******************************************************************************)
Fixpoint map_Batch {A B : Type} `(f : C1 -> C2) (b : Batch A B C1) : Batch A B C2 :=
  match b with
  | Done _ _ _ c =>
      Done A B C2 (f c)
  | Step _ _ _ rest a =>
      Step A B C2 (@map_Batch A B (B -> C1) (B -> C2) (compose f) rest) a
  end.

#[export] Instance Map_Batch {A B : Type} : Map (Batch A B) := @map_Batch A B.

#[export, program] Instance Functor_Batch {A B : Type} : Functor (Batch A B).

Next Obligation.
  ext j. induction j. easy.
  cbn; unfold id; now fequal.
Qed.

Next Obligation.
  rename A0 into C1.
  rename B0 into C2.
  rename C  into C3.
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

(*
#[global] Arguments Done {A Y}%type_scope [A]%type_scope _.
*)

(** ** Notations *)
(******************************************************************************)
Module Notations.
  Infix "⧆" := (Step _ _ _) (at level 51, left associativity) : tealeaves_scope.
End Notations.

Import Notations.

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

  Lemma mult_Batch_rw3 : forall `(b2 : Batch A B D) `(c : C),
      Done A B C c ⊗ b2 = map (Batch A B) (pair c) b2.
  Proof.
    induction b2.
    - reflexivity.
    - intros. cbn; change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. rewrite IHb2.
      compose near b2 on left.
      now rewrite (fun_map_map (F := Batch A B)).
  Qed.

  Lemma mult_Batch_rw4 : forall (a : A) `(b1 : @Batch A B (B -> C)) `(d : D),
      (b1 ⧆ a) ⊗ Done A B D d =
        map (Batch A B) (costrength_arrow ∘ pair_right d) b1 ⧆ a.
  Proof.
    reflexivity.
  Qed.

  Lemma mult_Batch_rw5 : forall `(b2 : @Batch A B (B -> D)) `(c : C) (a : A),
      Done A B C c ⊗ (b2 ⧆ a) = map (Batch A B) (strength_arrow ∘ pair c) b2 ⧆ a.
  Proof.
    cbn. change (mult_Batch ?x ?y) with (x ⊗ y) in *. intros.
    fequal. rewrite (mult_Batch_rw3). compose near b2 on left.
    now rewrite (fun_map_map (F := Batch A B)).
  Qed.

  Lemma mult_Batch_rw6 : forall (a1 a2 : A) `(b1 : Batch A B (B -> C)) `(b2 : Batch A B (B -> D)),
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

(** ** Examples of operations *)
(******************************************************************************)
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

(** * Functoriality of <<Batch A B>> in <<A>> and <<B>> *)
(******************************************************************************)
Fixpoint mapfst_Batch (A1 A2 : Type) {B C : Type} (f : A1 -> A2) (b : Batch A1 B C) : Batch A2 B C :=
  match b with
  | Done _ _ _  c => Done A2 B C c
  | Step _ _ _ rest a => Step A2 B C (mapfst_Batch A1 A2 f rest) (f a)
  end.

Fixpoint mapsnd_Batch {A : Type} (B1 B2 : Type) {C : Type} (f : B1 -> B2) (b : Batch A B2 C) : Batch A B1 C :=
  match b with
  | Done _ _ _ c => Done A B1 C c
  | Step _ _ _ rest c => Step A B1 C (map (Batch A B1) (precompose f) (mapsnd_Batch B1 B2 f rest)) c
  end.

(** ** Commuting independent maps *)
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

(** * Properties of [mapfst] *)
(******************************************************************************)

(** ** Rewriting principles *)
(******************************************************************************)
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

(** ** [mapfst] is a homomorphism *)
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

(** * <<Batch A B>> as a free applicative *)
(******************************************************************************)

(** ** Initiality (<<runBatch>>) *)
(******************************************************************************)
Fixpoint runBatch {A B : Type} {F : Type -> Type}
  (ϕ : A -> F B) `{Map F} `{Mult F} `{Pure F} (C : Type) (b : Batch A B C) : F C :=
  match b with
  | Done _ _ _ c => pure F c
  | Step _ _ _ rest a => runBatch ϕ (B -> C) rest <⋆> ϕ a
  end.

(** ** Rewriting principles *)
(******************************************************************************)
Lemma runBatch_rw1 `{Applicative F} `(ϕ : A -> F B) (C : Type) (c : C) :
  runBatch ϕ C (Done A B C c) = pure F c.
Proof.
  reflexivity.
Qed.

Lemma runBatch_rw2 `{Applicative F} `(ϕ : A -> F B)
  (a : A) (C : Type) (rest : Batch A B (B -> C)) :
  runBatch ϕ C (rest ⧆ a) = runBatch ϕ (B -> C) rest <⋆> ϕ a.
Proof.
  reflexivity.
Qed.

(** ** Naturality of of <<runBatch>> *)
(******************************************************************************)
Section runBatch_naturality.

  Context
    `{Applicative F}.

  Lemma natural_runBatch {A B C1 C2 : Type} (ϕ : A -> F B) (f : C1 -> C2) (b : Batch A B C1) :
    map F f (runBatch ϕ C1 b) = runBatch ϕ C2 (map (Batch A B) f b).
  Proof.
    generalize dependent C2.
    induction b; intros.
    - cbn. now rewrite (app_pure_natural F).
    - cbn. rewrite map_ap. fequal. now rewrite IHb.
  Qed.

  #[export] Instance Natural_runBatch `(ϕ : A -> F B) :
    Natural (@runBatch A B F ϕ _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    introv. ext j. unfold compose. apply natural_runBatch.
  Qed.

  Lemma runBatch_mapfst : forall `(s : Batch A1 B C) `(ϕ : A2 -> F B) (f : A1 -> A2),
      runBatch (ϕ ∘ f) C s = runBatch ϕ C (mapfst_Batch A1 A2 f s).
  Proof.
    intros; induction s.
    - easy.
    - cbn. now rewrite IHs.
  Qed.

  Lemma runBatch_mapsnd : forall `(s : @Batch A B2 C) `(ϕ : A -> F B1) (f : B1 -> B2),
      runBatch (map F f ∘ ϕ) C s = runBatch ϕ C (mapsnd_Batch B1 B2 f s).
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
    @ψ C (runBatch ϕ C b) = runBatch (@ψ B ∘ ϕ) C b.
  Proof.
    induction b.
    - cbn. now rewrite (appmor_pure F G).
    - cbn. rewrite ap_morphism_1.
      now rewrite IHb.
  Qed.

End runBatch_naturality.

(** ** <<runBatch>> is an applicative morphism **)
(******************************************************************************)
Section runBatch_morphism.

  Context
    `{Applicative F}
    `{ϕ : A -> F B}.

  Lemma appmor_pure_runBatch : forall (a : A),
      runBatch ϕ A (pure (Batch A B) a) = pure F a.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runBatch : forall {C D} (x : Batch A B C) (y : Batch A B D),
      runBatch ϕ (C * D) (x ⊗ y) = runBatch ϕ C x ⊗ runBatch ϕ D y.
  Proof.
    intros. generalize dependent x. induction y as [ANY any | ANY rest IH x'].
    - intros. rewrite mult_Batch_rw2.
      rewrite runBatch_rw1. rewrite triangle_4.
      now rewrite natural_runBatch.
    - intros.  rewrite runBatch_rw2.
      unfold ap. rewrite (app_mult_natural_r F).
      rewrite <- (app_assoc F).
      rewrite <- IH. clear IH.
      compose near (runBatch ϕ _ (x ⊗ rest) ⊗ ϕ x').
      rewrite (fun_map_map).
      cbn. unfold ap. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch. rewrite (app_mult_natural_l F).
      compose near (runBatch ϕ _ (x ⊗ rest) ⊗ ϕ x') on left.
      rewrite (fun_map_map). fequal. now ext [[? ?] ?].
  Qed.

  #[export] Instance Morphism_store_fold: ApplicativeMorphism (Batch A B) F (@runBatch A B F ϕ _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatch.
    - intros. easy.
    - intros. apply appmor_mult_runBatch.
  Qed.

End runBatch_morphism.

(** * <<runBatch>> specialized to monoids *)
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
      runBatch_monoid ϕ b = unconst (runBatch (mkConst (tag := B) ∘ ϕ) _ b).
  Proof.
    intros. induction b.
    - easy.
    - cbn. now rewrite IHb.
  Qed.

  Lemma runBatch_monoid2 : forall (ϕ : A -> M) `(b : Batch A B C),
      runBatch_monoid ϕ b = runBatch (F := const M) (ϕ : A -> const M B) _ b.
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
        length (runBatch (F := const (list A)) (ret list A) _ b).
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
    | Done _ _ _ d => Done A B _ (Done B C D d)
    | Step _ _ _ rest a => Step _ _ _ (map (Batch A B) (@Step B C D) (cojoin_Batch rest)) a
    end.

  (* TODO Finish rest of the parameterized comonad structure. *)
  Lemma extr_cojoin_Batch : `(extract_Batch ∘ cojoin_Batch = @id (Batch A B C)).
  Proof.
    intros. ext b. induction b.
    - reflexivity.
    - unfold compose. cbn.
  Abort.

End parameterized.
