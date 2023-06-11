From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Functors.Constant.

Import Monoid.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables A B C D W F G ψ.

(** * The <<Batch2>> functor *)
(******************************************************************************)
Section Batch2.

  Context
    {W T : Type -> Type}
    {A B : Type}.

  Inductive Batch2 C : Type :=
  | Done : C -> Batch2 C
  | Step : Batch2 (T B -> C) -> W A -> Batch2 C.

  Fixpoint map_Batch2 `{f : C -> D} `(c : Batch2 C) : Batch2 D :=
    match c with
    | Done _ c => Done D (f c)
    | Step _ rest a =>
      Step D (@map_Batch2 (T B -> C) (T B -> D) (compose f) rest) a
    end.

  #[export] Instance Map_Batch2 : Map Batch2 := @map_Batch2.

  Lemma map_id_Batch2 : forall (C : Type),
      map Batch2 id = @id (Batch2 C).
  Proof.
    intros. ext s. induction s.
    - easy.
    - unfold id in *.
      now rewrite <- IHs at 2.
  Qed.

  Lemma map_map_Batch2 : forall (C D E : Type) (f : C -> D) (g : D -> E),
      map Batch2 g ∘ map Batch2 f = map Batch2 (g ∘ f).
  Proof.
    intros. unfold compose. ext s. generalize dependent E.
    generalize dependent D. induction s.
    - easy.
    - intros. cbn. fequal.
      apply IHs.
  Qed.

  #[export] Instance Functor_Batch2 : Functor Batch2 :=
    {| fun_map_id := map_id_Batch2;
       fun_map_map := map_map_Batch2;
    |}.

  (** ** Applicative Instance *)
  (******************************************************************************)
  #[export] Instance Pure_Batch2 : Pure Batch2 :=
    fun (C : Type) (c : C) => Done C c.

  Fixpoint mult_Batch2 `(jc : Batch2 C) `(jd : Batch2 D) : Batch2 (C * D) :=
    match jd with
    | Done _ d => map Batch2 (fun (c : C) => (c, d)) jc
    | Step _ rest a =>
        Step (C * D) (map Batch2 strength_arrow (mult_Batch2 jc rest)) a
    end.

  #[export] Instance Mult_Batch2 : Mult Batch2 :=
    fun C D '(c, d) => mult_Batch2 c d.

  #[local] Infix "⧆" := (Step _) (at level 51, left associativity) : tealeaves_scope.

  Lemma mult_Batch2_rw1 : forall `(a : A) `(b : B),
      Done _ a ⊗ Done _ b = Done _ (a, b).
  Proof.
    easy.
  Qed.

  Lemma mult_Batch2_rw2 : forall `(d : D) `(jc : Batch2 C),
      jc ⊗ Done D d = map Batch2 (pair_right d) jc.
  Proof.
    intros. induction jc; easy.
  Qed.

  Lemma mult_Batch2_rw3 : forall `(d : D) `(jc : Batch2 C),
      Done D d ⊗ jc = map Batch2 (pair d) jc.
  Proof.
    induction jc.
    - easy.
    - cbn; change (mult_Batch2 ?x ?y) with (x ⊗ y).
      fequal. rewrite IHjc. compose near jc on left.
      now rewrite (fun_map_map Batch2).
  Qed.

  Lemma mult_Batch2_rw4 : forall (a : W A) `(jc : @Batch2 (T B -> C)) `(d : D),
      (jc ⧆ a) ⊗ Done D d = map Batch2 (costrength_arrow ∘ pair_right d) jc ⧆ a.
  Proof.
    easy.
  Qed.

  Lemma mult_Batch2_rw5 : forall (a : W A) `(jc : @Batch2 (T B -> C)) `(d : D),
      Done D d ⊗ (jc ⧆ a) = map Batch2 (strength_arrow ∘ pair d) jc ⧆ a.
  Proof.
    intros. cbn. change (mult_Batch2 ?x ?y) with (x ⊗ y) in *.
    fequal. rewrite (mult_Batch2_rw3 d). compose near jc on left.
    now rewrite (fun_map_map Batch2).
  Qed.

  Lemma mult_Batch2_rw6 :
    forall (a1 a2 : W A)
      `(jc : Batch2 (T B -> C)) `(jd : Batch2 (T B -> D)),
      (jc ⧆ a1) ⊗ (jd ⧆ a2) =
      map Batch2 strength_arrow ((jc ⧆ a1) ⊗ jd) ⧆ a2.
  Proof.
    reflexivity.
  Qed.

  Lemma app_pure_natural_Batch2 : forall (C D : Type) (f : C -> D) (x : C),
      map Batch2 f (pure Batch2 x) = pure Batch2 (f x).
  Proof.
    easy.
  Qed.

  Lemma app_mult_natural_Batch21 : forall (C D E : Type) (f : C -> D) (x : Batch2 C) (y : Batch2 E),
      map Batch2 f x ⊗ y = map Batch2 (map_fst f) (x ⊗ y).
  Proof.
    intros. generalize dependent E. induction y.
    - intros; cbn. compose near x.
      now do 2 rewrite (fun_map_map Batch2).
    - cbn; change (mult_Batch2 ?x ?y) with (x ⊗ y).
      rewrite IHy. compose near (x ⊗ y).
      do 2 rewrite (fun_map_map Batch2). do 2 fequal.
      now ext [? ?].
  Qed.

  Lemma app_mult_natural_Batch22 : forall (A B D : Type) (g : B -> D) (x : Batch2 A) (y : Batch2 B),
      x ⊗ map Batch2 g y = map Batch2 (map_snd g) (x ⊗ y).
  Proof.
    intros. generalize dependent D. induction y as [ANY any | ANY rest IH a].
    - intros; cbn. compose near x on right. now rewrite (fun_map_map Batch2).
    - intros; cbn. fequal.
      change (mult_Batch2 ?jx ?jy) with (jx ⊗ jy).
      rewrite IH. compose near (x ⊗ rest).
      do 2 rewrite (fun_map_map Batch2). fequal.
      now ext [a' mk].
  Qed.

  Lemma app_mult_natural_Batch2 : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : Batch2 A) (y : Batch2 B),
      map Batch2 f x ⊗ map Batch2 g y = map Batch2 (map_tensor f g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_Batch21, app_mult_natural_Batch22.
    compose near (x ⊗ y) on left. rewrite (fun_map_map Batch2). fequal.
    now ext [a b].
  Qed.

  Lemma app_assoc_Batch2 : forall (A B C : Type) (x : Batch2 A) (y : Batch2 B) (z : Batch2 C),
      map Batch2 associator ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. induction z as [ANY any | ANY rest IH a].
    - do 2 rewrite mult_Batch2_rw2.
      rewrite (app_mult_natural_Batch22). compose near (x ⊗ y) on left.
      now rewrite (fun_map_map Batch2).
    - cbn. repeat change (mult_Batch2 ?jx ?jy) with (jx ⊗ jy).
      fequal. rewrite (app_mult_natural_Batch22).
      rewrite <- IH. compose near (x ⊗ y ⊗ rest).
      do 2 rewrite (fun_map_map Batch2).
      compose near (x ⊗ y ⊗ rest) on right.
      rewrite (fun_map_map Batch2).
      fequal. now ext [[? ?] ?].
  Qed.

  Lemma app_unital_l_Batch2 : forall (A : Type) (x : Batch2 A),
      map Batch2 left_unitor (pure Batch2 tt ⊗ x) = x.
  Proof.
    intros. induction x as [ANY any | ANY rest IH a].
    - easy.
    - cbn. change (mult_Batch2 ?jx ?jy) with (jx ⊗ jy).
      fequal. compose near (pure Batch2 tt ⊗ rest).
      rewrite (fun_map_map Batch2).
      rewrite <- IH. repeat fequal. auto.
  Qed.

  Lemma app_unital_r_Batch2 : forall (A : Type) (x : Batch2 A),
      map Batch2 right_unitor (x ⊗ pure Batch2 tt) = x.
  Proof.
    intros. induction x as [ANY any | ANY rest IH a].
    - easy.
    - cbn in *. fequal. rewrite <- IH at 2.
      compose near rest. now do 2 rewrite (fun_map_map Batch2).
  Qed.

  Lemma app_mult_pure_Batch2 : forall (A B : Type) (a : A) (b : B),
      pure Batch2 a ⊗ pure Batch2 b = pure Batch2 (a, b).
  Proof.
    intros. easy.
  Qed.

  #[export, program] Instance App_Path : Applicative Batch2.

  Next Obligation. apply app_mult_natural_Batch2. Qed.
  Next Obligation. apply app_assoc_Batch2. Qed.
  Next Obligation. apply app_unital_l_Batch2. Qed.
  Next Obligation. apply app_unital_r_Batch2. Qed.

End Batch2.

Arguments Step {W T}%function_scope {A B}%type_scope [C]%type_scope _ _.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Infix "⧆" := Step (at level 51, left associativity) : tealeaves_scope.

End Notations.

Import Notations.

(** *** Examples of operations *)
(******************************************************************************)
Section demo.

  Context
    (T : Type -> Type)
    (A B C X W : Type)
    (a1 a2 : A) (b1 b2 b3 : B)
    (w1 w2 w3 w4 : W)
    (c1 c2 c3 c4 : C)
    (mk1 : C -> X) (mk2 : C -> C -> X) (mk0 : X).

  (*
  Check Done a1 ⊗ Done a2 : @Batch2 _ T W False False (A * A).
  Compute Done a1 ⊗ Done a2.
  Compute Done a1 ⊗ (Done mk1 ⧆ (w1, c1)).
  Compute (Done mk1 ⧆ (w1, c1)) ⊗ (Done mk1 ⧆ (w2, c2)).
  Compute (Done mk2 ⧆ (w1, c1) ⧆ (w2, c2)) ⊗ (Done mk1 ⧆ (w3, c3)).
   *)

End demo.

(** ** Functoriality of [Batch2] *)
(******************************************************************************)
Section functoriality_Batch2.

  Context
    (T : Type -> Type).

  Fixpoint mapfst_Batch2 `{Map W} {A1 A2 B C} (f : A1 -> A2) `(j : @Batch2 W T A1 B C) : @Batch2 W T A2 B C :=
    match j with
    | Done _ a => Done _ a
    | Step rest p => Step (mapfst_Batch2 f rest) (map W f p)
    end.

End functoriality_Batch2.

(** * The <<runBatch2>> operation *)
(******************************************************************************)
Fixpoint runBatch2
         (W T : Type -> Type) {A B : Type} (F : Type -> Type)
         `{Map F} `{Mult F} `{Pure F}
         (ϕ : W A -> F (T B))
         `(j : @Batch2 W T A B C) : F C :=
  match j with
  | Done _ a => pure F a
  | @Step _ _ _ _ _ rest a => runBatch2 W T F ϕ rest <⋆> ϕ a
  end.

Section runBatch2_rw.

  Context
    (W T : Type -> Type).

  Context
    (A B C : Type)
    `{Applicative F}
    (f : W A -> F (T B)).

  Lemma runBatch2_rw1 (c : C) :
    runBatch2 W T F f (Done _ c) = pure F c.
  Proof.
    reflexivity.
  Qed.

  Lemma runBatch2_rw2 (a : W A) (rest : Batch2 (T B -> C)) :
    runBatch2 W T F f (rest ⧆ a) = runBatch2 W T F f rest <⋆> f a.
  Proof.
    reflexivity.
  Qed.

End runBatch2_rw.

(** ** Naturality of of <<runBatch2>> *)
(******************************************************************************)
Section runBatch2_naturality.

  Context
    (W T : Type -> Type)
    `{Applicative F}.

  Context
    (A B C D : Type)
    `{Applicative F}
    (ϕ : W A -> F (T B)).

  Lemma natural_runBatch2 (f : C -> D) (j : @Batch2 W T A B C) :
    map F f (runBatch2 W T F ϕ j) = runBatch2 W T F ϕ (map Batch2 f j).
  Proof.
    generalize dependent D. induction j; intros.
    - cbn. now rewrite (app_pure_natural F).
    - cbn. rewrite map_ap. fequal.
      now rewrite IHj.
  Qed.

End runBatch2_naturality.

(** ** <<runBatch2>> is an applicative morphism **)
(******************************************************************************)
Section runBatch2_morphism.

  Context
    (W T : Type -> Type)
    (A B : Type)
    `{Applicative F}
    (f : W A -> F (T B)).

  Lemma appmor_pure_runBatch2 : forall (C : Type) (c : C),
      runBatch2 W T F f (pure Batch2 c) = pure F c.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runBatch2 : forall (C D : Type) (x : Batch2 C) (y : Batch2 D),
      runBatch2 W T F f (x ⊗ y) = runBatch2 W T F f x ⊗ runBatch2 W T F f y.
  Proof.
    intros. generalize dependent x. induction y.
    - intros. rewrite mult_Batch2_rw2.
      rewrite runBatch2_rw1. rewrite triangle_4.
      rewrite natural_runBatch2; auto.
    - intros. rewrite runBatch2_rw2.
      unfold ap. rewrite (app_mult_natural_r F).
      rewrite <- (app_assoc F).
      rewrite <- IHy. clear IHy.
      compose near (runBatch2 W T F f (x ⊗ y) ⊗ f w).
      rewrite (fun_map_map F).
      cbn. unfold ap. change (mult_Batch2 ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch2; auto.
      rewrite (app_mult_natural_l F).
      compose near (runBatch2 W T F f (x ⊗ y) ⊗ f w) on left.
      rewrite (fun_map_map F). fequal. now ext [[? ?] ?].
  Qed.

  #[export] Instance Morphism_store_fold: ApplicativeMorphism Batch2 F (@runBatch2 W T A B F _ _ _ f).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatch2.
    - intros. easy.
    - intros. apply appmor_mult_runBatch2.
  Qed.

End runBatch2_morphism.

(** ** <<runBatch2>> commuts with applicative morphisms **)
(******************************************************************************)
Section runBatch2_morphism.


  Context
    (W T : Type -> Type)
    (A B C : Type)
    `{Applicative F}
    `{Applicative G}
    `{! ApplicativeMorphism F G ψ}
    (f : W A -> F (T B)).

  Lemma runBatch2_morphism `(j : @Batch2 W T A B C) :
    @ψ C (runBatch2 W T F f j) = runBatch2 W T G (@ψ (T B) ∘ f) j.
  Proof.
    induction j.
    - cbn. now rewrite (appmor_pure F G).
    - cbn. rewrite ap_morphism_1.
      now rewrite IHj.
  Qed.

End runBatch2_morphism.
