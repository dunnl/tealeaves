From Tealeaves Require Import
  Classes.Categorical.Applicative
  Categories.TypeFamily.

Import Applicative.Notations.

#[local] Generalizable Variables A B C D W S G T.
#[local] Set Implicit Arguments.

(** * Multisorted <<Batch>> Functor (<<BatchM>>) *)
(**********************************************************************)
Section BatchM.

  Context
    `{ix: Index}
    {T: K -> Type -> Type}
    {W A B: Type}.

  Inductive BatchM C: Type:=
  | Go: C -> BatchM C
  | Ap: forall (k: K), BatchM (T k B -> C) -> W * A -> BatchM C.

  #[local] Infix "⧆":=
    Ap (at level 51, left associativity): tealeaves_multi_scope.

  (** ** Functor Instance *)
  (********************************************************************)
  Fixpoint map_BatchM `{f: C -> D} `(c: BatchM C): BatchM D:=
    match c with
    | Go c => Go (f c)
    | @Ap _ k rest (pair w a) =>
        Ap (@map_BatchM (T k B -> C) (T k B -> D) (compose f) rest) (w, a)
    end.

  #[global] Instance Map_BatchM: Map BatchM:= @map_BatchM.

  Lemma map_id_BatchM: forall (C: Type),
      map (F:= BatchM) id = @id (BatchM C).
  Proof.
    intros. ext s. induction s.
    - easy.
    - unfold id in *. destruct p.
      now rewrite <- IHs at 2.
  Qed.

  Lemma map_map_BatchM: forall (C D E: Type) (f: C -> D) (g: D -> E),
      map (F:= BatchM) g ∘ map (F:= BatchM) f = map (F:= BatchM) (g ∘ f).
  Proof.
    intros. unfold compose. ext s. generalize dependent E.
    generalize dependent D. induction s.
    - easy.
    - intros. destruct p. cbn. fequal.
      apply IHs.
  Qed.

  #[global, program] Instance Functor_BatchM: Functor BatchM:=
    {| fun_map_id:= map_id_BatchM;
      fun_map_map:= map_map_BatchM;
    |}.

  (** ** Applicative Instance *)
  (********************************************************************)
  #[global] Instance Pure_BatchM: Pure BatchM:=
    fun (C: Type) (c: C) => Go c.

  Fixpoint mult_BatchM `(jc: BatchM C) `(jd: BatchM D): BatchM (C * D) :=
    match jd with
    | Go d => map (F:= BatchM) (fun (c: C) => (c, d)) jc
    | Ap rest (pair w a) =>
        Ap (map (F:= BatchM)
              strength_arrow (mult_BatchM jc rest)) (pair w a)
    end.

  #[global] Instance Mult_BatchM: Mult BatchM:=
    fun C D '(c, d) => mult_BatchM c d.

  Lemma mult_BatchM_rw1:
    forall `(a: A) `(b: B),
      Go a ⊗ Go b = Go (a, b).
  Proof.
    easy.
  Qed.

  Lemma mult_BatchM_rw2:
    forall `(d: D) `(jc: BatchM C),
      jc ⊗ Go d = map (F:= BatchM) (pair_right d) jc.
  Proof.
    intros. induction jc; easy.
  Qed.

  Lemma mult_BatchM_rw3:
    forall `(d: D) `(jc: BatchM C),
      Go d ⊗ jc =
        map (F:= BatchM) (pair d) jc.
  Proof.
    induction jc.
    - easy.
    - destruct p. cbn; change (mult_BatchM ?x ?y) with (x ⊗ y).
      fequal. rewrite IHjc. compose near jc on left.
      now rewrite (fun_map_map (F:= BatchM)).
  Qed.

  Lemma mult_BatchM_rw4:
    forall (w: W) (a: A) (k: K) `(jc: @BatchM (T k B -> C)) `(d: D),
      (jc ⧆ (w, a)) ⊗ Go d =
        map (F:= BatchM) (costrength_arrow ∘ pair_right d) jc ⧆ (w, a).
  Proof.
    easy.
  Qed.

  Lemma mult_BatchM_rw5:
    forall (w: W) (a: A) (k: K) `(jc: @BatchM (T k B -> C)) `(d: D),
      Go d ⊗ (jc ⧆ (w, a)) =
        map (F:= BatchM) (strength_arrow ∘ pair d) jc ⧆ (w, a).
  Proof.
    intros. cbn.
    change (mult_BatchM ?x ?y) with (x ⊗ y).
    rewrite (mult_BatchM_rw3 d).
    compose near jc on left.
    rewrite (fun_map_map (F:= BatchM)).
    reflexivity.
  Qed.

  Lemma mult_BatchM_rw6:
    forall (w1 w2: W) (a1 a2: A) (k: K)
      `(jc: BatchM (T k B -> C)) `(jd: BatchM (T k B -> D)),
      (jc ⧆ (w1, a1)) ⊗ (jd ⧆ (w2, a2)) =
        map (F:= BatchM) strength_arrow ((jc ⧆ (w1, a1)) ⊗ jd) ⧆ (w2, a2).
  Proof.
    reflexivity.
  Qed.

  Lemma app_pure_natural_BatchM:
    forall (C D: Type) (f: C -> D) (x: C),
      map (F:= BatchM) f (pure (F:= BatchM) x) =
        pure (F:= BatchM) (f x).
  Proof.
    easy.
  Qed.

  Lemma app_mult_natural_BatchM1:
    forall (C D E: Type) (f: C -> D) (x: BatchM C) (y: BatchM E),
      map (F:= BatchM) f x ⊗ y = map (F:= BatchM) (map_fst f) (x ⊗ y).
  Proof.
    intros. generalize dependent E. induction y.
    - intros; cbn. compose near x.
      now do 2 rewrite (fun_map_map (F:= BatchM)).
    - destruct p. cbn; change (mult_BatchM ?x ?y) with (x ⊗ y).
      rewrite IHy. compose near (x ⊗ y).
      do 2 rewrite (fun_map_map (F:= BatchM)). do 2 fequal.
      now ext [? ?].
  Qed.

  Lemma app_mult_natural_BatchM2:
    forall (A B D: Type) (g: B -> D) (x: BatchM A) (y: BatchM B),
      x ⊗ map (F:= BatchM) g y = map (F:= BatchM) (map_snd g) (x ⊗ y).
  Proof.
    intros. generalize dependent D. induction y as [ANY any | ANY k rest IH [w a]].
    - intros; cbn. compose near x on right. now rewrite (fun_map_map (F:= BatchM)).
    - intros; cbn. fequal.
      change (mult_BatchM ?jx ?jy) with (jx ⊗ jy).
      rewrite IH. compose near (x ⊗ rest).
      do 2 rewrite (fun_map_map (F:= BatchM)). fequal.
      now ext [a' mk].
  Qed.

  Lemma app_mult_natural_BatchM:
    forall (A B C D: Type) (f: A -> C) (g: B -> D) (x: BatchM A) (y: BatchM B),
      map (F:= BatchM) f x ⊗ map (F:= BatchM) g y = map (F:= BatchM) (map_tensor f g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_BatchM1, app_mult_natural_BatchM2.
    compose near (x ⊗ y) on left. rewrite (fun_map_map (F:= BatchM)). fequal.
    now ext [a b].
  Qed.

  Lemma app_assoc_BatchM:
    forall (A B C: Type) (x: BatchM A) (y: BatchM B) (z: BatchM C),
      map (F:= BatchM) associator ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. induction z as [ANY any | ANY k rest IH [w a]].
    - do 2 rewrite mult_BatchM_rw2.
      rewrite (app_mult_natural_BatchM2). compose near (x ⊗ y) on left.
      now rewrite (fun_map_map (F:= BatchM)).
    - cbn. repeat change (mult_BatchM ?jx ?jy) with (jx ⊗ jy).
      fequal. rewrite (app_mult_natural_BatchM2).
      rewrite <- IH. compose near (x ⊗ y ⊗ rest).
      do 2 rewrite (fun_map_map (F:= BatchM)).
      compose near (x ⊗ y ⊗ rest) on right.
      rewrite (fun_map_map (F:= BatchM)).
      fequal. now ext [[? ?] ?].
  Qed.

  Lemma app_unital_l_BatchM:
    forall (A: Type) (x: BatchM A),
      map (F:= BatchM) left_unitor (pure (F:= BatchM) tt ⊗ x) = x.
  Proof.
    intros. induction x as [ANY any | ANY k rest IH [w a]].
    - easy.
    - cbn. change (mult_BatchM ?jx ?jy) with (jx ⊗ jy).
      fequal. compose near (pure (F:= BatchM) tt ⊗ rest).
      rewrite (fun_map_map (F:= BatchM)).
      rewrite <- IH. repeat fequal. auto.
  Qed.

  Lemma app_unital_r_BatchM:
    forall (A: Type) (x: BatchM A),
      map (F:= BatchM) right_unitor (x ⊗ pure (F:= BatchM) tt) = x.
  Proof.
    intros. induction x as [ANY any | ANY k rest IH [w a]].
    - easy.
    - cbn in *. fequal. rewrite <- IH at 2.
      compose near rest. now do 2 rewrite (fun_map_map (F:= BatchM)).
  Qed.

  Lemma app_mult_pure_BatchM:
    forall (A B: Type) (a: A) (b: B),
      pure (F:= BatchM) a ⊗ pure (F:= BatchM) b = pure (F:= BatchM) (a, b).
  Proof.
    intros. easy.
  Qed.

  #[global, program] Instance App_Path: Applicative BatchM.

  Next Obligation. apply app_mult_natural_BatchM. Qed.
  Next Obligation. apply app_assoc_BatchM. Qed.
  Next Obligation. apply app_unital_l_BatchM. Qed.
  Next Obligation. apply app_unital_r_BatchM. Qed.

End BatchM.

#[global] Arguments Ap {ix} {T}%function_scope
  {W A B}%type_scope {C}%type_scope {k} _ _.
#[local] Infix "⧆":= Ap (at level 51, left associativity): tealeaves_scope.

(** *** Examples of operations *)
(**********************************************************************)
Section demo.

  Context
    `{Index}
    (W: Type)
    (S: Type -> Type)
    `{T: K -> Type -> Type}
    (A B C X: Type)
    (a1 a2: A) (b1 b2 b3: B)
    (w1 w2 w3 w4: W)
    (c1 c2 c3 c4: C)
    (mk1: C -> X) (mk2: C -> C -> X) (mk0: X).

(*
  Check Go a1 ⊗ Go a2: @BatchM _ T W False False (A * A).
  Compute Go a1 ⊗ Go a2.
  Compute Go a1 ⊗ (Go mk1 ⧆ (w1, c1)).
  Compute (Go mk1 ⧆ (w1, c1)) ⊗ (Go mk1 ⧆ (w2, c2)).
  Compute (Go mk2 ⧆ (w1, c1) ⧆ (w2, c2)) ⊗ (Go mk1 ⧆ (w3, c3)).
 *)

End demo.

(** ** Functoriality of [BatchM] *)
(**********************************************************************)
Fixpoint mapfst_BatchM
  `{ix: Index}
  {W: Type}
  {T: K -> Type -> Type}
  {A1 A2 B C} (f: A1 -> A2)
  (j: @BatchM ix T W A1 B C):
  @BatchM ix T W A2 B C :=
  match j with
  | Go a => Go a
  | Ap rest p => Ap (mapfst_BatchM f rest) (map_snd f p)
  end.

(** * Operation <<runBatchM>> *)
(**********************************************************************)
Fixpoint runBatchM
  {ix: Index}
  {T: K -> Type -> Type}
  {W A B: Type} {F: Type -> Type}
  `{Map F} `{Mult F} `{Pure F}
  (ϕ: forall (k: K), W * A -> F (T k B))
  `(j: @BatchM ix T W A B C): F C :=
  match j with
  | Go a => pure a
  | @Ap _ _ _ _ _ _ k rest (pair w a) =>
      runBatchM ϕ rest <⋆> ϕ k (w, a)
  end.

Section runBatchM_rw.

  Context
    `{Index}
    `{Applicative G}
    {A B C: Type}
    `(f: forall (k: K), W * A -> G (T k B)).

  Lemma runBatchM_rw1 (c: C):
    runBatchM f (Go c) = pure c.
  Proof.
    reflexivity.
  Qed.

  Lemma runBatchM_rw2 (k: K) (w: W) (a: A) (rest: BatchM (T k B -> C)):
    runBatchM f (rest ⧆ (w, a)) = runBatchM f rest <⋆> f k (w, a).
  Proof.
    reflexivity.
  Qed.

End runBatchM_rw.

(** ** Naturality of <<runBatchM>> *)
(**********************************************************************)
Section runBatchM_naturality.

  Context
    `{Index}
    (W: Type)
    (S: Type -> Type)
    `{T: K -> Type -> Type}
    (A B C D: Type)
    `{Applicative G}
    (ϕ: forall k, W * A -> G (T k B)).

  Lemma natural_runBatchM (f: C -> D) (j: @BatchM _ T W A B C):
    map (F := G) f (runBatchM ϕ j) =
      runBatchM ϕ (map (F := BatchM) f j).
  Proof.
    generalize dependent D. induction j; intros.
    - cbn. now rewrite (app_pure_natural).
    - destruct p. cbn. rewrite map_ap. fequal.
      now rewrite IHj.
  Qed.

End runBatchM_naturality.

(** ** <<runBatchM>> as an Applicative Homomorphism *)
(**********************************************************************)
Section runBatchM_morphism.

  Context
    `{Index}
    (W: Type)
    (S: Type -> Type)
    `{T: K -> Type -> Type}
    (A B C D: Type)
    `{Applicative G}
    (f: forall k, W * A -> G (T k B)).

  Lemma appmor_pure_runBatchM:
    forall (C: Type) (c: C),
      runBatchM f (pure (F := BatchM) c) = pure c.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runBatchM:
    forall (C D: Type) (x: BatchM C) (y: BatchM D),
      runBatchM f (x ⊗ y) = runBatchM f x ⊗ runBatchM f y.
  Proof.
    intros. generalize dependent x. induction y.
    - intros. rewrite mult_BatchM_rw2.
      rewrite runBatchM_rw1. rewrite triangle_4.
      rewrite natural_runBatchM; auto.
    - intros. destruct p. rewrite runBatchM_rw2.
      unfold ap. rewrite (app_mult_natural_r G).
      rewrite <- (app_assoc).
      rewrite <- IHy. clear IHy.
      compose near (runBatchM f (x ⊗ y) ⊗ f k (w, a)).
      rewrite (fun_map_map).
      cbn. unfold ap. change (mult_BatchM ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatchM; auto.
      rewrite (app_mult_natural_l G).
      compose near (runBatchM f (x ⊗ y) ⊗ f k (w, a)) on left.
      rewrite (fun_map_map). fequal. now ext [[? ?] ?].
  Qed.

  #[global] Instance Morphism_store_fold:
    ApplicativeMorphism BatchM G
      (@runBatchM _ T W A B G _ _ _ f).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatchM.
    - intros. easy.
    - intros. apply appmor_mult_runBatchM.
  Qed.

End runBatchM_morphism.

(** ** <<runBatchM>> commutes with Applicative Homomorphisms **)
(**********************************************************************)
Section runBatchM_morphism.


  #[local] Generalizable All Variables.

  Context

    `{Index}
    (W: Type)
    (S: Type -> Type)
    `{T: K -> Type -> Type}
    (A B C D: Type)
    `{Applicative G1}
    `{Applicative G2}
    `{! ApplicativeMorphism G1 G2 ψ}
    (f: forall k, W * A -> G1 (T k B)).

  Lemma runBatchM_morphism `(j: @BatchM _ T W A B C):
    @ψ C (runBatchM f j) = runBatchM (fun k => @ψ (T k B) ∘ f k) j.
  Proof.
    induction j.
    - cbn. now rewrite (appmor_pure).
    - destruct p. cbn. rewrite ap_morphism_1.
      now rewrite IHj.
  Qed.

End runBatchM_morphism.

(** ** Notations *)
(**********************************************************************)
Module Notations.
  Infix "⧆" := Ap (at level 51, left associativity): tealeaves_scope.
End Notations.
