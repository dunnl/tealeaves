(*|
############################################################
Formalizing STLC with Named Variables
############################################################

============================
Imports and setup
============================
|*)

From Tealeaves.Classes Require Export
  Functor2
  Categorical.ApplicativeCommutativeIdempotent
  Categorical.TraversableFunctor
  Kleisli.DecoratedTraversableCommIdemFunctor
  Kleisli.DecoratedTraversableMonadPoly.

From Tealeaves.Functors Require Export
  List Z2.

From Tealeaves.Backends Require Export
  LN.Atom.

Import Product.Notations.
Import Monoid.Notations.
Import List.ListNotations.
Import DecoratedTraversableCommIdemFunctor.Notations.

#[local] Generalizable Variables G ϕ.
#[local] Set Implicit Arguments.

Import Applicative.Notations.

(** * Language definition *)
(******************************************************************************)
Inductive term (B V: Type) :=
| tvar: V -> term B V
| lam: B -> term B V -> term B V
| tap: term B V -> term B V -> term B V.
#[global] Arguments tvar {B}%type_scope {V}%type_scope _.

(** ** Notations and automation *)
(******************************************************************************)
Module Notations.
  Notation "'λ'" := (lam) (at level 45).
End Notations.

Import Notations.

Parameters (x y z: atom).

Example term1: term atom atom := lam x (tap (lam y (tvar z)) (tvar x)).

(*|
============================================
Decomposition into categorical components
============================================
|*)

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Map
+++++++++++++++++++++++++++++++++++++++++++++++
|*)
Fixpoint map_term {B1 V1 B2 V2: Type} (ρ: B1 -> B2) (σ: V1 -> V2)
  (t: term B1 V1): term B2 V2 :=
  match t with
  | tvar v => (@tvar B2 V2) (σ v)
  | lam v body => lam (ρ v) (map_term ρ σ body)
  | tap t1 t2 => tap (map_term ρ σ t1) (map_term ρ σ t2)
  end.

Lemma map_id_term: forall (B1 V1: Type),
    map_term (@id B1) (@id V1) = @id (term B1 V1).
Proof.
  intros. ext t. induction t.
  - reflexivity.
  - cbn. now rewrite IHt.
  - cbn. now rewrite IHt1, IHt2.
Qed.

Lemma map_map_term: forall (B1 V1 B2 V2 b3 v3: Type)
                      (ρ1: B1 -> B2) (σ1: V1 -> V2) (ρ2: B2 -> b3) (σ2: V2 -> v3),
    map_term ρ2 σ2 ∘ map_term ρ1 σ1 = map_term (ρ2 ∘ ρ1) (σ2 ∘ σ1).
Proof.
  intros. ext t. induction t.
  - reflexivity.
  - cbn. compose near t on left. now rewrite IHt.
  - cbn.
    compose near t1 on left. rewrite IHt1.
    compose near t2 on left. rewrite IHt2.
    reflexivity.
Qed.

Instance Map_term_r: forall B, Map (term B).
Proof.
  intros B V1 V2 f.
  exact (map_term id f).
Defined.

Instance Functor_term_r: forall B, Functor (term B).
Admitted.

Instance Map2_term: Map2 term.
Proof.
  intros A1 B1 A2 B2 f1 f2.
  apply (map_term f1 f2).
Defined.

Section map_term_rewriting.

  Context
    {B1 V1 B2 V2: Type}
      (ρ: B1 -> B2)
      (σ: V1 -> V2).

  Lemma map_term_rw1: forall (v: V1),
      map_term ρ σ (tvar (B := B1) v) = tvar (σ v).
  Proof.
    reflexivity.
  Qed.

  Lemma map_term_rw2: forall (b: B1) (body: term B1 V1),
      map_term ρ σ (lam b body) = lam (ρ b) (map_term ρ σ body).
  Proof.
    reflexivity.
  Qed.

  Lemma map_term_rw3: forall (t1 t2: term B1 V1),
      map_term ρ σ (tap t1 t2) = tap (map_term ρ σ t1) (map_term ρ σ t2).
  Proof.
    reflexivity.
  Qed.

End map_term_rewriting.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Decoration
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

Fixpoint dec_term_rec {B V: Type} (ctx: list B)
  (t: term B V): term (list B * B) (list B * V) :=
  match t with
  | tvar v => tvar (ctx, v)
  | lam b body => lam (ctx, b) (dec_term_rec (ctx ++ [b]) body)
  | tap t1 t2 => tap (dec_term_rec ctx t1) (dec_term_rec ctx t2)
  end.

Definition dec_term {B V: Type}:
  term B V ->
  term (list B * B) (list B * V) :=
  dec_term_rec nil.

Compute dec_term term1.

Section dec_term_rewriting.

  Context (B V: Type) (ctx: list B).

  Lemma dec_term_rec_rw1: forall (v: V),
      dec_term_rec ctx (tvar v) = tvar (ctx, v).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term_rec_rw2: forall (b: B) (body: term B V),
      dec_term_rec ctx (lam b body) =
        lam (ctx, b) (dec_term_rec (ctx ++ [b]) body).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term_rec_rw3: forall (t1 t2: term B V),
      dec_term_rec ctx (tap t1 t2) = tap (dec_term_rec ctx t1) (dec_term_rec ctx t2).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term_rw1: forall (v: V),
      dec_term (tvar (B := B) v) = tvar ([], v).
  Proof.
    cbn.
    reflexivity.
  Qed.

  Lemma dec_term_rw2: forall (b: B) (body: term B V),
      dec_term (lam b body) = lam ([], b) (dec_term_rec [b] body).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term_rw3: forall (t1 t2: term B V),
      dec_term (tap t1 t2) = tap (dec_term t1) (dec_term t2).
  Proof.
    reflexivity.
  Qed.

End dec_term_rewriting.

Lemma map_dec_rec:
  forall (B1 V1 B2 V2: Type)
    (ρ: list B1 * B1 -> B2) (σ: list B1 * V1 -> V2) (ctx: list B1),
    map_term ρ σ ∘ dec_term_rec ctx =
      map_term (ρ ⦿ ctx) (σ ⦿ ctx) ∘ dec_term.
Proof.
  intros. ext t. unfold compose.
  generalize dependent ctx.
  generalize dependent σ.
  generalize dependent ρ.
  induction t; intros ρ σ ctx.
  - cbn. unfold preincr, compose, incr.
    change (@nil B1) with (Ƶ: list B1).
    rewrite monoid_id_l.
    reflexivity.
  - cbn.
    rewrite IHt.
    rewrite IHt.
    fequal.
    + unfold preincr, incr, compose, monoid_op, Monoid_op_list.
      rewrite List.app_nil_r.
      reflexivity.
    + rewrite preincr_preincr.
      rewrite preincr_preincr.
      reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Lemma dec_rec_spec:
  forall (B V: Type) (ctx: list B),
    dec_term_rec ctx =
      map_term (incr ctx) (incr ctx) ∘ dec_term (V := V).
Proof.
  intros.
  change_left (id ∘ dec_term_rec ctx (V := V)).
  rewrite <- map_id_term.
  rewrite map_dec_rec.
  reflexivity.
Qed.

Lemma dec_rec_extract_term: forall (B V: Type) (ctx: list B),
    map_term (extract_Z2) (extract_Z2) ∘ dec_term_rec ctx = @id (term B V).
Proof.
  intros. ext t. unfold compose.
  generalize dependent ctx. induction t; intro ctx.
  - reflexivity.
  - cbn. now rewrite IHt.
  - cbn. now rewrite IHt1, IHt2.
Qed.

Lemma dec_extract_term: forall (B V: Type),
    map_term (extract_Z2) (extract_Z2) ∘ dec_term = @id (term B V).
Proof.
  intros. unfold dec_term. apply dec_rec_extract_term.
Qed.

Lemma dec_rec_dec_rec_term: forall (B V: Type) (ctx: list B),
    dec_term_rec (decorate_prefix_list ctx) ∘ dec_term_rec ctx =
      map_term (cojoin_Z2) (cojoin_Z2) ∘ dec_term_rec ctx (B := B) (V := V).
Proof.
  intros. ext t. unfold compose.
  generalize dependent ctx.
  induction t; intro ctx.
  - reflexivity.
  - cbn.
    rewrite <- IHt.
    rewrite decorate_prefix_list_rw_app.
    cbn. change (@nil B) with (Ƶ: list B).
    rewrite monoid_id_l.
    reflexivity.
  - cbn. now rewrite IHt1, IHt2.
Qed.

Lemma dec_dec_term: forall (B V: Type),
    dec_term ∘ dec_term (B := B) (V := V) =
      map_term (cojoin_Z2) (cojoin_Z2) ∘ dec_term.
Proof.
  intros. unfold dec_term.
  change (@nil (list B * B)) with (decorate_prefix_list (@nil B)).
  apply dec_rec_dec_rec_term.
Qed.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Applicative distribution
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

Fixpoint dist_term {B V: Type}
  {G: Type -> Type} `{Map G} `{Pure G} `{Mult G}
  (t: term (G B) (G V)): G (term B V) :=
  match t with
  | tvar vr => map (@tvar B V) vr
  | lam bin body => pure (@lam B V)
                     <⋆> bin
                     <⋆> dist_term body
  | tap t1 t2 => pure (@tap B V)
                  <⋆> dist_term t1
                  <⋆> dist_term t2
  end.

(*
Require Import Categorical.TraversableFunctor.
Print TraversableFunctor.
 *)

Lemma dist_term_morph:
  forall (G1 G2 : Type -> Type)
    `{Map G1} `{Mult G1} `{Pure G1}
    `{Map G2} `{Mult G2} `{Pure G2}
    (ϕ: forall (A: Type), G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ ->
    forall (B V: Type), dist_term ∘ map_term (ϕ B) (ϕ V) =
                     ϕ (term B V) ∘ dist_term (B := B) (V := V).
Proof.
  intros. ext t. unfold compose.
  induction t.
  - cbn.
    rewrite appmor_natural.
    reflexivity.
  - cbn.
    rewrite IHt.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    reflexivity.
Qed.

Lemma dist_term_linear:
  forall (G1 G2 : Type -> Type)
    `{Map G1} `{Mult G1} `{Pure G1} `{! Applicative G1}
    `{Map G2} `{Mult G2} `{Pure G2} `{! Applicative G2},
  forall (B V: Type),
    dist_term (G := G1 ∘ G2) =
    map (F := G1) (dist_term (G := G2)) ∘
      dist_term (G := G1) (B := G2 B) (V := G2 V).
Proof.
Admitted.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Join
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

#[export] Instance Return_lambda_term: forall B, Return (term B) :=
  @tvar.

Fixpoint join_term {B V: Type} (t: term B (term B V)): term B V :=
  match t with
  | tvar v => v
  | lam b body => lam b (join_term body)
  | tap t1 t2 => tap (join_term t1) (join_term t2)
  end.

Lemma join_ret_term {B V: Type}:
  join_term ∘ ret (A := term B V) = @id (term B V).
Proof.
  reflexivity.
Qed.

Lemma join_map_ret_term {B V: Type}:
  join_term ∘ map_term (@id B) (ret (A := V)) = @id (term B V).
Proof.
  ext t. unfold compose. induction t.
  - reflexivity.
  - cbn. rewrite IHt. reflexivity.
  - cbn. rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma join_join_term {B V: Type}:
  join_term ∘ join_term (B := B) (V := term B V) =
    join_term ∘ map_term id (join_term).
Proof.
  intros. ext t.
  unfold compose.
  induction t as [v | b body IHbody | t1 IHt1 t2 IHt2].
  - reflexivity.
  - cbn.
    rewrite IHbody.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Section join_term_rewriting.

  Context (B V: Type).

  Lemma join_term_rw1: forall (v: term B V),
      join_term (tvar (B := B) v) = v.
  Proof.
    reflexivity.
  Qed.

  Lemma join_term_rw2: forall (b: B) (body: term B (term B V)),
      join_term (lam b body) = lam b (join_term body).
  Proof.
    reflexivity.
  Qed.

  Lemma join_term_rw3: forall (t1 t2: term B (term B V)),
      join_term (tap t1 t2) = tap (join_term t1) (join_term t2).
  Proof.
    reflexivity.
  Qed.

End join_term_rewriting.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Naturality
+++++++++++++++++++++++++++++++++++++++++++++++
|*)
Section naturality.

  Context {B1 V1 B2 V2: Type}
    (ρ: B1 -> B2) (σ: V1 -> V2).

  Lemma join_map:
    join_term ∘ map_term ρ (map_term ρ σ) =
      map_term ρ σ ∘ join_term.
  Proof.
    ext t. unfold compose.
    induction t as [v | b body IHbody | t1 IHt1 t2 IHt2].
    - reflexivity.
    - cbn.
      rewrite IHbody.
      reflexivity.
    - cbn.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

  Lemma dec_rec_map: forall (ctx: list B1),
    dec_term_rec (map ρ ctx) ∘ map_term ρ σ =
      map_term (map_pair (map ρ) ρ) (map_pair (map ρ) σ) ∘ dec_term_rec ctx.
  Proof.
    intros. ext t. unfold compose.
    generalize dependent ρ; clear ρ.
    generalize dependent σ; clear σ.
    generalize dependent ctx.
    induction t as [v | b body IHbody | t1 IHt1 t2 IHt2];
      intros.
    - reflexivity.
    - cbn.
      fequal.
      replace (map ρ ctx ++ [ρ b])
        with (map ρ (ctx ++ [b])) by now rewrite map_list_app.
      rewrite IHbody.
      reflexivity.
    - cbn.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

  Lemma dec_map:
    dec_term ∘ map_term ρ σ =
      map_term (map_pair (map ρ) ρ) (map_pair (map ρ) σ) ∘ dec_term.
  Proof.
    unfold dec_term.
    change (@nil B2) with (map ρ nil).
    rewrite dec_rec_map.
    reflexivity.
  Qed.

  Lemma dist_map `{ApplicativeCommutativeIdempotent G}:
    map (map_term ρ σ) ∘ dist_term (G := G) =
      dist_term ∘ map_term (map ρ) (map σ).
  Proof.
    intros. ext t. unfold compose.
    induction t as [v | b body IHbody | t1 IHt1 t2 IHt2];
      change (@nil B2) with (map ρ nil).
    - cbn.
      compose near v on left.
      rewrite fun_map_map.
      compose near v on right.
      rewrite fun_map_map.
      reflexivity.
    - cbn.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite <- ap_map.
      rewrite app_pure_natural.
      rewrite <- IHbody.
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      reflexivity.
    - cbn.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite <- IHt1.
      rewrite <- ap_map.
      rewrite app_pure_natural.
      rewrite <- IHt2.
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      reflexivity.
  Qed.

End naturality.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Distribution and Decoration
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

Definition dist_pair
  {B1 V1: Type} {G}
  `{Map G} `{Mult G} `{Pure G}:
  list (G B1) * G V1 -> G (list B1 * V1) :=
  fun '(x, y) => pure (@pair (list B1) V1) <⋆> dist list G x <⋆> y.

Lemma dist_dec_rec_commute:
  forall (B V: Type)
    `{ApplicativeCommutativeIdempotent G}
    (ctx: list (G B))
    (t: term (G B) (G V)),
    dist_term (map_term dist_pair dist_pair (dec_term_rec ctx t)) =
      pure (dec_term_rec (B := B) (V := V)) <⋆> (dist list G ctx)
        <⋆> (dist_term t).
Proof.
  intros.
  generalize dependent ctx.
  induction t; intro ctx.
  - cbn.
    (* LHS *)
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    (* RHS *)
    rewrite map_to_ap.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    reflexivity.
  - cbn.
    (* LHS *)
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite IHt.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite dist_list_app.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite dist_list_one.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite (ap_ci2 (A := list B) (B := B) _ (dist list G ctx) b).
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite ap_cidup.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite (ap_ci2 (A := list B) (B := B) _ (dist list G ctx) b).
    rewrite app_pure_natural.
    rewrite ap_cidup.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite (ap_ci2 (B := list B) (A := B) _ b (dist list G ctx)).
    rewrite app_pure_natural.
    (* RHS *)
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    (* RHS *)
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite ap3.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite (ap_ci2 (A := list B) _ (dist list G ctx) (dist_term t1)).
    rewrite app_pure_natural.
    rewrite ap_cidup.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite (ap_ci2 _ (dist_term t1) (dist list G ctx)).
    rewrite app_pure_natural.
    rewrite ap3.
    rewrite <- ap4; repeat rewrite ap2.
    reflexivity.
Qed.

Lemma dist_dec_commute:
  forall (B V: Type)
    `{ApplicativeCommutativeIdempotent G}
    (t: term (G B) (G V)),
    dist_term (map_term dist_pair dist_pair (dec_term t)) =
      pure (dec_term (B := B) (V := V)) <⋆> (dist_term t).
Proof.
  intros.
  unfold dec_term.
  rewrite dist_dec_rec_commute; auto.
  rewrite dist_list_nil.
  rewrite ap2.
  reflexivity.
Qed.

Lemma dist_dec_commute2:
  forall (B V: Type)
    `{ApplicativeCommutativeIdempotent G},
    dist_term ∘ map_term dist_pair dist_pair ∘ dec_term =
      map dec_term ∘ dist_term (B := B) (V := V).
Proof.
  intros.
  ext t.
  unfold compose.
  rewrite dist_dec_commute; auto.
  rewrite <- map_to_ap.
  reflexivity.
Qed.

Lemma dist_dec_rec_commute_map:
  forall (B1 V1 B2 V2: Type)
    `{Applicative G}
    (ctx: list (G B1))
    (t: term (G B1) (G V1))
    (ρ: list B1 * B1 -> G B2)
    (σ: list B1 * V1 -> G V2),
    True.
Proof.
  intros.
  Check dec_term_rec ctx t.
  Check dist_term.
  Check dist_term.
  (*
  Check
    (map_term dist_pair dist_pair
       (dec_term_rec ctx
          (map_term ρ σ t)).
    dist_term (map_term dist_pair dist_pair (dec_term_rec ctx t)) =
      pure (dec_term_rec (B := B1) (V := V1)) <⋆> (dist list G ctx)
        <⋆> (dist_term t).
   *)
Proof.
Abort.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Join and Decoration
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

Lemma decorate_ret_term: forall (B V: Type) (V: V),
    dec_term (ret (T := term B) V) =
      ret ([], V).
Proof.
  reflexivity.
Qed.

Definition strength2 {F: Type -> Type -> Type}
  `{Map2 F} {A B C}:
  forall (p : A * F B C), F (A * B) (A * C) :=
    fun '(a, t) => map2 (pair a) (pair a) t.

Definition shift2 {F: Type -> Type -> Type} `{Map2 F} {W} `{Monoid_op W} {A1 A2} :
  W * F (W * A1) (W * A2) -> F (W * A1) (W * A2) :=
  map2 (uncurry incr) (uncurry incr) ∘ strength2.

Lemma decorate_rec_join_term: forall (B V: Type) (ctx: list B),
    dec_term_rec ctx ∘ join_term (V := V) =
      join_term
        ∘ map_term id (shift2 ∘ map_snd dec_term)
        ∘ dec_term_rec ctx.
Proof.
  intros. ext t. unfold compose at 1 2 3.
  generalize dependent ctx.
  induction t as [v | b body IHbody | t1 IHt1 t2 IHt2 ]; intro ctx.
  - (* LHS *)
    rewrite join_term_rw1.
    rewrite dec_rec_spec.
    (* RHS *)
    rewrite dec_term_rec_rw1.
    rewrite map_term_rw1.
    rewrite join_term_rw1.
    cbn.
    compose near (dec_term v) on right.
    unfold map2, Map2_term.
    rewrite (map_map_term).
    reflexivity.
  - cbn.
    fequal.
    rewrite IHbody.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Lemma decorate_join_term: forall (B V: Type),
    dec_term ∘ join_term (B := B) (V := V) =
      join_term ∘ map_term id (shift2 ∘ map_snd dec_term)
        ∘ dec_term.
Proof.
  intros.
  unfold dec_term.
  rewrite decorate_rec_join_term.
  reflexivity.
Qed.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Distribute and Join
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

(* (t: term (G B) (term (G B) (G V))) *)
Lemma dist_join_term {B V: Type}
  `{ApplicativeCommutativeIdempotent G}:
    dist_term ∘ join_term (B := G B) (V := (G V)) =
        map join_term ∘ dist_term ∘ map_term id (dist_term (G := G)).
Proof.
  intros. ext t. unfold compose.
  induction t as [v | b body IHbody | t1 IHt1 t2 IHt2].
  - cbn. compose near (dist_term v) on right.
    rewrite fun_map_map.
    change (tvar (B := B) (V := term B V)) with
      (ret (T := term B) (A := term B V)).
    setoid_rewrite join_ret_term. (* not sure why setoid_ required here *)
    rewrite fun_map_id.
    reflexivity.
  - cbn.
    rewrite IHbody.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    rewrite IHt2.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    reflexivity.
Qed.


(*|
========================================
Definition of binddt
========================================
|*)

Fixpoint binddt_term {B1 V1 B2 V2: Type}
  {G: Type -> Type} `{Map G} `{Pure G} `{Mult G}
  (ρ: list B1 * B1 -> G B2)
  (f: list B1 * V1 -> G (term B2 V2))
  (t: term B1 V1): G (term B2 V2) :=
  match t with
  | tvar v => f ([], v)
  | lam b body => pure (@lam B2 V2)
                   <⋆> ρ (nil, b)
                   <⋆> binddt_term (ρ ⦿ [b]) (f ⦿ [b]) body
  | tap t1 t2 => pure (@tap B2 V2)
                  <⋆> binddt_term ρ f t1
                  <⋆> binddt_term ρ f t2
  end.

#[export] Instance Substitute_lambda_term: Substitute term term :=
  @binddt_term.

(*|
===========================================
Decomposition of the <<binddt>> operation
===========================================
|*)
Lemma binddt_decomposed:
  forall (B1 B2 V1 V2: Type)
    `{ApplicativeCommutativeIdempotent G}
    (ρ: list B1 * B1 -> G B2)
    (σ: list B1 * V1 -> G (term B2 V2)),
    substitute ρ σ =
      map (F := G) join_term ∘ dist_term ∘ map_term ρ σ ∘ dec_term.
Proof.
  intros.
  unfold compose.
  ext t.
  generalize dependent ρ.
  generalize dependent σ.
  induction t; intros σ ρ.
  - cbn.
    compose near (σ ([], v)).
    rewrite fun_map_map.
    change (@tvar B2 (term B2 V2)) with (ret (T := term B2) (A := term B2 V2)).
    setoid_rewrite (join_ret_term (B := B2) (V := V2)).
    rewrite fun_map_id.
    reflexivity.
  - cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    compose near t on right.
    rewrite map_dec_rec.
    rewrite IHt.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    reflexivity.
  - cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite IHt1.
    rewrite IHt2.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    reflexivity.
Qed.



(*|
========================================
Axioms
========================================
|*)
Lemma kdtmp_substitute1_term:
    forall (B1 B2 A1 A2 : Type)
      `{Applicative G}
      (ρ : list B1 * B1 -> G B2)
      (σ : list B1 * A1 -> G (term B2 A2)),
      substitute ρ σ ∘ ret (T := term B1) (A := A1) = σ ∘ ret (T := (list B1 ×)) (A := A1).
Proof.
  intros.
  ext a.
  unfold compose.
  cbn.
  reflexivity.
Qed.

Lemma kdtm_substitute2_term:
    forall (B A : Type),
      substitute (G := fun A => A)
        (extract (W := (list B ×)))
        (ret (T := term B) (A := A) ∘ extract (W := (list B ×)))
      = @id (term B A).
Proof.
  intros.
  ext t.
  induction t.
  - reflexivity.
  - cbn.
    rewrite extract_preincr.
    rewrite extract_preincr2.
    erewrite IHt.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Lemma kdtm_morph_term:
    forall (B1 A1 B2 A2 : Type) (G1 G2 : Type -> Type)
      `{morph : ApplicativeMorphism G1 G2 ϕ}
      (ρ : list B1 * B1 -> G1 B2)
      (σ : list B1 * A1 -> G1 (term B2 A2)),
      ϕ (term B2 A2) ∘ substitute ρ σ =
        substitute (ϕ B2 ∘ ρ) (ϕ (term B2 A2) ∘ σ).
Proof.
  intros.
  ext t.
  generalize dependent σ.
  generalize dependent ρ.
  unfold compose.
  induction t; intros ρ σ.
  - reflexivity.
  - cbn.
    (* LHS *)
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    (* RHS *)
    rewrite IHt.
    reflexivity.
  - cbn.
    (* LHS *)
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    (* RHS *)
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

(*|
========================================
Composition law
========================================
|*)

Lemma composition_lambda_case:
   forall {B1 B2 B3: Type}
     {A1 A2 A3: Type}
    `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    (ρ2 : list B2 * B2 -> G2 B3)
    (σ2 : list B2 * A2 -> G2 (term B3 A3))
    (b: B1) (t : term B1 A1),
     (forall (ρ1 : list B1 * B1 -> G1 B2)
        (σ1 : list B1 * A1 -> G1 (term B2 A2)),
         (map (F := G1) (substitute ρ2 σ2) (substitute ρ1 σ1 t) =
            substitute (G := G1 ∘ G2)
              (ρ2 ⋆6_ci ρ1)
              (kc_subvar ρ2 σ2 ρ1 σ1) t)) ->
     forall (ρ1 : list B1 * B1 -> G1 B2) (σ1 : list B1 * A1 -> G1 (term B2 A2)),
       (map (F := G1) (substitute ρ2 σ2) (substitute ρ1 σ1 ((λ) b t)) =
          substitute (G := G1 ∘ G2)
            (ρ2 ⋆6_ci ρ1)
            (kc_subvar ρ2 σ2 ρ1 σ1) ((λ) b t)).
Proof.
  intros.
  cbn.
  (* LHS *)
  rewrite map_ap.
  rewrite map_ap.
  rewrite app_pure_natural.

  (* RHS *)
  unfold kc6_ci.

  (* unfold composes *)
  unfold_ops @Pure_compose.
  rewrite (ap_compose2 G2 G1).
  rewrite (ap_compose2 G2 G1).
  rewrite app_pure_natural.
  rewrite map_ap.
  rewrite app_pure_natural.

  unfold compose at 4 5.
  rewrite <- ap_map.
  rewrite app_pure_natural.
  cbn.
  rewrite <- ap4.
  rewrite ap2.
  rewrite <- ap4.
  do 3 rewrite ap2.
Abort.

Lemma composition_lambda_case:
   forall {B1 B2 B3: Type}
     {A1 A2 A3: Type}
    `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    (ρ2 : list B2 * B2 -> G2 B3)
    (σ2 : list B2 * A2 -> G2 (term B3 A3))
    (b: B1) (t : term B1 A1),
     (forall (ρ1 : list B1 * B1 -> G1 B2)
        (σ1 : list B1 * A1 -> G1 (term B2 A2)),
         (map (F := G1) (substitute ρ2 σ2) (substitute ρ1 σ1 t) =
            substitute (G := G1 ∘ G2)
              (ρ2 ⋆6_ci ρ1)
              (kc_subvar ρ2 σ2 ρ1 σ1) t)) ->
     forall (ρ1 : list B1 * B1 -> G1 B2) (σ1 : list B1 * A1 -> G1 (term B2 A2)),
       (map (F := G1) (substitute ρ2 σ2) (substitute ρ1 σ1 ((λ) b t)) =
          substitute (G := G1 ∘ G2)
            (ρ2 ⋆6_ci ρ1)
            (kc_subvar ρ2 σ2 ρ1 σ1) ((λ) b t)).
Proof.
  introv AppCIG1 AppCIG2 IHt. intros.
  cbn.
  (* LHS *)
  rewrite map_ap.
  rewrite map_ap.
  rewrite app_pure_natural.
  (* RHS *)
  unfold kc6_ci.
  (* unfold composes *)
  unfold_ops @Pure_compose.
  rewrite (ap_compose2 G2 G1).
  rewrite (ap_compose2 G2 G1).
  rewrite app_pure_natural.
  rewrite map_ap.
  rewrite app_pure_natural.
  (* inner *)
  unfold compose at 4 5.
  rewrite <- ap_map.
  rewrite app_pure_natural.
  rewrite cojoin_Z_rw_nil.
  rewrite traverse_Z_rw.

  (* Let's go! *)
  rewrite <- ap4.
  rewrite ap2.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.

  rewrite traverse_list_nil.
  rewrite ap2.

  (* outer *)
  induction t as [v | b' tbody IHtbody | t1 IHt1 t2 IHt2  ].
  { cbn.
    (* LHS *)
    unfold preincr at 1.
    unfold compose at 3.
    unfold incr at 1.
    change (@nil B1) with (Ƶ: list B1) at 3.
    rewrite monoid_id_l.
    (* RHS *)
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.

    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.

    rewrite ap3.
    rewrite ap3.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap_cidup.
    rewrite app_pure_natural.

    (* Let's go? *)
    reflexivity.
  }
  {
    admit.
  }
  { cbn.
    (* LHS *)
    (* innter *)
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    admit.
  }
Abort.

Lemma composition:
  forall (B1 B2 B3: Type)
    (A1 A2 A3: Type)
    `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    (ρ1 : list B1 * B1 -> G1 B2)
    (ρ2 : list B2 * B2 -> G2 B3)
    (σ1 : list B1 * A1 -> G1 (term B2 A2))
    (σ2 : list B2 * A2 -> G2 (term B3 A3)),
    map (F := G1) (substitute (G := G2) ρ2 σ2) ∘ substitute (G := G1)
      (T := term) (U := term) ρ1 σ1 =
      substitute (T := term) (U := term) (G := G1 ∘ G2)
        (ρ2 ⋆6_ci ρ1) (kc_subvar ρ2 σ2 ρ1 σ1).
Proof.
  intros. ext t.
  unfold compose at 1.
  generalize dependent σ1.
  generalize dependent ρ1.
  induction t; intros ρ1 σ1.
  - cbn.
    (* LHS *)
    rewrite map_to_ap.
    (* RHS *)
    rewrite ap2.
    rewrite map_ap.
    rewrite app_pure_natural.
    unfold compose.
    change (@nil B2: list B2) with (Ƶ: list B2).
    rewrite preincr_zero.
    rewrite preincr_zero.
    reflexivity.
  - admit.
  - cbn.
    (* LHS *)
    rewrite map_to_ap.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    (* RHS *)
    rewrite <- IHt1.
    rewrite <- IHt2.
    unfold_ops @Pure_compose.
    rewrite (ap_compose2 G2 G1) at 1.
    rewrite (ap_compose2 G2 G1) at 1.
    rewrite map_ap.
    rewrite (app_pure_natural (G := G1)).
    rewrite (app_pure_natural (G := G1)).
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- ap_map.
    fequal.
    fequal.
    rewrite app_pure_natural.
    reflexivity.
Abort.

Lemma composition:
  forall (B1 B2 B3: Type)
    (A1 A2 A3: Type)
    `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    (ρ1 : list B1 * B1 -> G1 B2)
    (ρ2 : list B2 * B2 -> G2 B3)
    (σ1 : list B1 * A1 -> G1 (term B2 A2))
    (σ2 : list B2 * A2 -> G2 (term B3 A3)),
    map (F := G1) (substitute (G := G2) ρ2 σ2) ∘ substitute (G := G1)
      (T := term) (U := term) ρ1 σ1 =
      substitute (T := term) (U := term) (G := G1 ∘ G2)
        (ρ2 ⋆6_ci ρ1) (kc_subvar ρ2 σ2 ρ1 σ1).
Proof.
  intros.
  (* LHS *)
  rewrite binddt_decomposed; try typeclasses eauto.
  rewrite binddt_decomposed; try typeclasses eauto.
  (* Move first applied join to the end of the composition *)
  repeat reassociate <-.
  rewrite fun_map_map.
  reassociate -> near (join_term).
  rewrite decorate_join_term.
  do 2 reassociate <- on left.
  reassociate -> near join_term.
  rewrite <- join_map.
  reassociate <- on left.
  reassociate -> near join_term.
  rewrite dist_join_term.
  do 2 reassociate <- on left.
  rewrite (fun_map_map).
  rewrite join_join_term.
  (* Move first applied distribution the end of the composition *)
  rewrite <- fun_map_map.
  reassociate -> near dist_term.
  Search map_term dist_term.
  Search dist_term dec_term.
  rewrite <- dist_dec_commute2; auto.
  do 2 reassociate <- on left.
  rewrite <- fun_map_map.
  reassociate -> near dist_term.
  rewrite dist_map; auto.
  reassociate <- on left.
  rewrite <- fun_map_map.
  reassociate -> near dist_term.
  rewrite dist_map; auto.
  reassociate <- on left.
  rewrite <- fun_map_map.
  reassociate -> near dist_term.
  rewrite dist_map; auto.
  rewrite <- fun_map_map.
  reassociate <- on left.
  reassociate -> near dist_term.
  rewrite <- dist_term_linear.
  2:{ now inversion H. }
  2:{ now inversion H0. }

  (* Bring dist past the first join *)
  rewrite <- fun_map_map.
  rewrite <- fun_map_map.
  change (map (F := G1) (map (F := G2) ?f)) with (map (F := G1 ∘ G2) f).
  reassociate -> near dist_term.
  rewrite dist_map.
  2:{ admit. }
  reassociate <- on left.
  reassociate -> near (map_term (map ρ2) (map (map_term ρ2 σ2))).
  rewrite fun_map_id.
  rewrite map_map_term.
  change (id ∘ ?x) with x.
  rewrite fun_map_map.
  reassociate -> near (map_term (map id) (map (shift2 ∘ map_snd dec_term))).
  rewrite map_map_term.
  rewrite (fun_map_map).
  rewrite (fun_map_map).
  reassociate -> near (map_term dist_pair dist_pair).
  rewrite map_map_term.
  change (id ∘ ?x) with x.
  change (?x ∘ id) with x.
  rewrite fun_map_map.
  change (map join_term ∘ dist_term ∘ ?x ∘ ?y) with (map join_term ∘ dist_term ∘ (x ∘ y)).
  rewrite (map_map_term).
  change (id ∘ ?x) with x.
  reassociate -> near (map_term ρ1 σ1).
  rewrite dec_map.
  reassociate <- on left.
  change (?rest ∘ map_term ?x ?y ∘ map_term ?z ?w)
    with (rest ∘ (map_term x y ∘ map_term z w)).
  rewrite (map_map_term).
  reassociate -> near dec_term.
  rewrite dec_dec_term.
  reassociate <- on left.
  change (?rest ∘ map_term ?x ?y ∘ map_term ?z ?w)
    with (rest ∘ (map_term x y ∘ map_term z w)).
  rewrite map_map_term.
  reassociate <- on left.
  unfold map at 4.
  unfold Map_compose at 3.
  Set Keyed Unification.
  rewrite (fun_map_map (F := G1)).
  Unset Keyed Unification.
  (* RHS *)
  rewrite binddt_decomposed; try typeclasses eauto.
  2: admit.
  (*
  Set Printing Implicit.
  rewrite (dist_term_linear (G1 := G1) (G2 := G2)) at 2.
  Unset Keyed Unification.
  Set Keyed Unification.
  rewrite (fun_map_map (F := G1)).
  Unset Keyed Unification.
   *)

  unfold kc_subvar, kc6_ci.
  fequal.
  fequal.
  fequal.
  - ext [ctx b].
    unfold compose.
    cbn.
    unfold id.
    admit.
  - ext [ctx l].
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    unfold compose.
    cbn.
    unfold id.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    fequal.
    fequal.
    2: admit.
    fequal.
    ext ctx2 t.
    unfold compose.
    rewrite binddt_decomposed; auto.
    admit.
Abort.
