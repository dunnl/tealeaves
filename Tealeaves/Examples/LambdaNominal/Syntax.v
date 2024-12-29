(*|
############################################################
Formalizing STLC with Named Variables
############################################################

============================
Imports and setup
============================
|*)
From Tealeaves Require Export
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.List.

Import Product.Notations.
Import Monoid.Notations.
Import List.ListNotations.
Import DecoratedTraversableCommIdemFunctor.Notations.

#[local] Generalizable Variables G ϕ.
#[local] Set Implicit Arguments.

Import Applicative.Notations.

(** * Language definition *)
(******************************************************************************)
Inductive term (b v : Type) :=
| tvar : v -> term b v
| lam : b -> term b v -> term b v
| app : term b v -> term b v -> term b v.

(** ** Notations and automation *)
(******************************************************************************)
Module Notations.
  Notation "'λ'" := (lam) (at level 45).
End Notations.

Import Notations.

(*|
========================================
Definition of binddt
========================================
|*)
Program Fixpoint binddt_term {b1 v1 b2 v2 : Type}
  (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
  (ρ : list b1 * b1 -> G b2)
  (f : list b1 * v1 -> G (term b2 v2))
  (t : term b1 v1) : G (term b2 v2) :=
  match t with
  | tvar _ v => f (nil, v)
  | lam v body => pure (@lam b2 v2)  <⋆> ρ (nil, v) <⋆> binddt_term (ρ ⦿ [v]) (preincr f [v]) body
  | app t1 t2 => pure (@app b2 v2)
                  <⋆> binddt_term ρ f t1
                  <⋆> binddt_term ρ f t2
  end.

#[export] Instance Return_lambda_term: forall B, Return (term B) :=
  @tvar.

#[export] Instance Substitute_lambda_term: Substitute term term :=
  @binddt_term.

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

(*|
========================================
Composition law
========================================
|*)
Lemma composition_lambda_case:
   forall (B1 B2 B3: Type)
    (A1 A2 A3: Type)
    `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    (ρ1 : list B1 * B1 -> G1 B2)
    (ρ2 : list B2 * B2 -> G2 B3)
    (σ1 : list B1 * A1 -> G1 (term B2 A2))
    (σ2 : list B2 * A2 -> G2 (term B3 A3)),
     forall (b: B1) (t: term B1 A1),
       (map (F := G1) (substitute ρ2 σ2) (substitute ρ1 σ1 t) =
          substitute (G := G1 ∘ G2)
            (ρ2 ⋆6_ci ρ1)
            (kc_subvar ρ2 σ2 ρ1 σ1) t) ->
       (map (F := G1) (substitute ρ2 σ2) (substitute ρ1 σ1 ((λ) b t)) =
          substitute (G := G1 ∘ G2)
            (ρ2 ⋆6_ci ρ1)
            (kc_subvar ρ2 σ2 ρ1 σ1) ((λ) b t)).
Proof.
  intros.
  rename H7 into IHt.
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
  destruct t.
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
Admitted.

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
  induction t.
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
  - auto using composition_lambda_case.
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

