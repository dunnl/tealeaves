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
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.Categorical.List
  Backends.LN.Atom
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
Inductive term (b v: Type) :=
| tvar: v -> term b v
| lam: b -> term b v -> term b v
| app: term b v -> term b v -> term b v.

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
Program Fixpoint binddt_term {b1 v1 b2 v2: Type}
  {G: Type -> Type} `{Map G} `{Pure G} `{Mult G}
  (ρ: list b1 * b1 -> G b2)
  (f: list b1 * v1 -> G (term b2 v2))
  (t: term b1 v1): G (term b2 v2) :=
  match t with
  | tvar _ v => f (nil, v)
  | lam v body => pure (@lam b2 v2)  <⋆> ρ (nil, v) <⋆> binddt_term (ρ ⦿ [v]) (f ⦿ [v]) body
  | app t1 t2 => pure (@app b2 v2)
                  <⋆> binddt_term ρ f t1
                  <⋆> binddt_term ρ f t2
  end.

#[export] Instance Return_lambda_term: forall B, Return (term B) :=
  @tvar.

#[export] Instance Substitute_lambda_term: Substitute term term :=
  @binddt_term.

Parameters (x y z: atom).

Example term1: term atom atom := lam x (app (lam y (tvar _ z)) (tvar _ x)).

(*|
============================================
Decomposition into categorical components
============================================
|*)
Fixpoint dec_term_rec {b1 v1: Type} (ctx: list b1)
  (t: term b1 v1): term (list b1 * b1) (list b1 * v1) :=
  match t with
  | tvar _ v => tvar _ (ctx, v)
  | lam v body => lam (ctx, v) (dec_term_rec (ctx ++ [v]) body)
  | app t1 t2 => app (dec_term_rec ctx t1) (dec_term_rec ctx t2)
  end.

Definition dec_term {b1 v1: Type}:
  term b1 v1 ->
  term (list b1 * b1) (list b1 * v1) :=
  dec_term_rec nil.

Compute dec_term term1.

Fixpoint dist_term {b1 v1: Type}
  {G: Type -> Type} `{Map G} `{Pure G} `{Mult G}
  (t: term (G b1) (G v1)): G (term b1 v1) :=
  match t with
  | tvar _ v => map (@tvar b1 v1) v
  | lam v body => pure (@lam b1 v1)
                   <⋆> v
                   <⋆> dist_term body
  | app t1 t2 => pure (@app b1 v1)
                  <⋆> dist_term t1
                  <⋆> dist_term t2
  end.

Fixpoint join_term {b1 v1: Type} (t: term b1 (term b1 v1)): term b1 v1 :=
  match t with
  | tvar _ tv => tv
  | lam v body => lam v (join_term body)
  | app t1 t2 => app (join_term t1) (join_term t2)
  end.

Fixpoint map_term {b1 v1 b2 v2: Type} (ρ: b1 -> b2) (σ: v1 -> v2)
  (t: term b1 v1): term b2 v2 :=
  match t with
  | tvar _ v => (@tvar b2 v2) (σ v)
  | lam v body => lam (ρ v) (map_term ρ σ body)
  | app t1 t2 => app (map_term ρ σ t1) (map_term ρ σ t2)
  end.

Lemma binddt_decomposed:
  forall (b1 b2 v1 v2: Type)
    `{ApplicativeCommutativeIdempotent G}
    (ρ: list b1 * b1 -> G b2)
    (σ: list b1 * v1 -> G (term b2 v2)),
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
    rewrite (fun_map_map).
    admit.
  - cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    assert (Hequiv:
             map_term ρ σ (dec_term_rec [b] t)
            = map_term (ρ ⦿ [b]) (σ ⦿ [b]) (dec_term t)).
    admit.
    rewrite Hequiv.
    clear Hequiv.
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
Admitted.


Definition dist_pair
  {b1 v1: Type}
  `{ApplicativeCommutativeIdempotent G}:
  list (G b1) * G v1 -> G (list b1 * v1) :=
  fun '(x, y) => pure (@pair (list b1) v1) <⋆> dist list G x <⋆> y.

Lemma dist_dec_commute:
  forall (b1 b2 v1 v2: Type)
    `{ApplicativeCommutativeIdempotent G},
    map (F := G) dec_term ∘ dist_term (b1 := b1) (v1 := v1) =
      dist_term ∘ map_term dist_pair dist_pair ∘ dec_term.
Proof.
  intros. ext t. unfold compose.
  induction t.
  - cbn.
    compose near v on left.
    rewrite fun_map_map.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite ap2.
    rewrite <- map_to_ap.
    reflexivity.
  - cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    admit.
  - cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- IHt1.
    rewrite <- IHt2.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    reflexivity.
Admitted.


Fixpoint bindt_term {b1 v1 b2 v2: Type}
  {G: Type -> Type} `{Map G} `{Pure G} `{Mult G}
  (ρ: b1 -> G b2)
  (σ: v1 -> G (term b2 v2))
  (t: term b1 v1): G (term b2 v2) :=
  match t with
  | tvar _ v => σ v
  | lam v body => pure (@lam b2 v2)
                   <⋆> ρ v
                   <⋆> bindt_term ρ σ body
  | app t1 t2 => pure (@app b2 v2)
                  <⋆> bindt_term ρ σ t1
                  <⋆> bindt_term ρ σ t2
  end.

(*|
========================================
Decoration commutes with bindt
========================================
|*)
Section commute.

  Context (b1 b2 v1 v2: Type).
  Context `{ApplicativeCommutativeIdempotent G}.

  Section decompose.

    Context (ρ: list b1 * b1 -> G b2).
    Context (σ: list b1 * v1 -> G (term b2 v2)).

    Lemma binddt_decompose_rec: forall (ctx: list b1),
        binddt_term (ρ ⦿ ctx) (σ ⦿ ctx) =
          bindt_term ρ σ ∘ dec_term_rec ctx.
    Proof.
      intros. ext t.
      unfold compose.
      generalize dependent ctx.
      induction t; intro ctx.
      - unfold preincr, compose. cbn.
        change (@nil b1) with (Ƶ: list b1).
        rewrite monoid_id_l.
        reflexivity.
      - unfold preincr. cbn. unfold compose. cbn.
        change (@nil b1) with (Ƶ: list b1).
        rewrite monoid_id_l. cbn.
        unfold preincr.
        change (?x ○ incr ctx) with (x ∘ incr ctx).
        reassociate -> on left.
        rewrite incr_incr.
        reassociate -> on left.
        rewrite incr_incr.
        change (?x ∘ incr ?w) with (x ⦿ w).
        rewrite IHt.
        reflexivity.
      - cbn.
        rewrite IHt1.
        rewrite IHt2.
        reflexivity.
    Qed.

    Lemma binddt_decompose:
        binddt_term ρ σ =
          bindt_term ρ σ ∘ dec_term.
    Proof.
      ext t.
      unfold dec_term.
      rewrite <- binddt_decompose_rec.
      change (@nil b1) with (Ƶ: list b1).
      rewrite preincr_zero.
      rewrite preincr_zero.
      reflexivity.
    Qed.

  End decompose.


  Section decompose.

    Context (ρ: b1 -> G b2).
    Context (σ': list b1 * v1 -> G (term b2 v2)).
    Context (σ: v1 -> G (term b2 v2)).

    Section Traverse_Reader.

      Context {E: Type}.

      #[export] Instance Traverse_Reader: Traverse (prod E).
      Proof.
        intros J Hmap Hpure Hmult A B f.
        exact (strength ∘ map (F := prod E) f).
      Defined.

    End Traverse_Reader.

  Lemma bindt_dec_commute: forall (t: term b1 v1), False.
  Proof.
    intros.
    clear σ'.
    Check bindt_term ρ σ.
    Check map (F := G) dec_term.
    Check map (F := G) dec_term ∘ bindt_term ρ σ.
    Check σ.
    Check traverse (T := (list b2 ×)) σ.
    Check dec_term t.
    Check bindt_term (v2 := list b2 * v2) (traverse (T := Z) ρ) _ ∘ dec_term (b1 := b1) (v1 := v1).
    assert (list b1 * v1 -> G (term (list b2 * b2) (list b2 * v2))).
    { Check fun '(w, v) => traverse (T := list) ρ w.
      Check fun '(w, v) => traverse (T := Z) ρ w.
      Check fun '(w, v) => map (F := G) (dec_term) (σ v).
      Check fun '(w, v) => pure pair
                          <⋆> traverse (T := Z) ρ w
                          <⋆> map (F := G) (dec_term) (σ v).
      admit.

    }
  Admitted.

  End decompose.

End commute.

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
  unfold substitute.
  unfold Substitute_lambda_term.
  rewrite binddt_decompose.
  rewrite binddt_decompose.
  rewrite binddt_decompose.

  (* RHS *)
  unfold kc6_ci.
  unfold kc_subvar.
Abort.

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
  induction t as [a1 | b1 tbody IHtbody | t1 IHt1 t2 IHt2  ].
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
  - apply (composition_lambda_case ρ2 σ2 b t); auto.
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

