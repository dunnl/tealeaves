From Tealeaves Require Export
  Examples.LambdaNominal.Syntax
  Examples.LambdaNominal.Categorical
  Examples.LambdaNominal.Raw
  Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly
  Classes.Categorical.DecoratedTraversableMonadPoly
  Functors.Subset
  Backends.Common.AtomSet
  Backends.Named.Named.

Import DecoratedTraversableMonadPoly.DerivedOperations.
Import Kleisli.DecoratedTraversableMonadPoly.DerivedOperations.
Import Kleisli.DecoratedTraversableMonadPoly.

#[local] Generalizable Variables G ϕ.

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

Section rw.

  Context
    {B1 V1 B2 V2: Type}
  {G: Type -> Type} `{Map G} `{Pure G} `{Mult G}
  (ρ: list B1 * B1 -> G B2)
  (f: list B1 * V1 -> G (term B2 V2)).

  Lemma sub_term_rw1: forall v,
      substitute ρ f (tvar v) = f ([], v).
  Proof.
    reflexivity.
  Qed.

  Lemma sub_term_rw2: forall b t,
      substitute ρ f (lam b t) =
        pure (lam (V:=V2)) <⋆> ρ ([], b) <⋆> substitute (ρ ⦿ [b]) (f ⦿ [b]) t.
  Proof.
    reflexivity.
  Qed.

  Lemma sub_term_rw3: forall t1 t2,
      substitute ρ f (tap t1 t2) =
        pure (@tap B2 V2) <⋆> (substitute ρ f t1)
          <⋆> (substitute ρ f t2).

  Proof.
    reflexivity.
  Qed.
End rw.

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
      map (F := G) join_term ∘ dist_term ∘ map2_term ρ σ ∘ dec_term.
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
(*
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
              (ρ2 ⋆3_ci ρ1)
              (kc_subvar ρ2 σ2 ρ1 σ1) t)) ->
     forall (ρ1 : list B1 * B1 -> G1 B2) (σ1 : list B1 * A1 -> G1 (term B2 A2)),
       (map (F := G1) (substitute ρ2 σ2) (substitute ρ1 σ1 ((λ) b t)) =
          substitute (G := G1 ∘ G2)
            (ρ2 ⋆3_ci ρ1)
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
*)

