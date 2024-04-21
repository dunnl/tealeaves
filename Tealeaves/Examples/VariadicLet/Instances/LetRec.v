(*|
############################################################
Formalizing variadic syntax with Tealeaves
############################################################

^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
let with letrec semantics
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|*)
From Tealeaves Require Export
  Examples.VariadicLet.Terms
  Functors.List_Telescoping
  Adapters.Compositions.DecoratedTraversableModule.

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.
#[local] Open Scope nat_scope.

#[local] Notation "'P'" := pure.
#[local]  Notation "'BD'" := binddt.

Fixpoint binddt_term
  (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
  {v1 v2 : Type}
  (f : nat * v1 -> G (term v2))
  (t : term v1) : G (term v2) :=
  match t with
  | tvar v => f (0, v)
  | letin defs body =>
      pure (@letin v2) <⋆>
        ((fix F ls :=
            match ls with
            | nil => pure nil
            | cons d drest =>
                pure cons <⋆> binddt_term (f ⦿ length defs) d <⋆> F drest
            end) defs) <⋆> binddt_term (f ⦿ length defs) body
  | app t1 t2 =>
      pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance Binddt_term: Binddt nat term term := @binddt_term.

Definition subst_in_defs
  `{Applicative G} {v1 v2 : Type}
  (f : nat * v1 -> G (term v2)):
  list (term v1) -> G (list (term v2)) :=
  binddt (Binddt := Mapdt_Binddt_compose (Mapdt_F := Mapdt_List_Full))
    (U := list ∘ term) f.

Section rewriting.

  Section pointful.

    Context
      `{Applicative G} (v1 v2 : Type)
        (f : nat * v1 -> G (term v2)).

    Lemma binddt_term_rw1: forall (v: v1),
        binddt f (tvar v) = f (Ƶ, v).
    Proof.
      reflexivity.
    Qed.

    Lemma binddt_term_rw2: forall (l : list (term v1)) (body: term v1),
        binddt f (letin l body) =
          pure (@letin v2) <⋆> subst_in_defs f l <⋆>
            binddt (f ⦿ length l) body.
    Proof.
      intros. cbn.
      do 2 fequal.
      unfold subst_in_defs.
      unfold_ops @Mapdt_Binddt_compose.
      unfold_ops @Mapdt_List_Full;
        unfold mapdt_list_full.
      match goal with
      | |- context[(fun '(w1, t) => ?binddt (f ⦿ w1) t)] =>
          replace (fun '(w1, t) => binddt (f ⦿ w1) t) with
          ((fun '(w1, t) => binddt (f ⦿ w1) t) ⦿ 0)
          by now ext [w t]
      end.
      match goal with
      | |- context[BD (f ⦿ length l)] =>
          replace (BD (f ⦿ length l)) with
          (BD (f ⦿ (length l + 0)%nat))
      end.
      2: { fequal. fequal. lia. }
      generalize dependent f; clear f.
      generalize 0.
      induction l; intros n f.
      - reflexivity.
      - cbn.
        fequal.
        + repeat fequal.
          unfold_all_transparent_tcs.
          lia.
        + specialize (IHl (S n) f).
          replace (length l + S n)
            with (S (length l + n)) in IHl by lia.
          rewrite IHl.
          fequal.
          ext t.
          cbn. fequal. fequal.
          unfold_all_transparent_tcs.
          lia.
    Qed.

    Lemma binddt_term_rw3: forall (t1 t2: term v1),
          binddt f (app t1 t2) =
            pure (@app v2) <⋆> binddt f t1 <⋆> binddt f t2.
      Proof.
        reflexivity.
      Qed.

    End pointful.

    Section pointfree.

      Context
        `{Applicative G2}
          {B C: Type}
          (g : nat * B -> G2 (term C)).

      Lemma binddt_pointfree_letin_defs: forall l,
          binddt g ∘ letin (v:=B) l =
            (precompose (binddt (g ⦿ length l)) ∘ ap G2)
              (pure (letin (v:=C)) <⋆> (subst_in_defs g l)).
      Proof.
        intros l.
        ext body.
        unfold precompose, compose.
        rewrite binddt_term_rw2.
        reflexivity.
      Qed.

      Lemma binddt_pointfree_letin: forall `(l:list A),
          compose (binddt g) ∘ letin (v:=B) ∘ mapdt_make l (B := term B) =
            ((compose (precompose (binddt (g ⦿ length l)) ∘ ap G2) ∘
                precompose (subst_in_defs g) ∘
                ap G2 ∘ pure (F := G2)) (letin (v:=C))) ∘ mapdt_make l (B := term B).
      Proof.
        intros A l.
        ext l' body.
        unfold precompose, compose.
        rewrite binddt_term_rw2.
        do 2 rewrite <- list_plength_length.
        unfold mapdt_make.
        rewrite <- plength_trav_make.
        reflexivity.
      Qed.

    End pointfree.

  End rewriting.

Ltac simplify_binddt_term :=
  match goal with
  | |- context[BD ?f (tvar ?y)] =>
      ltac_trace "step_BD_tvar";
      rewrite binddt_term_rw1
  | |- context[((BD ?f) (letin ?l ?body))] =>
      ltac_trace "step_BD_letin";
      rewrite binddt_term_rw2
  | |- context[((BD ?f) (app ?t1 ?t2))] =>
      ltac_trace "step_BD_app";
      rewrite binddt_term_rw3
  end.

Ltac cbn_binddt ::=
  simplify_binddt_term.

Theorem dtm1_term:
  forall `{Applicative G} (A B : Type),
  forall f : nat * A -> G (term B),
    binddt f ∘ ret  = f ∘ ret (T := (nat ×)).
Proof.
  derive_dtm1.
Qed.

Theorem dtm2_term : forall A : Type,
    binddt (T := term) (U := term)
      (G := fun A => A) (ret (T := term) ∘ extract (W := (nat ×))) = @id (term A).
Proof.
  intros.
  derive_dtm2.
  unfold subst_in_defs.
  unfold_ops @Mapdt_Binddt_compose.
  apply mapdt_respectful_id; intros.
  do 2 push_preincr_into_fn.
  apply ind_implies_in in H.
  auto.
Qed.

Set Keyed Unification.

Theorem dtm3_term:
  forall `{Applicative G1} `{Applicative G2},
    forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
      map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
Proof.
  intros.
  derive_dtm3.

  assert (IHdefs':
           map (F := G1) (subst_in_defs g) (subst_in_defs f defs) =
             subst_in_defs (G := G1 ∘ G2) (g ⋆7 f) defs).
  {
    unfold subst_in_defs.
    unfold_ops @Mapdt_Binddt_compose.
    compose near defs on left.
    rewrite kdtfun_mapdt2.
    apply (mapdt_respectful (G := G1 ∘ G2) (T := list) _ _ defs).
    intros e t' Hin.
    rewrite kc6_spec.
    setoid_rewrite <- (kc7_preincr g f e).
    apply ind_implies_in in Hin.
    rewrite <- (IHdefs t' Hin (g ⦿ e) (f ⦿ e)).
    reflexivity.
  }

  unfold subst_in_defs at 1.
  unfold_ops @Mapdt_Binddt_compose.
  rewrite mapdt_repr at 1.
  dtm3_push_map_right_to_left.
  repeat change (precompose ?f ?g) with (g ∘ f).
  rewrite binddt_pointfree_letin.
  change (?g ∘ ?trav_make defs) with (precompose (trav_make defs) g).
  rewrite <- app_pure_natural.
  rewrite ap_map.
  rewrite <- mapdt_repr.
  change (mapdt (A := term A) (B := term B)
            _ defs) with (subst_in_defs f defs).
  rewrite <- IHdefs'.
  dtm3_rhs_one_constructor.
  dtm3_rhs_one_constructor.
  reflexivity.
Qed.


Theorem dtm4_term :
  forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Mult G1)
    (H3 : Pure G1) (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
    (ϕ : forall A : Type, G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ ->
    forall (A B : Type) (f : nat * A -> G1 (term B)),
      ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
Proof.
  derive_dtm4.
  compose near defs on left.
  unfold subst_in_defs.
  unfold_ops @Mapdt_Binddt_compose.
  change ((?g ∘ ?f) ⦿ ?w) with (g ∘ (f ⦿ w)).
  rewrite <- kdtfun_morph.
  apply mapdt_respectful;[typeclasses eauto|].
  introv Hin.
  unfold compose.
  apply ind_implies_in in Hin.
  apply IHdefs.
  assumption.
Qed.

#[export] Instance DTM_LetIn: DecoratedTraversableMonad nat term.
Proof.
  constructor.
  - typeclasses eauto.
  - intros. apply dtm1_term.
  - constructor.
    + apply dtm2_term.
    + intros. apply dtm3_term.
    + apply dtm4_term.
Qed.
