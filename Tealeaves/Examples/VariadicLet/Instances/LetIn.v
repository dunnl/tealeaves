

(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
let with no pairwise binding
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To illustrate the use of the traversal representation theorem, we
consider an example where the syntax has no mutual binding structure.

|*)
Module ex_binding_type2.

  Fixpoint binddt_term
    (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type}
    (f : nat * v1 -> G (term v2))
    (t : term v1) : G (term v2) :=
    match t with
    | tvar v => f (0, v)
    | letin defs body =>
        pure (@letin v2) <⋆>
          ((fix F acc ls :=
              match ls with
              | nil => pure nil
              | cons d0 drest =>
                  pure cons <⋆> binddt_term (f ⦿ acc) d0 <⋆> F (S acc) drest
              end) 0 defs) <⋆> binddt_term (f ⦿ length defs) body
    | app t1 t2 =>
        pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
    end.

  #[export] Instance Binddt_Lam: Binddt nat term term := @binddt_term.

  Definition subst_in_defs
    `{Applicative G} {v1 v2 : Type}
    (f : nat * v1 -> G (term v2)):
    list (term v1) -> G (list (term v2)) :=
    binddt (Binddt := Mapdt_Binddt_compose (Mapdt_F := Mapdt_List_Telescope))
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
        unfold_ops @Mapdt_List_Telescope.
        match goal with
        | |- context[(fun '(w1, t) => ?binddt (f ⦿ w1) t)] =>
            replace (fun '(w1, t) => binddt (f ⦿ w1) t) with
            ((fun '(w1, t) => binddt (f ⦿ w1) t) ⦿ 0)
            by now ext [w t]
        end.
        generalize dependent f; clear f.
        generalize 0.
        induction l; intros n f.
        - cbn.
          reflexivity.
        - cbn.
          rewrite preincr_preincr.
          specialize (IHl (n ● 1) f).
          rewrite <- IHl.
          replace (n ● 0) with (n) by
            (unfold_ops @Monoid_op_plus; lia).
          replace (n ● 1) with (S n) by
            (unfold_ops @Monoid_op_plus; lia).
          reflexivity.
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
          compose (binddt g) ∘ letin (v:=B) ∘
            mapdt_make (H := Mapdt_List_Telescope) l (B := term B) =
            ((compose (precompose (binddt (g ⦿ length l)) ∘ ap G2) ∘
                precompose (subst_in_defs g) ∘
                ap G2 ∘ pure (F := G2)) (letin (v:=C))) ∘
              mapdt_make (H := Mapdt_List_Telescope) l (B := term B).
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

  #[local] Notation "'P'" := pure.
  #[local] Notation "'BD'" := binddt.

  Ltac simplify_binddt_term :=
    match goal with
    | |- context[BD ?f (tvar ?y)] =>
        debug "step_BD_tvar";
        rewrite binddt_term_rw1
    | |- context[((BD ?f) (letin ?l ?body))] =>
        debug "step_BD_letin";
        rewrite binddt_term_rw2
    | |- context[((BD ?f) (app ?t1 ?t2))] =>
        debug "step_BD_app";
        rewrite binddt_term_rw3
    end.

  Ltac cbn_binddt ::=
    simplify_binddt_term.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Instantiate simplification infrastructure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)
  Theorem dtm1_lam:
    forall `{Applicative G} (A B : Type),
    forall f : nat * A -> G (term B),
      binddt f ∘ ret  = f ∘ ret (T := (nat ×)).
  Proof.
    reflexivity.
  Qed.

  Theorem dtm2_term : forall A : Type,
      binddt (T := term) (U := term)
        (G := fun A => A) (ret (T := term) ∘ extract (W := (nat ×))) = @id (term A).
  Proof.
    intros. derive_dtm2.
    unfold subst_in_defs.
    unfold_ops @Mapdt_Binddt_compose.
    apply mapdt_respectful_id; intros.
    do 2 push_preincr_into_fn.
    apply ind_implies_in in H.
    auto.
  Qed.

  Theorem dtm3_term:
    forall `{Applicative G1} `{Applicative G2},
    forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
      map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros.
    derive_dtm3.
    generalize dependent g.
    generalize dependent f.
    assert (Functor G1) by (now inversion H2).
    assert (Functor G2) by (now inversion H6).
    unfold compose at 1.
    induction t using term_mut_ind2; intros f g.
    - cbn.
      change (g ⦿ 0) with (g ⦿ Ƶ).
      now rewrite preincr_zero.
    - do 2 simplify_binddt_term.
      (* left *)
      repeat dtm3_lhs_step.
      unfold subst_in_defs at 1;
        unfold binddt at 2, Mapdt_Binddt_compose at 1.
      { rewrite mapdt_repr.
        rewrite map_to_ap.
        repeat rewrite <- ap4;
          repeat rewrite ap2.
        rewrite binddt_pointfree_letin.
        rewrite <- map_to_ap.
        rewrite <- (fun_map_map).
        unfold compose at 1.
        rewrite map_to_ap.
        rewrite <- mapdt_repr.
        change (mapdt (A := term A) (B := term B)
                  _ defs) with (subst_in_defs f defs).
        (* rhs *)
        unfold_ops @Pure_compose.
        (* rhs defs *)
        assert (lemma_for_defs:
                 subst_in_defs (G := G1 ∘ G2) (g ⋆7 f) defs =
                   map (F := G1) (subst_in_defs (G := G2) g)
                     (subst_in_defs (G := G1) f defs)).
        { unfold subst_in_defs.
          unfold_ops @Mapdt_Binddt_compose.
          compose near defs on right.
          rewrite kdtfun_mapdt2.
          apply mapdt_respectful.
          - typeclasses eauto.
          - intros w u Hin.
            rewrite <- (kc7_preincr (G1 := G1) g f w).
            apply ind_implies_in in Hin.
            rewrite <- IHdefs; auto.
            rewrite kc6_spec.
            reflexivity.
        }
        Set Keyed Unification.
        rewrite lemma_for_defs.
        Unset Keyed Unification.
        dtm3_rhs_applicative_compose.
        dtm3_rhs_applicative_map.
        (* last part *)
        rewrite <- (kc7_preincr (G1 := G1) g f (length defs)).
        rewrite <- IHt.
        dtm3_rhs_applicative_compose.
        dtm3_rhs_applicative_map.
        reflexivity.
      }
    - do 2 simplify_binddt_term.
      repeat dtm3_rhs_step.
      dtm3_rhs_step.
      rewrite <- IHt1.
      dtm3_rhs_step.
      rewrite <- IHt2.
      dtm3_rhs_step.
      reflexivity.
  Qed.

  Theorem dtm4_stlc :
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Mult G1)
      (H3 : Pure G1) (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : nat * A -> G1 (term B)),
        ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
  Proof.
    introv Happl. intros. ext t.
    assert (Applicative G1) by (now inversion Happl).
    assert (Applicative G2) by (now inversion Happl).
    generalize dependent f.
    unfold compose at 1.
    induction t using term_mut_ind2; intro f. (* .unfold *)
    - reflexivity.
    - do 2 simplify_binddt_term.
      repeat rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHt.
      change (ϕ (list (term B)) (subst_in_defs f defs))
        with ((ϕ (list (term B)) ∘ subst_in_defs f) defs).
      unfold subst_in_defs.
      unfold_ops @Mapdt_Binddt_compose.
      change ((?g ∘ ?f) ⦿ ?w) with (g ∘ (f ⦿ w)).
      rewrite <- kdtfun_morph.
      do 2 fequal.
      apply mapdt_respectful;[typeclasses eauto|].
      intros. cbn.
      unfold compose.
      apply ind_implies_in in H7.
      apply IHdefs.
      assumption.
    - cbn.
      repeat rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

End ex_binding_type2.
