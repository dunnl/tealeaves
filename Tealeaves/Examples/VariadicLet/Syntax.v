(*|
############################################################
Formalizing variadic syntax with Tealeaves
############################################################

|*)
From Tealeaves Require Export
  Examples.VariadicLet.Terms
  Examples.Simplification_Support
  Functors.List_Telescoping
  Tactics.Debug
  Theory.TraversableFunctor
  Adapters.Compositions.DecoratedTraversableModule.

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.

Open Scope nat_scope.

#[local] Notation "'P'" := pure.
#[local] Notation "'BD'" := binddt.

(* TODO: this is needed because <<list>> has no other instance *)
#[local] Existing Instance ToBatch_Traverse.

Import Classes.Kleisli.TraversableFunctor.Notations.
Import Classes.Kleisli.DecoratedTraversableFunctor.Notations.

  (* left *)
  Ltac dtm3_lhs_step :=
    repeat rewrite map_ap;
    rewrite app_pure_natural.

  (* right *)
  Ltac dtm3_rhs_applicative_compose :=
    match goal with
    | |- context[ap (?G1 ∘ ?G2)] =>
        (rewrite_strat innermost
           (terms (ap_compose2 G2 G1)));
        (repeat rewrite map_ap);
        (repeat rewrite app_pure_natural)
    end.
  Ltac dtm3_rhs_applicative_map :=
    rewrite <- ap_map;
    repeat rewrite map_ap;
    repeat rewrite app_pure_natural.
  Ltac dtm3_rhs_step :=
    unfold_ops @Pure_compose;
    repeat (dtm3_rhs_applicative_compose;
            dtm3_rhs_applicative_map).


Module ex_binding_type1.

(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
let with no pairwise binding
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To illustrate the use of the traversal representation theorem, we
consider an example where the syntax has no mutual binding structure.

|*)
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
          pure cons <⋆> binddt_term f d <⋆> F drest
      end) defs) <⋆> binddt_term (f ⦿ length defs) body
  | app t1 t2 =>
      pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance Binddt_Lam: Binddt nat term term
  := @binddt_term.

#[export] Instance Map_term: Map term
  := Map_Binddt nat term term.
#[export] Instance Mapd_term: Mapd nat term
  := Mapd_Binddt nat term term.
#[export] Instance Traverse_term: Traverse term
  := Traverse_Binddt nat term term.
#[export] Instance Mapdt_term: Mapdt nat term
  := Mapdt_Binddt nat term term.
#[export] Instance Bind_term: Bind term term
  := Bind_Binddt nat term term.
#[export] Instance Bindd_term: Bindd nat term term
  := Bindd_Binddt nat term term.
#[export] Instance Bindt_term: Bindt term term
  := Bindt_Binddt nat term term.

#[export] Instance ToSubset_term: ToSubset term
  := ToSubset_Traverse.
#[export] Instance ToBatch_Lam: ToBatch term
  := ToBatch_Traverse.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Rewriting principles
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

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
          pure (@letin v2) <⋆> traverse (binddt f) l <⋆>
            binddt (f ⦿ length l) body.
    Proof.
      intros. cbn.
      do 2 fequal.
      induction l.
      - cbn.
        reflexivity.
      - cbn.
        rewrite IHl.
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
        (pure (letin (v:=C)) <⋆> (traverse (binddt g) l)).
  Proof.
    intros l.
    ext body.
    unfold precompose, compose.
    rewrite binddt_term_rw2.
    reflexivity.
  Qed.

  Lemma binddt_pointfree_letin: forall `(l:list A),
    compose (binddt g) ∘ letin (v:=B) ∘ trav_make l (B := term B) =
      ((compose (precompose (binddt (g ⦿ length l)) ∘ ap G2) ∘
          precompose (traverse (T := list) (binddt g)) ∘
          ap G2 ∘ pure (F := G2)) (letin (v:=C))) ∘ trav_make l (B := term B).
  Proof.
    intros A l.
    ext l' body.
    unfold precompose, compose.
    rewrite binddt_term_rw2.
    do 2 rewrite <- list_plength_length.
    rewrite <- plength_trav_make.
    reflexivity.
  Qed.

  End pointfree.

End rewriting.

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

Ltac simplify_binddt_term_lazy unit :=
    simplify_binddt_term.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Instantiate simplification infrastructure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Ltac derive_dtm_law :=
  derive_dtm_law_with_simplify_binddt_IH
    term_mut_ind2 simplify_binddt_term_lazy.

Ltac simplify_pass1 :=
  simplify_pass1_with_simplify_binddt term simplify_binddt_term_lazy.

Ltac derive_dtm_law_case :=
  derive_dtm_law_case_with_simplify_binddt simplify_binddt_term_lazy.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
DTM laws
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
    derive_dtm_law.
    derive_dtm_law_case.
    apply traverse_respectful_id; auto.
  Qed.

  Theorem dtm3_term:
    forall `{Applicative G1} `{Applicative G2},
    forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
      map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros. ext t.
    generalize dependent g.
    generalize dependent f.
    assert (Functor G1) by (now inversion H2).
    assert (Functor G2) by (now inversion H6).
    unfold compose at 1.
    induction t using term_mut_ind2; intros f g.
    - derive_dtm_law_case.
      dtm_law_pass.
      derive_dtm_law_case.
    - derive_dtm_law_case.
      (* left *)
      repeat dtm3_lhs_step.
      (* right *)
      assert (IHdefs':
               traverse (G := G1 ∘ G2) (map (BD g) ∘ BD f) defs =
                 traverse (G := G1 ∘ G2)
                   (binddt (G := G1 ∘ G2) (g ⋆7 f)) defs).
      { apply traverse_respectful; try typeclasses eauto.
        intros t' t'_in.
        apply (IHdefs t' t'_in f g).
      }
      (* defs *)
      rewrite <- IHdefs'.
      change (map ?g ∘ ?f) with (g ⋆2 f).
      rewrite <- trf_traverse_traverse.
      change ((?g ∘ ?f) defs) with (g (f defs)).
      dtm3_rhs_step.
      (* rhs body *)
      rewrite <- (kc7_preincr g f (G1 := G1) (G2 := G2) (length defs)).
      rewrite <- (IHt (f ⦿ length defs) (g ⦿ length defs)).
      dtm3_rhs_step.
      (* rhs pure *)
      fequal.
      { rewrite traverse_repr.
        rewrite map_to_ap.
        repeat rewrite <- ap4;
          repeat rewrite ap2.
        rewrite binddt_pointfree_letin.
        reflexivity.
      }
    - derive_dtm_law_case.
      repeat dtm3_lhs_step.
      dtm3_rhs_step.
      rewrite <- IHt1.
      dtm3_rhs_step.
      rewrite <- IHt2.
      dtm3_rhs_step.
      reflexivity.
  Qed.

  Theorem dtm4_stlc :
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : nat * A -> G1 (term B)),
        ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
  Proof.
    intros. ext t.
    unfold compose at 1.
    assert (Applicative G1) by (now inversion H).
    assert (Applicative G2) by (now inversion H).
    generalize dependent f.
    induction t using term_mut_ind2; intro f.
    - derive_dtm_law_case.
    - derive_dtm_law_case.
      fequal.
      + compose near defs on left.
        rewrite (trf_traverse_morphism).
        apply traverse_respectful.
        unfold compose.
        intros t' t'_in.
        apply (IHdefs t' t'_in f).
      + apply IHt.
    - do 2 derive_dtm_law_case.
  Qed.

End ex_binding_type1.

Module ex_binding_type2.
(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
let with no pairwise binding
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To illustrate the use of the traversal representation theorem, we
consider an example where the syntax has no mutual binding structure.

|*)

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

  Ltac simplify_binddt_term_lazy unit :=
    simplify_binddt_term.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Instantiate simplification infrastructure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

  Ltac derive_dtm_law :=
    derive_dtm_law_with_simplify_binddt_IH
      term_mut_ind2 simplify_binddt_term_lazy.

  Ltac simplify_pass1 :=
    simplify_pass1_with_simplify_binddt term simplify_binddt_term_lazy.

  Ltac derive_dtm_law_case :=
    derive_dtm_law_case_with_simplify_binddt simplify_binddt_term_lazy.

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
    intros.
    derive_dtm_law.
    derive_dtm_law_case.
    unfold subst_in_defs.
    unfold_ops @Mapdt_Binddt_compose.
    apply mapdt_respectful_id.
    intros.
    apply ind_implies_in in H.
    simplify_pass2.
    eauto.
  Qed.

  Theorem dtm3_term:
    forall `{Applicative G1} `{Applicative G2},
    forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
      map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros. ext t.
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


Module ex_binding_type3.
(*|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
fully mutually recursive
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To illustrate the use of the traversal representation theorem, we
consider an example where the syntax has no mutual binding structure.

|*)

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

  #[export] Instance Binddt_Lam: Binddt nat term term := @binddt_term.

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

  Ltac simplify_binddt_term_lazy unit :=
    simplify_binddt_term.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Instantiate simplification infrastructure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

  Ltac derive_dtm_law :=
    derive_dtm_law_with_simplify_binddt_IH
      term_mut_ind2 simplify_binddt_term_lazy.

  Ltac simplify_pass1 :=
    simplify_pass1_with_simplify_binddt term simplify_binddt_term_lazy.

  Ltac derive_dtm_law_case :=
    derive_dtm_law_case_with_simplify_binddt simplify_binddt_term_lazy.

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
    intros.
    derive_dtm_law.
    derive_dtm_law_case.
    unfold subst_in_defs.
    unfold_ops @Mapdt_Binddt_compose.
    apply mapdt_respectful_id.
    intros.
    apply ind_implies_in in H.
    simplify_pass2.
    eauto.
  Qed.

  Theorem dtm3_term:
    forall `{Applicative G1} `{Applicative G2},
    forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
      map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros. ext t.
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
      { assert (ToBatch list).
        typeclasses eauto.
        rewrite mapdt_repr.
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

End ex_binding_type3.
