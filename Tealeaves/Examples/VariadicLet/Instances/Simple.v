(*|
############################################################
Formalizing variadic syntax with Tealeaves
############################################################

^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
let with no pairwise binding
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To illustrate the use of the traversal representation theorem, we
consider an example where the syntax has no mutual binding structure.
|*)
From Tealeaves Require Export
  Examples.VariadicLet.Terms
  Functors.List_Telescoping
  Adapters.Compositions.DecoratedTraversableModule.

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.
#[local] Open Scope nat_scope.

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

Section rewriting.

  Section pointful.

    Context
      `{Applicative G} (v1 v2 : Type)
        (f : nat * v1 -> G (term v2)).

    Lemma binddt_term_rw1: forall (v: v1),
        binddt f (tvar v) = f (0, v).
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
      unfold traverse.
      unfold Traverse_list.
      unfold traverse_list.
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

Ltac simplify_binddt_letin :=
  debug "simplify_binddt_letin";
  match goal with
  | |- context[binddt ?f (tvar ?y)] =>
      rewrite binddt_term_rw1
  | |- context[((binddt ?f) (letin ?l ?body))] =>
      rewrite binddt_term_rw2
  | |- context[((binddt ?f) (app ?t1 ?t2))] =>
      rewrite binddt_term_rw3
  end.

Ltac cbn_binddt ::=
  simplify_binddt_letin.

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
  intros.
  derive_dtm2.
  apply traverse_respectful_id; auto.
Qed.

Theorem dtm3_term:
  forall `{Applicative G1} `{Applicative G2},
  forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
    map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
Proof.
  intros.
  derive_dtm3.
  (* TODO investigate how to stop ^^^ from unfold Pure_compose in traverse *)
  binddt_typeclass_normalize.
  (* ^ Hence necessity to repair the damage so rewrite <- IHdefs' works below *)
  { (* left hand side *)
    rewrite traverse_repr at 1.
    dtm3_push_map_right_to_left.
    repeat change (precompose ?f ?g) with (g ∘ f).
    rewrite binddt_pointfree_letin.
    change (?g ∘ ?trav_make defs) with (precompose (trav_make defs) g).
    rewrite <- app_pure_natural.
    rewrite ap_map.
    rewrite <- traverse_repr.
    (* right hand side *)
    assert (IHdefs':
             traverse (G := G1 ∘ G2) (map (binddt g) ∘ binddt f) defs =
               traverse (G := G1 ∘ G2)
                 (binddt (G := G1 ∘ G2) (g ⋆7 f)) defs).
    { apply traverse_respectful; try typeclasses eauto.
      intros t' t'_in.
      unfold compose at 2.
      apply (IHdefs t' t'_in g f). }
    rewrite <- IHdefs'.
    change (map ?g ∘ ?f) with (g ⋆2 f).
    rewrite <- trf_traverse_traverse.
    change ((?g ∘ ?f) defs) with (g (f defs)).
    dtm3_rhs_one_constructor.
    dtm3_rhs_one_constructor.
    reflexivity.
  }
Qed.

Theorem dtm4_stlc :
  forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
    (ϕ : forall A : Type, G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ ->
    forall (A B : Type) (f : nat * A -> G1 (term B)),
      ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
Proof.
  intros.
  derive_dtm4.
  compose near defs on left.
  rewrite (trf_traverse_morphism).
  apply traverse_respectful.
  unfold compose.
  intros t' t'_in.
  apply (IHdefs t' t'_in f).
Qed.
