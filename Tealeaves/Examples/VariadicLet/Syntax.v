From Tealeaves Require Export
  Examples.VariadicLet.Terms.

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.

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
      end) defs) <⋆> binddt_term (f ⦿ List.length defs) body
  | app t1 t2 =>
      pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance Binddt_Lam: Binddt nat term term := @binddt_term.

Lemma binddt_rw_letin: forall `{Applicative G} (v1 v2 : Type)
                         (l : list (term v1)) (body: term v1),
  forall f : nat * v1 -> G (term v2),
    binddt f (letin l body) =
      pure (@letin v2) <⋆> traverse (binddt f) l <⋆>
        binddt (f ⦿ List.length l) body.
Proof.
  intros.
  destruct l.
  - cbn.
    change 0 with (Ƶ:nat).
    rewrite preincr_zero.
    reflexivity.
  - cbn.
    repeat fequal.
    induction l.
    + reflexivity.
    + cbn. rewrite IHl.
      reflexivity.
Qed.

Lemma binddt_helper_letin
        `{Applicative G2}
        B C (l : list (term B))
        (g : nat * B -> G2 (term C)):
  binddt g ∘ letin (v:=B) l =
    (precompose (binddt (g ⦿ List.length l)) ∘ ap G2)
      (pure (letin (v:=C)) <⋆> (traverse (binddt g) l)).
Proof.
  cbn.
  unfold precompose, compose.
  ext body.
  rewrite binddt_rw_letin.
  reflexivity.
Qed.

Lemma binddt_helper_letin2
        `{Applicative G2}
        A B C (l : list (term A))
    (g : nat * B -> G2 (term C)):
  compose (binddt_term g) ∘ letin (v:=B) ∘ toMake_ l (term B) =
    ((compose (precompose (binddt_term (g ⦿ List.length l)) ∘ ap G2) ∘
             precompose (traverse (T := list) (binddt_term g)) ∘
             ap G2 ∘ pure (F := G2)) (letin (v:=C))) ∘ toMake_ l (term B).
Proof.
  intros.
  ext defs. unfold compose, precompose. ext body.


  Check compose (binddt_term g) ∘ letin (v:=B) ∘ toMake_ l (term B).
  (* : Vector.t (term B) (length_gen l) -> term B -> G2 (term C) *)
  Check
    (compose (precompose (binddt_term g) ∘ ap G2) ∘
             precompose (traverse (T := list) (binddt_term g)) ∘
             ap G2 ∘ pure (F := G2)) (letin (v:=C)).
  (* : list (term B) -> term B -> G2 (term C) *)
  Check
    ((compose (precompose (binddt_term g) ∘ ap G2) ∘
             precompose (traverse (T := list) (binddt_term g)) ∘
             ap G2 ∘ pure (F := G2)) (letin (v:=C))) ∘ toMake_ l (term B).
Admitted.

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
  intros. ext t.
  induction t using term_mut_ind2.
  - cbn. reflexivity.
  - rewrite binddt_rw_letin.
    rewrite extract_preincr2.
    rewrite IHt.
    unfold_ops @Pure_I; unfold id.
    fequal.
Abort.

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
    change (preincr g 0) with (preincr g Ƶ).
    now rewrite preincr_zero.
  - do 2 rewrite binddt_rw_letin.
    pose (IHt' := IHt (f ⦿ List.length defs) (g ⦿ List.length defs)).
    rewrite kc7_preincr in IHt'.
    (* left *)
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    erewrite traverse_repr;
      try typeclasses eauto.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite binddt_helper_letin2.
    rewrite <- map_to_ap.
    rewrite <- (fun_map_map (F := G1)).
    unfold compose at 1.
    rewrite (map_to_ap (toMake_mono list defs _)).
    rewrite <- (traverse_repr list G1 defs (term B) (binddt f)).
    rewrite (map_to_ap).
    (* right *)
    unfold_ops @Pure_compose.
    assert (Heqdefs: traverse (binddt (G := G1 ∘ G2) (g ⋆7 f)) defs =
              map (F := G1)
                  (traverse (T := list) (binddt (G := G2) g))
                  (traverse (T := list) (binddt (G := G1) f) defs)).
    { compose near defs on right.
      rewrite traverse_traverse.
      all: try typeclasses eauto.
      apply traverse_respectful.
      typeclasses eauto.
      symmetry.
      now apply IHdefs. }
    #[local] Set Keyed Unification.
    rewrite_strat innermost (terms (ap_compose2 G2 G1)).
    rewrite app_pure_natural.
    rewrite Heqdefs.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    rewrite_strat innermost (terms (ap_compose2 G2 G1)).
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- IHt'.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    reflexivity.
  - cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    unfold_ops @Pure_compose.
    rewrite_strat innermost (terms (ap_compose2 G2 G1)).
    rewrite app_pure_natural.
    rewrite <- IHt1.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    rewrite_strat innermost (terms (ap_compose2 G2 G1)).
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- IHt2.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    reflexivity.
    #[local] Unset Keyed Unification.
Qed.

Theorem dtm4_stlc :
  forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
    (ϕ : forall A : Type, G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ ->
    forall (A B : Type) (f : nat * A -> G1 (term B)),
      ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
Proof.
  intros. ext t.
  inversion H.
  generalize dependent f.
  unfold compose at 1.
  induction t using term_mut_ind2; intro f. (* .unfold *)
  - reflexivity.
  - do 2 rewrite binddt_rw_letin.
    repeat rewrite ap_morphism_1.
    rewrite appmor_pure.
    rewrite IHt.
    change (ϕ (list (term B)) (traverse (binddt f) defs))
      with ((ϕ (list (term B)) ∘ traverse (binddt f)) defs).
    rewrite (trf_traverse_morphism).
    assert (Heqdefs: (traverse (ϕ (term B) ∘ binddt f) defs) =
                       traverse (binddt (ϕ (term B) ∘ f)) defs).
    { apply traverse_respectful.
      typeclasses eauto.
      intros.
      unfold compose.
      now apply IHdefs. }
    rewrite Heqdefs.
    reflexivity.
  - cbn.
    repeat rewrite ap_morphism_1.
    rewrite appmor_pure.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.
