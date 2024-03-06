From Tealeaves Require Export
  Misc.NaturalNumbers
  Functors.List
  Adapters.Isomorphisms.BatchtoKStore
  Theory.DecoratedTraversableMonad.

Export Kleisli.DecoratedTraversableMonad.Notations. (* ∈d *)
Import Monoid.Notations. (* Ƶ and ● *)
Import Misc.Subset.Notations. (* ∪ *)
Export Applicative.Notations. (* <⋆> *)
Export List.ListNotations. (* [] :: *)
Export Product.Notations. (* × *)
Export ContainerFunctor.Notations. (* ∈ *)
Export DecoratedContainerFunctor.Notations. (* ∈d *)

#[local] Generalizable Variables G A B C.

#[local] Set Implicit Arguments.

(** * Language definition *)
(******************************************************************************)
Inductive term (v : Type) :=
| tvar : v -> term v
| letin : list (term v) -> term v -> term v
| app : term v -> term v -> term v.

#[export] Instance Return_Lam: Return term := tvar.

Print term_rect.

Section term_induction.

  Section term_mut_ind.

  Variables
    (v : Type)
    (P : term v -> Prop).

  Hypotheses
    (tvar_case : forall v, P (tvar v))
    (letin_nil_case :  forall t, P t -> P (letin nil t))
    (letin_cons_case : forall (u: term v) (l : list (term v)) (t: term v)
                         (IHu: P u) (IHl: List.Forall P l)
                         (IHt: P t), P (letin (u :: l) t))
    (app_case : forall t: term v, P t -> forall u: term v, P u -> P (app t u)).


  #[program] Definition term_mut_ind_program: forall t, P t.
  refine (fix F t := match t with
          | tvar v => tvar_case v
          | letin defs body =>
              match defs with
              | nil => @letin_nil_case body (F body)
              | cons u rest =>
                  @letin_cons_case u rest body
                                   (F u)
                                   _
                                   (F body)
              end
          | app t1 t2 =>
              @app_case t1 (F t1) t2 (F t2)
                     end).
  induction rest.
  - apply List.Forall_nil.
  - apply List.Forall_cons; auto.
  Defined.

  Definition term_mut_ind: forall t, P t :=
    fix F t :=
      match t with
      | tvar v => tvar_case v
      | letin defs body =>
          match defs with
          | nil => @letin_nil_case body (F body)
          | cons u rest =>
              @letin_cons_case u rest body
                               (F u)
                               ((fix G l : List.Forall P l
                                 := match l with
                                    | nil =>
                                        List.Forall_nil P
                                    | cons x xs =>
                                        List.Forall_cons x (l := xs) (F x) (G xs)
                                    end) rest)
                               (F body)
          end
      | app t1 t2 =>
          @app_case t1 (F t1) t2 (F t2)
      end.

  End term_mut_ind.

  Section term_mut_ind.

    Lemma Forall_compat_list: forall (A: Type) (l : list A) (P: A -> Prop),
        List.Forall P l <-> Forall_List P l.
    Proof.
      intros.
      induction l.
      - split.
        + intros _. exact I.
        + intros. apply List.Forall_nil.
      - split.
        + intro H.
          inversion H; subst.
          cbn. split. assumption. now apply IHl.
        + intro H.
          inversion H.
          apply List.Forall_cons. assumption. now apply IHl.
    Qed.

  Variables
    (v : Type)
      (P : term v -> Prop).

  Hypotheses
    (tvar_case : forall v, P (tvar v))
      (letin_case : forall (defs: list (term v))
                      (body: term v)
                      (IHdefs: forall (t : term v), t ∈ defs -> P t)
                      (IHbody: P body),
          P (letin defs body))
      (app_case : forall t: term v, P t -> forall u: term v, P u -> P (app t u)).

  Definition term_mut_ind2: forall t, P t.
  Proof.
    intros.
    induction t using term_mut_ind.
    - auto.
    - apply letin_case.
      + inversion 1.
      + assumption.
    - apply letin_case.
      + introv Hin.
        autorewrite with tea_list in Hin.
        inversion Hin.
        * now subst.
        * rewrite Forall_compat_list in IHl.
          rewrite List.forall_iff in IHl.
          now apply IHl.
      + assumption.
    - auto.
  Qed.

End term_mut_ind.

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
      | cons d0 drest =>
          pure cons <⋆> binddt_term f d0 <⋆> F drest
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
  unfold precompose, compose.
  ext body.
  rewrite binddt_rw_letin.
  reflexivity.
Qed.

Lemma binddt_helper_letin2
        `{Applicative G2}
        A B C (l : list (term A))
    (g : nat * B -> G2 (term C)):
  compose (binddt_term g) ∘ letin (v:=B) ∘ toMake_mono list l (term B) =
    ((compose (precompose (binddt_term (g ⦿ List.length l)) ∘ ap G2) ∘
             precompose (traverse (T := list) (binddt_term g)) ∘
             ap G2 ∘ pure (F := G2)) (letin (v:=C))) ∘ toMake_mono list l (term B).
Proof.
  intros.
  Check compose (binddt_term g) ∘ letin (v:=B) ∘ toMake list l (term B).
  (* : Vector.t (term B) (length_gen l) -> term B -> G2 (term C) *)
  Check
    (compose (precompose (binddt_term g) ∘ ap G2) ∘
             precompose (traverse (T := list) (binddt_term g)) ∘
             ap G2 ∘ pure (F := G2)) (letin (v:=C)).
  (* : list (term B) -> term B -> G2 (term C) *)
  Check
    ((compose (precompose (binddt_term g) ∘ ap G2) ∘
             precompose (traverse (T := list) (binddt_term g)) ∘
             ap G2 ∘ pure (F := G2)) (letin (v:=C))) ∘ toMake list l (term B).
  ext l'.
  change_left (binddt_term g ∘ letin (toMake_mono list l (term B) l')).
  ext body.

  rewrite binddt_helper_letin.
  rewrite length_helper_mono.
  reflexivity.
Qed.

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
    apply (traverse_respectful_id (T := list)).
    assumption.
  - cbn.
    rewrite IHt1, IHt2.
    reflexivity.
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
