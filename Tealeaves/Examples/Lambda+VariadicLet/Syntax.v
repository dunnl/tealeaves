From Tealeaves Require Export
  Misc.NaturalNumbers
  Functors.List
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


  Print term_rect.
  #[program] Definition term_mut_ind: forall t, P t.
  refine (fix F t := match t with
          | tvar v => tvar_case v
          | letin defs body =>
              match defs with
              | nil => @letin_nil_case body (F body)
              | cons u rest =>
                  @letin_cons_case u rest body
                                   (F u) _ (F body)
              end
          | app t1 t2 =>
              @app_case t1 (F t1) t2 (F t2)
                     end).
  admit.
  Admitted.

End term_induction.

(*
Section term_induction.

  Variables
    (v : Type)
    (P : term v -> Type).

  Hypotheses
    (tvar_case : forall v, P (tvar v))
    (letin_case : forall (l : list (term v)) (t : term v)
                      (rec: forall t, t ∈ l -> P t),
          P t -> P (letin l t))
    (app_case : forall t: term v, P t -> forall u: term v, P u -> P (app t u)).


  #[program] Definition term_mut_rect: forall t, P t.
  refine (fix F t :=
      match t with
      | tvar v =>
          tvar_case v
      | letin defs body =>
          @letin_case defs body
                      ((fix G (ls : list (term v)): forall t, t ∈ ls -> P t :=
                          match ls with
                          | nil => _
                          | cons x rest => _
                          end
                       ) defs)
                      (F body)
      | app t u =>
          @app_case t (F t) u (F u)
      end).
  - inversion 1.
  - intros t' t_in.
    cbn in t_in.
    admit.
  Admitted.

End term_induction.
*)

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
      end) defs) <⋆> binddt_term (f ⦿ length defs) body
  | app t1 t2 =>
      pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance Binddt_Lam: Binddt nat term term := @binddt_term.

Lemma binddt_rw_letin: forall `{Applicative G} (v1 v2 : Type)
                         (l : list (term v1)) (body: term v1),
  forall f : nat * v1 -> G (term v2),
    binddt_term f (letin l body) =
      pure (@letin v2) <⋆> traverse (binddt_term f) l <⋆>
        binddt_term (f ⦿ length l) body.
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
        `{Applicative G1}
        `{Applicative G2}
        A B C
    (f : nat * A -> G1 (term B))
    (g : nat * B -> G2 (term C)):
    pure (compose (binddt_term g) ∘ letin (v:=B)) =
      pure (compose (binddt_term g) ∘ letin (v:=B)).
Proof.
  unfold compose.
Abort.

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
  intros. ext t. unfold id.
  induction t using term_mut_ind.
  - cbn. reflexivity.
  - cbn.
    change 0 with (Ƶ:nat).
    rewrite preincr_zero.
    rewrite IHt.
    reflexivity.
  - cbn.
    rewrite extract_preincr2.
Admitted.

Theorem dtm3_term:
  forall `{Applicative G1} `{Applicative G2},
  forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
    map (binddt_term g) ∘ binddt_term f = binddt_term (G := G1 ∘ G2) (g ⋆7 f).
Proof.
  intros. ext t.
  generalize dependent g.
  generalize dependent f.
  unfold compose at 1.
  induction t; intros f g.
  - cbn. change (preincr g 0) with (preincr g Ƶ).
    now rewrite preincr_zero.
  - specialize (IHt (f ⦿ length l) (g ⦿ length l)).
    rewrite kc7_preincr in IHt.
    (* left *)
    rewrite binddt_rw_letin.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    (* right *)
    rewrite binddt_rw_letin.

    Set Keyed Unification.
    rewrite <- IHt.
    unfold compose at 1.
Abort.

Theorem dtm4_stlc :
  forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
    (ϕ : forall A : Type, G1 A -> G2 A), ApplicativeMorphism G1 G2 ϕ ->
                                   forall (A B : Type) (f : nat * A -> G1 (term B)),
                                     ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
Proof.
  intros. ext t.
  inversion H.
  generalize dependent f.
  unfold compose at 1.
  induction t; intro f. (* .unfold *)
  - reflexivity.
  - cbn.
    repeat rewrite ap_morphism_1.
    rewrite appmor_pure.
    rewrite IHt.
    admit.
  - cbn.
    repeat rewrite ap_morphism_1.
    rewrite appmor_pure.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Abort.
