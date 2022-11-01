From Tealeaves Require Export
     Classes.Functor
     Classes.Applicative
     Classes.TraversableFunctor
     Functors.Constant.

Import List.ListNotations.
#[local] Open Scope list_scope.

Import Functor.Notations.
Import SetlikeFunctor.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

(** * Domain-restricted operations *)
Section restrictions.

  Import SetlikeFunctor.
  Import SetlikeFunctor.Notations.

  Context
    `{TraversableFunctor T}
    (A : Type)
    (P : A -> Prop)
    (B : Type).

  Hypothesis ax : forall `(t : T A),
      (forall a, a ∈ t -> P a) ->
      runBatch_monoid (unit0 := True) (op := and) (B := B) P (iterate _ t).

  Context
    (t : T A)
    (hyp : forall a, a ∈ t -> P a)
    (f : sig P -> B).

  Definition sigma_fmap : T B.
    apply ax in hyp.
    induction (iterate _ t).
    - auto.
    - cbn in hyp.
      destruct hyp as [x1 x2].
      apply IHb. auto. auto.
      apply f. eexists. eauto.
  Defined.

End restrictions.



(** ** Specifications for sub-operations *)
(******************************************************************************)
Section KleisliTraversableMonad_suboperations.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma bind_to_bindt : forall `(f : A -> T B),
      bind T f = bindt T (fun A => A) f.
  Proof.
    intros. unfold_ops @Bindt_alg. now rewrite (dist_unit T).
  Qed.

  Lemma traverse_to_bindt `{Applicative G} : forall `(f : A -> G B),
      traverse T G f = bindt T G (fmap G (ret T) ∘ f).
  Proof.
    introv. unfold_ops @Bindt_alg.
    rewrite <- (fun_fmap_fmap T).
    change_right (fmap G (join T) ∘ (dist T G ∘ fmap (T ∘ G) (ret T)) ∘ fmap T f).
    #[local] Set Keyed Unification.
    rewrite <- (natural (ϕ := @dist T _ G _ _ _)).
    #[local] Unset Keyed Unification.
    unfold_ops @Fmap_compose.
    repeat reassociate <-.
    rewrite (fun_fmap_fmap G).
    rewrite (mon_join_fmap_ret T).
    now rewrite (fun_fmap_id G).
  Qed.

  Lemma fmap_to_bindt : forall `(f : A -> B),
      fmap T f = bindt T (fun A => A) (ret T ∘ f).
  Proof.
    introv. rewrite (fmap_to_traverse T). now rewrite traverse_to_bindt.
  Qed.

End KleisliTraversableMonad_suboperations.


(** ** Kleisli category laws *)
(******************************************************************************)
Section TraversableMonad_kleisli_category.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}
    `{Applicative G}.

  Notation "'1'" := (fun A => A).

  (** Composition when <<f>> has no applicative effect *)
  Theorem tm_kleisli_star1 {A B C} : forall (g : B -> G (T C)) (f : A -> T B),
      g ⋆tm (f : A -> 1 (T B)) = bindt T G g ∘ f.
  Proof.
    easy.
  Qed.

  (** Composition when <<f>> has a pure applicative effect *)
  Theorem tm_kleisli_star2 {A B C} : forall (g : B -> G (T C)) (f : A -> T B),
      g ⋆tm (pure G ∘ f) = pure G ∘ bindt T G g ∘ f.
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    fequal. unfold compose; ext t. now apply (app_pure_natural G).
  Qed.

  (** Composition when <<g>> has no applicative effect *)
  Theorem tm_kleisli_star3 {A B C} : forall (g : B -> T C) (f : A -> G (T B)),
      (g : B -> 1 (T C)) ⋆tm f =
      fmap G (bind T g) ∘ f.
  Proof.
    introv. unfold kcompose_tm. unfold bindt. unfold_ops @Fmap_I @Bindt_alg.
    now rewrite (dist_unit T).
  Qed.

  (** Composition when <<g>> has a pure applicative effect *)
  Theorem tm_kleisli_star4 {A B C} : forall (g : B -> T C) (f : A -> G1 (T B)),
      (pure G2 ∘ g) ⋆tm f =
      fmap G1 (pure G2 ∘ bind T g) ∘ f.
  Proof.
    introv. unfold kcompose_tm.
    rewrite (bind_to_bindt T). fequal. fequal.
    rewrite <- (bindt_purity T (G2 := G2) (G1 := 1) g).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  (** Composition when <<f>> does not perform a substitution *)
  Theorem tm_kleisli_star5 {A B C} : forall (g : B -> G2 (T C)) (f : A -> G1 B),
      g ⋆tm (fmap G1 (ret T) ∘ f) =
      fmap G1 g ∘ f.
  Proof.
    intros. unfold kcompose_tm.
    reassociate <-. rewrite (fun_fmap_fmap G1).
    now rewrite (bindt_comp_ret T).
  Qed.

  (** Composition when <<g>> does not perform a substitution *)
  Theorem tm_kleisli_star6 {A B C} : forall (g : B -> G2 C) (f : A -> G1 (T B)),
      (fmap G2 (ret T) ∘ g) ⋆tm f =
      fmap G1 (traverse T G2 g) ∘ f.
  Proof.
    intros. unfold kcompose_tm. fequal.
    now rewrite (traverse_to_bindt T).
  Qed.

  (** Composition when <<f>> is just a map *)
  Theorem tm_kleisli_star7 {A B C} : forall (g : B -> G (T C)) (f : A -> B),
      g ⋆tm (ret T ∘ f : A -> 1 (T B)) = g ∘ f.
  Proof.
    intros. unfold kcompose_tm. fequal.
    unfold_ops @Fmap_compose. change (fmap 1 ?f) with f.
    reassociate <-. now rewrite (bindt_comp_ret T).
  Qed.

  (** Composition when <<g>> is just a map *)
  Theorem tm_kleisli_star8 {A B C} : forall (g : B -> C) (f : A -> G (T B)),
      (ret T ∘ g : B -> 1 (T C)) ⋆tm f =
      (fmap (G ∘ T) g ∘ f : A -> G (T C)).
  Proof.
    intros. unfold kcompose_tm. fequal.
    unfold_ops @Fmap_compose. now rewrite (fmap_to_bindt T).
  Qed.

  (** Right identity for <<kcompose_tm>> *)
  Theorem tm_kleisli_id_r {B C} : forall (g : B -> G (T C)),
      g ⋆tm (ret T : B -> 1 (T B)) = g.
  Proof.
    intros. rewrite tm_kleisli_star1.
    now rewrite (bindt_comp_ret T).
  Qed.

  (** Left identity for <<kcompose_tm>> *)
  Theorem tm_kleisli_id_l {A B} : forall (f : A -> G (T B)),
      (ret T : B -> (fun A => A)(T B)) ⋆tm f = f.
  Proof.
    intros. rewrite tm_kleisli_star3.
    rewrite (mon_bind_id T).
    now rewrite (fun_fmap_id G).
  Qed.

  (** Associativity law for <<kcompose_tm>> *)
  Theorem tm_kleisli_assoc {A B C D} :
    forall (h : C -> G3 (T D)) (g : B -> G2 (T C)) (f : A -> G1 (T B)),
       h ⋆tm (g ⋆tm f : A -> (G1 ∘ G2) (T C)) =
       (h ⋆tm g : B -> (G2 ∘ G3) (T D)) ⋆tm f.
  Proof.
    intros. unfold kcompose_tm.
    repeat reassociate <-. fequal.
    unfold fmap at 1, Fmap_compose.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G1 _ _ _ (bindt T G2 g)). fequal.
    now rewrite <- (bindt_bindt T).
  Qed.

End TraversableMonad_kleisli_category.

(** ** Composition with suboperations *)
(******************************************************************************)
Section TraversableMonad_suboperation_composition.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}.

  Corollary bindt_fmapt {A B C} : forall (g : B -> G2 (T C)) (f : A -> G1 B),
      fmap G1 (bindt T G2 g) ∘ traverse T G1 f = bindt T (G1 ∘ G2) (fmap G1 g ∘ f).
  Proof.
    intros. rewrite (traverse_to_bindt T).
    rewrite <- (bindt_bindt T). fequal.
    now rewrite (tm_kleisli_star5).
  Qed.

  Corollary bind_bindt {A B C} : forall (g : B -> T C) (f : A -> G (T B)),
      fmap G (bind T g) ∘ bindt T G f = bindt T G (fmap G (bind T g) ∘ f).
  Proof.
    intros. rewrite (bind_to_bindt T).
    rewrite <- (bindt_bindt T (G2 := fun A => A) (G1 := G) g f).
    fequal. (* todo *) ext X Y [? ?]; cbn. unfold_ops @Mult_compose.
    unfold_ops @Mult_I. now rewrite (fun_fmap_id G).
  Qed.

  Corollary fmapt_bindt {A B C} : forall (g : B -> G2 C) (f : A -> G1 (T B)),
      fmap G1 (traverse T G2 g) ∘ bindt T G1 f = bindt T (G1 ∘ G2) (fmap G1 (traverse T G2 g) ∘ f).
  Proof.
    intros. rewrite (traverse_to_bindt T (G := G2)).
    now rewrite <- (bindt_bindt T).
  Qed.

  Corollary bindt_bind {A B C} : forall (g : B -> G (T C)) (f : A -> T B),
      bindt T G g ∘ bind T f = bindt T G (bindt T G g ∘ f).
  Proof.
    intros. rewrite (bind_to_bindt T).
    change (bindt T G g) with (fmap (fun A => A) (bindt T G g)).
    rewrite <- (bindt_bindt T (G1 := fun A => A)). fequal.
     (* todo *) ext X Y [? ?]; cbn. unfold_ops @Mult_compose.
    unfold_ops @Mult_I. reflexivity.
  Qed.

  Corollary bindt_fmap {A B C} : forall (g : B -> G (T C)) (f : A -> B),
      bindt T G g ∘ fmap T f = bindt T G (g ∘ f).
  Proof.
    intros. unfold_ops Bindt_alg. reassociate ->. now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary fmap_bindt {A B C} : forall (g : B -> C) (f : A -> G (T B)),
      fmap G (fmap T g) ∘ bindt T G f = bindt T G (fmap (G ∘ T) g ∘ f).
  Proof.
    intros. rewrite (fmap_to_bindt T). rewrite <- (bindt_bindt T (G2 := fun A => A)).
    fequal.
     (* todo *) ext X Y [? ?]; cbn. unfold_ops @Mult_compose.
    unfold_ops @Mult_I. now rewrite (fun_fmap_id G).
    now rewrite (tm_kleisli_star8).
  Qed.

End TraversableMonad_suboperation_composition.


(** ** Purity laws for [bindt] *)
(******************************************************************************)
Section TraversableMonad_purity.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Theorem bindt_purity1 `{Applicative G} {A B} : forall (f : A -> T B),
      bindt T G (pure G ∘ f) = pure G ∘ bind T f.
  Proof.
    intros. unfold_ops @Bind_Join. reassociate <-.
    unfold_ops @Bindt_alg. rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    reassociate -> near (fmap T (pure G)).
    rewrite (fmap_purity_1 T). fequal.
    ext t; unfold compose. now rewrite (app_pure_natural G).
  Qed.

  Theorem bindt_purity2 `{Applicative G} {A} :
    bindt T G (pure G ∘ ret T) = pure G (A := T A).
  Proof.
    rewrite bindt_purity1. now rewrite (mon_bind_id T).
  Qed.

End TraversableMonad_purity.
(*
(** ** Respectfulness properties *)
(******************************************************************************)
Section TraversableMonad_respectfulness.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}
    `{Applicative G}.


  Corollary bindt_respectful {A B} : forall t (f g : A -> G (T B)),
      (forall a, a ∈ t -> f a = g a) -> bindt T G f t = bindt T G g t.
  Proof.
    intros. unfold bindt, compose. fequal. fequal.
    now apply (fmap_respectful T).
  Qed.

  Corollary bindt_respectful_id {A} : forall t (f : A -> G (T A)),
      (forall a, a ∈ t -> f a = pure G (ret T a)) -> bindt T f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity T).
    rewrite (traverse_to_bindt T).
    apply bindt_respectful. unfold compose.
    now setoid_rewrite (app_pure_natural G).
  Qed.

End TraversableMonad_respectfulness.
*)
