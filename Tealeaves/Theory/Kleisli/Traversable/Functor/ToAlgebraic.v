From Tealeaves.Classes Require Export
  Algebraic.Traversable.Functor
  Kleisli.Traversable.Functor.

From Tealeaves.Theory Require Import
  Kleisli.Traversable.Functor.ToFunctor.

#[local] Generalizable Variables A B C.

Import ToFunctor.Operation.

(** * Traversable Functors: Kleisli to Algebraic *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Module Operations.
  Section with_kleisli.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Traverse T}.

    #[export] Instance Dist_Traverse: Dist T := fun G _ _ _ A => traverse T G (@id (G A)).

  End with_kleisli.
End Operations.

Import Operations.

(** ** Instances *)
(******************************************************************************)
Section with_kleisli.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Kleisli.Traversable.Functor.TraversableFunctor T}.

  Export Kleisli.Traversable.Functor.ToFunctor.Operation.
  Export Kleisli.Traversable.Functor.ToFunctor.Instances.

  (** *** Traversable functor instance *)
  (******************************************************************************)
  Lemma dist_natural_T : forall (G : Type -> Type) (H2 : Fmap G) (H3 : Pure G) (H4 : Mult G),
      Applicative G -> Natural (@dist T _ G H2 H3 H4).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Fmap_compose @Dist_Traverse @Fmap_Traverse.
      rewrite (trf_traverse_traverse T G (fun A => A)); try typeclasses eauto.
      change (traverse T G (@id (G B))) with (fmap (fun A => A) (traverse T G (@id (G B)))).
      rewrite (trf_traverse_traverse T (fun A => A) G); try typeclasses eauto.
      fequal. rewrite Mult_compose_identity1, Mult_compose_identity2.
      reflexivity.
  Qed.

  Lemma dist_morph_T : forall (G1 G2 : Type -> Type) (H2 : Fmap G1) (H3 : Pure G1) (H4 : Mult G1) (H5 : Fmap G2)
                         (H6 : Pure G2) (H7 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist T G2 ∘ fmap T (ϕ A) = ϕ (T A) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Traverse @Fmap_Traverse.
    change (traverse T G2 (@id (G2 A))) with (fmap (fun A => A) (traverse T G2 (@id (G2 A)))).
    inversion H1.
    rewrite (trf_traverse_traverse T (fun A => A) G2); try typeclasses eauto.
    change (fmap (fun A => A) id ∘ ?f) with f.
    rewrite (trf_traverse_morphism T).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma dist_unit_T : forall A : Type,
      dist T (fun A0 : Type => A0) = @id (T A).
  Proof.
    intros. unfold_ops @Dist_Traverse.
    apply (trf_traverse_id T).
  Qed.

  Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Fmap G1) (H3 : Pure G1) (H4 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H6 : Fmap G2) (H7 : Pure G2) (H8 : Mult G2),
        Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = fmap G1 (dist T G2) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Traverse.
    rewrite (trf_traverse_traverse T G1); try typeclasses eauto.
    rewrite (fun_fmap_id G1).
    reflexivity.
  Qed.

  #[export] Instance: Algebraic.Traversable.Functor.TraversableFunctor T :=
    {| dist_natural := dist_natural_T;
       dist_morph := dist_morph_T;
       dist_unit := dist_unit_T;
       dist_linear := dist_linear_T;
    |}.

End with_kleisli.
