From Tealeaves Require Export
  Classes.Categorical.TraversableFunctor
  Classes.Kleisli.TraversableFunctor.

Export Kleisli.TraversableFunctor.DerivedInstances.

(** * Traversable Functors: Kleisli to Algebraic *)
(******************************************************************************)

(** ** Instances *)
(******************************************************************************)
Module ToCategorical.

  (** ** Operations *)
  (******************************************************************************)
  #[export] Instance Dist_Traverse (T : Type -> Type) `{Traverse T}
  : ApplicativeDist T := fun G _ _ _ A => traverse T G (@id (G A)).

  (** ** Laws *)
  (******************************************************************************)
  Section proofs.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Kleisli.TraversableFunctor.TraversableFunctor T}.

  (** *** Traversable functor instance *)
  (******************************************************************************)
  Lemma dist_natural_T : forall (G : Type -> Type) (H2 : Map G) (H3 : Pure G) (H4 : Mult G),
      Applicative G -> Natural (@dist T _ G H2 H3 H4).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Map_compose @Dist_Traverse @Map_Traverse.
      rewrite (trf_traverse_traverse (T := T) G (fun A => A)); try typeclasses eauto.
      change (traverse T G (@id (G B))) with (map (fun A => A) (traverse T G (@id (G B)))).
      rewrite (trf_traverse_traverse (T := T) (fun A => A) G); try typeclasses eauto.
      fequal. rewrite (Mult_compose_identity1 G), (Mult_compose_identity2 G).
      reflexivity.
  Qed.

  Lemma dist_morph_T : forall (G1 G2 : Type -> Type) (H2 : Map G1) (H3 : Pure G1) (H4 : Mult G1) (H5 : Map G2)
                         (H6 : Pure G2) (H7 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist T G2 ∘ map T (ϕ A) = ϕ (T A) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Traverse @Map_Traverse.
    change (traverse T G2 (@id (G2 A))) with (map (fun A => A) (traverse T G2 (@id (G2 A)))).
    inversion H1.
    rewrite (trf_traverse_traverse (T := T) (fun A => A) G2); try typeclasses eauto.
    change (map (fun A => A) id ∘ ?f) with f.
    rewrite (trf_traverse_morphism (T := T)).
    fequal. now rewrite (Mult_compose_identity2 G2).
  Qed.

  Lemma dist_unit_T : forall A : Type,
      dist T (fun A0 : Type => A0) = @id (T A).
  Proof.
    intros. unfold_ops @Dist_Traverse.
    apply (trf_traverse_id (T := T)).
  Qed.

  Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Map G1) (H3 : Pure G1) (H4 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H6 : Map G2) (H7 : Pure G2) (H8 : Mult G2),
        Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = map G1 (dist T G2) ∘ dist T G1.
  Proof.
    intros. unfold_ops @Dist_Traverse.
    rewrite (trf_traverse_traverse (T := T) G1); try typeclasses eauto.
    unfold kc2.
    rewrite (fun_map_id (F := G1)).
    reflexivity.
  Qed.

  #[export] Instance: Categorical.TraversableFunctor.TraversableFunctor T :=
    {| dist_natural := dist_natural_T;
       dist_morph := dist_morph_T;
       dist_unit := dist_unit_T;
       dist_linear := dist_linear_T;
    |}.

  End proofs.

End ToCategorical.
