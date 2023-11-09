From Tealeaves Require Export
  Classes.Categorical.TraversableMonad
  Classes.Kleisli.TraversableMonad.

Import Kleisli.Monad.Notations.

#[local] Arguments bindt {U} (T)%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(** * Traversable Monads: Kleisli to Algebraic *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section operations.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Return T}
      `{Bindt T T}.

    #[export] Instance Dist_Bindt: ApplicativeDist T :=
      fun G _ _ _ A => bindt T G (G A) A (map G (ret T A)).
    #[export] Instance Join_Bindt: Join T :=
      fun A => bindt T (fun A => A) (T A) A (@id (T A)).

End operations.

(** ** Instances *)
(******************************************************************************)
Module ToCategorical.
  Section with_monad.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Kleisli.TraversableMonad.TraversableMonad T}.

    Import TraversableMonad.DerivedOperations.
    Existing Instance DerivedOperations.TraversableMonadFull_Default.

    (** *** Traversable functor instance *)
    (******************************************************************************)
    Lemma dist_natural_T : forall (G : Type -> Type) (H2 : Map G) (H3 : Pure G) (H4 : Mult G),
        Applicative G -> Natural (@dist T _ G H2 H3 H4).
    Proof.
      intros. constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Map_compose @Dist_Bindt.
        unfold_ops @DerivedOperations.Map_Bindt.
        (* Simplify left side *)
        change (bindt T G (G A) A (map G (ret T A))) with (traverse T G (A := G A) (B := A) id).
        change (bindt T (fun A => A) A B (ret T B ∘ f)) with (map T f).
        rewrite (map_traverse T); auto.
        change (?f ∘ id) with f.
        (* Simplify right side *)
        change (bindt T (fun A => A) (G A) (G B) (ret T (G B) ∘ map G f)) with (map (T ∘ G) f).
        unfold_ops @Map_compose.
        rewrite (bindt_map T G).
        reflexivity.
    Qed.

    Lemma dist_morph_T : forall (G1 G2 : Type -> Type) (H2 : Map G1) (H3 : Pure G1) (H4 : Mult G1) (H5 : Map G2)
                           (H6 : Pure G2) (H7 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist T G2 ∘ map T (ϕ A) = ϕ (T A) ∘ dist T G1.
    Proof.
      intros. unfold_ops @Dist_Bindt @Map_Bindt.
      assert (Applicative G1) by now inversion H8.
      assert (Applicative G2) by now inversion H8.
      (* Simplify LHS *)
      change (bindt T G2 (G2 A) A (?rest)) with (traverse T G2 (A := G2 A) (B := A) id).
      change (bindt T (fun A0 : Type => A0) _ _ (ret T _ ∘ ϕ A)) with (map T (ϕ A)).
      rewrite (traverse_map T G2).
      (* RHS *)
      change (bindt T G1 (G1 A) A (map G1 (ret T A))) with (traverse T G1 (@id (G1 A))).
      rewrite (trf_traverse_morphism (T := T) (B := A)).
      reflexivity.
    Qed.

    Lemma dist_unit_T : forall A : Type,
        dist T (fun A0 : Type => A0) = @id (T A).
    Proof.
      intros. unfold_ops @Dist_Bindt.
      change (map (fun A => A) ?f) with f.
      now rewrite (ktm_bindt1 (T := T)).
    Qed.

    Lemma dist_linear_T : forall (G1 : Type -> Type) (H2 : Map G1) (H3 : Pure G1) (H4 : Mult G1),
        Applicative G1 ->
        forall (G2 : Type -> Type) (H6 : Map G2) (H7 : Pure G2) (H8 : Mult G2),
          Applicative G2 -> forall A : Type, dist T (G1 ∘ G2) (A := A) = map G1 (dist T G2) ∘ dist T G1.
    Proof.
      intros. unfold_ops @Dist_Bindt.
      change (bindt T G2 (G2 A) A (map G2 (ret T A))) with (traverse T G2 (@id (G2 A))).
      change (bindt T G1 (G1 (G2 A)) (G2 A) (map G1 (ret T (G2 A)))) with (traverse T G1 (@id (G1 (G2 A)))).
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

    (** *** Monad instance *)
    (******************************************************************************)
    #[export] Instance: Natural (@ret T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Map_Bindt.
        rewrite (ktm_bindt0 (T := T) (fun A => A)).
        reflexivity.
    Qed.

    #[export] Instance: Natural (@join T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Map_compose @Join_Bindt.
        change (bindt T (fun A => A) _ _ ?g) with (bind T g).
        unfold_compose_in_compose.
        rewrite (map_bind T).
        rewrite (bind_map T).
        reflexivity.
    Qed.

    Lemma mon_join_ret_T : forall A : Type, join T ∘ ret T (T A) = @id (T A).
    Proof.
      intros. unfold_ops @Join_Bindt.
      unfold_compose_in_compose.
      change_left (bind (B := A) T id ∘ ret T (T A)).
      now rewrite (kmon_bind0 (T := T)).
    Qed.

    Lemma mon_join_map_ret_T : forall A : Type, join T ∘ map T (ret T A) = @id (T A).
    Proof.
      intros.
      unfold_ops @Join_Bindt @Map_Bindt.
      change_left (bind T (@id (T A)) ∘ map T (ret T A)).
      rewrite (bind_map T).
      change (id ∘ ?g) with g.
      now rewrite (kmon_bind1 (T := T)).
    Qed.

    Lemma mon_join_join_T : forall A : Type, join (A := A) T ∘ join T = join T ∘ map T (join T).
    Proof.
      intros.
      unfold_ops @Join_Bindt @Map_Bindt.
      change (bindt T (fun A => A) _ _ ?g) with (bind T g).
      change (bindt T (fun A => A) _ _ ?g) with (bind T g).
      unfold_compose_in_compose.
      rewrite (kmon_bind2 (T := T)).
      rewrite (kmon_bind2 (T := T)).
      rewrite (kc1_10 T).
      reflexivity.
    Qed.

    #[export] Instance: Categorical.Monad.Monad T :=
      {| mon_join_ret := mon_join_ret_T;
        mon_join_map_ret := mon_join_map_ret_T;
        mon_join_join := mon_join_join_T;
      |}.

    (** *** Traversable monad instance *)
    (******************************************************************************)
    Lemma trvmon_ret_T : forall (G : Type -> Type) (H3 : Map G) (H4 : Pure G) (H5 : Mult G),
        Applicative G -> forall A : Type, dist T G ∘ ret T (G A) = map G (ret T A).
    Proof.
      intros. unfold_ops @Dist_Bindt.
      rewrite (ktm_bindt0 (T := T)); auto.
    Qed.

    Lemma trvmon_join_T : forall (G : Type -> Type) (H3 : Map G) (H4 : Pure G) (H5 : Mult G),
        Applicative G -> forall A : Type, dist T G ∘ join T (A := G A) = map G (join T) ∘ dist T G ∘ map T (dist T G).
    Proof.
      intros. unfold_ops @Dist_Bindt @Join_Bindt.
      change_left (bindt T G _ _ (map G (ret T A)) ∘ bind T id).
      rewrite (bindt_bind T); auto.
      change (?f ∘ id) with f.
      change (bindt T (fun A => A) _ _ ?g) with (bind T g).
      unfold_compose_in_compose.
      rewrite (bind_bindt T G).
      rewrite (fun_map_map (F := G)).
      rewrite (bindt_map T G).
      rewrite (kmon_bind0 (T := T)).
      rewrite (fun_map_id (F := G)).
      reflexivity.
    Qed.

    #[export] Instance: Categorical.TraversableMonad.TraversableMonad T :=
      {| trvmon_ret := trvmon_ret_T;
        trvmon_join := trvmon_join_T;
      |}.

  End with_monad.

End ToCategorical.
