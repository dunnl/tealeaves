From Tealeaves Require Export
  Classes.Categorical.TraversableMonad
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.Monad (map_bind, bind_map, kmon_bind0, kmod_bind1, kmon_bind2).

Import Kleisli.Monad.Notations.
Import Kleisli.TraversableMonad.Notations.

#[local] Generalizable Variables T G ϕ.

(** * Categorical Traversable Monads from Kleisli Traversable Monads *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.
  Section operations.

    Context
      (T: Type -> Type)
      `{Return_T: Return T}
      `{Bindt_TT: Bindt T T}.

    #[export] Instance Dist_Bindt: ApplicativeDist T :=
      fun G _ _ _ A => bindt (G := G) (map (F := G) ret).
    #[export] Instance Join_Bindt: Join T :=
      fun A => bindt (G := fun A => A) id.
  End operations.
End DerivedOperations.

(** ** Derived Instances *)
(******************************************************************************)
Module DerivedInstances.

  Section with_monad.

    Context
      `{Kleisli.TraversableMonad.TraversableMonad T}.

    Import DerivedOperations.
    Import Kleisli.TraversableMonad.DerivedOperations.
    Import Kleisli.TraversableMonad.DerivedInstances.

    (** *** Monad instance *)
    (******************************************************************************)
    #[export] Instance Natural_Return: Natural (@ret T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        rewrite map_to_bindt.
        rewrite (ktm_bindt0 (T := T) (G := fun A => A)).
        reflexivity.
    Qed.

    #[export] Instance Natural_Join: Natural (@join T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Map_compose @Join_Bindt.
        rewrite <- bind_to_bindt.
        rewrite <- bind_to_bindt.
        unfold_compose_in_compose.
        rewrite map_bind.
        rewrite bind_map.
        reflexivity.
    Qed.

    Lemma mon_join_ret_T: forall A: Type,
        join ∘ ret (T := T) (A := T A) = @id (T A).
    Proof.
      intros. unfold_ops @Join_Bindt.
      unfold_compose_in_compose.
      rewrite <- bind_to_bindt.
      rewrite kmon_bind0.
      reflexivity.
    Qed.

    Lemma mon_join_map_ret_T: forall A: Type,
        join (T := T) ∘ map (F := T) ret = @id (T A).
    Proof.
      intros.
      unfold_ops @Join_Bindt.
      rewrite <- bind_to_bindt.
      unfold_compose_in_compose.
      rewrite bind_map.
      change (id ∘ ?g) with g.
      rewrite kmod_bind1.
      reflexivity.
    Qed.

    Lemma mon_join_join_T: forall A: Type,
        join (T := T) (A := A) ∘ join (T := T) =
          join ∘ map (F := T) (join (T := T)).
    Proof.
      intros.
      unfold_ops @Join_Bindt.
      rewrite <- bind_to_bindt.
      rewrite <- bind_to_bindt.
      unfold_compose_in_compose.
      rewrite kmon_bind2.
      rewrite bind_map.
      reflexivity.
    Qed.

    #[export] Instance CategoricalMonad_KleisliTraversableMonad:
      Categorical.Monad.Monad T :=
      {| mon_join_ret := mon_join_ret_T;
        mon_join_map_ret := mon_join_map_ret_T;
        mon_join_join := mon_join_join_T;
      |}.

    (** *** Traversable functor instance *)
    (******************************************************************************)
    Lemma dist_natural_T :
      forall (G: Type -> Type) (mapG: Map G) (pureG: Pure G) (multG: Mult G),
        Applicative G -> Natural (@dist T _ G mapG pureG multG).
    Proof.
      intros. constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Map_compose @Dist_Bindt.
        rewrite map_bindt.
        rewrite bindt_map.
        rewrite fun_map_map.
        rewrite fun_map_map.
        rewrite (natural (ϕ := @ret T _)).
        reflexivity.
    Qed.

    Lemma dist_morph_T: forall `{morphism: ApplicativeMorphism G1 G2 ϕ},
      forall A: Type, dist T G2 ∘ map (F := T) (ϕ A) = ϕ (T A) ∘ dist T G1.
    Proof.
      intros.
      assert (Applicative G1) by now inversion morphism.
      assert (Applicative G2) by now inversion morphism.
      unfold_ops @Dist_Bindt.
      rewrite bindt_map.
      rewrite ktm_morph.
      inversion morphism.
      rewrite (natural (ϕ := ϕ)).
      reflexivity.
    Qed.

    Lemma dist_unit_T: forall A: Type,
        dist T (fun A0: Type => A0) = @id (T A).
    Proof.
      intros.
      unfold_ops @Dist_Bindt.
      unfold_ops @Map_I.
      rewrite ktm_bindt1.
      reflexivity.
    Qed.

    Lemma dist_linear_T: forall `{Applicative G1} `{Applicative G2},
      forall A: Type, dist T (G1 ∘ G2) (A := A) = map (F := G1) (dist T G2) ∘ dist T G1.
    Proof.
      intros.
      unfold_ops @Dist_Bindt @Map_compose.
      rewrite ktm_bindt2.
      unfold kc6.
      rewrite fun_map_map.
      rewrite ktm_bindt0.
      reflexivity.
    Qed.

    #[export] Instance CategoricalTraversableFunctor_KleisliTraversableMonad:
      Categorical.TraversableFunctor.TraversableFunctor T :=
      {| dist_natural := dist_natural_T;
        dist_morph := @dist_morph_T;
        dist_unit := dist_unit_T;
        dist_linear := @dist_linear_T;
      |}.

    (** *** Traversable monad instance *)
    (******************************************************************************)
    Lemma trvmon_ret_T: forall (G: Type -> Type) (H3: Map G) (H4: Pure G) (H5: Mult G),
        Applicative G ->
        forall A: Type, dist T G ∘ ret (T := T) (A := G A) =
                     map (F := G) (ret (T := T)).
    Proof.
      intros. unfold_ops @Dist_Bindt.
      rewrite (ktm_bindt0 (T := T)); auto.
    Qed.

    Lemma trvmon_join_T: forall (G: Type -> Type) (H3: Map G) (H4: Pure G) (H5: Mult G),
        Applicative G -> forall A: Type,
          dist T G ∘ join (T := T) (A := G A) =
            map (F := G) (join (T := T)) ∘ dist T G ∘ map (F := T) (dist T G).
    Proof.
      intros. unfold_ops @Dist_Bindt @Join_Bindt.
      do 2 rewrite <- bind_to_bindt.
      unfold_compose_in_compose.
      rewrite bindt_bind.
      unfold compose at 5.
      rewrite bind_bindt.
      rewrite fun_map_map.
      rewrite bindt_map.
      rewrite bind_ret.
      rewrite fun_map_id.
      reflexivity.
    Qed.

    #[export] Instance CategoricalTraversableMonad_KleisliTraversableMonad
      : Categorical.TraversableMonad.TraversableMonad T :=
      {| trvmon_ret := trvmon_ret_T;
        trvmon_join := trvmon_join_T;
      |}.

  End with_monad.

End DerivedInstances.
