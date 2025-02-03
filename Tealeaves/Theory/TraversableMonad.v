From Tealeaves Require Export
  Classes.Kleisli.ContainerMonad
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableFunctor
  Classes.Coalgebraic.TraversableMonad
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Kleisli.Theory.TraversableMonad
  Theory.TraversableFunctor.

#[local] Generalizable Variables U T G A B C ϕ M.

Import Monoid.Notations.
Import Applicative.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import ContainerFunctor.Notations.
Import Subset.Notations.

Import Kleisli.TraversableMonad.DerivedInstances.

(** * Theory of Traversable Monads *)
(******************************************************************************)
Section traversable_monad_theory.

  Context
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Bindt_T_inst: Bindt T T}
    `{ToSubset_T_inst: ToSubset T}
    `{ToBatch_T_inst: ToBatch T}
    `{ToBatch6_T_inst: ToBatch6 T T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}
    `{! Compat_ToBatch6_Bindt T T}.

  Context
    `{Map_U_inst: Map U}
    `{Traverse_U_inst: Traverse U}
    `{Bind_U_inst: Bind T U}
    `{Bindt_U_inst: Bindt T U}
    `{ToSubset_U_inst: ToSubset U}
    `{ToBatch_U_inst: ToBatch U}
    `{ToBatch6_U_inst: ToBatch6 T U}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{! Compat_ToSubset_Traverse U}
    `{! Compat_ToBatch_Traverse U}
    `{! Compat_ToBatch6_Bindt T U}.


  Context
    `{Monad_inst: ! TraversableMonad T}
    `{Module_inst: ! TraversableRightPreModule T U}.

  (** ** Factoring operations through <<toBatch>> *)
  (******************************************************************************)
  Section runBatch.

    Lemma bindt_through_runBatch `{Applicative G} `(f : A -> G (T B)):
      bindt (U := U) f = runBatch f ∘ toBatch6 (B := B).
    Proof.
      intros.
      rewrite toBatch6_to_bindt.
      rewrite (ktm_morph (ϕ := @runBatch _ _ G _ _ _ f)).
      rewrite (runBatch_batch G).
      reflexivity.
    Qed.

    Corollary bind_through_runBatch `{Applicative G} `(f : A -> T B):
      bind (U := U) f = runBatch (G := fun A => A) f ∘ toBatch6.
    Proof.
      rewrite toBatch6_to_bindt.
      rewrite bind_to_bindt.
      rewrite bindt_through_runBatch.
      rewrite toBatch6_to_bindt.
      reflexivity.
    Qed.

    Corollary traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
      traverse (T := U) f = runBatch (map ret ∘ f) ∘ toBatch6.
    Proof.
      rewrite traverse_to_bindt.
      rewrite bindt_through_runBatch.
      reflexivity.
    Qed.

    Corollary map_through_runBatch `(f : A -> B) :
      map (F := U) f = runBatch (G := fun A => A) (ret (T := T) ∘ f) ∘ toBatch6.
    Proof.
      rewrite map_to_traverse.
      rewrite traverse_through_runBatch.
      reflexivity.
    Qed.

    Corollary id_through_runBatch : forall (A : Type),
        id (A := U A) = runBatch (G := fun A => A) (ret (T := T)) ∘ toBatch6.
    Proof.
      intros.
      rewrite <- (fun_map_id (F := U)).
      rewrite map_through_runBatch.
      reflexivity.
    Qed.

    (** ** Relating <<toBatch6>> with <<toBatch>> *)
    (******************************************************************************)
    Lemma toBatch6_toBatch
      {A B: Type} (t: U A):
      toBatch (A' := B) t = mapsnd_Batch (ret (T := T)) (toBatch6 t).
      Proof.
        intros.
        rewrite toBatch_to_traverse.
        rewrite traverse_to_bindt.
        rewrite toBatch6_to_bindt.
        compose near t on right.
        rewrite (ktm_morph (G1 := Batch A (T B)) (G2 := Batch A B)
                   (ϕ := fun C => mapsnd_Batch (ret (T := T)))).
        rewrite ret_dinatural.
        reflexivity.
      Qed.

  End runBatch.

  (** ** Naturality of <<toBatch6>> *)
  (******************************************************************************)
  Lemma toBatch6_mapfst
    {A B: Type} (f: A -> B) {C: Type}:
    toBatch6 (B := C) ∘ map (F := U) f =
      mapfst_Batch f ∘ toBatch6.
  Proof.
    intros.
    rewrite toBatch6_to_bindt.
    rewrite (bindt_map (G2 := Batch B (T C))).
    rewrite (bindt_through_runBatch (G := Batch B (T C))).
    rewrite toBatch6_to_bindt.
    rewrite (bindt_through_runBatch (G := Batch A (T C))).
    ext t.
    unfold compose.
    induction (toBatch6 t).
    - cbn. reflexivity.
    - rewrite runBatch_rw2.
      rewrite mapfst_Batch2.
      Set Keyed Unification.
      rewrite <- IHb; clear IHb.
      Unset Keyed Unification.
  Abort. (* TODO *)

  (** ** Respectfulness properties *)
  (******************************************************************************)
  Lemma bindt_respectful :
    forall (G: Type -> Type)
      `{Applicative G} `(f1: A -> G (T B)) `(f2: A -> G (T B)) (t: U A),
      (forall (a: A), a ∈ t -> f1 a = f2 a) ->
      bindt (U := U) f1 t = bindt f2 t.
  Proof.
    introv ? hyp.
    rewrite bindt_through_runBatch.
    rewrite bindt_through_runBatch.
    unfold element_of in hyp.
    rewrite (tosubset_through_runBatch2 A B) in hyp.
    unfold compose at 1 2.
    unfold compose at 1 in hyp.
    setoid_rewrite toBatch6_toBatch in hyp.
    rewrite <- runBatch_mapsnd in hyp.
    induction (toBatch6 t).
    - cbn in *.
      reflexivity.
    - cbn.
      rewrite IHb.
      + rewrite hyp.
        * reflexivity.
        * cbn. unfold compose.
          change (List.In ?a ?l) with (element_of (F := list) l a).
          unfold_ops @Monoid_op_list.
          autorewrite with tea_list.
          right.
          reflexivity.
      + intros. apply hyp. cbn.
        change (List.In ?a ?l) with (element_of (F := list) l a).
        unfold_ops @Monoid_op_list.
        autorewrite with tea_list.
        now left.
  Qed.

  Corollary bind_respectful :
    forall (A B: Type) (t: U A) (f1: A -> T B) `(f2: A -> T B),
      (forall (a: A), a ∈ t -> f1 a = f2 a) ->
      bind (U := U) f1 t = bind (U := U) f2 t.
  Proof.
    introv hyp.
    rewrite bind_to_bindt.
    rewrite bind_to_bindt.
    now apply (bindt_respectful (fun A => A) f1 f2).
  Qed.

  (** ** <<tosubset>> is a Homomorphism *)
  (******************************************************************************)
  #[export] Instance tosubset_hom2_Module:
    ParallelRightModuleHom T subset U subset
      (@tosubset T _)
      (@tosubset U _).
  Proof.
    constructor.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite tosubset_to_foldMap.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_bind.
    rewrite (foldMap_morphism (subset A) (subset B)
               (T := U)
               (ϕ := bind (foldMap (ret (T := subset)) ∘ f))).
    rewrite set_bind0.
    reflexivity.
  Qed.

End traversable_monad_theory.

(** ** Monad Homomorphisms *)
(******************************************************************************)
Section homomorphisms.

  Context
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Bindt_T_inst: Bindt T T}
    `{ToSubset_T_inst: ToSubset T}
    `{ToBatch_T_inst: ToBatch T}
    `{ToBatch6_T_inst: ToBatch6 T T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}
    `{! Compat_ToBatch6_Bindt T T}.

  Context
    `{Map_U_inst: Map U}
    `{Traverse_U_inst: Traverse U}
    `{Bind_U_inst: Bind T U}
    `{Bindt_U_inst: Bindt T U}
    `{ToSubset_U_inst: ToSubset U}
    `{ToBatch_U_inst: ToBatch U}
    `{ToBatch6_U_inst: ToBatch6 T U}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{! Compat_ToSubset_Traverse U}
    `{! Compat_ToBatch_Traverse U}
    `{! Compat_ToBatch6_Bindt T U}.


  Context
    `{Monad_inst: ! TraversableMonad T}
    `{Module_inst: ! TraversableRightPreModule T U}.

  #[export] Instance Monad_Hom_Tolist
    : MonadHom T list (@tolist T _) :=
    {| kmon_hom_ret := tolist_ret;
      kmon_hom_bind := tolist_bind;
    |}.

  #[export] Instance Monad_Hom_Toset
    : MonadHom T subset (@tosubset T _) :=
    {| kmon_hom_ret := tosubset_hom1;
      kmon_hom_bind := tosubset_hom2;
    |}.

  #[export] Instance ContainerMonad_Traversable:
    ContainerMonad T.
  Proof.
    constructor; try typeclasses eauto.
    intros. now apply bind_respectful.
  Qed.

  #[export] Instance ContainerModule_Traversable:
    ContainerRightModule T U :=
        {| contmod_pointwise := bind_respectful;
           contmod_hom := tosubset_hom2_Module;
        |}.

End homomorphisms.
