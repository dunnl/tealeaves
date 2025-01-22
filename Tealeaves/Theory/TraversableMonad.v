From Tealeaves Require Export
  Classes.Kleisli.ContainerMonad
  Classes.Kleisli.TraversableMonad
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

#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

(** * Theory of Traversable Monads *)
(******************************************************************************)
Section traversable_monad_theory.

  Context
    `{ret_inst : Return T}
    `{Map_T_inst : Map T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Bindt_T_inst : Bindt T T}
    `{ToSubset_T_inst: ToSubset T}
    `{ToBatch_T_inst: ToBatch T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Context
    `{Map_U_inst : Map U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Bindt_U_inst : Bindt T U}
    `{ToSubset_U_inst: ToSubset U}
    `{ToBatch_U_inst: ToBatch U}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{! Compat_ToSubset_Traverse U}
    `{! Compat_ToBatch_Traverse U}.

  Context
    `{Monad_inst : ! TraversableMonad T}
      `{Module_inst : ! TraversableRightPreModule T U}.

  (** ** Respectfulness properties *)
  (******************************************************************************)
  Lemma bindt_respectful :
    forall (G : Type -> Type)
      `{Applicative G} `(f1 : A -> G (T B)) `(f2 : A -> G (T B)) (t : U A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) ->
      bindt (U := U) f1 t = bindt f2 t.
  Proof.
    introv ? hyp.
    rewrite bindt_through_runBatch.
    rewrite bindt_through_runBatch.
    unfold element_of in hyp.
    rewrite (tosubset_through_runBatch2 A B) in hyp.
    unfold compose at 1 2.
    unfold compose at 1 in hyp.
    setoid_rewrite toBatch3_toBatch in hyp.
    rewrite <- runBatch_mapsnd in hyp.
    induction (toBatch3 t).
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
    forall (A B : Type) (t : U A) (f1 : A -> T B) `(f2 : A -> T B),
      (forall (a : A), a ∈ t -> f1 a = f2 a) ->
      bind (U := U) f1 t = bind (U := U) f2 t.
  Proof.
    introv hyp.
    rewrite bind_to_bindt.
    rewrite bind_to_bindt.
    now apply (bindt_respectful (fun A => A) f1 f2).
  Qed.

  #[local] Instance tosubset_hom2_Module:
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
               (ϕ := bind (foldMap (ret subset) ∘ f))).
    rewrite set_bind0.
    reflexivity.
  Qed.

End traversable_monad_theory.

Section instances.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Bindt_T_inst : Bindt T T}
      `{ToSubset_T_inst: ToSubset T}
      `{ToBatch_T_inst: ToBatch T}
      `{! Compat_Map_Bindt T T}
      `{! Compat_Traverse_Bindt T T}
      `{! Compat_Bind_Bindt T T}
      `{! Compat_ToSubset_Traverse T}
      `{! Compat_ToBatch_Traverse T}.

  Context
      `{Map_U_inst : Map U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Bindt_U_inst : Bindt T U}
      `{ToSubset_U_inst: ToSubset U}
      `{ToBatch_U_inst: ToBatch U}
      `{! Compat_Map_Bindt T U}
      `{! Compat_Traverse_Bindt T U}
      `{! Compat_Bind_Bindt T U}
      `{! Compat_ToSubset_Traverse U}
      `{! Compat_ToBatch_Traverse U}.

  Context
    `{Monad_inst : ! TraversableMonad T}
      `{Module_inst : ! TraversableRightPreModule T U}.


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
      ContainerMonad T :=
      {| contm_pointwise := bind_respectful;
      |}.

    #[export] Instance ContainerModule_Traversable:
      ContainerRightModule T U :=
      {| contmod_pointwise := bind_respectful;
        contmod_hom := tosubset_hom2_Module;
      |}.

End instances.
