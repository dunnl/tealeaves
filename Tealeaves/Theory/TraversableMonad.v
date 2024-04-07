From Tealeaves Require Export
  Classes.Kleisli.ContainerMonad
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Theory.TraversableFunctor
  Classes.Kleisli.TraversableMonad
  Functors.Subset.

#[local] Generalizable Variables U T G A B C ϕ M.

Import Monoid.Notations.
Import Applicative.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import ContainerFunctor.Notations.
Import Subset.Notations.

#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

Section traversable_monad_theory.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Bindt_T_inst : Bindt T T}
      `{! Compat_Map_Bindt T T}
      `{! Compat_Traverse_Bindt T T}
      `{! Compat_Bind_Bindt T T}
      `{Map_U_inst : Map U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Bindt_U_inst : Bindt T U}
      `{! Compat_Map_Bindt T U}
      `{! Compat_Traverse_Bindt T U}
      `{! Compat_Bind_Bindt T U}
      `{Monad_inst : ! TraversableMonad T}
      `{Module_inst : ! TraversableRightPreModule T U}
      `{ToSubset_T_inst: ToSubset T}
      `{ToSubset_U_inst: ToSubset U}
      `{! Compat_ToSubset_Traverse T}
      `{! Compat_ToSubset_Traverse U}.

  (** * <<foldMap>> on monads *)
  (******************************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M} :
    forall `(g : B -> M) `(f : A -> G (T B)),
      map (foldMap g) ∘ bindt (U := U) f =
        foldMap (T := U) (map (foldMap g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt (G1 := G) (G2 := const M) A B False).
    rewrite 2(traverse_to_bindt).
    fequal.
    - ext A' B' f'.
      unfold Map_compose, Map_const.
      unfold const in *.
      unfold map at 2.
      now rewrite (fun_map_id (F := G)).
    - ext A' B' [a b].
      unfold Mult_compose, Mult_const.
      unfold compose in *.
      unfold const in *.
      cbn.
      reflexivity.
  Qed.

  Lemma foldMap_bind `{Monoid M} : forall `(g : B -> M) `(f : A -> T B),
      foldMap g ∘ bind (U := U) f = foldMap (foldMap g ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bind (G2 := const M) A B False).
    rewrite traverse_to_bindt.
    rewrite traverse_to_bindt.
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M} : forall `(f : A -> M),
      foldMap f ∘ ret T = f.
  Proof.
    intros. unfold foldMap.
    rewrite traverse_to_bindt.
    rewrite (ktm_bindt0 (G := const M) A False).
    reflexivity.
  Qed.

  (** * <<Tolist>> and <<element_of>> *)
  (******************************************************************************)
  Lemma tolist_ret : forall (A : Type),
      tolist ∘ ret T = ret list (A := A).
  Proof.
    intros.
    unfold_ops @Tolist_Traverse.
    now rewrite foldMap_ret.
  Qed.

  Lemma tolist_bind : forall (A B : Type) (f : A -> T B),
      tolist ∘ bind f = bind (tolist ∘ f) ∘ tolist.
  Proof.
    intros.
    unfold_ops @Tolist_Traverse.
    rewrite (foldMap_bind (ret list) f).
    rewrite (foldMap_morphism (list A) (list B)).
    rewrite (kmon_bind0 (T := list)).
    reflexivity.
  Qed.

  Lemma element_of_hom1 : forall (A : Type),
      element_of ∘ ret T = ret subset (A := A).
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite foldMap_ret.
    reflexivity.
  Qed.

  Lemma element_of_hom2 : forall (A B : Type) (f : A -> T B),
      element_of ∘ bind (U := U) f = bind (element_of ∘ f) ∘ element_of.
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite foldMap_bind.
    rewrite (element_of_to_foldMap (T := U)).
    rewrite (foldMap_morphism (subset A) (subset B)).
    rewrite (kmon_bind0 (T := subset)).
    rewrite element_of_to_foldMap.
    reflexivity.
  Qed.

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
    rewrite (element_through_runBatch2 A B) in hyp.
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

  #[local] Instance element_of_hom2_Module:
    ParallelRightModuleHom T subset U subset
      (@element_of T _)
      (@element_of U _).
  Proof.
    constructor.
    intros.
    rewrite element_of_to_foldMap.
    rewrite element_of_to_foldMap.
    rewrite element_of_to_foldMap.
    rewrite foldMap_bind.
    rewrite (foldMap_morphism (subset A) (subset B)
                              (ϕ := bind (foldMap (ret subset) ∘ f))).
    rewrite set_bind0.
    reflexivity.
  Qed.

End traversable_monad_theory.

Section instances.

    Context
    `{Return_inst : Return T}
    `{Map_T_inst : Map T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Bindt_T_inst : Bindt T T}
    `{ToSubset_T_inst: ToSubset T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! Compat_ToSubset_Traverse T}
    `{! TraversableMonad T}
    `{Map_U_inst : Map U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Bindt_U_inst : Bindt T U}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{ToSubset_U_inst: ToSubset U}
    `{! Compat_ToSubset_Traverse U}
    `{Module_inst : ! TraversableRightModule T U}.

    #[export] Instance Monad_Hom_Tolist
      : MonadHom T list (@tolist T _) :=
      {| kmon_hom_ret := tolist_ret;
        kmon_hom_bind := tolist_bind;
      |}.

    #[export] Instance Monad_Hom_Toset
      : MonadHom T subset (@element_of T _) :=
      {| kmon_hom_ret := element_of_hom1;
        kmon_hom_bind := element_of_hom2;
      |}.

    #[export] Instance ContainerMonad_Traversable:
      ContainerMonad T :=
      {| contm_pointwise := bind_respectful;
      |}.

    #[export] Instance ContainerModule_Traversable:
      ContainerRightModule T U :=
      {| contmod_pointwise := bind_respectful;
        contmod_hom := element_of_hom2_Module;
      |}.

End instances.
