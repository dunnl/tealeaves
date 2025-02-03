From Tealeaves Require Export
  Classes.Kleisli.ContainerMonad
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Kleisli.Theory.ContainerMonad.

Import Monoid.Notations.
Import Applicative.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import ContainerFunctor.Notations.
Import Subset.Notations.

#[local] Generalizable Variables U T G A B C ϕ M.
#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

Import Kleisli.TraversableMonad.DerivedInstances.

(** * Theory of Traversable Monads *)
(**********************************************************************)
Section traversable_monad_theory.

  Context
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Bindt_T_inst: Bindt T T}
    `{ToSubset_T_inst: ToSubset T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! Compat_ToSubset_Traverse T}.

  Context
    `{Map_U_inst: Map U}
    `{Traverse_U_inst: Traverse U}
    `{Bind_U_inst: Bind T U}
    `{Bindt_U_inst: Bindt T U}
    `{ToSubset_U_inst: ToSubset U}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{! Compat_ToSubset_Traverse U}.

  Context
    `{Monad_inst: ! TraversableMonad T}
    `{Module_inst: ! TraversableRightPreModule T U}.

  (** ** <<foldMap>> on Traversble Monads *)
  (********************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M}:
    forall `(g: B -> M) `(f: A -> G (T B)),
      map (foldMap g) ∘ bindt (U := U) f =
        foldMap (T := U) (map (foldMap g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt (G1 := G) (G2 := const M) A B False).
    rewrite 2(traverse_to_bindt).
    reassociate <- on right.
    unfold_ops @Map_const.
    change (fun (x: ?A) => x) with (@id A).
    do 2 change (id ∘ ?f) with f.
    fequal.
    - ext A' B' f'.
      unfold Map_compose, Map_const, const.
      unfold map at 2.
      now rewrite (fun_map_id (F := G)).
    - ext A' B' [a b].
      unfold Mult_compose, Mult_const.
      unfold compose in *.
      unfold const in *.
      cbn.
      reflexivity.
  Qed.

  Lemma foldMap_bind `{Monoid M}:
    forall `(g: B -> M) `(f: A -> T B),
      foldMap g ∘ bind (U := U) f = foldMap (foldMap g ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bind (G2 := const M) A B False).
    rewrite traverse_to_bindt.
    rewrite traverse_to_bindt.
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M}: forall `(f: A -> M),
      foldMap f ∘ ret T = f.
  Proof.
    intros. unfold foldMap.
    rewrite traverse_to_bindt.
    rewrite (ktm_bindt0 (G := const M) A False).
    reflexivity.
  Qed.

  (** ** <<tolist>> on Traversable Monads *)
  (********************************************************************)
  Lemma tolist_ret: forall (A: Type),
      tolist ∘ ret T = ret list (A := A).
  Proof.
    intros.
    unfold_ops @Tolist_Traverse.
    now rewrite foldMap_ret.
  Qed.

  Lemma tolist_bind: forall (A B: Type) (f: A -> T B),
      tolist ∘ bind f = bind (tolist ∘ f) ∘ tolist.
  Proof.
    intros.
    unfold_ops @Tolist_Traverse.
    rewrite (foldMap_bind (ret list) f).
    rewrite (foldMap_morphism (list A) (list B)).
    rewrite (kmon_bind0 (T := list)).
    reflexivity.
  Qed.

  (** ** <<tosubset>> on Traversable Monads *)
  (********************************************************************)
  Lemma tosubset_hom1: forall (A: Type),
      tosubset ∘ ret T = ret subset (A := A).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_ret.
    reflexivity.
  Qed.

  Lemma tosubset_hom2: forall (A B: Type) (f: A -> T B),
      tosubset ∘ bind (U := U) f = bind (tosubset ∘ f) ∘ tosubset.
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_bind.
    rewrite (tosubset_to_foldMap (T := U)).
    rewrite (foldMap_morphism (subset A) (subset B)).
    rewrite (kmon_bind0 (T := subset)).
    rewrite tosubset_to_foldMap.
    reflexivity.
  Qed.

  (** ** <<element_of>> on Traversable Monads *)
  (********************************************************************)
  Lemma element_of_hom1: forall (A: Type) (a: A),
      element_of a ∘ ret T = {{a}}.
  Proof.
    intros.
    ext a'.
    unfold element_of, compose.
    compose near a' on left.
    rewrite tosubset_hom1.
    cbv.
    now propext.
  Qed.

  Lemma element_of_hom2: forall (A B: Type) (f: A -> T B) (b: B),
      element_of b ∘ bind (U := U) f =
        foldMap (op := Monoid_op_or) (unit := Monoid_unit_false)
          (foldMap (op := Monoid_op_or) (unit := Monoid_unit_false)
             {{b}} ∘ f).
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite foldMap_bind.
    reflexivity.
  Qed.

End traversable_monad_theory.
