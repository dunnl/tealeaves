From Tealeaves Require Export
  Classes.Kleisli.TraversableMonad
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Theory.TraversableFunctor
  Functors.Subset.

#[local] Generalizable Variables T G A B C ϕ M.

Import Monoid.Notations.
Import Applicative.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import ContainerFunctor.Notations.
Import Subset.Notations.

#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

Section traversable_monad_theory.

  Context
    `{TraversableMonadFull T}.

  (** * <<foldMap>> on monads *)
  (******************************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M} :
    forall `(g : B -> M) `(f : A -> G (T B)),
      map (foldMap g) ∘ bindt f = foldMap (map (foldMap g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt (G1 := G) (G2 := const M) A B False).
    rewrite 2(ktmf_traverse_to_bindt).
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
      foldMap g ∘ bind f = foldMap (foldMap g ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bind (G2 := const M) A B False).
    rewrite (ktmf_traverse_to_bindt (T := T)).
    rewrite (ktmf_traverse_to_bindt (T := T)).
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M} : forall `(f : A -> M),
      foldMap f ∘ ret T = f.
  Proof.
    intros. unfold foldMap.
    rewrite (ktmf_traverse_to_bindt (G := const M)).
    rewrite (ktm_bindt0 (T := T) (G := const M) A _).
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

  #[export] Instance Monad_Hom_Tolist : MonadHom T list (@tolist T _) :=
    {| kmon_hom_ret := tolist_ret;
      kmon_hom_bind := tolist_bind;
    |}.

  Lemma element_of_hom1 : forall (A : Type),
      element_of ∘ ret T = ret subset (A := A).
  Proof.
    intros.
    unfold_ops @Elements_Tolist.
    unfold_ops @Tolist_Traverse.
    reassociate -> on left.
    rewrite foldMap_ret.
    apply element_of_list_hom1.
  Qed.

  Lemma element_of_hom2 : forall (A B : Type) (f : A -> T B),
      element_of ∘ bind f = bind (element_of ∘ f) ∘ element_of.
  Proof.
    intros.
    unfold_ops @Elements_Tolist.
    reassociate -> on left.
    rewrite tolist_bind.
    reassociate <- on right.
    reassociate -> near f.
    rewrite <- element_of_list_hom2.
    reflexivity.
  Qed.

  #[export] Instance Monad_Hom_Toset : MonadHom T subset (@element_of T _) :=
    {| kmon_hom_ret := element_of_hom1;
       kmon_hom_bind := element_of_hom2;
    |}.

  (** * Characterizing <<∈>> *)
  (******************************************************************************)
  Theorem in_ret_iff :
    forall (A : Type) (a1 a2 : A), a1 ∈ ret T a2 <-> a1 = a2.
  Proof.
    intros.
    compose near a2 on left.
    rewrite (kmon_hom_ret (ϕ := @element_of T _)).
    easy.
  Qed.

  Theorem in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros. compose near t on left.
    rewrite (kmon_hom_bind (ϕ := @element_of T _)).
    reflexivity.
  Qed.

  Corollary in_map_iff :
    forall `(f : A -> B) (t : T A) (b : B),
      b ∈ map f t <-> exists a, a ∈ t /\ f a = b.
  Proof.
    intros.
    rewrite in_map_iff.
    reflexivity.
  Qed.

  (** * Respectfulness properties *)
  (******************************************************************************)
  Lemma bindt_respectful :
    forall (G : Type -> Type)
      `{Applicative G} `(f1 : A -> G (T B)) `(f2 : A -> G (T B)) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> bindt f1 t = bindt f2 t.
  Proof.
    introv ? hyp.
    rewrite bindt_through_runBatch.
    rewrite bindt_through_runBatch.
    unfold compose at 1 2.
    unfold element_of, Elements_Tolist, tolist, Tolist_Traverse in hyp.
    unfold compose at 1 in hyp.
    rewrite (foldMap_through_runBatch2 A B) in hyp.
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
          autorewrite with tea_list. right.
          cbv. now left.
      + intros. apply hyp. cbn.
        change (List.In ?a ?l) with (element_of (F := list) l a).
        unfold_ops @Monoid_op_list.
        autorewrite with tea_list.
        now left.
  Qed.

  Corollary bind_respectful :
    forall `(f1 : A -> T B) `(f2 : A -> T B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> bind f1 t = bind f2 t.
  Proof.
    introv hyp.
    rewrite ktmf_bind_to_bindt.
    now eapply (bindt_respectful (fun A => A)).
  Qed.
  
  Corollary bind_respectful_map :
    forall `(f1 : A -> T B) `(f2 : A -> B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = ret T (f2 a)) -> bind f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite ktmf_map_to_bind.
    now eapply bind_respectful.
  Qed.

  Corollary bind_respectful_id :
    forall `(f1 : A -> T A) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = ret T a) -> bind f1 t = t.
  Proof.
    introv hyp.
    change t with (id t) at 2.
    rewrite <- bind_id.
    now apply bind_respectful.
  Qed.

End traversable_monad_theory.
