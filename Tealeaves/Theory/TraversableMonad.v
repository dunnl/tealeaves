From Tealeaves Require Export
  Classes.Kleisli.TraversableMonad
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Theory.TraversableFunctor
  Functors.Subset.

#[local] Generalizable Variables T G A B C ϕ M.

Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import ContainerFunctor.Notations.
Import Subset.Notations.

(* Halfway explicit *)
#[local] Arguments bindt (U T)%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bind (U T)%function_scope {Bind} (A B)%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} A%type_scope _.

Section traversable_monad_theory.

  Context
    (T : Type -> Type)
    `{TraversableMonadFull T}.

  (** * <<foldMap>> on monads *)
  (******************************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M} : forall `(g : B -> M) `(f : A -> G (T B)),
      map G (T B) M (foldMap T g) ∘ bindt T T G A B f =
        foldMap T (map G (T B) M (foldMap T g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt T G (const M) A B False).
    rewrite 2(ktmf_traverse_to_bindt _).
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
      foldMap T g ∘ bind T T A B f =
        foldMap T (foldMap T g ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bind T (const M) A B False).
    rewrite (ktmf_traverse_to_bindt (T := T) (const M)).
    rewrite (ktmf_traverse_to_bindt (T := T) (const M)).
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M} : forall `(f : A -> M),
      foldMap T f ∘ ret T A = f.
  Proof.
    intros. unfold foldMap.
    rewrite (ktmf_traverse_to_bindt (const M)).
    rewrite (ktm_bindt0 (T := T) (const M) A _).
    reflexivity.
  Qed.

  (** * <<Tolist>> and <<element_of>> *)
  (******************************************************************************)
  Lemma tolist_ret : forall (A : Type),
      tolist T ∘ ret T A = ret list A.
  Proof.
    intros.
    unfold_ops @Tolist_Traverse.
    now rewrite (foldMap_ret).
  Qed.

  Lemma tolist_bind : forall (A B : Type) (f : A -> T B),
      tolist T ∘ bind T T A B f = bind list list A B (tolist T ∘ f) ∘ tolist T.
  Proof.
    intros.
      unfold_ops @Tolist_Traverse.
      rewrite (foldMap_bind (ret list B) f).
      rewrite (foldMap_morphism T (list A) (list B)).
      rewrite (kmon_bind0 (T := list)).
      reflexivity.
  Qed.

  #[export] Instance Monad_Hom_Tolist : MonadHom T list (@tolist T _) :=
    {| kmon_hom_ret := tolist_ret;
      kmon_hom_bind := tolist_bind;
    |}.

  Lemma element_of_hom1 : forall (A : Type),
      element_of T ∘ ret T A = ret subset A.
  Proof.
    intros.
    unfold_ops @Elements_Tolist.
    unfold_ops @Tolist_Traverse.
    reassociate -> on left.
    rewrite (foldMap_ret).
    unfold compose; ext a.
    apply elements_list_ret.
  Qed.

  Lemma element_of_hom2 : forall (A B : Type) (f : A -> T B),
      element_of T ∘ bind T T A B f = bind subset _ _ _ (element_of T ∘ f) ∘ element_of T.
  Proof.
    intros.
    unfold_ops @Elements_Tolist.
    reassociate -> on left.
    rewrite (tolist_bind).
  Admitted.

  #[export] Instance Monad_Hom_Toset : MonadHom T subset (@element_of T _) :=
    {| kmon_hom_ret := element_of_hom1;
      kmon_hom_bind := element_of_hom2;
    |}.

(** * Characterizing <<∈>> *)
(******************************************************************************)
  Theorem in_ret_iff :
    forall (A : Type) (a1 a2 : A), a1 ∈ ret T A a2 <-> a1 = a2.
  Proof.
    intros.
    compose near a2 on left.
    rewrite (kmon_hom_ret (ϕ := @element_of T _)).
    easy.
  Qed.

  Theorem in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T T A B f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros. compose near t on left.
    rewrite (kmon_hom_bind (ϕ := @element_of T _)).
    reflexivity.
  Qed.

  Corollary in_map_iff :
    forall `(f : A -> B) (t : T A) (b : B),
      b ∈ map T A B f t <-> exists a, a ∈ t /\ f a = b.
  Proof.
    intros.
    rewrite (in_map_iff T).
    reflexivity.
  Qed.

  (** * Respectfulness properties *)
  (******************************************************************************)
  Lemma bindt_respectful : forall (G : Type -> Type)
                             `{Applicative G} `(f1 : A -> G (T B)) `(f2 : A -> G (T B)) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> bindt T T G A B f1 t = bindt T T G A B f2 t.
  Proof.
    introv ? hyp. do 2 (rewrite (bindt_to_runBatch T); auto).
    unfold element_of, Elements_Tolist, tolist, Tolist_Traverse in hyp.
    rewrite (foldMap_to_runBatch2 T A B) in hyp.
    unfold compose in *.
    setoid_rewrite (toBatchM_toBatch T) in hyp.
    rewrite <- (runBatch_mapsnd) in hyp.
    change (map (const (list A)) _ _ _ ∘ ?x) with x in hyp.
    induction (toBatchM T A B t).
    cbn in *.
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros.
        apply hyp. admit.
      + apply hyp. cbn. admit.
  Admitted.

End traversable_monad_theory.
