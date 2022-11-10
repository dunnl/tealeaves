From Tealeaves Require Export
  Functors.List
  Classes.Monoid
  Classes.Algebraic.Traversable.Monad
  Classes.Kleisli.Traversable.Monad
  Theory.Algebraic.Traversable.Monad.ToKleisli
  Theory.Kleisli.Traversable.Monad.DerivedInstances.

Import Classes.Algebraic.Setlike.Functor.Notations.
Import List.ListNotations.
#[local] Open Scope list_scope.

(** ** [list]/[list] right module *)
(******************************************************************************)
#[export] Instance Bindt_list : Bindt list _
  := ToKleisli.Operation.Bindt_alg list.
#[export] Instance Bind_list : Bind list list
  := DerivedInstances.Operations.Bind_Bindt list.
#[export] Instance KleisliTravMonad_list : Kleisli.Traversable.Monad.Monad list
  := ToKleisli.Instance.TravMon_ToKleisli list.
(*
#[export] Instance KleisliMonad_list : Kleisli.Monad.Monad list
  := ToKleisli.Instance.toKleisli list.
*)

(** ** Rewriting lemmas for <<bindt>> *)
(******************************************************************************)
Section bindt_rewriting_lemmas.

  Context (A B : Type) (G : Type -> Type) `{Applicative G}.

  Lemma bindt_list_nil : forall (f : A -> G (list B)),
      bindt list G f (@nil A) = pure G (@nil B).
  Proof.
    intros. unfold_ops @Bindt_list @Operation.Bindt_alg.
    unfold compose. simpl_list.
    rewrite (app_pure_natural G).
    reflexivity.
  Qed.
  
  Lemma bindt_list_one : forall (f : A -> G (list B)) (a : A),
      bindt list G f (ret list a) = f a.
  Proof.
    intros.
    unfold_ops @Bindt_list @Operation.Bindt_alg.
    compose near a on left.
    reassociate -> near (ret list).
    rewrite (natural (G := list) (ϕ := @ret list _)).
    unfold_ops @Fmap_I.
    reassociate <-.
    reassociate -> near (ret list).
    rewrite trvmon_ret_list.
    rewrite (fun_fmap_fmap G).
    #[local] Set Keyed Unification.
    rewrite (join_ret_list).
    #[local] Unset Keyed Unification.
    rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

  Import Applicative.Notations.

  Lemma bindt_list_cons : forall (f : A -> G (list B)) (a : A) (l : list A),
      bindt list G f (cons a l) =
        pure G (@app _) <⋆> f a <⋆> bindt list G f l.
  Proof.
    intros. unfold_ops @Bindt_list @Operation.Bindt_alg.
    unfold compose.
    rewrite (fmap_list_cons).
    rewrite dist_list_cons_1.
    do 2 rewrite ap6.
    rewrite (app_pure_natural G).
    assert (lemma : compose (join list) ∘ cons (A:=list B) =
                      (precompose (join list) ∘ (@app B))).
    { ext l1 lrest. unfold compose.
      rewrite join_list_cons.
      reflexivity. }
    Set Keyed Unification.
    rewrite lemma.
    Unset Keyed Unification.
    rewrite <- (fmap_to_ap).
    rewrite <- (fun_fmap_fmap G).
    unfold compose.
    rewrite ap7.
    rewrite (fmap_to_ap).
    reflexivity.
  Qed.
  
  Lemma bindt_list_app : forall (f : A -> G (list B)) (l1 l2 : list A),
      bindt list G f (l1 ++ l2) =
        pure G (@app B) <⋆> (bindt list G f l1) <⋆> (bindt list G f l2).
  Proof.
    intros. unfold_ops @Bindt_list @Operation.Bindt_alg.
    unfold compose.
    rewrite (fmap_list_app).
    rewrite (dist_list_app).
    do 2 rewrite ap6.
    rewrite (app_pure_natural G).
    assert (lemma : compose (join list) ∘ app (A:=list B) =
              (precompose (join list) ∘ (@app B) ∘ (join list))).
    { ext x y. unfold compose.
      rewrite join_list_app.
      reflexivity. }
    Set Keyed Unification.        
    rewrite lemma.
    Unset Keyed Unification.
    rewrite <- (fmap_to_ap).
    reassociate -> on left.
    rewrite <- (fun_fmap_fmap G).
    unfold compose at 1.
    rewrite ap7.
    rewrite <- (fun_fmap_fmap G).
    unfold compose at 1.
    rewrite fmap_to_ap.
    reflexivity.
  Qed.
  
End bindt_rewriting_lemmas.

Require Classes.Algebraic.Setlike.Functor.
Require Theory.Kleisli.Traversable.Functor.Container.

(** ** Rewriting lemmas for <<foldMapd>> *)
(******************************************************************************)
Section foldMap_rewriting_lemmas.
  
  Import Classes.Algebraic.Setlike.Functor.
  Import Theory.Kleisli.Traversable.Functor.Container.
  Import Traversable.Monad.DerivedInstances.Operations.
  Import Monoid.Notations.

  Context (A : Type) (M : Type) `{Monoid M}.

  Lemma foldMap_list_nil : forall (f : A -> M),
      foldMap list f (@nil A) = Ƶ.
  Proof.
    reflexivity.
  Qed.
  
  Lemma foldMap_list_one : forall (f : A -> M) (a : A),
      foldMap list f (ret list a) = f a.
  Proof.
    intros. cbv. simpl_monoid.
    reflexivity.
  Qed.
  
  Lemma foldMap_list_cons : forall (f : A -> M) (a : A) (l : list A),
      foldMap list f (cons a l) = f a ● foldMap list f l.
  Proof.
    cbv. do 2 simpl_monoid.
    reflexivity.
  Qed.
  
  Lemma foldMap_list_app : forall (f : A -> M) (l1 l2 : list A),
      foldMap list f (l1 ++ l2) = foldMap list f l1 ● foldMap list f l2.
  Proof.
    intros. unfold foldMap, traverse, Traverse_Bindt.
    rewrite (bindt_list_app); try typeclasses eauto.
    cbv. do 2 simpl_monoid.
    reflexivity.
  Qed.
  
  Lemma Toset_list_spec: Toset_list = @Toset_Traverse list _.
  Proof.
    unfold_ops @Toset_list @Toset_Traverse.
    ext A' l a. 
    unfold foldMap, traverse, Traverse_Bindt.
    induction l.
    - reflexivity.
    - rewrite bindt_list_cons; try typeclasses eauto.
      cbn. unfold_ops @Pure_const.
      simpl_monoid.
      unfold_ops @Monoid_op_set.
      unfold set_add.
      Set Keyed Unification.
      rewrite <- IHl.
      Unset Keyed Unification.
      reflexivity.
  Qed.
  
End foldMap_rewriting_lemmas.

(** ** Rewriting lemmas for <<bind>> *)
(******************************************************************************)
Section bind_rewriting_lemmas.

  Context
    (A B : Type)
    (f : A -> list B).

  Lemma bind_list_nil : bind list f [] = [].
  Proof.
    reflexivity.
  Qed.

  Lemma bind_list_one : forall x, bind list f [ x ] = f x.
  Proof.
    intros. unfold_ops @Bind_list @Operations.Bind_Bindt.
    unfold bindt, Bindt_list, Operation.Bindt_alg.
    rewrite dist_unit_list.
    unfold compose. cbn.
    now rewrite List.app_nil_r.
  Qed.

  Lemma bind_list_cons : forall (x : A) (xs : list A),
      bind list f (x :: xs) = f x ++ bind list f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_list_app : forall (l1 l2 : list A),
      bind list f (l1 ++ l2) = bind list f l1 ++ bind list f l2.
  Proof.
    intros. unfold_ops @Bind_list.
    unfold_ops @Bind_list @Operations.Bind_Bindt.
    unfold bindt, Bindt_list, Operation.Bindt_alg.
    rewrite dist_unit_list.
    unfold id, compose.
    unfold_ops @Fmap_I.
    now autorewrite with tea_list.
  Qed.

End bind_rewriting_lemmas.

#[export] Hint Rewrite bind_list_nil bind_list_one bind_list_cons bind_list_app :
  tea_list.

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind {A B f} : Monoid_Morphism (bind list f) :=
  {| monmor_unit := bind_list_nil A B f;
     monmor_op := bind_list_app A B f;
  |}.

(** ** Other rewriting lemmas for <<bind>> *)
(******************************************************************************)
Section bind_rewriting_lemmas.

  Context
    (A B : Type)
    (f : A -> list B).

  Lemma in_bind_list_iff : forall (b : B) (l : list A),
      b ∈ bind list f l <-> exists a : A, a ∈ l /\ b ∈ f a.
  Proof.
    intros. induction l.
    - cbn. intuition. now destruct H.
    - destruct IHl as [IHl1 IHl2]. simpl_list. split.
      + intros [H | H].
        exists a. split. left; easy. easy.
        specialize (IHl1 H). destruct IHl1 as [a' rest].
        exists a'. split. right. easy. easy.
      + intros [a' [rest1 rest2]]. destruct rest1 as [rest1 | rest1].
        left. inverts rest1. assumption.
        right. apply IHl2. exists a'. easy.
  Qed.
  
End bind_rewriting_lemmas.
