From Tealeaves Require Export
     Singlesorted.Classes.ListableModule
      Singlesorted.Classes.TraversableMonad.

Import Functor.Notations.
Import SetlikeFunctor.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

(** * Traversable right modules *)
(******************************************************************************)
Section TraversableModule.

  Context
    (F T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T}  `{Dist T}
    `{Fmap F} `{RightAction F T} `{Dist F}.

  Class TraversableModule :=
    { trvmod_module :> RightModule F T;
      trvmod_functor :> TraversableFunctor F;
      trvmod_monad :> TraversableMonad T;
      trvmod_action : forall `{Applicative G},
          `(dist F G ∘ right_action F =
            fmap G (right_action F) ∘ dist (F ∘ T) G (A := A));
    }.

End TraversableModule.

(** ** Traversable monads are traversable modules *)
(******************************************************************************)
Section module_of_monad.

  Context
    (T : Type -> Type).

  Existing Instance RightAction_Join.
  Existing Instance RightModule_Monad.

  Program Instance TraversableModule_Monad `{TraversableMonad T} :
    TraversableModule T T :=
    {| trvmod_action := fun _ _ _ _ _ => trvmon_join T;
    |}.

End module_of_monad.

(** ** Traversable modules are closed under composition with functors *)
(******************************************************************************)
Section TraversableModule_compose.

  Context
    `{TraversableFunctor F2}
    `{TraversableModule F1 T}.

  Instance: RightModule (F2 ∘ F1) T := RightModule_compose.

  #[local] Set Keyed Unification.
  Theorem dist_right_action_compose `{Applicative G} {A} :
    dist (F2 ∘ F1) G ∘ fmap F2 (right_action F1 (A := G A)) =
    fmap G (fmap F2 (right_action F1)) ∘ dist (F2 ∘ F1 ∘ T) G.
  Proof.
    unfold_ops @Dist_compose. unfold dist at 3.
    unfold_ops @Fmap_compose. do 2 reassociate <-.
    reassociate -> on right. rewrite (fun_fmap_fmap F2).
    reassociate -> on left. rewrite (fun_fmap_fmap F2).
    rewrite (trvmod_action F1 T). rewrite <- (fun_fmap_fmap F2).
    reassociate <- on left. unfold_ops @Dist_compose. fequal.
    change (fmap G (fmap F2 ?f)) with (fmap (G ∘ F2) f).
    now rewrite (dist_natural F2).
  Qed.

  Instance TraversableModule_compose : TraversableModule (F2 ∘ F1) T :=
    {| trvmod_action := @dist_right_action_compose; |}.

End TraversableModule_compose.

(** * Kleisli-style presentation of traversable monads *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section KleisliTraversableModule_operations.

  Definition subt (F : Type -> Type)
             `{Fmap F} `{RightAction F T} `{Dist F}
             {A B} `{Applicative G} : (A -> G (T B)) -> F A -> G (F B) :=
    fun f => fmap G (right_action F) ∘ dist F G ∘ fmap F f.

End KleisliTraversableModule_operations.

Import TraversableMonad.Notations.

(** ** Specifications for sub-operations *)
(******************************************************************************)
Section KleisliTraversableMonad_suboperations.

  Context
    (F T : Type -> Type)
    `{TraversableModule F T}.

  Lemma sub_to_subt : forall `(f : A -> T B),
      sub F f = subt F (f : A -> (fun A => A) (T B)).
  Proof.
    intros. unfold subt. now rewrite (dist_unit F).
  Qed.

  Lemma traverse_to_subt `{Applicative G} : forall `(f : A -> G B),
      traverse F G f = subt F (fmap G (ret T) ∘ f).
  Proof.
    introv. unfold subt.
    rewrite <- (fun_fmap_fmap F).
    change_right (fmap G (right_action F) ∘
                       (dist F G ∘ fmap (F ∘ G) (ret T)) ∘ fmap F f).
    rewrite <- (dist_natural F (ret T)).
    unfold_ops @Fmap_compose.
    repeat reassociate <-.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G).
    rewrite (rmod_action_fmap_ret F T).
    now rewrite (fun_fmap_id G).
  Qed.

  Lemma fmap_to_sub : forall `(f : A -> B),
      fmap F f = subt F (ret T ∘ f : A -> (fun A => A) (T B)).
  Proof.
    introv. rewrite (fmap_to_traverse F). now rewrite traverse_to_subt.
  Qed.

End KleisliTraversableMonad_suboperations.

(** ** Kleisli laws for [subtm] *)
(******************************************************************************)
Section KleisliTraversableModule_subt.

  Context
    (F : Type -> Type)
    `{TraversableModule F T}.

  Context
    {A B C : Type}
    `{Applicative G1}
    `{Applicative G2}.

  (** *** Identity law *)
  Lemma subt_id :
    `(subt F (G := fun A => A) (ret T) = @id (F A)).
  Proof.
    intros. unfold subt.
    unfold_ops @Fmap_I. rewrite (dist_unit F).
    change (?g ∘ id ∘ ?f) with (g ∘ f).
    now rewrite (rmod_action_fmap_ret F T).
  Qed.

  (** *** Composition law *)
  Lemma subt_subt : forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
      subt F (G := G1 ∘ G2) (g ⋆tm f) =
      fmap G1 (subt F g) ∘ subt F f.
  Proof.
    intros. unfold subt at 2 3.
    reassociate -> on right. repeat reassociate <-.
    rewrite (fun_fmap_fmap G1).
    reassociate -> near (right_action F). rewrite (natural (ϕ := @right_action F T _)).
    reassociate <-. reassociate -> near (right_action F).
    rewrite (trvmod_action F T). reassociate <-.
    rewrite (fun_fmap_fmap G2).
    rewrite (rmod_action_action F T).
    rewrite <- (fun_fmap_fmap G1).
    reassociate -> near (dist F G1).
    change (fmap G1 (fmap (F ∘ T) g) ∘ dist F G1)
      with (fmap (G1 ∘ F) (fmap T g) ∘ dist F G1).
    rewrite (dist_natural F).
    reassociate <-. rewrite <- (fun_fmap_fmap G1).
    reassociate -> near (dist F G1).
    unfold_ops @Dist_compose.
    rewrite <- (fun_fmap_fmap G1).
    reassociate <-. reassociate -> near (dist F G1).
    change (fmap G1 (fmap F (dist (A:=?A) T G2)))
      with (fmap (G1 ∘ F) (dist (A:=A) T G2)).
    reassociate -> near (dist F G1).
    rewrite (dist_natural F (G:=G1)).
    repeat reassociate <-. reassociate -> near (dist F G1).
    rewrite <- (dist_linear F).
    change (fmap G1 (fmap G2 ?f)) with (fmap (G1 ∘ G2) f).
    rewrite <- (fun_fmap_fmap (G1 ∘ G2)).
    reassociate -> near (dist F (G1 ∘ G2)).
    change (fmap (G1 ∘ G2) (fmap F ?f)) with (fmap ((G1 ∘ G2) ∘ F) f).
    #[local] Set Keyed Unification.
    rewrite (dist_natural F (G := G1 ∘ G2)).
    reassociate <-. reassociate -> near (fmap F f).
    rewrite (fun_fmap_fmap F).
    reassociate ->.
    rewrite (fun_fmap_fmap F).
    reassociate ->.
    rewrite (fun_fmap_fmap F).
    reassociate <-.
    rewrite (fun_fmap_fmap G1).
    reassociate <-. rewrite (fun_fmap_fmap G1).
    #[local] Unset Keyed Unification.
    reflexivity.
  Qed.

End KleisliTraversableModule_subt.

(** ** Respectfulness properties *)
(******************************************************************************)
Section TraversableModule_respectfulness.

  Context
    (F : Type -> Type)
    `{TraversableModule F T}
    `{Applicative G}.

  Corollary subt_respectful {A B} : forall t (f g : A -> G (T B)),
      (forall a, a ∈ t -> f a = g a) -> subt F f t = subt F g t.
  Proof.
    intros. unfold subt, compose. fequal. fequal.
    now apply (fmap_respectful F).
  Qed.

  Corollary subt_respectful_id {A} : forall t (f : A -> G (T A)),
      (forall a, a ∈ t -> f a = pure G (ret T a)) -> subt F f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity F).
    rewrite (traverse_to_subt F T).
    apply subt_respectful. unfold compose.
    now setoid_rewrite (app_pure_natural G).
  Qed.

End TraversableModule_respectfulness.

(** * Traversable modules are listable *)
(******************************************************************************)
Section TraversableModule_listable.

  Existing Instance Fmap_list_const.
  Existing Instance Pure_list_const.
  Existing Instance Mult_list_monoid.
  Existing Instance Applicative_list_monoid.
  Existing Instance ApplicativeMorphism_unconst.
  Existing Instance ApplicativeMorphism_join_list.

  Context
    `{TraversableModule F T}.

  Theorem tolist_right_action : forall A : Type,
      tolist F ∘ right_action F =
      join list ∘ tolist F ∘ fmap F (tolist T) (A := T A).
  Proof.
    intros. rewrite 2(tolist_spec F), (tolist_spec T). reassociate ->.
    rewrite (natural (ϕ := @right_action F T _)).
    reassociate <-. rewrite (trvmod_action F T (G := const (list A))).
    change (fmap (const (list A)) (right_action F) ∘ ?f) with f.
    rewrite <- (fun_fmap_fmap F).
    repeat reassociate <-. fequal.
    unfold_ops @Dist_compose. fequal.
    rewrite <- (dist_morph F (ϕ := (fun X : Type => @join list Join_list A))).
    reassociate -> on right. rewrite (fun_fmap_fmap F).
    rewrite (mon_join_ret list). rewrite (fun_fmap_id F).
    change (?f ∘ id) with f.
    now rewrite (traversable_tolist1 (T := F)).
  Qed.

  #[global] Instance ListableModule_Traversable : ListableModule F T.
  Proof.
    constructor; try typeclasses eauto.
    - apply tolist_right_action.
  Qed.

End TraversableModule_listable.
