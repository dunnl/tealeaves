From Tealeaves Require Export
     Singlesorted.Classes.ListableMonad
      Singlesorted.Classes.TraversableFunctor.

Import Functor.Notations.
Import SetlikeFunctor.Notations.
Import TraversableFunctor.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

(** * Traversable monads *)
(******************************************************************************)
Section TraversableMonad.

  Context
    (T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Dist T}.

  Class TraversableMonad :=
    { trvmon_monad :> Monad T;
      trvmon_functor :> TraversableFunctor T;
      trvmon_ret : forall `{Applicative G},
          `(dist T G ∘ ret T (A := G A) = fmap G (ret T));
      trvmon_join : forall `{Applicative G},
          `(dist T G ∘ join T = fmap G (join T) ∘ dist (T ∘ T) G (A := A));
    }.

End TraversableMonad.

(** * Kleisli-style presentation of traversable monads *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section KleisliTraversableMonad_operations.

  Definition bindt (T : Type -> Type)
             `{Fmap T} `{Join T} `{Dist T}
             {A B} `{Fmap G} `{Pure G} `{Mult G} :
    (A -> G (T B)) -> T A -> G (T B)
    := fun f => fmap G (join T) ∘ dist T G ∘ fmap T f.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Definition kcomposetm {A B C}
             `{Applicative G1}
             `{Applicative G2} :
    (B -> G2 (T C)) ->
    (A -> G1 (T B)) ->
    (A -> G1 (G2 (T C))) :=
    fun g f => fmap G1 (bindt T g) ∘ f.

End KleisliTraversableMonad_operations.

#[local] Notation "g ⋆tm f" := (kcomposetm _ g f) (at level 40) : tealeaves_scope.

(** ** Specifications for sub-operations *)
(******************************************************************************)
Section KleisliTraversableMonad_suboperations.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma bind_to_bindt : forall `(f : A -> T B),
      bind T f = bindt T (f : A -> (fun A => A) (T B)).
  Proof.
    intros. unfold bindt. now rewrite (dist_unit T).
  Qed.

  Lemma traverse_to_bindt `{Applicative G} : forall `(f : A -> G B),
      traverse T G f = bindt T (fmap G (ret T) ∘ f).
  Proof.
    introv. unfold bindt.
    rewrite <- (fun_fmap_fmap T).
    change_right (fmap G (join T) ∘ (dist T G ∘ fmap (T ∘ G) (ret T)) ∘ fmap T f).
    rewrite <- (dist_natural T).
    unfold_ops @Fmap_compose.
    repeat reassociate <-.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G).
    rewrite (mon_join_fmap_ret T).
    now rewrite (fun_fmap_id G).
  Qed.

  Lemma fmap_to_bindt : forall `(f : A -> B),
      fmap T f = bindt T (ret T ∘ f : A -> (fun A => A) (T B)).
  Proof.
    introv. rewrite (fmap_to_traverse T). now rewrite traverse_to_bindt.
  Qed.

End KleisliTraversableMonad_suboperations.

(** ** Kleisli laws for [bindtm] *)
(******************************************************************************)
Section KleisliTraversableMonad_kleisli_laws.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Context
    {A B C : Type}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}.

  (** *** Identity law *)
  Lemma bindtm_id :
    `(bindt (G := fun A => A) T (ret T) = @id (T A)).
  Proof.
    intros. unfold bindt.
    unfold_ops @Fmap_I. rewrite (dist_unit T).
    change (?g ∘ id ∘ ?f) with (g ∘ f).
    now rewrite (mon_join_fmap_ret T).
  Qed.

  (** *** Composition law *)
  Lemma bindt_bindt : forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
      bindt T (G := G1 ∘ G2) (g ⋆tm f) =
      fmap G1 (bindt T g) ∘ bindt T f.
  Proof.
    intros. unfold bindt at 2 3.
    reassociate -> on right. repeat reassociate <-.
    rewrite (fun_fmap_fmap G1).
    reassociate -> near (join T). rewrite (natural (ϕ := @join T _)).
    reassociate <-. reassociate -> near (join T).
    rewrite (trvmon_join T). reassociate <-.
    rewrite (fun_fmap_fmap G2). rewrite (mon_join_join T).
    rewrite <- (fun_fmap_fmap G1).
    reassociate -> near (dist T G1).
    change (fmap G1 (fmap (T ∘ T) g) ∘ dist T G1)
      with (fmap (G1 ∘ T) (fmap T g) ∘ dist T G1).
    rewrite (dist_natural T).
    reassociate <-. rewrite <- (fun_fmap_fmap G1).
    reassociate -> near (dist T G1).
    unfold_ops @Dist_compose.
    rewrite <- (fun_fmap_fmap G1).
    reassociate <-. reassociate -> near (dist T G1).
    change (fmap G1 (fmap T (dist (A:=?A) T G2)))
      with (fmap (G1 ∘ T) (dist (A:=A) T G2)).
    reassociate -> near (dist T G1).
    rewrite (dist_natural T (G:=G1)).
    repeat reassociate <-. reassociate -> near (dist T G1).
    rewrite <- (dist_linear T).
    change (fmap G1 (fmap G2 ?f)) with (fmap (G1 ∘ G2) f).
    rewrite <- (fun_fmap_fmap (G1 ∘ G2)).
    reassociate -> near (dist T (G1 ∘ G2)).
    change (fmap (G1 ∘ G2) (fmap T ?f)) with (fmap ((G1 ∘ G2) ∘ T) f).
    #[local] Set Keyed Unification.
    rewrite (dist_natural T (G := G1 ∘ G2)).
    reassociate <-. reassociate -> near (fmap T f).
    rewrite (fun_fmap_fmap T).
    reassociate ->.
    rewrite (fun_fmap_fmap T).
    reassociate ->.
    rewrite (fun_fmap_fmap T).
    reassociate <-.
    rewrite (fun_fmap_fmap G1).
    reassociate <-. rewrite (fun_fmap_fmap G1).
    #[local] Unset Keyed Unification.
    reflexivity.
  Qed.

  (** *** Unit law *)
  Lemma bindt_comp_ret `(f : A -> G (T B)) :
    bindt T f ∘ ret T = f.
  Proof.
    intros. unfold bindt.
    reassociate -> on left.
    rewrite (natural (Natural := mon_ret_natural T)).
    unfold_ops @Fmap_I.
    reassociate <-; reassociate -> near (ret T).
    rewrite (trvmon_ret T).
    rewrite (fun_fmap_fmap G).
    rewrite (mon_join_ret T).
    now rewrite (fun_fmap_id G).
  Qed.

  Theorem bindt_purity
          `{Applicative G1} `{Applicative G2} : forall (f : A -> G1 (T B)),
      bindt T (G := G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ bindt T f.
  Proof.
    intros. unfold bindt.
    change_left (fmap (G2 ∘ G1) (join T) ∘ (traverse T (G2 ∘ G1) (pure G2 ∘ f))).
    rewrite (traverse_purity).
    reassociate <-. reassociate -> near (fmap T f).
    reassociate <-. fequal. ext t. unfold compose.
    unfold_ops @Fmap_compose. now rewrite (app_pure_natural G2).
  Qed.

End KleisliTraversableMonad_kleisli_laws.

(** ** Kleisli category laws *)
(******************************************************************************)
Section TraversableMonad_kleisli_category.

  Context
    `{TraversableMonad T}
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}
    `{Applicative G}.

  Notation "'1'" := (fun A => A).

  (** Composition when <<f>> has no applicative effect *)
  Theorem tm_kleisli_star1 {A B C} : forall (g : B -> G (T C)) (f : A -> T B),
      g ⋆tm (f : A -> 1 (T B)) = bindt T g ∘ f.
  Proof.
    easy.
  Qed.

  (** Composition when <<f>> has a pure applicative effect *)
  Theorem tm_kleisli_star2 {A B C} : forall (g : B -> G (T C)) (f : A -> T B),
      g ⋆tm (pure G ∘ f) = pure G ∘ bindt T g ∘ f.
  Proof.
    intros. unfold kcomposetm. reassociate <-.
    fequal. unfold compose; ext t. now apply (app_pure_natural G).
  Qed.

  (** Composition when <<g>> has no applicative effect *)
  Theorem tm_kleisli_star3 {A B C} : forall (g : B -> T C) (f : A -> G (T B)),
      (g : B -> 1 (T C)) ⋆tm f =
      fmap G (bind T g) ∘ f.
  Proof.
    introv. unfold kcomposetm. unfold bindt. unfold_ops @Fmap_I.
    now rewrite (dist_unit T).
  Qed.

  (** Composition when <<g>> has a pure applicative effect *)
  Theorem tm_kleisli_star4 {A B C} : forall (g : B -> T C) (f : A -> G1 (T B)),
      (pure G2 ∘ g) ⋆tm f =
      fmap G1 (pure G2 ∘ bind T g) ∘ f.
  Proof.
    introv. unfold kcomposetm.
    rewrite (bind_to_bindt T). fequal. fequal.
    rewrite <- (bindt_purity T (G2 := G2) (G1 := 1) g).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  (** Composition when <<f>> does not perform a substitution *)
  Theorem tm_kleisli_star5 {A B C} : forall (g : B -> G2 (T C)) (f : A -> G1 B),
      g ⋆tm (fmap G1 (ret T) ∘ f) =
      fmap G1 g ∘ f.
  Proof.
    intros. unfold kcomposetm.
    reassociate <-. rewrite (fun_fmap_fmap G1).
    now rewrite (bindt_comp_ret T).
  Qed.

  (** Composition when <<g>> does not perform a substitution *)
  Theorem tm_kleisli_star6 {A B C} : forall (g : B -> G2 C) (f : A -> G1 (T B)),
      (fmap G2 (ret T) ∘ g) ⋆tm f =
      fmap G1 (traverse T G2 g) ∘ f.
  Proof.
    intros. unfold kcomposetm. fequal.
    now rewrite (traverse_to_bindt T).
  Qed.

  (** Composition when <<f>> is just a map *)
  Theorem tm_kleisli_star7 {A B C} : forall (g : B -> G (T C)) (f : A -> B),
      g ⋆tm (ret T ∘ f : A -> 1 (T B)) = g ∘ f.
  Proof.
    intros. unfold kcomposetm. fequal.
    unfold_ops @Fmap_compose. change (fmap 1 ?f) with f.
    reassociate <-. now rewrite (bindt_comp_ret T).
  Qed.

  (** Composition when <<g>> is just a map *)
  Theorem tm_kleisli_star8 {A B C} : forall (g : B -> C) (f : A -> G (T B)),
      (ret T ∘ g : B -> 1 (T C)) ⋆tm f =
      (fmap (G ∘ T) g ∘ f : A -> G (T C)).
  Proof.
    intros. unfold kcomposetm. fequal.
    unfold_ops @Fmap_compose. now rewrite (fmap_to_bindt T).
  Qed.

  (** Right identity for <<kcomposetm>> *)
  Theorem tm_kleisli_id_r {B C} : forall (g : B -> G (T C)),
      g ⋆tm (ret T : B -> 1 (T B)) = g.
  Proof.
    intros. rewrite tm_kleisli_star1.
    now rewrite (bindt_comp_ret T).
  Qed.

  (** Left identity for <<kcomposetm>> *)
  Theorem tm_kleisli_id_l {A B} : forall (f : A -> G (T B)),
      (ret T : B -> (fun A => A)(T B)) ⋆tm f = f.
  Proof.
    intros. rewrite tm_kleisli_star3.
    rewrite (Monad.bind_id T).
    now rewrite (fun_fmap_id G).
  Qed.

  (** Associativity law for <<kcomposetm>> *)
  Theorem tm_kleisli_assoc {A B C D} :
    forall (h : C -> G3 (T D)) (g : B -> G2 (T C)) (f : A -> G1 (T B)),
       h ⋆tm (g ⋆tm f : A -> (G1 ∘ G2) (T C)) =
       (h ⋆tm g : B -> (G2 ∘ G3) (T D)) ⋆tm f.
  Proof.
    intros. unfold kcomposetm.
    repeat reassociate <-. fequal.
    unfold fmap at 1, Fmap_compose.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G1 (f := bindt T g)). fequal.
    now rewrite <- (bindt_bindt T).
  Qed.

End TraversableMonad_kleisli_category.

(** ** Composition with suboperations *)
(******************************************************************************)
Section TraversableMonad_suboperation_composition.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}.

  Corollary bindt_fmapt {A B C} : forall (g : B -> G2 (T C)) (f : A -> G1 B),
      fmap G1 (bindt T g) ∘ traverse T G1 f = bindt T (G := G1 ∘ G2) (fmap G1 g ∘ f).
  Proof.
    intros. rewrite (traverse_to_bindt T).
    rewrite <- (bindt_bindt T). fequal.
    now rewrite (tm_kleisli_star5).
  Qed.

  Corollary bind_bindt {A B C} : forall (g : B -> T C) (f : A -> G (T B)),
      fmap G (bind T g) ∘ bindt T f = bindt T (fmap G (bind T g) ∘ f).
  Proof.
    intros. rewrite (bind_to_bindt T).
    rewrite <- (bindt_bindt T (G2 := fun A => A) (G1 := G) g f).
    fequal. (* todo *) ext X Y [? ?]; cbn. unfold_ops @Mult_compose.
    unfold_ops @Mult_I. now rewrite (fun_fmap_id G).
  Qed.

  Corollary fmapt_bindt {A B C} : forall (g : B -> G2 C) (f : A -> G1 (T B)),
      fmap G1 (traverse T G2 g) ∘ bindt T f = bindt (G := G1 ∘ G2) T (fmap G1 (traverse T G2 g) ∘ f).
  Proof.
    intros. rewrite (traverse_to_bindt T (G := G2)).
    now rewrite <- (bindt_bindt T).
  Qed.

  Corollary bindt_bind {A B C} : forall (g : B -> G (T C)) (f : A -> T B),
      bindt T g ∘ bind T f = bindt T (bindt T g ∘ f).
  Proof.
    intros. rewrite (bind_to_bindt T).
    change (bindt T g) with (fmap (fun A => A) (bindt T g)).
    rewrite <- (bindt_bindt T (G1 := fun A => A)). fequal.
     (* todo *) ext X Y [? ?]; cbn. unfold_ops @Mult_compose.
    unfold_ops @Mult_I. reflexivity.
  Qed.

  Corollary bindt_fmap {A B C} : forall (g : B -> G (T C)) (f : A -> B),
      bindt T g ∘ fmap T f = bindt T (g ∘ f).
  Proof.
    intros. unfold bindt. reassociate ->. now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary fmap_bindt {A B C} : forall (g : B -> C) (f : A -> G (T B)),
      fmap G (fmap T g) ∘ bindt T f = bindt T (fmap (G ∘ T) g ∘ f).
  Proof.
    intros. rewrite (fmap_to_bindt T). rewrite <- (bindt_bindt T (G2 := fun A => A)).
    fequal.
     (* todo *) ext X Y [? ?]; cbn. unfold_ops @Mult_compose.
    unfold_ops @Mult_I. now rewrite (fun_fmap_id G).
    now rewrite (tm_kleisli_star8).
  Qed.

End TraversableMonad_suboperation_composition.

(** ** General laws *)
(******************************************************************************)
Section traverable_monad_theory.

  Context
    `{TraversableMonad T}.

  Lemma dist_ret_spec :
    TraversableMorphism (T := (fun A => A)) (U := T) (@ret T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. now rewrite (trvmon_ret T).
  Qed.

  Lemma dist_join_spec :
      TraversableMorphism (T := T ∘ T) (U := T) (@join T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. now rewrite <- (trvmon_join T).
  Qed.

End traverable_monad_theory.

(** ** Purity laws for [bindt] *)
(******************************************************************************)
Section TraversableMonad_purity.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Theorem bindt_purity1 `{Applicative G} {A B} : forall (f : A -> T B),
      bindt T (pure G ∘ f) = pure G ∘ bind T f.
  Proof.
    intros. unfold_ops @Bind_Join. reassociate <-.
    unfold bindt. rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    reassociate -> near (fmap T (pure G)).
    rewrite (fmap_purity_1 T). fequal.
    ext t; unfold compose. now rewrite (app_pure_natural G).
  Qed.

  Theorem bindt_purity2 `{Applicative G} {A} :
    bindt T (pure G ∘ ret T) = pure G (A := T A).
  Proof.
    rewrite bindt_purity1. now rewrite (bind_id T).
  Qed.

End TraversableMonad_purity.

(** ** Respectfulness properties *)
(******************************************************************************)
Section TraversableMonad_respectfulness.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}
    `{Applicative G}.

  Corollary bindt_respectful {A B} : forall t (f g : A -> G (T B)),
      (forall a, a ∈ t -> f a = g a) -> bindt T f t = bindt T g t.
  Proof.
    intros. unfold bindt, compose. fequal. fequal.
    now apply (fmap_respectful T).
  Qed.

  Corollary bindt_respectful_id {A} : forall t (f : A -> G (T A)),
      (forall a, a ∈ t -> f a = pure G (ret T a)) -> bindt T f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity T).
    rewrite (traverse_to_bindt T).
    apply bindt_respectful. unfold compose.
    now setoid_rewrite (app_pure_natural G).
  Qed.

End TraversableMonad_respectfulness.

(** * Instance for [list] *)
(******************************************************************************)
Section TraversableMonad_list.

  Context
    `{Applicative G}
    {A : Type}.

  Theorem trvmon_ret_list :
    `(dist list G ∘ ret list (A := G A) = fmap G (ret list)).
  Proof.
    ext x. unfold compose.
    unfold_ops @Return_list.
    rewrite dist_list_cons_2.
    rewrite dist_list_nil.
    rewrite ap3, ap5.
    reflexivity.
  Qed.

  #[local] Set Keyed Unification.
  Theorem trvmon_join_list :
    `(dist list G ∘ join list = fmap G (join list) ∘ dist (list ∘ list) G (A := A)).
  Proof.
    ext l. unfold compose. induction l.
    - rewrite join_list_nil. rewrite dist_list_nil.
      unfold_ops @Dist_compose. unfold compose.
      rewrite fmap_list_nil, dist_list_nil.
      now rewrite (app_pure_natural G).
    - rewrite join_list_cons.
      unfold_ops @Dist_compose. unfold compose.
      rewrite (fmap_list_cons). rewrite dist_list_cons_2.
      rewrite dist_list_app. rewrite IHl; clear IHl.
      unfold_ops @Dist_compose. unfold compose.
      rewrite <- (fmap_to_ap).
      rewrite ap6. compose near (dist list G a) on right.
      rewrite (fun_fmap_fmap G).
      rewrite <- ap7.
      compose near (dist list G a) on left.
      now rewrite (fun_fmap_fmap G).
  Qed.
  #[local] Set Keyed Unification.

End TraversableMonad_list.

(** * Traversable monads are listable *)
(******************************************************************************)
Section TraversableMonad_listable.

  Existing Instance Fmap_list_const.
  Existing Instance Pure_list_const.
  Existing Instance Mult_list_monoid.
  Existing Instance Applicative_list_monoid.
  Existing Instance ApplicativeMorphism_unconst.

  Context
    `{TraversableMonad T}.

  Instance ApplicativeMorphism_join_list : forall A : Type,
      ApplicativeMorphism
        (const (list (list A)))
        (const (list A))
        (fun X => @join list Join_list A).
  Proof.
    intros. constructor; try typeclasses eauto.
    - intros X Y f x. cbv in x.
      rewrite (@fmap_list_const_spec (list A) X Y f).
      rewrite (@fmap_list_const_spec A X Y f).
      reflexivity.
    - intros X x. cbn. reflexivity.
    - intros X Y x y. cbv in x, y.
      change (?x ⊗ ?y) with (List.app x y).
      now rewrite join_list_app.
  Qed.

  Theorem tolist_ret : forall A : Type,
      tolist T ∘ ret T = ret list (A := A).
  Proof.
    intros. unfold_ops @Tolist_Traversable.
    rewrite <- (fun_fmap_fmap T).
    repeat reassociate -> on left. reassociate <- near (dist T (Const (list A))).
    rewrite (natural (ϕ := @ret T _));
      unfold_ops @Fmap_I.
    repeat reassociate -> on left.
    reassociate <- near (fmap T (@mkConst (list A) False)).
    rewrite (natural (ϕ := @ret T _));
      unfold_ops @Fmap_I.
    repeat reassociate -> on left;
      reassociate <- near (dist T _).
    rewrite (trvmon_ret T).
    ext a. reflexivity.
  Qed.

  Theorem tolist_join : forall A : Type,
      tolist T ∘ join T = join list ∘ tolist T ∘ fmap T (tolist T) (A := T A).
  Proof.
    intros. rewrite (tolist_spec T). reassociate ->.
    rewrite (natural (ϕ := @join T _)).
    reassociate <-. rewrite (trvmon_join T (G := const (list A))).
    change (fmap (const (list A)) (join T) ∘ ?f) with f.
    rewrite <- (fun_fmap_fmap T).
    repeat reassociate <-. fequal.
    unfold_ops @Dist_compose. fequal.
    rewrite (tolist_spec T).
    reassociate <- on right.
    rewrite <- (dist_morph T (ϕ := (fun X : Type => @join list Join_list A))).
    reassociate -> on right. rewrite (fun_fmap_fmap T).
    rewrite (mon_join_ret list). rewrite (fun_fmap_id T).
    change (?f ∘ id) with f.
    now rewrite (traversable_tolist1).
  Qed.

  #[global] Instance ListableMonad_TraversableMonad : ListableMonad T :=
    {| lmon_ret := tolist_ret;
       lmon_join := tolist_join;
    |}.

End TraversableMonad_listable.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "g ⋆tm f" := (kcomposetm _ g f) (at level 40) : tealeaves_scope.
End Notations.
