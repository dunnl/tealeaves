From Tealeaves Require Export
  Classes.Monad
  Classes.Traversable.Functor.

Import Functor.Notations.
Import Monad.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables F G T A B.

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

(** * The monad operations as <<traverse>>-respecting morphisms *)
(******************************************************************************)
Section traverable_monad_theory.

  Context
    (T : Type -> Type)
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

From Tealeaves Require Kleisli.Traversable.Monad.

(** * Algebraic traversable monads to Kleisli traversable monads *)
(******************************************************************************)

Module ToKleisli.

  Import Kleisli.Traversable.Monad.

  Section operation.

    Context
      (T : Type -> Type)
      `{Fmap T} `{Join T} `{Dist T}.

    #[export] Instance Bindt_distjoin : Bindt T T :=
      fun (G : Type -> Type) (A B : Type) _ _ _ (f : A -> G (T B)) =>
        fmap G (join T) ∘ dist T G ∘ fmap T f.

  End operation.

  Import Setlike.Functor.Notations.
  Import Kleisli.Traversable.Monad.Notations.
  Import Classes.Traversable.Functor.ToKleisli.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Classes.Traversable.Monad.TraversableMonad T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma ktm_bindt1_T :
      forall (A : Type), bindt T (fun A => A) (ret T) = @id (T A).
    Proof.
      intros. unfold bindt. unfold_ops @Bindt_distjoin.
      unfold_ops @Fmap_I. rewrite (dist_unit T).
      change (?g ∘ id ∘ ?f) with (g ∘ f).
      now rewrite (mon_join_fmap_ret T).
    Qed.


    (** *** Composition law *)
    (******************************************************************************)
    Lemma ktm_bindt2_T : forall
        (A B C : Type)
        (G1 : Type -> Type) `{Fmap G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
        (G2 : Type -> Type) `{Fmap G2} `{Pure G2} `{Mult G2} `{! Applicative G2}
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        fmap G1 (bindt T G2 g) ∘ bindt T G1 f =
          bindt T (G1 ∘ G2) (g ⋆tm f).
    Proof.
      intros. unfold bindt at 1 2 3.
      unfold_ops @Bindt_distjoin.
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
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      #[local] Unset Keyed Unification.
      reassociate <-. rewrite <- (fun_fmap_fmap G1).
      reassociate -> near (dist T G1).
      unfold_ops @Dist_compose.
      rewrite <- (fun_fmap_fmap G1).
      reassociate <-. reassociate -> near (dist T G1).
      change (fmap G1 (fmap T (dist (A:=?A) T G2)))
        with (fmap (G1 ∘ T) (dist (A:=A) T G2)).
      reassociate -> near (dist T G1).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      #[local] Unset Keyed Unification.
      repeat reassociate <-. reassociate -> near (dist T G1).
      rewrite <- (dist_linear T).
      change (fmap G1 (fmap G2 ?f)) with (fmap (G1 ∘ G2) f).
      rewrite <- (fun_fmap_fmap (G1 ∘ G2)).
      reassociate -> near (dist T (G1 ∘ G2)).
      change (fmap (G1 ∘ G2) (fmap T ?f)) with (fmap ((G1 ∘ G2) ∘ T) f).
      #[local] Set Keyed Unification.
      rewrite (natural (ϕ := @dist T _ (G1 ∘ G2) _ _ _)).
      reassociate <-. reassociate -> near (fmap T f).
      rewrite (fun_fmap_fmap T).
      reassociate -> near (fmap T (fmap G1 (fmap T g) ∘ f)).
      rewrite (fun_fmap_fmap T).
      reassociate ->.
      reassociate ->.
      rewrite (fun_fmap_fmap T).
      reassociate <-.
      reassociate <-.
      rewrite (fun_fmap_fmap G1).
      reassociate <-.
      rewrite (fun_fmap_fmap G1).
      #[local] Unset Keyed Unification.
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma ktm_bindt0_T : forall
        (A B: Type)
        (G1 : Type -> Type) `{Fmap G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
        (f : A -> G1 (T B)),
        bindt T G1 f ∘ ret T = f.
    Proof.
      intros. unfold_ops @Bindt_distjoin.
      reassociate -> on left.
      rewrite (natural (Natural := mon_ret_natural T)).
      unfold_ops @Fmap_I.
      reassociate <-; reassociate -> near (ret T).
      rewrite (trvmon_ret T).
      rewrite (fun_fmap_fmap G1).
      rewrite (mon_join_ret T).
      now rewrite (fun_fmap_id G1).
    Qed.

    (** *** Morphism law *)
    (******************************************************************************)
    Lemma ktm_morph_T : forall
        (G1 G2 : Type -> Type) `{Fmap G1} `{Pure G1} `{Mult G1}
        `{Fmap G2} `{Pure G2} `{Mult G2}
        (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : A -> G1 (T B)), ϕ (T B) ∘ bindt T G1 f = bindt T G2 (ϕ (T B) ∘ f).
    Proof.
      introv morph.
      inversion morph. intros.
      unfold_ops @Bindt_distjoin.
      do 2 reassociate <- on left.
      unfold compose. ext a.
      rewrite (appmor_natural _ (T B) (join T)).
      unfold compose. compose near (fmap T f a).
      rewrite <- (dist_morph T).
      unfold compose. compose near a on left.
      rewrite (fun_fmap_fmap T).
      reflexivity.
    Qed.

    (** *** Purity law *)
    (******************************************************************************)
    Theorem bindt_purity_T
      `{Applicative G1} `{Applicative G2} : forall `(f : A -> G1 (T B)),
        bindt T (G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ bindt T G1 f.
    Proof.
      intros. unfold_ops @Bindt_distjoin.
      reassociate -> on left.
      rewrite (fmap_purity_2 T (G2 := G2) f).
      do 2 reassociate <- on left.
      do 2 reassociate <- on right.
      do 2 fequal.
      unfold_ops @Fmap_compose.
      ext t; unfold compose.
      now rewrite (app_pure_natural G2).
    Qed.

    #[export] Instance TravMon_ToKleisli: Kleisli.Traversable.Monad.Monad T :=
      {| ktm_bindt0 := @ktm_bindt0_T;
        ktm_bindt1 := @ktm_bindt1_T;
        ktm_bindt2 := @ktm_bindt2_T;
        ktm_morph := @ktm_morph_T;
      |}.

  End with_monad.

End ToKleisli.

From Tealeaves Require Import
  Functors.List.

(** * Traversable monad instance for [list] *)
(******************************************************************************)
Section TraversableMonad_list.

  Section with_context.

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
    rewrite ap3, pure_ap_fmap.
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
      rewrite fmap_ap. compose near (dist list G a) on right.
      rewrite (fun_fmap_fmap G).
      rewrite <- ap_fmap.
      compose near (dist list G a) on left.
      now rewrite (fun_fmap_fmap G).
  Qed.
  #[local] Set Keyed Unification.

  End with_context.

  #[export] Instance: TraversableMonad list :=
    {| trvmon_ret := @trvmon_ret_list;
       trvmon_join := @trvmon_join_list;
    |}.

End TraversableMonad_list.


Import Kleisli.Traversable.Monad.
Import Kleisli.Monad.
Import ToKleisli.

(** ** [list]/[list] right module *)
(******************************************************************************)
#[export] Instance Bindt_list : Bindt list _
  := ToKleisli.Bindt_distjoin list.
#[export] Instance Bind_list : Bind list list
  := Derived.Bind_Bindt list.
#[export] Instance KleisliTravMonad_list : Kleisli.Traversable.Monad.Monad list
  := ToKleisli.TravMon_ToKleisli list.
(*
#[export] Instance KleisliMonad_list : Kleisli.Monad.Monad list.
  := ToKleisli.Kleisli_Monad list.
*)

(** ** Rewriting lemmas for <<bindt>> *)
(******************************************************************************)
Section bindt_rewriting_lemmas.

  Context (A B : Type) (G : Type -> Type) `{Applicative G}.

  Lemma bindt_list_nil : forall (f : A -> G (list B)),
      bindt list G f (@nil A) = pure G (@nil B).
  Proof.
    intros. unfold_ops @Bindt_list @ToKleisli.Bindt_distjoin.
    unfold compose. simpl_list.
    rewrite (app_pure_natural G).
    reflexivity.
  Qed.

  Lemma bindt_list_one : forall (f : A -> G (list B)) (a : A),
      bindt list G f (ret list a) = f a.
  Proof.
    intros.
    unfold_ops @Bindt_list @ToKleisli.Bindt_distjoin.
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
    intros. unfold_ops @Bindt_list @ToKleisli.Bindt_distjoin.
    unfold compose.
    rewrite (fmap_list_cons).
    rewrite dist_list_cons_1.
    do 2 rewrite fmap_ap.
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
    rewrite ap_fmap.
    rewrite (fmap_to_ap).
    reflexivity.
  Qed.

  Lemma bindt_list_app : forall (f : A -> G (list B)) (l1 l2 : list A),
      bindt list G f (l1 ++ l2) =
        pure G (@app B) <⋆> (bindt list G f l1) <⋆> (bindt list G f l2).
  Proof.
    intros. unfold_ops @Bindt_list @ToKleisli.Bindt_distjoin.
    unfold compose.
    rewrite (fmap_list_app).
    rewrite (dist_list_app).
    do 2 rewrite fmap_ap.
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
    rewrite ap_fmap.
    rewrite <- (fun_fmap_fmap G).
    unfold compose at 1.
    rewrite fmap_to_ap.
    reflexivity.
  Qed.

End bindt_rewriting_lemmas.

(** ** Rewriting lemmas for <<foldMapd>> *)
(******************************************************************************)
Section foldMap_rewriting_lemmas.

  Import Classes.Setlike.Functor.
  Import Kleisli.Traversable.Functor.
  Import Traversable.Monad.Derived.
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
    intros. cbn. unfold_ops @Pure_const.
    simpl_monoid. reflexivity.
  Qed.

  Lemma foldMap_list_cons : forall (f : A -> M) (a : A) (l : list A),
      foldMap list f (cons a l) = f a ● foldMap list f l.
  Proof.
    intros. cbn. unfold_ops @Pure_const.
    now do 2 simpl_monoid.
  Qed.

  Lemma foldMap_list_app : forall (f : A -> M) (l1 l2 : list A),
      foldMap list f (l1 ++ l2) = foldMap list f l1 ● foldMap list f l2.
  Proof.
    intros. unfold foldMap, traverse, Traverse_Bindt.
    rewrite (bindt_list_app); try typeclasses eauto.
    unfold ap. unfold_ops @Pure_const @Mult_const.
    now simpl_monoid.
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

Import Setlike.Functor.Notations.
Import List.ListNotations.

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
    intros. unfold_ops @Bind_list @Derived.Bind_Bindt.
    unfold bindt, Bindt_list, ToKleisli.Bindt_distjoin.
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
    unfold_ops @Bind_list @Derived.Bind_Bindt.
    unfold bindt, Bindt_list, ToKleisli.Bindt_distjoin.
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

(*
(******************************************************************************)
Section TraversableMonad_listable.

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
      rewrite (@fmap_const_spec (list A) X Y f).
      rewrite (@fmap_const_spec (list (list A)) X Y f).
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
    intros. rewrite (traversable_tolist_spec T False). reassociate ->.
    unfold traverse. reassociate -> on left.
    rewrite (natural (ϕ := @join T _)).
    reassociate <- on left. rewrite (trvmon_join T (G := const (list A))).
    change (fmap (const (list A)) (join T) ∘ ?f) with f.
    rewrite <- (fun_fmap_fmap T).
    repeat reassociate <-. fequal.
    unfold_ops @Dist_compose. fequal.
    rewrite (traversable_tolist_spec T False). unfold traverse.
    reassociate <- on right.
    rewrite <- (dist_morph T (ϕ := (fun X : Type => @join list Join_list A))).
    reassociate -> on right. rewrite (fun_fmap_fmap T).
    rewrite (mon_join_ret list). rewrite (fun_fmap_id T).
    change (?f ∘ id) with f.
    now rewrite (dist_const1 T (T False)).
  Qed.

  #[global] Instance ListableMonad_TraversableMonad : ListableMonad T :=
    {| lmon_ret := tolist_ret;
       lmon_join := tolist_join;
    |}.

End TraversableMonad_listable.
*)
