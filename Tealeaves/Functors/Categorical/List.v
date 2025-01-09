From Tealeaves Require Import
  Classes.Categorical.TraversableFunctor
  Functors.List.

Import List.ListNotations.
Import Applicative.Notations.

#[local] Open Scope list_scope.
#[local] Generalizable Variable G.

(** * Traversable instance for [list] *)
(******************************************************************************)
#[global] Instance Dist_list: ApplicativeDist list :=
  fun G map mlt pur A =>
    (fix dist (l : list (G A)) :=
       match l with
       | nil => pure nil
       | cons x xs =>
           pure (F := G) (@cons A) <⋆> x <⋆> (dist xs)
       end).

(** ** Rewriting lemmas for <<dist>> *)
(******************************************************************************)
Section list_dist_rewrite.

  Context
    `{Applicative G}.

  Variable (A : Type).

  Lemma dist_list_nil :
    dist list G (@nil (G A)) = pure nil.
  Proof.
    reflexivity.
  Qed.


  Lemma dist_list_cons_1: forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      pure cons <⋆> x <⋆> (dist list G xs).
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_2 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      map (@cons A) x <⋆> dist list G xs.
  Proof.
    intros. rewrite dist_list_cons_1.
    now rewrite map_to_ap.
  Qed.

  Lemma dist_list_one (a : G A) : dist list G [ a ] = map (ret (T := list)) a.
  Proof.
    cbn. rewrite map_to_ap. rewrite ap3.
    rewrite <- ap4. now do 2 rewrite ap2.
  Qed.

  Lemma dist_list_app : forall (l1 l2 : list (G A)),
      dist list G (l1 ++ l2) = pure (@app _) <⋆> dist list G l1 <⋆> dist list G l2.
  Proof.
    intros. induction l1.
    - cbn. rewrite ap2. change (app []) with (@id (list A)).
      now rewrite ap1.
    - cbn [app]. rewrite dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl1; clear IHl1.
      rewrite <- map_to_ap.
      rewrite <- map_to_ap.
      rewrite <- ap4. rewrite <- map_to_ap.
      fequal. rewrite <- ap_map.
      rewrite map_ap. fequal.
      compose near a.
      rewrite (fun_map_map).
      rewrite (fun_map_map).
      compose near a on left.
      now rewrite (fun_map_map).
  Qed.

End list_dist_rewrite.

#[export] Hint Rewrite @dist_list_nil @dist_list_cons_1
     @dist_list_one @dist_list_app : tea_list.

Section dist_list_properties.

  #[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
  #[local] Arguments dist _%function_scope {ApplicativeDist}
    _%function_scope {H H0 H1} A%type_scope _.

  Generalizable All Variables.

  Lemma dist_list_1 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      map G (map list f) ((map G (@cons A) a) <⋆> dist list G A l) =
      (map G (@cons B ○ f) a) <⋆> map G (map list f) (dist list G A l).
  Proof.
    intros. rewrite map_ap. rewrite <- ap_map.
    fequal. compose near a.
    now rewrite 2(fun_map_map).
  Qed.

  Lemma dist_list_2 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      map G (map list f) ((pure (@cons A) <⋆> a) <⋆> dist list G A l) =
      (pure cons <⋆> map G f a) <⋆> map G (map list f) (dist list G A l).
  Proof.
    intros. rewrite <- map_to_ap.
    rewrite map_ap.
    compose near a on left.
    rewrite (fun_map_map).
    rewrite pure_ap_map.
    unfold ap. rewrite (app_mult_natural).
    rewrite (app_mult_natural_1 G).
    compose near ((a ⊗ dist list G A l)) on right.
    rewrite (fun_map_map). fequal. ext [? ?].
    reflexivity.
  Qed.

  Lemma dist_natural_list : forall `{Applicative G} `(f : A -> B),
      map (G ∘ list) f ∘ dist list G A =
      dist list G B ∘ map (list ∘ G) f.
  Proof.
    intros; cbn. unfold_ops @Map_compose. unfold compose.
    ext l. induction l.
    + cbn. now rewrite (app_pure_natural).
    + rewrite dist_list_cons_2.
      rewrite map_list_cons, dist_list_cons_2.
      rewrite <- IHl. rewrite dist_list_1.
      compose near a on right.
      now rewrite (fun_map_map).
  Qed.

  Instance dist_natural_list_ : forall `{Applicative G}, Natural (@dist list _ G _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    intros. eapply (dist_natural_list f).
  Qed.

  Lemma dist_morph_list : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist list G2 A ∘ map list (ϕ A) = ϕ (list A) ∘ dist list G1 A.
  Proof.
    intros. ext l. unfold compose. induction l.
    - rewrite map_list_nil.
      rewrite dist_list_nil.
      rewrite dist_list_nil.
      rewrite appmor_pure.
      reflexivity.
    - infer_applicative_instances.
      rewrite map_list_cons.
      rewrite dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl.
      rewrite ap_morphism_1.
      rewrite (appmor_natural).
      reflexivity.
  Qed.

  Lemma dist_unit_list : forall (A : Type),
      dist list (fun A => A) A = @id (list A).
  Proof.
    intros. ext l. induction l.
    - reflexivity.
    - cbn. now rewrite IHl.
  Qed.

  #[local] Set Keyed Unification.
  Lemma dist_linear_list
    : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist list (G1 ∘ G2) A =
      map G1 (dist list G2 A) ∘ dist list G1 (G2 A).
  Proof.
    intros. unfold compose. ext l. induction l.
    - cbn. unfold_ops @Pure_compose.
      rewrite map_to_ap. now rewrite ap2.
    - rewrite (dist_list_cons_2 (G := G1 ○ G2)).
      rewrite (dist_list_cons_2 (G := G1)).
      rewrite IHl; clear IHl.
      unfold_ops @Mult_compose @Pure_compose @Map_compose.
      rewrite (ap_compose2 G2 G1).
      compose near a on left.
      rewrite (fun_map_map).
      unfold ap at 1.
      rewrite (app_mult_natural).
      unfold ap at 2. rewrite (app_mult_natural_1 G1).
      fequal. compose near (a ⊗ dist list G1 (G2 A) l).
      rewrite (fun_map_map).
      rewrite (fun_map_map).
      fequal.
      ext [? ?].
      cbn. unfold compose.
      now rewrite map_to_ap.
  Qed.
  #[local] Unset Keyed Unification.

End dist_list_properties.

#[export] Instance Traversable_list: Categorical.TraversableFunctor.TraversableFunctor list :=
  {| dist_natural := @dist_natural_list_;
     dist_morph := @dist_morph_list;
     dist_unit := @dist_unit_list;
     dist_linear := @dist_linear_list;
  |}.

(*
(** * Traversable monad instance for [list] *)
(******************************************************************************)
Section TraversableMonad_list.

  Section with_context.

  Context
    `{Applicative G}
    {A : Type}.

  Theorem trvmon_ret_list :
    `(dist list G ∘ ret list (A := G A) = map G (ret list)).
  Proof.
    ext x. unfold compose.
    unfold_ops @Return_list.
    rewrite dist_list_cons_2.
    rewrite dist_list_nil.
    rewrite ap3, pure_ap_map.
    reflexivity.
  Qed.

  #[local] Set Keyed Unification.
  Theorem trvmon_join_list :
    `(dist list G ∘ join list = map G (join list) ∘ dist (list ∘ list) G (A := A)).
  Proof.
    ext l. unfold compose. induction l.
    - rewrite join_list_nil. rewrite dist_list_nil.
      unfold_ops @Dist_compose. unfold compose.
      rewrite map_list_nil, dist_list_nil.
      now rewrite (app_pure_natural G).
    - rewrite join_list_cons.
      unfold_ops @Dist_compose. unfold compose.
      rewrite (map_list_cons). rewrite dist_list_cons_2.
      rewrite dist_list_app. rewrite IHl; clear IHl.
      unfold_ops @Dist_compose. unfold compose.
      rewrite <- (map_to_ap).
      rewrite map_ap. compose near (dist list G a) on right.
      rewrite (fun_map_map G).
      rewrite <- ap_map.
      compose near (dist list G a) on left.
      now rewrite (fun_map_map G).
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

*)
