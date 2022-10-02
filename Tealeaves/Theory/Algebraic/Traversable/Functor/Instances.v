From Tealeaves Require Import
  Classes.Algebraic.Monad
  Classes.Algebraic.Traversable.Functor
  Functors.List
  Functors.Compose
  Functors.Environment.

Import List.ListNotations.
Import Applicative.Notations.
#[local] Open Scope list_scope.

#[local] Generalizable Variable G A B ϕ.

(** * Traversable instance for [list] *)
(******************************************************************************)
#[global] Instance Dist_list : Dist list :=
  fun G map mlt pur A =>
    (fix dist (l : list (G A)) :=
       match l with
       | nil => pure G nil
       | cons x xs =>
         (pure G (@cons A) <⋆> x) <⋆> (dist xs)
       end).

(** ** Rewriting lemmas for <<dist>> *)
(******************************************************************************)
Section list_dist_rewrite.

  Context
    `{Applicative G}.

  Variable (A : Type).

  Lemma dist_list_nil :
    dist list G (@nil (G A)) = pure G nil.
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_1 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      (pure G cons <⋆> x) <⋆> (dist list G xs).
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_2 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      (fmap G (@cons A) x) <⋆> (dist list G xs).
  Proof.
    intros. rewrite dist_list_cons_1.
    now rewrite fmap_to_ap.
  Qed.

  Lemma dist_list_one (a : G A) : dist list G [ a ] = fmap G (ret list) a.
  Proof.
    cbn. rewrite fmap_to_ap. rewrite ap3.
    rewrite <- ap4. now do 2 rewrite ap2.
  Qed.

  Lemma dist_list_app : forall (l1 l2 : list (G A)),
      dist list G (l1 ++ l2) = pure G (@app _) <⋆> dist list G l1 <⋆> dist list G l2.
  Proof.
    intros. induction l1.
    - cbn. rewrite ap2. change (app []) with (@id (list A)).
      now rewrite ap1.
    - cbn [app]. rewrite dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl1; clear IHl1.
      rewrite <- fmap_to_ap.
      rewrite <- fmap_to_ap.
      rewrite <- ap4. rewrite <- fmap_to_ap.
      fequal. rewrite <- ap7.
      rewrite ap6. fequal.
      compose near a.
      rewrite (fun_fmap_fmap G).
      rewrite (fun_fmap_fmap G).
      compose near a on left.
      now rewrite (fun_fmap_fmap G).
  Qed.

End list_dist_rewrite.

#[global] Hint Rewrite @dist_list_nil @dist_list_cons_1
     @dist_list_one @dist_list_app : tea_list.

Section dist_list_properties.

  #[local] Arguments dist _%function_scope {Dist} _%function_scope {H H0 H1}
   A%type_scope _.

  Lemma dist_list_1 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      fmap G (fmap list f) ((fmap G (@cons A) a) <⋆> dist list G A l) =
      (fmap G (@cons B ○ f) a) <⋆> fmap G (fmap list f) (dist list G A l).
  Proof.
    intros. rewrite ap6. rewrite <- ap7.
    fequal. compose near a. now rewrite 2(fun_fmap_fmap G).
  Qed.

  Lemma dist_list_2 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      fmap G (fmap list f) ((pure G (@cons A) <⋆> a) <⋆> dist list G A l) =
      (pure G cons <⋆> fmap G f a) <⋆> fmap G (fmap list f) (dist list G A l).
  Proof.
    intros. rewrite <- fmap_to_ap.
    rewrite ap6.
    compose near a on left.
    rewrite (fun_fmap_fmap G).
    rewrite ap5.
    unfold ap. rewrite (app_mult_natural G).
    rewrite (app_mult_natural_1 G).
    compose near ((a ⊗ dist list G A l)) on right.
    rewrite (fun_fmap_fmap G). fequal. ext [? ?].
    reflexivity.
  Qed.

  Lemma dist_natural_list : forall `{Applicative G} `(f : A -> B),
      fmap (G ∘ list) f ∘ dist list G A =
      dist list G B ∘ fmap (list ∘ G) f.
  Proof.
    intros; cbn. unfold_ops @Fmap_compose. unfold compose.
    ext l. induction l.
    + cbn. now rewrite (app_pure_natural G).
    + rewrite dist_list_cons_2.
      rewrite fmap_list_cons, dist_list_cons_2.
      rewrite <- IHl. rewrite dist_list_1.
      compose near a on right. now rewrite (fun_fmap_fmap G).
  Qed.

  Instance dist_natural_list_ : forall `{Applicative G}, Natural (@dist list _ G _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    intros. eapply (dist_natural_list f).
  Qed.

  Lemma dist_morph_list : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist list G2 A ∘ fmap list (ϕ A) = ϕ (list A) ∘ dist list G1 A.
  Proof.
    intros. ext l. unfold compose. induction l.
    - cbn. now rewrite (appmor_pure G1 G2).
    - specialize (appmor_app_F G1 G2);
        specialize (appmor_app_G G1 G2);
        intros.
      rewrite fmap_list_cons, dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl. rewrite ap_morphism_1.
      fequal. now rewrite (appmor_natural G1 G2 A).
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
      fmap G1 (dist list G2 A) ∘ dist list G1 (G2 A).
  Proof.
    intros. unfold compose. ext l. induction l.
    - cbn. unfold_ops @Pure_compose.
      rewrite fmap_to_ap. now rewrite ap2.
    - rewrite (dist_list_cons_2 (G := G1 ○ G2)).
      rewrite (dist_list_cons_2 (G := G1)).
      rewrite IHl; clear IHl.
      unfold_ops @Mult_compose @Pure_compose @Fmap_compose.
      rewrite (ap_compose2 G2 G1).
      rewrite (app_mult_natural G1).
      unfold ap at 2. rewrite (app_mult_natural_1 G1).
      fequal. compose near (a ⊗ dist list G1 (G2 A) l).
      repeat rewrite (fun_fmap_fmap G1). fequal.
      ext [? ?]. cbn. now rewrite fmap_to_ap.
  Qed.
  #[local] Unset Keyed Unification.

End dist_list_properties.

#[global] Instance Traversable_list : TraversableFunctor list :=
  {| dist_natural := @dist_natural_list_;
     dist_morph := @dist_morph_list;
     dist_unit := @dist_unit_list;
     dist_linear := @dist_linear_list;
  |}.

(** * Traversable instance for <<prod>> *)
(******************************************************************************)
Section TraversableFunctor_prod.

  Context
    (X : Type).

  #[global] Instance Dist_prod : Dist (prod X) :=
    fun F map mlt pur A '(x, a) => fmap F (pair x) a.

  Lemma dist_natural_prod : forall `{Applicative G} `(f : A -> B),
      fmap (G ∘ prod X) f ∘ dist (prod X) G = dist (prod X) G ∘ fmap (prod X ∘ G) f.
  Proof.
    intros; unfold compose; cbn. ext [x a]; cbn.
    unfold_ops @Fmap_compose. compose near a.
    now do 2 rewrite (fun_fmap_fmap G).
  Qed.

  Instance dist_natural_prod_ : forall `{Applicative G}, Natural (@dist (prod X) _ G _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    intros. eapply (dist_natural_prod f).
  Qed.

  Lemma dist_morph_prod : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist (prod X) G2 ∘ fmap (prod X) (ϕ A) = ϕ (X * A) ∘ dist (prod X) G1.
  Proof.
    intros; unfold compose; cbn. ext [x a]; cbn.
    specialize (appmor_app_F G1 G2);
        specialize (appmor_app_G G1 G2);
        intros.
    now rewrite (appmor_natural G1 G2).
  Qed.

  Lemma dist_unit_prod : forall (A : Type),
      dist (prod X) (fun A => A) = @id (prod X A).
  Proof.
    intros; unfold compose; cbn. ext [x a]; now cbn.
  Qed.

  Lemma dist_linear_prod : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (prod X) (G1 ∘ G2) (A := A) =
      fmap G1 (dist (prod X) G2) ∘ dist (prod X) G1.
  Proof.
    intros; unfold compose; cbn. ext [x a].
    unfold_ops @Dist_prod @Fmap_compose.
    compose near a on right. now rewrite (fun_fmap_fmap G1).
  Qed.

  #[global] Instance Traversable_prod : TraversableFunctor (prod X) :=
    {| dist_natural := @dist_natural_prod_;
       dist_morph := @dist_morph_prod;
       dist_unit := @dist_unit_prod;
       dist_linear := @dist_linear_prod;
    |}.

End TraversableFunctor_prod.
