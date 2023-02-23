From Tealeaves Require Export
  Classes.Functor
  Applicative.

Import Functor.Notations.
Import Applicative.Notations.

#[local] Generalizable Variable X Y T U G ϕ A.

(** * Traversable functors *)
(******************************************************************************)
Section TraversableFunctor_operation.

  Context
    (F : Type -> Type).

  Class Dist :=
    dist : forall (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}, F ○ G ⇒ G ○ F.

End TraversableFunctor_operation.

Section TraversableFunctor.

  Context
    (F : Type -> Type)
    `{Functor F}
    `{Dist F}.

  Class TraversableFunctor :=
    { trav_functor :> Functor F;
      dist_natural :> forall `{Applicative G},
          @Natural (F ∘ G) _ (G ∘ F) _ (dist F G);
      dist_morph : forall `{ApplicativeMorphism G1 G2 ϕ} A,
          dist F G2 A ∘ fmap F (ϕ A) = ϕ (F A) ∘ dist F G1 A;
      dist_unit :
        `(dist F (fun A => A) A = id);
      dist_linear : forall `{Applicative G1} `{Applicative G2},
          `(dist F (G1 ∘ G2) A = fmap G1 (dist F G2 A) ∘ dist F G1 (G2 A));
    }.

End TraversableFunctor.

#[global] Arguments dist F%function_scope {Dist} G%function_scope {H H0 H1} {A}%type_scope.

(** ** Distribution-respecting natural transformations *)
(******************************************************************************)
Section TraversableMorphism.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  Class TraversableMorphism (ϕ : T ⇒ U) :=
    { trvmor_trv_F : TraversableFunctor T;
      trvmor_trv_G : TraversableFunctor U;
      trvmor_nat :> Natural ϕ;
      trvmor_hom : forall `{Applicative G},
          `(fmap G (ϕ A) ∘ dist T G = dist U G ∘ ϕ (G A));
    }.

End TraversableMorphism.

(** * Monoid structure of traversable functors *)
(******************************************************************************)

(** ** The identity functor is traversable *)
(******************************************************************************)
#[export] Instance Dist_I : Dist (fun A => A) := fun F fmap mult pure A a => a.

#[export, program] Instance Traversable_I : TraversableFunctor (fun A => A).

Next Obligation.
  constructor; try typeclasses eauto.
  intros. ext a. unfold transparent tcs.
  reflexivity.
Qed.

Next Obligation.
  unfold transparent tcs. ext a.
  symmetry. now rewrite (fun_fmap_id G1).
Qed.

(** ** Traversable functors are closed under composition *)
(******************************************************************************)
Section TraversableFunctor_compose.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  #[export] Instance Dist_compose : Dist (T ∘ U) :=
    fun G map mult pure A =>
      dist T G ∘ fmap T (dist U G (A := A)).

  Lemma dist_unit_compose : forall A,
      dist (T ∘ U) (fun A => A) = @id (T (U A)).
  Proof.
    intros. unfold transparent tcs.
    rewrite (dist_unit T).
    rewrite (dist_unit U).
    now rewrite (fun_fmap_id T).
  Qed.

  Lemma dist_natural_compose : forall `{Applicative G} `(f : X -> Y),
      fmap (G ∘ (T ∘ U)) f ∘ dist (T ∘ U) G = dist (T ∘ U) G ∘ fmap ((T ∘ U) ∘ G) f.
  Proof.
    intros. unfold transparent tcs.
    change_left (fmap (G ∘ T) (fmap U f) ∘ dist T G ∘ fmap T (dist U G)).
    #[local] Set Keyed Unification.
    rewrite (natural (ϕ := @dist T _ G _ _ _ ) (F := T ∘ G)).
    #[local] Unset Keyed Unification.
    unfold_ops @Fmap_compose.
    reassociate -> on left.
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    rewrite (fun_fmap_fmap T).
    change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f).
    now rewrite <- (natural (ϕ := @dist U _ G _ _ _)).
  Qed.

  Instance dist_natural_compose_ : forall `{Applicative G}, Natural (@dist (T ∘ U) _ G _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    intros. apply dist_natural_compose.
  Qed.

  Lemma dist_morph_compose : forall `{ApplicativeMorphism G1 G2 ϕ} (A : Type),
      dist (T ∘ U) G2 ∘ fmap (T ∘ U) (ϕ A) = ϕ (T (U A)) ∘ dist (T ∘ U) G1.
  Proof.
    intros. unfold transparent tcs.
    reassociate -> on left.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    rewrite (dist_morph U).
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on left.
    now rewrite (dist_morph T).
  Qed.

  Lemma dist_linear_compose : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (T ∘ U) (G1 ∘ G2) = fmap G1 (dist (T ∘ U) G2) ∘ dist (T ∘ U) G1 (A := G2 A).
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap G1).
    reassociate -> on right;
      change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f);
      reassociate <- near (fmap (G1 ∘ T) (dist U G2)).
    #[local] Set Keyed Unification.
    rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
    #[local] Unset Keyed Unification.
    reassociate -> on right;
      unfold_ops @Fmap_compose;
      rewrite (fun_fmap_fmap T).
    #[local] Set Keyed Unification.
    rewrite (dist_linear U).
    rewrite (dist_linear T).
    #[local] Unset Keyed Unification.
    reflexivity.
  Qed.

  #[export] Instance Traversable_compose : TraversableFunctor (T ∘ U) :=
    {| dist_morph := @dist_morph_compose;
       dist_unit := @dist_unit_compose;
       dist_linear := @dist_linear_compose;
    |}.

End TraversableFunctor_compose.

(** * Basic properties of traversable functors *)
(******************************************************************************)

(** ** <<pure>> is an applicative homomorphism *)
(******************************************************************************)
Section pure_as_applicative_transformation.

  Context
    `{Applicative G}.

  Lemma pure_appmor_1 : forall A B (f : A -> B) (t : A),
      pure G (fmap (fun A : Type => A) f t) = fmap G f (pure G t).
  Proof.
    intros. now rewrite (app_pure_natural G).
  Qed.

  Lemma pure_appmor_2 : forall (A : Type) (a : A),
      pure G (pure (fun A => A) a) = pure G a.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma pure_appmor_3 : forall (A B : Type) (a : A) (b : B),
      pure G (mult (fun A => A) (a, b)) = mult G (pure G a, pure G b).
  Proof.
    unfold transparent tcs. intros. now rewrite (app_mult_pure G).
  Qed.

  #[export] Instance ApplicativeMorphism_pure :
    ApplicativeMorphism (fun A => A) G (@pure G _) :=
    {| appmor_natural := pure_appmor_1;
       appmor_pure := pure_appmor_2;
       appmor_mult := pure_appmor_3;
    |}.

End pure_as_applicative_transformation.

(** ** Other rules for <<pure>> *)
(******************************************************************************)
Section purity_law.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Corollary fmap_purity_1 `{Applicative G} : forall A,
    dist T G ∘ fmap T (pure G) (A := A) = pure G.
  Proof.
    intros. rewrite (dist_morph T (ϕ := @pure G _)).
    now rewrite (dist_unit T).
  Qed.

  Corollary fmap_purity_2 {B} `{Applicative G1} `{Applicative G2} : forall `(f : A -> G1 B),
      dist T (G2 ∘ G1) ∘ fmap T (pure G2 ∘ f) = pure G2 ∘ dist T G1 ∘ fmap T f.
  Proof.
    intros. rewrite <- (fun_fmap_fmap T).
    reassociate <-. rewrite (dist_linear T).
    reassociate -> near (fmap T (pure G2)).
    rewrite fmap_purity_1.
    fequal. ext t. unfold compose.
    now rewrite (app_pure_natural G2).
  Qed.

End purity_law.

(** * Kleisi presentation of traversable functors *)
(******************************************************************************)

From Tealeaves Require
  Classes.Kleisli.Traversable.Functor.

Module ToKleisli.

  Import Classes.Kleisli.Traversable.Functor.
  
  Section operation.

    Context
      (T : Type -> Type)
      `{Fmap T} `{Dist T}.

    #[export] Instance Traverse_dist : Traverse T :=
      fun (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
        (A B : Type) (f : A -> G B) => dist T G ∘ fmap T f.

  End operation.
  
  Section with_functor.

    Generalizable All Variables.
    
    Context
      (T : Type -> Type)
      `{Classes.Traversable.Functor.TraversableFunctor T}.

    Theorem traverse_id : forall (A : Type),
        traverse T (fun A => A) id = @id (T A).
    Proof.
      intros. unfold traverse. unfold_ops @Traverse_dist.
      ext t. rewrite (dist_unit T).
      now rewrite (fun_fmap_id T).
    Qed.

    Theorem traverse_id_purity : forall `{Applicative G} (A : Type),
        traverse T G (pure G) = @pure G _ (T A).
    Proof.
      intros. unfold traverse.
      unfold_ops @Traverse_dist.
      ext t. now rewrite fmap_purity_1.
    Qed.

    Lemma traverse_traverse (G1 G2 : Type -> Type) `{Applicative G2} `{Applicative G1} :
      forall `(g : B -> G2 C) `(f : A -> G1 B),
        fmap G1 (traverse T G2 g) ∘ traverse T G1 f = traverse T (G1 ∘ G2) (fmap G1 g ∘ f).
    Proof.
      introv. unfold traverse.
      unfold_ops @Traverse_dist.
      rewrite (dist_linear T).
      repeat reassociate <-.
      rewrite <- (fun_fmap_fmap T).
      repeat reassociate <-.
      reassociate -> near (fmap T (fmap G1 g)).
      change (fmap T (fmap G1 g)) with (fmap (T ∘ G1) g).
      rewrite <- (natural (ϕ := @dist T _ G1 _ _ _)).
      unfold_ops @Fmap_compose.
      reassociate <-.
      unfold_compose_in_compose.
      now rewrite (fun_fmap_fmap G1).
    Qed.

    Lemma traverse_morphism `{morph : ApplicativeMorphism G1 G2 ϕ} : forall `(f : A -> G1 B),
        ϕ (T B) ∘ traverse T G1 f = traverse T G2 (ϕ B ∘ f).
    Proof.
      intros. unfold traverse.  unfold_ops @Traverse_dist.
      reassociate <-.
      inversion morph.
      rewrite <- (dist_morph T).
      reassociate ->.
      now rewrite (fun_fmap_fmap T).
    Qed.

    #[export] Instance: Kleisli.Traversable.Functor.TraversableFunctor T :=
      {| trf_traverse_id := @traverse_id;
        trf_traverse_traverse := @traverse_traverse;
        trf_traverse_morphism := @traverse_morphism;
      |}.

  End with_functor.

End ToKleisli.

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

Require Import Tealeaves.Classes.Monad.
Require Import Tealeaves.Functors.List.
Import List.ListNotations.

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

#[export] Hint Rewrite @dist_list_nil @dist_list_cons_1
     @dist_list_one @dist_list_app : tea_list.

Section dist_list_properties.

  #[local] Arguments dist _%function_scope {Dist} _%function_scope {H H0 H1}
    A%type_scope _.

  Generalizable All Variables.
  
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

#[export] Instance Traversable_list : Classes.Traversable.Functor.TraversableFunctor list :=
  {| dist_natural := @dist_natural_list_;
     dist_morph := @dist_morph_list;
     dist_unit := @dist_unit_list;
     dist_linear := @dist_linear_list;
  |}.

Require Import Tealeaves.Functors.Environment.

(** * Traversable instance for <<prod>> *)
(******************************************************************************)
Section TraversableFunctor_prod.

  Generalizable All Variables.
  
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

  #[global] Instance Traversable_prod : Classes.Traversable.Functor.TraversableFunctor (prod X) :=
    {| dist_natural := @dist_natural_prod_;
       dist_morph := @dist_morph_prod;
       dist_unit := @dist_unit_prod;
       dist_linear := @dist_linear_prod;
    |}.

End TraversableFunctor_prod.

From Tealeaves Require Import Classes.Monoid Functors.Constant.
  
(** * Operations involving constant applicative functors *)
(******************************************************************************)
(** To distributive over constant applicative functors, i.e. to fold
    over monoidal values, we can use the <<Const>> applicative
    functor. Unfortunately this tends to clutter operations with
    <<unconst>> operations which get in the way of convenient
    rewriting. We provide a lighter-weight alternative in this section
    and some specifications proving equivalence with the <<Const>>
    versions. *)
Section TraversableFunctor_const.

  Generalizable Variable M.
  
  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  (** *** Distribution over <<const>> is agnostic about the tag. *)
  (** Distribution over a constant applicative functor is agnostic
      about the type argument ("tag") to the constant functor. On
      paper it is easy to ignore this, but in Coq this must be
      proved. Observe this equality is ill-typed if [Const] is used instead. *)
  (******************************************************************************)
  Lemma dist_const1 : forall (X : Type) `{Monoid M},
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) X)
      =
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) False).
  Proof.
    intros. symmetry. change (?f = ?g) with (f = g ∘ (@id (T M))).
    rewrite <- (fun_fmap_id T).
    change (@id M) with
        (fmap (A := False) (B:=X) (const M) exfalso).
    change (fmap T (fmap (const M) ?f))
      with (fmap (T ∘ const M) f).
    rewrite <- (natural (ϕ := @dist T _ (const M) _ _ _) (B := X) (A := False)).
    reflexivity.
  Qed.

  Lemma dist_const2 : forall (X Y : Type) `{Monoid M},
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) X)
      =
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) Y).
  Proof.
    intros. now rewrite (dist_const1 X), (dist_const1 Y).
  Qed.

  (** *** Distribution over [Const] vs <<const>> *)
  (******************************************************************************)
  Theorem traversable_const_spec (tag : Type) `{Monoid M} :
    unconst ∘ @dist T _ (Const M)
            (Fmap_Const)
            (Pure_Const)
            (Mult_Const) tag ∘ fmap T (mkConst)
    = @dist T _ (const M)
            (Fmap_const)
            (Pure_const)
            (Mult_const) tag.
  Proof.
    intros. rewrite <- (dist_morph T (ϕ := @unconst _)).
    reassociate -> on left. rewrite (fun_fmap_fmap T).
    change (unconst ∘ mkConst) with (@id M).
    now rewrite (fun_fmap_id T).
  Qed.

End TraversableFunctor_const.

From Tealeaves Require Import Functors.ProductFunctor.
Import ProductFunctor.Notations.

Definition traversal_combine {F G A B} `(f : A -> F B) `(g : A -> G B) : A -> (F ◻ G) B :=
  fun a => product (f a) (g a).

#[local] Notation "f <◻> g" := (traversal_combine f g) (at level 60) : tealeaves_scope.

(** * Characterization of distribution w.r.t. (F ◻ G) *)
(******************************************************************************)
Section traversable_product.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G1}
    `{Applicative G2}.

  Export Classes.Kleisli.Traversable.Functor.
  Import Traversable.Functor.ToKleisli.

  Variables
    (A B : Type)
    (f : A -> G1 B) (g : A -> G2 B).

  Lemma dist_combine1 : forall (t : T A),
    pi1 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G1 f t.
  Proof.
    intros. pose (ApplicativeMorphism_pi1 G1 G2).
    compose near t on left.
    now rewrite (trf_traverse_morphism T).
  Qed.

  Lemma dist_combine2 : forall (t : T A),
    pi2 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G2 g t.
  Proof.
    intros. pose (ApplicativeMorphism_pi2 G1 G2).
    compose near t on left.
    now rewrite (traverse_morphism T).
  Qed.

  Theorem dist_combine : forall (t : T A),
    dist T (G1 ◻ G2) (fmap T (f <◻> g) t) =
    product (traverse T G1 f t) (traverse T G2 g t).
  Proof.
    intros. compose near t on left.
    erewrite <- (dist_combine1).
    erewrite <- (dist_combine2).
    now rewrite <- product_eta.
  Qed.

  Theorem traverse_combine :
    traverse T (G1 ◻ G2) (f <◻> g) = (traverse T G1 f) <◻> (traverse T G2 g).
  Proof.
    intros. unfold_ops Traverse_dist.
    ext t. unfold compose.
    now rewrite dist_combine.
  Qed.

End traversable_product.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'δ'" := (dist) : tealeaves_scope.
  Notation "f <◻> g" := (traversal_combine f g) (at level 60) : tealeaves_scope.
End Notations.

(** * Decomposing <<dist>> in terms of <<iterate>> *)
(******************************************************************************)
Section traversal_iterate.

  Import Classes.Kleisli.Traversable.Functor.

  Context
    `{Classes.Traversable.Functor.TraversableFunctor T}.

  Import Traversable.Functor.ToKleisli.

  Lemma dist_to_runBatch `{Applicative G} {A : Type} :
    dist T G (A := A) = runBatch (@id (G A)) ∘ Functor.toBatch T A.
  Proof.
    ext t.
    replace t with (fmap T id t) at 1 by (now rewrite (fun_fmap_id T)).
    change_left (traverse T G (@id (G A)) t).
    now rewrite (traverse_to_runBatch T).
  Qed.

End traversal_iterate.
