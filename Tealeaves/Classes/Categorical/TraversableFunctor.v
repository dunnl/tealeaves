From Tealeaves Require Export
  Classes.Functor
  Classes.Categorical.Applicative.

Import Functor.Notations.
Import Applicative.Notations.

#[local] Generalizable Variable X Y T U G ϕ A B.

(** * Traversable functors *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Class ApplicativeDist (F : Type -> Type) :=
  dist : forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G},
      F ○ G ⇒ G ○ F.

#[global] Arguments dist (F)%function_scope {ApplicativeDist} G%function_scope  {H H0 H1} {A}%type_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments pure F%function_scope {Pure} {A}%type_scope _.
#[local] Arguments mult F%function_scope {Mult} {A B}%type_scope _.

(** ** Typeclass *)
(******************************************************************************)
Class TraversableFunctor
  (F : Type -> Type)
  `{Map F} `{ApplicativeDist F} :=
  { trav_functor :> Functor F;
    dist_natural :> forall `{Applicative G},
        @Natural (F ∘ G) _ (G ∘ F) _ (@dist F _ G _ _ _);
    dist_morph : forall `{ApplicativeMorphism G1 G2 ϕ},
      `(dist F G2 ∘ map F (ϕ A) = ϕ (F A) ∘ dist F G1);
    dist_unit :
    `(dist F (fun A => A) = id (A := F A));
    dist_linear : forall `{Applicative G1} `{Applicative G2},
      `(dist F (G1 ∘ G2) = map G1 (dist F G2) ∘ dist F G1 (A := G2 A));
  }.

(** ** Distribution-respecting natural transformations *)
(******************************************************************************)
Class TraversableMorphism
  (T U : Type -> Type)
  `{Map T} `{Map U} `{ApplicativeDist T}
  `{ApplicativeDist U} (ϕ : T ⇒ U) :=
    { trvmor_trv_F : TraversableFunctor T;
      trvmor_trv_G : TraversableFunctor U;
      trvmor_nat :> Natural ϕ;
      trvmor_hom : forall `{Applicative G},
          `(map G (ϕ A) ∘ dist T G = dist U G ∘ ϕ (G A));
    }.

(** * Basic properties of traversable functors *)
(******************************************************************************)

(** ** <<pure>> is an applicative homomorphism *)
(******************************************************************************)
Section pure_as_applicative_transformation.

  Context
    `{Applicative G}.

  Lemma pure_appmor_1 : forall A B (f : A -> B) (t : A),
      pure G (map (fun A : Type => A) f t) = map G f (pure G t).
  Proof.
    intros. now rewrite app_pure_natural.
  Qed.

  Lemma pure_appmor_2 : forall (A : Type) (a : A),
      pure G (pure (fun A => A) a) = pure G a.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma pure_appmor_3 : forall (A B : Type) (a : A) (b : B),
      pure G (mult (fun A => A) (a, b)) = mult G (pure G a, pure G b).
  Proof.
    unfold transparent tcs. intros. now rewrite app_mult_pure.
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
    `{TraversableFunctor T}.

  Corollary map_purity_1 : forall `{Applicative G},
      `(dist T G ∘ map T (pure G) = pure G (A := T A)).
  Proof.
    intros. rewrite (dist_morph (ϕ := @pure G _)).
    now rewrite (dist_unit).
  Qed.

  Corollary map_purity_2 :
    forall `{Applicative G1} `{Applicative G2} `(f : A -> G1 B),
      dist T (G2 ∘ G1) ∘ map T (pure G2 ∘ f) = pure G2 ∘ dist T G1 ∘ map T f.
  Proof.
    intros. rewrite <- (fun_map_map).
    reassociate <-. rewrite dist_linear.
    reassociate -> near (map T (pure G2)).
    rewrite map_purity_1.
    fequal. ext t. unfold compose.
    now rewrite app_pure_natural.
  Qed.

End purity_law.

Require Import Tealeaves.Functors.Categorical.Reader.

(** * Traversable instance for certain functors *)
(******************************************************************************)

(** ** Traversable instance for (E ×)> *)
(******************************************************************************)
Section TraversableFunctor_prod.

  Generalizable All Variables.

  Context
    (E : Type).

  #[global] Instance Dist_prod : ApplicativeDist (prod E) :=
    fun F Fmap mlt pur A '(x, a) => map F (pair x) a.

  Lemma dist_natural_prod : forall `{Applicative G} `(f : A -> B),
      map (G ∘ prod E) f ∘ dist (prod E) G = dist (prod E) G ∘ map (prod E ∘ G) f.
  Proof.
    intros. ext [x a]; cbn.
    unfold compose; cbn.
    unfold_ops @Map_compose.
    compose near a.
    do 2 rewrite fun_map_map.
    reflexivity.
  Qed.

  Instance dist_natural_prod_ : forall `{Applicative G}, Natural (@dist (prod E) _ G _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    intros. eapply (dist_natural_prod f).
  Qed.

  Lemma dist_morph_prod : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist (prod E) G2 ∘ map (prod E) (ϕ A) = ϕ (E * A) ∘ dist (prod E) G1.
  Proof.
    intros; unfold compose; cbn. ext [x a]; cbn.
    now rewrite appmor_natural.
  Qed.

  Lemma dist_unit_prod : forall (A : Type),
      dist (prod E) (fun A => A) = @id (prod E A).
  Proof.
    intros; unfold compose; cbn. ext [x a]; now cbn.
  Qed.

  Lemma dist_linear_prod : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (prod E) (G1 ∘ G2) =
      map G1 (dist (prod E) G2) ∘ dist (prod E) G1 (A := G2 A).
  Proof.
    intros; unfold compose; cbn. ext [x a].
    unfold_ops @Dist_prod @Map_compose.
    compose near a on right.
    now rewrite fun_map_map.
  Qed.

  #[global] Instance Traversable_prod :
    Classes.Categorical.TraversableFunctor.TraversableFunctor (prod E) :=
    {| dist_natural := @dist_natural_prod_;
       dist_morph := @dist_morph_prod;
       dist_unit := @dist_unit_prod;
       dist_linear := @dist_linear_prod;
    |}.

End TraversableFunctor_prod.

(** * Distribution over certain applicative functors *)
(******************************************************************************)

(** ** Constant applicative functors *)
(** To distributive over constant applicative functors, i.e. to fold
    over monoidal values, we can use the <<Const>> applicative
    functor. This tends to clutter operations with <<unconst>>
    operations which get in the way of convenient rewriting. We
    provide a lighter-weight alternative in this section and some
    specifications proving equivalence with the <<Const>> versions. *)
(******************************************************************************)
From Tealeaves Require Import Classes.Monoid Functors.Constant.

Section TraversableFunctor_const.

  #[local] Generalizable Variable M.

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
             Map_const Pure_const Mult_const X)
      =
      (@dist T _ (const M)
             Map_const Pure_const Mult_const False).
  Proof.
    intros. symmetry. change (?f = ?g) with (f = g ∘ (@id (T M))).
    rewrite <- fun_map_id.
    change (@id M) with
        (map (A := False) (B:=X) (const M) exfalso).
    change (map T (map (const M) ?f))
      with (map (T ∘ const M) f).
    rewrite <- (natural (ϕ := @dist T _ (const M) _ _ _) (B := X) (A := False)).
    reflexivity.
  Qed.

  Lemma dist_const2 : forall (X Y : Type) `{Monoid M},
      (@dist T _ (const M)
             Map_const Pure_const Mult_const X)
      =
      (@dist T _ (const M)
             Map_const Pure_const Mult_const Y).
  Proof.
    intros. now rewrite (dist_const1 X), (dist_const1 Y).
  Qed.

  (** *** Distribution over [Const] vs <<const>> *)
  (******************************************************************************)
  Theorem traversable_const_spec (tag : Type) `{Monoid M} :
    unconst ∘ @dist T _ (Const M)
            Map_Const
            Pure_Const
            Mult_Const tag ∘ map T mkConst
    = @dist T _ (const M)
            Map_const
            Pure_const
            Mult_const tag.
  Proof.
    intros. rewrite <- (dist_morph (ϕ := @unconst _)).
    reassociate -> on left. rewrite fun_map_map.
    change (unconst ∘ mkConst) with (@id M).
    now rewrite fun_map_id.
  Qed.

End TraversableFunctor_const.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'δ'" := dist : tealeaves_scope.
End Notations.
