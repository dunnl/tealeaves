From Tealeaves Require Export
  Classes.Categorical.Applicative.

Import Functor.Notations.

#[local] Generalizable Variable X Y T U G ϕ A B.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments pure F%function_scope {Pure} {A}%type_scope _.
#[local] Arguments mult F%function_scope {Mult} {A B}%type_scope _.

(** * Traversable functors *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Class ApplicativeDist (F : Type -> Type) :=
  dist : forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G},
      F ○ G ⇒ G ○ F.

#[global] Arguments dist (F)%function_scope {ApplicativeDist} G%function_scope  {H H0 H1} {A}%type_scope _.

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

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'δ'" := dist : tealeaves_scope.
End Notations.
