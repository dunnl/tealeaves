From Tealeaves.Classes Require Export
  Functor
  Categorical.Applicative
  Monoid.

Import Monoid.Notations.

(** * Cartesian product of functors *)
(******************************************************************************)
Inductive ProductFunctor (G1 G2 : Type -> Type) (A : Type) :=
| product : G1 A -> G2 A -> ProductFunctor G1 G2 A.

#[global] Arguments product {G1 G2}%function_scope {A}%type_scope _ _.

#[local] Notation "G1 ◻ G2" := (ProductFunctor G1 G2) (at level 50) : tealeaves_scope.

Definition pi1 {F G A} : (F ◻ G) A -> F A :=
  fun '(product x _) => x.

Definition pi2 {F G A} : (F ◻ G) A -> G A :=
  fun '(product _ y) => y.

Theorem product_eta G1 G2 A : forall (x : (G1 ◻ G2) A),
    x = product (pi1 x) (pi2 x).
Proof.
  intros. now destruct x.
Qed.

(** ** Functor instance *)
(******************************************************************************)
#[export] Instance Map_Product (F G : Type -> Type) `{Map F} `{Map G} : Map (F ◻ G) :=
  fun A B (f : A -> B) (p : (F ◻ G) A) =>
    match p with product x y => product (map f x) (map f y)
    end.

#[export] Instance Functor_Product (F G : Type -> Type) `{Functor F} `{Functor G} : Functor (F ◻ G).
Proof.
  constructor.
  - introv. ext [?]. cbn. now rewrite 2(fun_map_id _).
  - introv. ext [?]. cbn. now rewrite <- 2(fun_map_map _).
Qed.

(** ** Applicative functor instance *)
(******************************************************************************)

(** *** Operations *)
(******************************************************************************)
#[export] Instance Pure_Product (F G : Type -> Type)
  `{Pure F} `{Pure G} : Pure (F ◻ G) :=
  fun A (a : A) => product (pure a) (pure a).

#[export] Instance Mult_Product (F G : Type -> Type)
  `{Mult F} `{Mult G} : Mult (F ◻ G) :=
  fun A B (p : (F ◻ G) A * (F ◻ G) B) =>
    match p with
    | (product fa ga , product fb gb) =>
        product (mult (fa, fb)) (mult (ga, gb))
    end.

(** *** Applicative instance *)
(******************************************************************************)
Section product_applicative.

  Context
    (F G : Type -> Type)
    `{Applicative F}
    `{Applicative G}.

  #[export] Instance Applicative_Product : Applicative (F ◻ G).
  Proof.
    constructor; try typeclasses eauto.
    - introv. cbn. now rewrite 2(app_pure_natural _).
    - introv. unfold transparent tcs. destruct x, y.
      now rewrite 2(app_mult_natural _).
    - introv. unfold transparent tcs. destruct x, y, z.
      now rewrite 2(app_assoc _).
    - introv. unfold transparent tcs. destruct x.
      now rewrite 2(app_unital_l _).
    - introv. unfold transparent tcs. destruct x.
      now rewrite 2(app_unital_r _).
    - introv. unfold transparent tcs. cbn.
      now rewrite 2(app_mult_pure _).
  Qed.

End product_applicative.

(** *** Some applicative morphisms *)
(******************************************************************************)
Theorem ApplicativeMorphism_pi1
  (F G : Type -> Type)
  `{Applicative F}
  `{Applicative G}
  : ApplicativeMorphism (F ◻ G) F (@pi1 _ _).
Proof.
  intros. constructor; try typeclasses eauto.
  - intros. now destruct x.
  - intros. reflexivity.
  - intros. now destruct x, y.
Qed.

Theorem ApplicativeMorphism_pi2
  (F G : Type -> Type)
  `{Applicative F}
  `{Applicative G}
  : ApplicativeMorphism (F ◻ G) G (@pi2 _ _).
Proof.
  intros. constructor; try typeclasses eauto.
  - intros. now destruct x.
  - intros. reflexivity.
  - intros. now destruct x, y.
Qed.

Theorem ApplicativeMorphism_product
  (F1 F2 G1 G2 : Type -> Type)
  `{Applicative F1}
  `{Applicative F2}
  `{Applicative G1}
  `{Applicative G2}
  ϕ1 ϕ2
  `{! ApplicativeMorphism F1 G1 ϕ1} `{! ApplicativeMorphism F2 G2 ϕ2}
  : ApplicativeMorphism (F1 ◻ F2) (G1 ◻ G2) (fun A '(product f1 f2) => product (ϕ1 A f1) (ϕ2 A f2)).
Proof.
  intros. inversion ApplicativeMorphism0.
  inversion ApplicativeMorphism1.
  constructor; try typeclasses eauto.
  - intros. destruct x. cbn.
    rewrite appmor_natural.
    rewrite appmor_natural0.
    reflexivity.
  - intros. cbn.
    rewrite appmor_pure.
    rewrite appmor_pure0.
    reflexivity.
  - intros. destruct x; destruct y. cbn.
    rewrite appmor_mult.
    rewrite appmor_mult0.
    reflexivity.
Qed.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "F ◻ G" := (ProductFunctor F G) (at level 50) : tealeaves_scope.
End Notations.
