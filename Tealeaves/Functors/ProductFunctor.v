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

(** ** Cartesian product of applicative functors *)
(******************************************************************************)
Section product_applicative.

  Context
    (F G : Type -> Type)
    `{Applicative F}
    `{Applicative G}.

  #[export] Instance Map_Product : Map (F ◻ G) :=
    fun A B (f : A -> B) (p : (F ◻ G) A) =>
      match p with product x y => product (map F f x) (map G f y) end.

  #[export] Instance Functor_Product : Functor (F ◻ G).
  Proof.
    constructor.
    - introv. ext [?]. cbn. now rewrite 2(fun_map_id _).
    - introv. ext [?]. cbn. now rewrite <- 2(fun_map_map _).
  Qed.

  #[export] Instance Pure_Product : Pure (F ◻ G) :=
    fun A (a : A) => product (pure F a) (pure G a).

  #[export] Instance Mult_Product : Mult (F ◻ G) :=
    fun A B (p : (F ◻ G) A * (F ◻ G) B) =>
      match p with
      | (product fa ga , product fb gb) =>
        product (mult F (fa, fb)) (mult G (ga, gb))
      end.

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

  Theorem ApplicativeMorphism_pi1 : ApplicativeMorphism (F ◻ G) F (@pi1 _ _).
  Proof.
    intros. constructor; try typeclasses eauto.
    - intros. now destruct x.
    - intros. reflexivity.
    - intros. now destruct x, y.
  Qed.

  Theorem ApplicativeMorphism_pi2 : ApplicativeMorphism (F ◻ G) G (@pi2 _ _).
  Proof.
    intros. constructor; try typeclasses eauto.
    - intros. now destruct x.
    - intros. reflexivity.
    - intros. now destruct x, y.
  Qed.

End product_applicative.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "F ◻ G" := (ProductFunctor F G) (at level 50) : tealeaves_scope.
End Notations.
