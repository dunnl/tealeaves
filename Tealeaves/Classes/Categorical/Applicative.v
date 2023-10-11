From Tealeaves Require Export
  Tactics.Prelude
  Classes.Functor
  Misc.Product
  Misc.Strength
  Functors.Identity
  Functors.Compose.

Import Product.Notations.

#[local] Generalizable Variables F G A B C.

(** * Applicative functors *)
(******************************************************************************)
Section Applicative_operations.

  Context
    (F : Type -> Type).

  Class Pure := pure : forall {A}, A -> F A.
  Class Mult := mult : forall {A B : Type}, F A * F B -> F (A * B).

End Applicative_operations.

#[local] Notation "x ⊗ y" := (mult _ (x, y)) (at level 50, left associativity).

Section Applicative.

  Context
    (G : Type -> Type)
      `{Map G} `{Pure G} `{Mult G}.

  Class Applicative :=
    { app_functor :> Functor G;
      app_pure_natural : forall (A B : Type) (f : A -> B) (x : A),
        map G f (pure G x) = pure G (f x);
      app_mult_natural : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : G A) (y : G B),
        map G f x ⊗ map G g y = map G (map_tensor f g) (x ⊗ y);
      app_assoc : forall (A B C : Type) (x : G A) (y : G B) (z : G C),
        map G α ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z);
      app_unital_l : forall (A : Type) (x : G A),
        map G left_unitor (pure G tt ⊗ x) = x;
      app_unital_r : forall (A : Type) (x : G A),
        map G right_unitor (x ⊗ pure G tt) = x;
      app_mult_pure : forall (A B : Type) (a : A) (b : B),
        pure G a ⊗ pure G b = pure G (a, b);
    }.

End Applicative.

(** ** Homomorphisms between applicative functors *)
(******************************************************************************)
Section applicative_morphism.

  Context
    (F G : Type -> Type)
    `{Applicative F}
    `{Applicative G}.

  Class ApplicativeMorphism (ϕ : forall {A}, F A -> G A) :=
    { appmor_app_F : `{Applicative F};
      appmor_app_G : `{Applicative G};
      appmor_natural : forall (A B : Type) (f : A -> B) (x : F A),
          ϕ (map F f x) = map G f (ϕ x);
      appmor_pure : forall (A : Type) (a : A),
          ϕ (pure F a) = pure G a;
      appmor_mult : forall (A B : Type) (x : F A) (y : F B),
          ϕ (x ⊗ y) = ϕ x ⊗ ϕ y;
    }.

End applicative_morphism.

(** *** The identity transformation on any <<F>> is a homomorphism *)
(******************************************************************************)
#[export] Instance ApplicativeMorphism_id `{Applicative F} :
  ApplicativeMorphism F F (fun A => @id (F A)).
Proof.
  constructor; now try typeclasses eauto.
Qed.

(** * Basic coherence properties *)
(** TODO: Find a better name. I don't remember why these are
named @triangle_x@. *)
(******************************************************************************)
Lemma triangle_1 `{Applicative F} : forall A (t : F A),
    pure F tt ⊗ t = map F (left_unitor_inv) t.
Proof.
  intros. rewrite <- (app_unital_l F A t) at 2.
  compose near (pure F tt ⊗ t). rewrite (fun_map_map).
  rewrite (unitors_1). now rewrite (fun_map_id).
Qed.

Lemma triangle_2 `{Applicative F} : forall A (t : F A),
    t ⊗ pure F tt = map F (right_unitor_inv) t.
Proof.
  intros. rewrite <- (app_unital_r F A t) at 2.
  compose near (t ⊗ pure F tt). rewrite (fun_map_map).
  rewrite (unitors_3). now rewrite (fun_map_id).
Qed.

Lemma triangle_3 `{Applicative F} : forall A (a : A) B (t : F B),
    pure F a ⊗ t = strength F (a, t).
Proof.
  intros. unfold strength. rewrite <- (app_unital_l F B t) at 2.
  compose near (pure F tt ⊗ t).
  rewrite (fun_map_map).
  replace (pair a ∘ left_unitor) with (map_fst (X := unit) (Y := B) (const a)).
  2:{ now ext [[] ?]. }
  unfold map_fst. rewrite <- (app_mult_natural F).
  rewrite (app_pure_natural F).
  now rewrite (fun_map_id).
Qed.

Lemma triangle_4 `{Applicative F} : forall A (a : A) B (t : F B),
    t ⊗ pure F a = map F (fun b => (b, a)) t.
Proof.
  intros. rewrite <- (app_unital_r F B t) at 2.
  compose near (t ⊗ pure F tt).
  rewrite (fun_map_map).
  replace ((fun b => (b, a)) ∘ right_unitor) with (map_snd (X := B) (Y := unit) (const a)).
  2:{ now ext [? []]. }
  unfold map_snd. rewrite <- (app_mult_natural F).
  rewrite (app_pure_natural F).
  now rewrite (fun_map_id).
Qed.

Lemma weird_1 `{Applicative F} : forall A,
    map F left_unitor ∘ mult F ∘ pair (pure F tt) = @id (F A).
Proof.
  intros. ext t. unfold compose. rewrite triangle_1.
  compose near t on left.
  rewrite (fun_map_map).
  rewrite unitors_2.
  now rewrite (fun_map_id).
Qed.

Lemma weird_2  `{Applicative F} : forall A,
    map F right_unitor ∘ mult F ∘ (fun b : F A => (b, pure F tt)) = @id (F A).
Proof.
  intros. ext t. unfold compose. rewrite triangle_2.
  compose near t on left.
  rewrite (fun_map_map).
  rewrite unitors_4.
  now rewrite (fun_map_id).
Qed.

(** ** Mapping and reassociating <<⊗>> *)
(******************************************************************************)
Section Applicative_corollaries.

  Context
    (F : Type -> Type)
    `{Applicative F}.

  Lemma app_mult_natural_l :
    forall {A B C : Type} (f : A -> C) (x : F A) (y : F B),
      map F f x ⊗ y = map F (map_fst f) (x ⊗ y).
  Proof.
    intros. replace y with (map F id y) at 1
      by (now rewrite (fun_map_id)).
    now rewrite (app_mult_natural F).
  Qed.

  Lemma app_mult_natural_r :
    forall {A B D : Type} (g : B -> D) (x : F A) (y : F B),
      x ⊗ map F g y = map F (map_snd g) (x ⊗ y).
  Proof.
    intros. replace x with (map F id x) at 1
      by (now rewrite (fun_map_id)).
    now rewrite (app_mult_natural F).
  Qed.

  Corollary app_mult_natural_1 :
    forall {A B C E : Type} (f : A -> C) (h : C * B -> E) (x : F A) (y : F B),
      map F h (map F f x ⊗ y) = map F (h ∘ map_fst f) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_l.
    compose near (x ⊗ y) on left. now rewrite (fun_map_map).
  Qed.

  Corollary app_mult_natural_2 :
    forall {A B D E : Type} (g : B -> D) (h : A * D -> E) (x : F A) (y : F B),
      map F h (x ⊗ map F g y) = map F (h ∘ map_snd g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_r.
    compose near (x ⊗ y) on left. now rewrite (fun_map_map).
  Qed.

  Lemma app_assoc_inv : forall (A B C : Type) (x : F A) (y : F B) (z : F C),
      map F (α^-1) (x ⊗ (y ⊗ z)) = (x ⊗ y ⊗ z).
  Proof.
    intros. rewrite <- (app_assoc F).
    compose near (x ⊗ y ⊗ z). rewrite (fun_map_map).
    rewrite (associator_iso_1). now rewrite (fun_map_id).
  Qed.

End Applicative_corollaries.

(** * The category of applicative functors *)
(******************************************************************************)

(** ** The identity applicative functor *)
(******************************************************************************)
#[export] Instance Pure_I : Pure (fun A => A) := @id.

#[export] Instance Mult_I : Mult (fun A => A) := fun A B (p : A * B) => p.

#[export, program] Instance Applicative_I : Applicative (fun A => A).

(** *** <<pure F>> is a homomorphism from the identity functor *)
(******************************************************************************)
Section pure_as_applicative_transformation.

  Context
    `{Applicative G}.

  Lemma pure_appmor_1 : forall A B (f : A -> B) (t : A),
      pure G (map (fun A : Type => A) f t) = map G f (pure G t).
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

(** ** Composition of applicative functors *)
(******************************************************************************)
Section applicative_compose.

  Context
    (G2 G1 : Type -> Type)
    `{Applicative G1}
    `{Applicative G2}.

  #[export] Instance Pure_compose : Pure (G2 ∘ G1) :=
    fun (A : Type) (a : A) => pure G2 (pure G1 a).

  #[export] Instance Mult_compose : Mult (G2 ∘ G1) :=
    fun (A B : Type) (p : G2 (G1 A) * G2 (G1 B)) =>
        map G2 (mult G1) (mult G2 (fst p, snd p)) : G2 (G1 (A * B)).

  Lemma app_mult_pure_compose : forall (A B : Type) (a : A) (b : B),
      pure (G2 ∘ G1) a ⊗ pure (G2 ∘ G1) b = pure (G2 ∘ G1) (a, b).
  Proof.
    intros. unfold transparent tcs. cbn.
    assert (square: forall (p : G1 A * G1 B), map G2 (mult G1) (pure G2 p) = pure G2 (mult G1 p))
      by (intros; now rewrite (app_pure_natural G2)).
    rewrite <- (app_mult_pure G1). (* top triangle *)
    rewrite <- square. (* bottom right square *)
    rewrite <- (app_mult_pure G2). (* bottom left triangle *)
    reflexivity.
  Qed.

  Lemma app_pure_nat_compose : forall (A B : Type) (f : A -> B) (x : A),
      map (G2 ∘ G1) f (pure (G2 ∘ G1) x) = pure (G2 ∘ G1) (f x).
  Proof.
    intros. unfold transparent tcs.
    rewrite 2(app_pure_natural _).
    reflexivity.
  Qed.

  Lemma app_mult_nat_compose : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : G2 (G1 A)) (y : G2 (G1 B)),
      mult _ (map _ f x, map _ g y) = map _ (map_tensor f g) (mult _ (x, y)).
  Proof.
    intros. unfold transparent tcs. cbn [fst snd].
    rewrite (app_mult_natural G2).
    compose near (mult G2 (x, y)) on left.
    rewrite (fun_map_map).
    compose near (mult G2 (x, y)) on right.
    rewrite (fun_map_map).
    fequal. ext [fa fb].
    unfold compose.
    rewrite <- (app_mult_natural G1).
    reflexivity.
  Qed.

  Theorem app_asc_compose : forall A B C (x : G2 (G1 A)) (y : G2 (G1 B)) (z : G2 (G1 C)),
      map (G2 ∘ G1) α (x ⊗ y ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. unfold transparent tcs. cbn.
    replace (map G2 (mult G1) (x ⊗ y) ⊗ z) with
        (map G2 (map_tensor (mult G1) id) ((x ⊗ y) ⊗ z)).
    2: { rewrite <- (app_mult_natural G2). now rewrite (fun_map_id). }
    compose near ((x ⊗ y) ⊗ z); rewrite (fun_map_map).
    compose near ((x ⊗ y) ⊗ z); rewrite (fun_map_map).
    replace (x ⊗ map G2 (mult G1) (y ⊗ z)) with
        (map G2 (map_tensor id (mult G1)) (x ⊗ (y ⊗ z))).
    2: { rewrite <- (app_mult_natural G2). now rewrite (fun_map_id). }
    compose near (x ⊗ (y ⊗ z)); rewrite (fun_map_map).
    rewrite <- (app_assoc G2).
    compose near (x ⊗ y ⊗ z) on right; rewrite (fun_map_map).
    { fequal. ext [[? ?] ?]. unfold compose, id; cbn.
      now rewrite (app_assoc G1). }
  Qed.

  Theorem app_unital_l_compose : forall A (x : G2 (G1 A)),
      map (G2 ∘ G1) left_unitor (pure (G2 ∘ G1) tt ⊗ x) = x.
  Proof.
    intros. unfold transparent tcs. cbn.
    compose near (pure G2 (pure G1 tt) ⊗ x).
    rewrite (fun_map_map). rewrite triangle_3.
    unfold strength. compose near x on left.
    rewrite (fun_map_map). rewrite weird_1.
    now rewrite (fun_map_id).
  Qed.

  Theorem app_unital_r_compose : forall (A : Type) (x : (G2 ∘ G1) A),
      map (G2 ∘ G1) right_unitor (x ⊗ pure (G2 ∘ G1) tt) = x.
  Proof.
    unfold compose. intros. unfold transparent tcs. cbn.
    compose near (x ⊗ pure G2 (pure G1 tt)).
    rewrite (fun_map_map). rewrite triangle_4.
    compose near x on left. rewrite (fun_map_map).
     rewrite weird_2.
    now rewrite (fun_map_id).
  Qed.

  #[export, program] Instance Applicative_compose : Applicative (G2 ∘ G1) :=
    {| app_mult_pure := app_mult_pure_compose;
       app_pure_natural := app_pure_nat_compose;
       app_mult_natural := app_mult_nat_compose;
       app_assoc := app_asc_compose;
       app_unital_l := app_unital_l_compose;
       app_unital_r := app_unital_r_compose;
    |}.

End applicative_compose.

(** *** Composing applicative functors with the identity *)
(******************************************************************************)
Section applicative_compose_laws.

  Context
    `{Applicative G}.

  Theorem Pure_compose_identity1 :
    Pure_compose G (fun A => A) = @pure G _.
  Proof.
    easy.
  Qed.

  Theorem Pure_compose_identity2 :
    Pure_compose (fun A => A) G = @pure G _.
  Proof.
    easy.
  Qed.

  Theorem Mult_compose_identity1 :
    Mult_compose G (fun A => A) = @mult G _.
  Proof.
    ext A B [x y]. cbv in x, y. unfold Mult_compose.
    rewrite (fun_map_id). reflexivity.
  Qed.

  Theorem Mult_compose_identity2 :
    Mult_compose (fun A => A) G = @mult G _.
  Proof.
    ext A B [x y]. cbv in x, y. unfold Mult_compose.
    reflexivity.
  Qed.

End applicative_compose_laws.

(** * The "ap" combinator << <⋆> >> *)
(******************************************************************************)
Definition ap (G : Type -> Type) `{Map G} `{Mult G} {A B : Type} :
  G (A -> B) -> G A -> G B
  := fun Gf Ga => map G (fun '(f, a) => f a) (Gf ⊗ Ga).

#[local] Notation "Gf <⋆> Ga" := (ap _ Gf Ga) (at level 50, left associativity).

Section ApplicativeFunctor_ap.

  Context
    `{Applicative G}.

  Theorem map_to_ap : forall `(f : A -> B) (t : G A),
      map G f t = pure G f <⋆> t.
  Proof.
    intros. unfold ap; cbn.
    rewrite triangle_3. unfold strength.
    compose near t on right. rewrite (fun_map_map).
    reflexivity.
  Qed.

  Theorem ap_morphism_1 :
    forall `{ApplicativeMorphism G G2} {A B}
      (x : G (A -> B)) (y : G A),
      ϕ B (x <⋆> y) = (ϕ (A -> B) x) <⋆> ϕ A y.
  Proof.
    intros. unfold ap.
    rewrite (appmor_natural G G2).
    now rewrite (appmor_mult G G2).
  Qed.

  Theorem ap1 : forall `(t : G A),
      pure G id <⋆> t = t.
  Proof.
    intros. rewrite <- map_to_ap.
    now rewrite (fun_map_id).
  Qed.

  Theorem ap2 : forall `(f : A -> B) (a : A),
      pure G f <⋆> pure G a = pure G (f a).
  Proof.
    intros. unfold ap. rewrite (app_mult_pure G).
    now rewrite (app_pure_natural G).
  Qed.

  Theorem ap3 : forall `(f : G (A -> B)) (a : A),
      f <⋆> pure G a = pure G (fun f => f a) <⋆> f.
  Proof.
    intros. unfold ap. rewrite triangle_3, triangle_4.
    unfold strength. compose near f.
    now do 2 rewrite (fun_map_map).
  Qed.

  Theorem ap4 : forall {A B C : Type} (f : G (B -> C)) (g : G (A -> B)) (a : G A),
      (pure G compose) <⋆> f <⋆> g <⋆> a =
      f <⋆> (g <⋆> a).
  Proof.
    intros. unfold ap; cbn.
    rewrite (app_mult_natural_1 G).
    rewrite (app_mult_natural_2 G).
    rewrite triangle_3. unfold strength.
    compose near f on left. rewrite (fun_map_map).
    rewrite <- (app_assoc G).
    compose near (f ⊗ g ⊗ a). rewrite (fun_map_map).
    rewrite <- (app_assoc_inv G).
    rewrite (app_mult_natural_1 G).
    rewrite <- (app_assoc G).
    compose near (f ⊗ g ⊗ a) on left.
    rewrite (fun_map_map).
    compose near (f ⊗ g ⊗ a) on left.
    repeat rewrite (fun_map_map).
    fequal. now ext [[x y] z].
  Qed.

End ApplicativeFunctor_ap.

(** ** Convenience laws for <<ap>> *)
(******************************************************************************)
Section ApplicativeFunctor_ap_utility.

  Context
    `{Applicative G}
     {A B C D : Type}.

  (** Fuse <<pure>> into <<map>> *) (*ap5*)
  Corollary pure_ap_map : forall (f : A -> B) (g : B -> C) (a : G A),
      pure G g <⋆> map G f a = map G (g ∘ f) a.
  Proof.
    intros.
    do 2 rewrite map_to_ap.
    rewrite <- ap4.
    do 2 rewrite ap2.
    reflexivity.
  Qed.

  (** Push an <<map>> under an <<ap>> *)
  Corollary map_ap : forall (f : G (A -> B)) (g : B -> C) (a : G A),
      map G g (f <⋆> a) = map G (compose g) f <⋆> a.
  Proof.
    intros.
    do 2 rewrite map_to_ap.
    rewrite <- ap4.
    rewrite ap2.
    reflexivity.
  Qed.

  Theorem map_ap2 : forall (g : B -> C),
    compose (map G g) ∘ ap G (A := A) = ap G ∘ map G (compose g).
  Proof.
    intros. ext f a. unfold compose.
    rewrite map_ap. reflexivity.
  Qed.

  (** Bring an <<map>> from right of an <<ap>> to left *)
  Corollary ap_map : forall {A B C} (x : G (A -> B)) (y : G C) (f : C -> A),
      (map G (precompose f) x <⋆> y) = x <⋆> map G f y.
  Proof.
    intros. do 2 rewrite map_to_ap.
    rewrite <- ap4.
    rewrite ap3.
    rewrite <- ap4.
    do 2 rewrite ap2.
    reflexivity.
  Qed.

  Corollary ap_curry : forall (a : G A) (b: G B) (f : A -> B -> C),
      map G (uncurry f) (a ⊗ b) = pure G f <⋆> a <⋆> b.
  Proof.
    intros. unfold ap.
    rewrite (app_mult_natural_l G).
    compose near (pure G f ⊗ a ⊗ b).
    rewrite (fun_map_map).
    rewrite <- (app_assoc_inv G).
    compose near ((pure G f ⊗ (a ⊗ b))).
    rewrite (fun_map_map).
    rewrite triangle_3. unfold strength.
    compose near (a ⊗ b) on right.
    rewrite (fun_map_map).
    fequal. ext [a' b']. reflexivity.
  Qed.

  Section ap_compose.

  End ap_compose.

End ApplicativeFunctor_ap_utility.

(** ** Composition of functors and <<ap>> / << <⋆> >> *)
(******************************************************************************)
Section ap_compose.

  Context
    (G1 G2 : Type -> Type)
    `{Applicative G1}
    `{Applicative G2}
    {A B : Type}.

  Theorem ap_compose1 : forall (f : G2 (G1 (A -> B))) (a : G2 (G1 A)),
      ap (G2 ∘ G1) f a =
      pure G2 (ap G1) <⋆> f <⋆> a.
  Proof.
    intros. unfold ap at 1.
    unfold_ops @Map_compose.
    unfold_ops @Mult_compose.
    cbn. rewrite <- map_to_ap.
    compose near (f ⊗ a).
    rewrite (fun_map_map).
    unfold ap at 1.
    rewrite (app_mult_natural_l G2).
    compose near (f ⊗ a) on right.
    rewrite (fun_map_map).
    fequal. now ext [G1f G1a].
  Qed.

  Theorem ap_compose2 : forall (f: G2 (G1 (A -> B))) (a : G2 (G1 A)),
      ap (G2 ∘ G1) f a =
      map G2 (ap G1) f <⋆> a.
  Proof.
    intros. rewrite ap_compose1.
    now rewrite map_to_ap.
  Qed.


(*
  Theorem ap_compose3 :
    ap (G2 ∘ G1) (A := A) (B := B) =
      ap G2 ∘ map G2 (ap G1).
  Proof.
    intros. ext f a.
    rewrite (ap_compose1).
    now rewrite <- map_to_ap.
  Qed.

  Theorem ap_compose_new : forall `{Applicative G1} `{Applicative G2},
    forall (A B : Type) (x : G1 (G2 A))(f : A -> B),
      P (G1 ∘ G2) f <⋆> x =
        P G1 (ap G2 (P G2 f)) <⋆> x.
  Proof.
    intros. rewrite (ap_compose1 G2 G1).
    unfold_ops @Pure_compose.
    rewrite ap2.
    reflexivity.
  Qed.

*)
End ap_compose.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "x ⊗ y" := (mult _ (x, y)) (at level 50, left associativity) : tealeaves_scope.
  Notation "Gf <⋆> Ga" := (ap _ Gf Ga) (at level 50, left associativity).
End Notations.

Import Notations.

(** * Notations *)
(******************************************************************************)
From Tealeaves Require Import
  Classes.Monoid.

Import Monoid.Notations.

#[local] Generalizable Variables ϕ.

Section with_monoid.

  Context
    (G : Type -> Type)
    (M : Type)
    `{Applicative G}
    `{Monoid M}.

  #[export] Instance Monoid_op_applicative : Monoid_op (G M) :=
    fun m1 m2 => map G (uncurry monoid_op) (m1 ⊗ m2).

  #[export] Instance Monoid_unit_applicative : Monoid_unit (G M) :=
    pure G Ƶ.

  #[export] Instance Monoid_applicative : Monoid (G M).
  Proof.
    constructor.
    - intros. cbn. unfold_ops @Monoid_op_applicative.
      rewrite (app_mult_natural_l G).
      compose near (x ⊗ y ⊗ z) on left.
      rewrite (fun_map_map).
      rewrite (app_mult_natural_r G).
      rewrite <- (app_assoc G).
      compose near (x ⊗ y ⊗ z) on right.
      rewrite (fun_map_map).
      compose near (x ⊗ y ⊗ z) on right.
      rewrite (fun_map_map).
      fequal. ext [[m1 m2] m3].
      cbn. simpl_monoid.
      reflexivity.
    - intros. unfold_ops @Monoid_op_applicative.
      unfold_ops @Monoid_unit_applicative.
      rewrite ap_curry.
      rewrite <- map_to_ap.
      rewrite ap3.
      rewrite pure_ap_map.
      change x with (id x) at 2. rewrite <- (fun_map_id).
      fequal. ext m.
      unfold compose. now rewrite monoid_id_l.
    - intros. unfold_ops @Monoid_op_applicative.
      unfold_ops @Monoid_unit_applicative.
      rewrite ap_curry.
      rewrite ap2.
      rewrite <- map_to_ap.
      change x with (id x) at 2. rewrite <- (fun_map_id).
      fequal. ext m.
      unfold compose. now rewrite monoid_id_r.
  Qed.

End with_monoid.

Section with_hom.

  Context
    `{Applicative G}
    (M1 M2 : Type)
    `{Monoid_Morphism M1 M2 ϕ}.

  #[export] Instance Monoid_hom_applicative :
    Monoid_Morphism (map G ϕ).
  Proof.
    inversion H7.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - unfold_ops @Monoid_unit_applicative.
      rewrite (app_pure_natural G).
      now rewrite monmor_unit.
    - intros. unfold_ops @Monoid_op_applicative.
      compose near (a1 ⊗ a2).
      rewrite (fun_map_map).
      rewrite (app_mult_natural G).
      compose near (a1 ⊗ a2) on right.
      rewrite (fun_map_map).
      fequal. ext [m1 m2].
      unfold compose. cbn. rewrite monmor_op.
      reflexivity.
  Qed.

End with_hom.
