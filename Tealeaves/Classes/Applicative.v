From Tealeaves Require Export
     Util.Product
     Classes.Monoid
     Classes.Functor.

Import Product.Notations.
Import Functor.Notations.
#[local] Open Scope tealeaves_scope.

Create HintDb tea_applicative discriminated.

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
    `{Fmap G} `{Pure G} `{Mult G}.

  Class Applicative :=
    { app_functor :> Functor G;
      app_pure_natural : forall (A B : Type) (f : A -> B) (x : A),
          fmap G f (pure G x) = pure G (f x);
      app_mult_natural : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : G A) (y : G B),
          fmap G f x ⊗ fmap G g y = fmap G (map_tensor f g) (x ⊗ y);
      app_assoc : forall (A B C : Type) (x : G A) (y : G B) (z : G C),
          fmap G α ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z);
      app_unital_l : forall (A : Type) (x : G A),
          fmap G left_unitor (pure G tt ⊗ x) = x;
      app_unital_r : forall (A : Type) (x : G A),
          fmap G right_unitor (x ⊗ pure G tt) = x;
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
          ϕ (fmap F f x) = fmap G f (ϕ x);
      appmor_pure : forall (A : Type) (a : A),
          ϕ (pure F a) = pure G a;
      appmor_mult : forall (A B : Type) (x : F A) (y : F B),
          ϕ (x ⊗ y) = ϕ x ⊗ ϕ y;
    }.

End applicative_morphism.

(** ** Other coherence properties *)
(******************************************************************************)
Lemma triangle_1 `{Applicative F} : forall A (t : F A),
    pure F tt ⊗ t = fmap F (left_unitor_inv) t.
Proof.
  intros. rewrite <- (app_unital_l F A t) at 2.
  compose near (pure F tt ⊗ t). rewrite (fun_fmap_fmap F).
  rewrite (unitors_1). now rewrite (fun_fmap_id F).
Qed.

Lemma triangle_2 `{Applicative F} : forall A (t : F A),
    t ⊗ pure F tt = fmap F (right_unitor_inv) t.
Proof.
  intros. rewrite <- (app_unital_r F A t) at 2.
  compose near (t ⊗ pure F tt). rewrite (fun_fmap_fmap F).
  rewrite (unitors_3). now rewrite (fun_fmap_id F).
Qed.

Lemma triangle_3 `{Applicative F} : forall A (a : A) B (t : F B),
    pure F a ⊗ t = strength F (a, t).
Proof.
  intros. unfold strength. rewrite <- (app_unital_l F B t) at 2.
  compose near (pure F tt ⊗ t).
  rewrite (fun_fmap_fmap F).
  replace (pair a ∘ left_unitor) with (map_fst (X := unit) (Y := B) (const a)).
  2:{ now ext [[] ?]. }
  unfold map_fst. rewrite <- (app_mult_natural F).
  rewrite (app_pure_natural F).
  now rewrite (fun_fmap_id F).
Qed.

Lemma triangle_4 `{Applicative F} : forall A (a : A) B (t : F B),
    t ⊗ pure F a = fmap F (fun b => (b, a)) t.
Proof.
  intros. rewrite <- (app_unital_r F B t) at 2.
  compose near (t ⊗ pure F tt).
  rewrite (fun_fmap_fmap F).
  replace ((fun b => (b, a)) ∘ right_unitor) with (map_snd (X := B) (Y := unit) (const a)).
  2:{ now ext [? []]. }
  unfold map_snd. rewrite <- (app_mult_natural F).
  rewrite (app_pure_natural F).
  now rewrite (fun_fmap_id F).
Qed.

Lemma weird_1 `{Applicative F} : forall A,
    fmap F left_unitor ∘ mult F ∘ pair (pure F tt) = @id (F A).
Proof.
  intros. ext t. unfold compose. rewrite triangle_1.
  compose near t on left.
  rewrite (fun_fmap_fmap F).
  rewrite unitors_2.
  now rewrite (fun_fmap_id F).
Qed.

Lemma weird_2  `{Applicative F} : forall A,
    fmap F right_unitor ∘ mult F ∘ (fun b : F A => (b, pure F tt)) = @id (F A).
Proof.
  intros. ext t. unfold compose. rewrite triangle_2.
  compose near t on left.
  rewrite (fun_fmap_fmap F).
  rewrite unitors_4.
  now rewrite (fun_fmap_id F).
Qed.

(** ** Other basic consequences *)
(******************************************************************************)
Section Applicative_corollaries.

  Context
    (F : Type -> Type)
    `{Applicative F}.

  Lemma app_mult_natural_l :
    forall {A B C : Type} (f : A -> C) (x : F A) (y : F B),
      fmap F f x ⊗ y = fmap F (map_fst f) (x ⊗ y).
  Proof.
    intros. replace y with (fmap F id y) at 1
      by (now rewrite (fun_fmap_id F)).
    now rewrite (app_mult_natural F).
  Qed.

  Lemma app_mult_natural_r :
    forall {A B D : Type} (g : B -> D) (x : F A) (y : F B),
      x ⊗ fmap F g y = fmap F (map_snd g) (x ⊗ y).
  Proof.
    intros. replace x with (fmap F id x) at 1
      by (now rewrite (fun_fmap_id F)).
    now rewrite (app_mult_natural F).
  Qed.

  Corollary app_mult_natural_1 :
    forall {A B C E : Type} (f : A -> C) (h : C * B -> E) (x : F A) (y : F B),
      fmap F h (fmap F f x ⊗ y) = fmap F (h ∘ map_fst f) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_l.
    compose near (x ⊗ y) on left. now rewrite (fun_fmap_fmap F).
  Qed.

  Corollary app_mult_natural_2 :
    forall {A B D E : Type} (g : B -> D) (h : A * D -> E) (x : F A) (y : F B),
      fmap F h (x ⊗ fmap F g y) = fmap F (h ∘ map_snd g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_r.
    compose near (x ⊗ y) on left. now rewrite (fun_fmap_fmap F).
  Qed.

  Lemma app_assoc_inv : forall (A B C : Type) (x : F A) (y : F B) (z : F C),
      fmap F (α^-1) (x ⊗ (y ⊗ z)) = (x ⊗ y ⊗ z).
  Proof.
    intros. rewrite <- (app_assoc F).
    compose near (x ⊗ y ⊗ z). rewrite (fun_fmap_fmap F).
    rewrite (associator_iso_1). now rewrite (fun_fmap_id F).
  Qed.

End Applicative_corollaries.

Definition ap (G : Type -> Type) `{Fmap G} `{Mult G} {A B : Type} :
  G (A -> B) -> G A -> G B
  := fun Gf Ga => fmap G (fun '(f, a) => f a) (Gf ⊗ Ga).

#[local] Notation "Gf <⋆> Ga" := (ap _ Gf Ga) (at level 50, left associativity).

(** * The "ap" combinator << <⋆> >> *)
(******************************************************************************)
Section ApplicativeFunctor_ap.

  Context
    `{Applicative G}.

  Theorem fmap_to_ap : forall `(f : A -> B) (t : G A),
      fmap G f t = pure G f <⋆> t.
  Proof.
    intros. unfold ap; cbn.
    rewrite triangle_3. unfold strength.
    compose near t on right. rewrite (fun_fmap_fmap G).
    reflexivity.
  Qed.

  Theorem ap1 : forall `(t : G A),
      pure G id <⋆> t = t.
  Proof.
    intros. rewrite <- fmap_to_ap.
    now rewrite (fun_fmap_id G).
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
    now do 2 rewrite (fun_fmap_fmap G).
  Qed.

  Theorem ap4 : forall `(f : G (B -> C)) `(g : G (A -> B)) (a : G A),
      pure G (compose) <⋆> f <⋆> g <⋆> a =
      f <⋆> (g <⋆> a).
  Proof.
    intros. unfold ap; cbn.
    rewrite (app_mult_natural_1 G).
    rewrite (app_mult_natural_2 G).
    rewrite triangle_3. unfold strength.
    compose near f on left. rewrite (fun_fmap_fmap G).
    rewrite <- (app_assoc G).
    compose near (f ⊗ g ⊗ a). rewrite (fun_fmap_fmap G).
    rewrite <- (app_assoc_inv G).
    rewrite (app_mult_natural_1 G).
    rewrite <- (app_assoc G).
    compose near (f ⊗ g ⊗ a) on left.
    rewrite (fun_fmap_fmap G).
    compose near (f ⊗ g ⊗ a) on left.
    repeat rewrite (fun_fmap_fmap G).
    fequal. now ext [[x y] z].
  Qed.

  Corollary ap5 : forall {A B C} (f : A -> B) (g : B -> C) (t : G A),
      pure G g <⋆> fmap G f t = fmap G (g ∘ f) t.
  Proof.
    intros. rewrite fmap_to_ap. rewrite <- ap4.
    rewrite ap2. rewrite ap2. now rewrite fmap_to_ap.
  Qed.

  Corollary ap6 : forall {A B C} (x : G (A -> B)) (y : G A) (f : B -> C),
      fmap G f (x <⋆> y) = fmap G (compose f) x <⋆> y.
  Proof.
    intros. rewrite fmap_to_ap. rewrite fmap_to_ap.
    rewrite <- ap4. now rewrite <- ap2.
  Qed.

  Definition precompose {A B C } := (fun (f : A -> B) (g : B -> C)  => g ○ f).

  Corollary ap7 : forall {A B C} (x : G (A -> B)) (y : G C) (f : C -> A),
      (fmap G (precompose f) x <⋆> y) = x <⋆> fmap G f y.
  Proof.
    intros. rewrite fmap_to_ap. rewrite fmap_to_ap.
    rewrite <- ap4. rewrite ap3. rewrite <- ap4.
    rewrite ap2. rewrite ap2. reflexivity.
  Qed.

  Corollary ap8 : forall `(f : G (B -> C)) `(g : G (A -> B)) (a : G A),
      fmap G compose f <⋆> g <⋆> a =
      f <⋆> (g <⋆> a).
  Proof.
    intros. rewrite <- ap4. now rewrite fmap_to_ap.
  Qed.

  Theorem ap_morphism_1 : forall `{ApplicativeMorphism G G2} {A B}
                            (x : G (A -> B)) (y : G A),
      ϕ B (x <⋆> y) = (ϕ (A -> B) x) <⋆> ϕ A y.
  Proof.
    intros. unfold ap.
    rewrite (appmor_natural G G2).
    now rewrite (appmor_mult G G2).
  Qed.

End ApplicativeFunctor_ap.

(** * Applicative functors form a monoidal category *)
(******************************************************************************)

(** ** The identity applicative functor *)
(******************************************************************************)
Instance Pure_I : Pure (fun A => A) := @id.

Instance Mult_I : Mult (fun A => A) := fun A B (p : A * B) => p.

#[program] Instance Applicative_I : Applicative (fun A => A).

(** ** Composition of applicative functors *)
(******************************************************************************)
Section applicative_compose.

  Context
    (G1 G2 : Type -> Type)
    `{Applicative G1}
    `{Applicative G2}.

  #[global] Instance Pure_compose : Pure (G2 ∘ G1) :=
    fun (A : Type) (a : A) => pure G2 (pure G1 a).

  #[global] Instance Mult_compose : Mult (G2 ∘ G1) :=
    fun (A B : Type) (p : G2 (G1 A) * G2 (G1 B)) =>
        fmap G2 (mult G1) (mult G2 (fst p, snd p)) : G2 (G1 (A * B)).

  Lemma app_mult_pure_compose : forall (A B : Type) (a : A) (b : B),
      pure (G2 ∘ G1) a ⊗ pure (G2 ∘ G1) b = pure (G2 ∘ G1) (a, b).
  Proof.
    intros. unfold transparent tcs. cbn.
    assert (square: forall (p : G1 A * G1 B), fmap G2 (mult G1) (pure G2 p) = pure G2 (mult G1 p))
      by (intros; now rewrite (app_pure_natural G2)).
    rewrite <- (app_mult_pure G1). (* top triangle *)
    rewrite <- square. (* bottom right square *)
    rewrite <- (app_mult_pure G2). (* bottom left triangle *)
    reflexivity.
  Qed.

  Lemma app_pure_nat_compose : forall (A B : Type) (f : A -> B) (x : A),
      fmap (G2 ∘ G1) f (pure (G2 ∘ G1) x) = pure (G2 ∘ G1) (f x).
  Proof.
    intros. unfold transparent tcs.
    rewrite 2(app_pure_natural _).
    reflexivity.
  Qed.

  Lemma app_mult_nat_compose : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : G2 (G1 A)) (y : G2 (G1 B)),
      mult _ (fmap _ f x, fmap _ g y) = fmap _ (map_tensor f g) (mult _ (x, y)).
  Proof.
    intros. unfold transparent tcs. cbn [fst snd].
    rewrite (app_mult_natural G2).
    compose near (mult G2 (x, y)) on left.
    rewrite (fun_fmap_fmap G2).
    compose near (mult G2 (x, y)) on right.
    rewrite (fun_fmap_fmap G2).
    fequal. ext [fa fb].
    unfold compose.
    rewrite <- (app_mult_natural G1).
    reflexivity.
  Qed.

  Theorem app_asc_compose : forall A B C (x : G2 (G1 A)) (y : G2 (G1 B)) (z : G2 (G1 C)),
      fmap (G2 ∘ G1) α (x ⊗ y ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. unfold transparent tcs. cbn.
    replace (fmap G2 (mult G1) (x ⊗ y) ⊗ z) with
        (fmap G2 (map_tensor (mult G1) id) ((x ⊗ y) ⊗ z)).
    2: { rewrite <- (app_mult_natural G2). now rewrite (fun_fmap_id G2). }
    compose near ((x ⊗ y) ⊗ z); rewrite (fun_fmap_fmap G2).
    compose near ((x ⊗ y) ⊗ z); rewrite (fun_fmap_fmap G2).
    replace (x ⊗ fmap G2 (mult G1) (y ⊗ z)) with
        (fmap G2 (map_tensor id (mult G1)) (x ⊗ (y ⊗ z))).
    2: { rewrite <- (app_mult_natural G2). now rewrite (fun_fmap_id G2). }
    compose near (x ⊗ (y ⊗ z)); rewrite (fun_fmap_fmap G2).
    rewrite <- (app_assoc G2).
    compose near (x ⊗ y ⊗ z) on right; rewrite (fun_fmap_fmap G2).
    { fequal. ext [[? ?] ?]. unfold compose, id; cbn.
      now rewrite (app_assoc G1). }
  Qed.

  Theorem app_unital_l_compose : forall A (x : G2 (G1 A)),
      fmap (G2 ∘ G1) left_unitor (pure (G2 ∘ G1) tt ⊗ x) = x.
  Proof.
    intros. unfold transparent tcs. cbn.
    compose near (pure G2 (pure G1 tt) ⊗ x).
    rewrite (fun_fmap_fmap G2). rewrite triangle_3.
    unfold strength. compose near x on left.
    rewrite (fun_fmap_fmap G2). rewrite weird_1.
    now rewrite (fun_fmap_id G2).
  Qed.

  Theorem app_unital_r_compose : forall (A : Type) (x : (G2 ∘ G1) A),
      fmap (G2 ∘ G1) right_unitor (x ⊗ pure (G2 ∘ G1) tt) = x.
  Proof.
    unfold compose. intros. unfold transparent tcs. cbn.
    compose near (x ⊗ pure G2 (pure G1 tt)).
    rewrite (fun_fmap_fmap G2). rewrite triangle_4.
    compose near x on left. rewrite (fun_fmap_fmap G2).
     rewrite weird_2.
    now rewrite (fun_fmap_id G2).
  Qed.

  #[global] Program Instance Applicative_compose : Applicative (G2 ∘ G1) :=
    {| app_mult_pure := app_mult_pure_compose;
       app_pure_natural := app_pure_nat_compose;
       app_mult_natural := app_mult_nat_compose;
       app_assoc := app_asc_compose;
       app_unital_l := app_unital_l_compose;
       app_unital_r := app_unital_r_compose;
    |}.

  Theorem ap_compose_1 {A B} : forall (x : G2 (G1 (A -> B))) (y : G2 (G1 A)),
      (x <⋆> (y : (G2 ∘ G1) A)) =
      fmap G2 (uncurry (ap G1)) (x ⊗ y : G2 (G1 (A -> B) * G1 A)).
  Proof.
    intros. unfold ap. unfold_ops @Fmap_compose.
    unfold_ops @Mult_compose. cbn.
    compose near (x ⊗ y) on left.
    rewrite (fun_fmap_fmap G2). fequal. now ext [? ?].
  Qed.

  Theorem ap_compose_2 {A B} : forall (x : G2 (G1 (A -> B))) (y : G2 (G1 A)),
      (ap (G2 ○ G1) x y) = fmap G2 (uncurry (ap G1)) (x ⊗ y).
  Proof.
    apply ap_compose_1.
  Qed.

  Theorem ap_compose_3 {A B} : forall (x : G2 (G1 (A -> B))) (y : G2 (G1 A)),
      (ap (G2 ○ G1) x y) = ap G2 (fmap G2 (ap G1) x) y.
  Proof.
    intros. rewrite ap_compose_2.
    unfold ap at 2.
    rewrite (app_mult_natural_l G2).
    compose near (x ⊗ y) on right.
    rewrite (fun_fmap_fmap G2). fequal.
    now ext [? ?].
  Qed.

End applicative_compose.

Section applicative_compose_laws.

  Context
    `{Applicative G}.

  Theorem Mult_compose_identity1 :
    Mult_compose (fun A => A) G = @mult G _.
  Proof.
    ext A B [x y]. cbv in x, y. unfold Mult_compose.
    rewrite (fun_fmap_id G). reflexivity.
  Qed.

  Theorem Mult_compose_identity2 :
    Mult_compose G (fun A => A) = @mult G _.
  Proof.
    ext A B [x y]. cbv in x, y. unfold Mult_compose.
    reflexivity.
  Qed.

End applicative_compose_laws.

(** * Cartesian product of applicative functors *)
(******************************************************************************)
Inductive ProductFunctor (G1 G2 : Type -> Type) (A : Type) :=
| product : G1 A -> G2 A -> ProductFunctor G1 G2 A.

#[global] Arguments product {G1 G2}%function_scope {A}%type_scope _ _.

#[local] Notation "G1 ◻ G2" := (ProductFunctor G1 G2) (at level 50) : tealeaves_scope.

Definition pi1 {F G A} : (F ◻ G) A -> F A :=
  fun '(product x _) => x.

Definition pi2 {F G A} : (F ◻ G) A -> G A :=
  fun '(product _ y) => y.

Definition traversal_combine `(f : A -> F B) `(g : A -> G B) : A -> (F ◻ G) B :=
  fun a => product (f a) (g a).

#[local] Notation "f <◻> g" := (traversal_combine f g) (at level 60) : tealeaves_scope.

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

  #[global] Instance Fmap_Product : Fmap (F ◻ G) :=
    fun A B (f : A -> B) (p : (F ◻ G) A) =>
      match p with product x y => product (fmap F f x) (fmap G f y) end.

  #[global] Instance Functor_Product : Functor (F ◻ G).
  Proof.
    constructor.
    - introv. ext [?]. cbn. now rewrite 2(fun_fmap_id _).
    - introv. ext [?]. cbn. now rewrite <- 2(fun_fmap_fmap _).
  Qed.

  #[global] Instance Pure_Product : Pure (F ◻ G) :=
    fun A (a : A) => product (pure F a) (pure G a).

  #[global] Instance Mult_Product : Mult (F ◻ G) :=
    fun A B (p : (F ◻ G) A * (F ◻ G) B) =>
      match p with
      | (product fa ga , product fb gb) =>
        product (mult F (fa, fb)) (mult G (ga, gb))
      end.

  #[global] Instance Applicative_Product : Applicative (F ◻ G).
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
  Notation "x ⊗ y" := (mult _ (x, y)) (at level 50, left associativity) : tealeaves_scope.
  Notation "Gf <⋆> Ga" := (ap _ Gf Ga) (at level 50, left associativity).
  Notation "F ◻ G" := (ProductFunctor F G) (at level 50) : tealeaves_scope.
  Notation "f <◻> g" := (traversal_combine f g) (at level 60) : tealeaves_scope.
End Notations.
