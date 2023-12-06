From Tealeaves Require Export
  Tactics.Prelude
  Classes.Functor
  Misc.Product
  Misc.Strength
  Functors.Identity
  Functors.Compose.

Import Product.Notations.

#[local] Generalizable Variables ϕ F G A B C.

(** * Applicative functors *)
(******************************************************************************)
Class Pure (F : Type -> Type) :=
  pure : forall {A}, A -> F A.
Class Mult (F : Type -> Type) :=
  mult : forall {A B : Type}, F A * F B -> F (A * B).

#[local] Notation "x ⊗ y" := (mult (x, y)) (at level 50, left associativity).

Class Applicative (G : Type -> Type)
    `{Map G} `{Pure G} `{Mult G} :=
  { app_functor :> Functor G;
    app_pure_natural : forall (A B : Type) (f : A -> B) (x : A),
      map f (pure x) = pure (f x);
    app_mult_natural : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : G A) (y : G B),
      map f x ⊗ map g y = map (map_tensor f g) (x ⊗ y);
    app_assoc : forall (A B C : Type) (x : G A) (y : G B) (z : G C),
      map α ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z);
    app_unital_l : forall (A : Type) (x : G A),
      map left_unitor (pure tt ⊗ x) = x;
    app_unital_r : forall (A : Type) (x : G A),
      map right_unitor (x ⊗ pure tt) = x;
    app_mult_pure : forall (A B : Type) (a : A) (b : B),
      pure a ⊗ pure b = pure (a, b);
  }.

(** ** Homomorphisms between applicative functors *)
(******************************************************************************)
Class ApplicativeMorphism (F G : Type -> Type)
  `{Applicative F} `{Applicative G} (ϕ : forall {A}, F A -> G A) :=
  { appmor_app_F : `{Applicative F};
    appmor_app_G : `{Applicative G};
    appmor_natural : forall (A B : Type) (f : A -> B) (x : F A),
      ϕ (map f x) = map f (ϕ x);
    appmor_pure : forall (A : Type) (a : A),
      ϕ (pure a) = pure a;
    appmor_mult : forall (A B : Type) (x : F A) (y : F B),
      ϕ (x ⊗ y) = ϕ x ⊗ ϕ y;
  }.

(** *** The identity transformation on any <<F>> is a homomorphism *)
(******************************************************************************)
#[export] Instance ApplicativeMorphism_id `{Applicative F} :
  ApplicativeMorphism F F (fun A => @id (F A)).
Proof.
  constructor; now try typeclasses eauto.
Qed.

(** ** Basic lemmas *)
(** TODO: Find a better name. I don't remember why these are
named @triangle_x@. *)
(******************************************************************************)
Section basics.

  Context
    (F : Type -> Type)
    `{Applicative F}.

  Lemma triangle_1 : forall (A : Type) (t : F A),
      pure tt ⊗ t = map left_unitor_inv t.
  Proof.
    intros.
    rewrite <- (app_unital_l A t) at 2.
    compose near (pure tt ⊗ t).
    rewrite fun_map_map.
    rewrite unitors_1.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma triangle_2 : forall (A : Type) (t : F A),
      t ⊗ pure tt = map right_unitor_inv t.
  Proof.
    intros.
    rewrite <- (app_unital_r A t) at 2.
    compose near (t ⊗ pure tt).
    rewrite fun_map_map.
    rewrite unitors_3.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma triangle_3 : forall (A B : Type) (a : A) (t : F B),
      pure a ⊗ t = strength (a, t).
  Proof.
    intros.
    unfold strength.
    rewrite <- (app_unital_l B t) at 2.
    compose near (pure tt ⊗ t).
    rewrite fun_map_map.
    replace (pair a ∘ left_unitor) with
      (map_fst (X := unit) (Y := B) (const a)) by
      (now ext [[] ?]).
    unfold map_fst.
    rewrite <- app_mult_natural.
    rewrite app_pure_natural.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma triangle_4 : forall (A B : Type) (a : A) (t : F B),
      t ⊗ pure a = map (fun b => (b, a)) t.
  Proof.
    intros.
    rewrite <- (app_unital_r B t) at 2.
    compose near (t ⊗ pure tt).
    rewrite (fun_map_map).
    replace ((fun b => (b, a)) ∘ right_unitor) with
      (map_snd (X := B) (Y := unit) (const a))
      by (now ext [? []]).
    unfold map_snd.
    rewrite <- app_mult_natural.
    rewrite app_pure_natural.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma weird_1 : forall (A : Type),
      map left_unitor ∘ mult ∘ pair (pure tt) = @id (F A).
  Proof.
    intros. ext t.
    unfold compose.
    rewrite triangle_1.
    compose near t on left.
    rewrite fun_map_map.
    rewrite unitors_2.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma weird_2 : forall A,
      map right_unitor ∘ mult ∘ (fun b : F A => (b, pure tt)) = @id (F A).
  Proof.
    intros. ext t.
    unfold compose.
    rewrite triangle_2.
    compose near t on left.
    rewrite fun_map_map.
    rewrite unitors_4.
    rewrite fun_map_id.
    reflexivity.
  Qed.

End basics.

(** ** Mapping and reassociating <<⊗>> *)
(******************************************************************************)
Section Applicative_corollaries.

  Context
    (F : Type -> Type)
    `{Applicative F}.

  Lemma app_mult_natural_l :
    forall {A B C : Type} (f : A -> C) (x : F A) (y : F B),
      map f x ⊗ y = map (map_fst f) (x ⊗ y).
  Proof.
    intros.
    replace y with (map id y) at 1
      by (now rewrite fun_map_id).
    rewrite app_mult_natural.
    reflexivity.
  Qed.

  Lemma app_mult_natural_r :
    forall {A B D : Type} (g : B -> D) (x : F A) (y : F B),
      x ⊗ map g y = map (map_snd g) (x ⊗ y).
  Proof.
    intros.
    replace x with (map id x) at 1
      by (now rewrite fun_map_id).
    rewrite app_mult_natural.
    reflexivity.
  Qed.

  Corollary app_mult_natural_1 :
    forall {A B C E : Type} (f : A -> C) (h : C * B -> E) (x : F A) (y : F B),
      map h (map f x ⊗ y) = map (h ∘ map_fst f) (x ⊗ y).
  Proof.
    intros.
    rewrite app_mult_natural_l.
    compose near (x ⊗ y) on left.
    rewrite (fun_map_map).
    reflexivity.
  Qed.

  Corollary app_mult_natural_2 :
    forall {A B D E : Type} (g : B -> D) (h : A * D -> E) (x : F A) (y : F B),
      map h (x ⊗ map g y) = map (h ∘ map_snd g) (x ⊗ y).
  Proof.
    intros.
    rewrite app_mult_natural_r.
    compose near (x ⊗ y) on left.
    rewrite fun_map_map.
    reflexivity.
  Qed.

  Lemma app_assoc_inv :
    forall (A B C : Type) (x : F A) (y : F B) (z : F C),
      map α^-1 (x ⊗ (y ⊗ z)) = (x ⊗ y ⊗ z).
  Proof.
    intros.
    rewrite <- app_assoc.
    compose near (x ⊗ y ⊗ z).
    rewrite fun_map_map.
    rewrite associator_iso_1.
    rewrite fun_map_id.
    reflexivity.
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

  Lemma pure_appmor_1 : forall (A B : Type) (f : A -> B) (t : A),
      pure (map (F := fun A => A) f t) = map f (pure t).
  Proof.
    intros.
    rewrite app_pure_natural.
    reflexivity.
  Qed.

  Lemma pure_appmor_2 : forall (A : Type) (a : A),
      pure (F := G) (pure (F := fun A => A) a) = pure a.
  Proof.
    reflexivity.
  Qed.

  Lemma pure_appmor_3 : forall (A B : Type) (a : A) (b : B),
      pure (mult (F := fun A => A) (a, b)) = pure a ⊗ pure b.
  Proof.
    intros.
    unfold transparent tcs.
    rewrite app_mult_pure.
    reflexivity.
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
    fun (A : Type) (a : A) => pure (F := G2) (pure (F := G1) a).

  #[export] Instance Mult_compose : Mult (G2 ∘ G1) :=
    fun (A B : Type) (p : G2 (G1 A) * G2 (G1 B)) =>
      map (F := G2) (mult (F := G1))
        (mult (F := G2) (fst p, snd p)) : G2 (G1 (A * B)).

  Lemma app_mult_pure_compose : forall (A B : Type) (a : A) (b : B),
      pure (F := G2 ∘ G1) a ⊗ pure (F := G2 ∘ G1) b =
        pure (F := G2 ∘ G1) (a, b).
  Proof.
    intros.
    unfold transparent tcs. cbn.
    assert (square: forall (p : G1 A * G1 B),
               map mult (pure (F := G2) p) = pure (F := G2) (mult p)).
    { intros.
      rewrite app_pure_natural.
      reflexivity. }
    rewrite <- (app_mult_pure (G := G1)). (* top triangle *)
    rewrite <- square. (* bottom right square *)
    rewrite <- (app_mult_pure (G := G2)). (* bottom left triangle *)
    reflexivity.
  Qed.

  Lemma app_pure_nat_compose : forall (A B : Type) (f : A -> B) (x : A),
      map (F := G2 ∘ G1) f (pure (F := G2 ∘ G1) x) = pure (f x).
  Proof.
    intros.
    unfold transparent tcs.
    rewrite 2(app_pure_natural _).
    reflexivity.
  Qed.

  Lemma app_mult_nat_compose : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : G2 (G1 A)) (y : G2 (G1 B)),
      map f x ⊗ map g y = map (map_tensor f g) (x ⊗ y).
  Proof.
    intros. unfold transparent tcs. cbn [fst snd].
    rewrite (app_mult_natural).
    compose near (mult (x, y)) on left.
    rewrite (fun_map_map).
    compose near (mult (x, y)) on right.
    rewrite (fun_map_map).
    fequal. ext [fa fb].
    unfold compose.
    rewrite <- (app_mult_natural).
    reflexivity.
  Qed.

  Theorem app_asc_compose : forall A B C (x : G2 (G1 A)) (y : G2 (G1 B)) (z : G2 (G1 C)),
      map (F := G2 ∘ G1) α (x ⊗ y ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros.
    unfold transparent tcs. cbn.
    replace (map (F := G2) (mult (F := G1)) (x ⊗ y) ⊗ z) with
        (map (F := G2) (map_tensor (mult (F := G1)) id) ((x ⊗ y) ⊗ z)).
    2: { rewrite <- (app_mult_natural (G := G2)).
         now rewrite fun_map_id. }
    compose near (x ⊗ y ⊗ z) on left.
    rewrite fun_map_map.
    compose near (x ⊗ y ⊗ z) on left.
    rewrite fun_map_map.
    replace (x ⊗ map mult (y ⊗ z)) with
        (map (map_tensor id mult) (x ⊗ (y ⊗ z))).
    2: { rewrite <- app_mult_natural.
         rewrite fun_map_id.
         reflexivity. }
    compose near (x ⊗ (y ⊗ z)).
    rewrite fun_map_map.
    rewrite <- app_assoc.
    compose near (x ⊗ y ⊗ z) on right.
    rewrite fun_map_map.
    - fequal. ext [[ga gb] gc].
      unfold compose, id; cbn.
      rewrite app_assoc.
      reflexivity.
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
    (G : Type -> Type)
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

(** *** Parallel composition of applicative morphisms *)
(******************************************************************************)

Section applicative_compose_laws.

  #[export] Instance ApplicativeMorphism_parallel
    (F1 F2 G1 G2 : Type -> Type)
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative F1}
    `{Applicative F2}
    `{! ApplicativeMorphism F1 G1 ϕ1}
    `{! ApplicativeMorphism F2 G2 ϕ2} :
  ApplicativeMorphism (F1 ∘ F2) (G1 ∘ G2) (fun A => ϕ1 (G2 A) ∘ map F1 (ϕ2 A)).
  Proof.
    inversion ApplicativeMorphism0.
    inversion ApplicativeMorphism1.
    constructor; try typeclasses eauto.
    - intros.
      unfold_ops @Map_compose. unfold compose.
      compose near x.
      rewrite (fun_map_map (F := F1)).
      assert (appmor_natural1' : forall (A B : Type) (f : A -> B), ϕ2 B ∘ map F2 f = map G2 f ∘ ϕ2 A).
      { intros. ext f2a. apply appmor_natural1. }
      rewrite appmor_natural1'.
      rewrite <- (fun_map_map (F := F1)).
      unfold compose.
      rewrite appmor_natural0.
      reflexivity.
    - intros.
      unfold_ops @Pure_compose. unfold compose.
      rewrite (app_pure_natural F1).
      rewrite appmor_pure0.
      rewrite appmor_pure1.
      reflexivity.
    - intros.
      unfold_ops @Mult_compose. unfold compose in *.
      cbn.
      compose near (x ⊗ y).
      rewrite (fun_map_map (F := F1)).
      assert (appmor_mult1' :
               forall (A B : Type),
                 ϕ2 (A * B) ∘ mult F2 = mult G2 ∘ map_tensor (ϕ2 A) (ϕ2 B)).
      { intros. ext [x' y'].
        unfold compose; cbn. rewrite appmor_mult1. reflexivity. }
      rewrite appmor_mult1'.
      rewrite appmor_natural0.
      rewrite <- (fun_map_map (F := G1)).
      rewrite appmor_mult0.
      unfold compose; cbn.
      (* rhs *)
      rewrite appmor_natural0.
      rewrite appmor_natural0.
      rewrite (app_mult_natural G1).
      reflexivity.
  Qed.

  #[export] Instance ApplicativeMorphism_parallel_left
    (F1 F2 G1 : Type -> Type)
    `{Applicative G1}
    `{Applicative F1}
    `{Applicative F2}
    `{! ApplicativeMorphism F1 G1 ϕ1} :
    ApplicativeMorphism (F1 ∘ F2) (G1 ∘ F2) (fun A => ϕ1 (F2 A)).
  Proof.
    replace (ϕ1 ○ F2) with (fun A => ϕ1 (F2 A) ∘ map F1 (@id (F2 A))).
    - apply (ApplicativeMorphism_parallel F1 F2 G1 F2).
    - ext A. now rewrite (fun_map_id (F := F1)).
  Qed.

  #[export] Instance ApplicativeMorphism_parallel_right
    (F1 F2 G2 : Type -> Type)
    `{Applicative G2}
    `{Applicative F1}
    `{Applicative F2}
    `{! ApplicativeMorphism F2 G2 ϕ2} :
    ApplicativeMorphism (F1 ∘ F2) (F1 ∘ G2) (fun A => map F1 (ϕ2 A)).
  Proof.
    change (fun A => map F1 (ϕ2 A)) with
      ((fun A : Type => (fun X => @id (F1 X)) (G2 A) ∘ map F1 (ϕ2 A))).
    apply (ApplicativeMorphism_parallel F1 F2 F1 G2).
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
    Monoid_Morphism (G M1) (G M2) (map G ϕ).
  Proof.
    inversion H3.
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
