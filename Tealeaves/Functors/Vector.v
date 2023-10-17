From Tealeaves Require Export
  Functors.Batch
  Classes.Categorical.Applicative
  Classes.Categorical.TraversableFunctor.

#[local] Generalizable Variables T G A M F.

Import Applicative.Notations.

(** * Vectors *)
(******************************************************************************)
Inductive Vector (A : Type) : forall (n : nat), Type :=
| Vnil : Vector A 0
| Vcons : A -> forall (n : nat), Vector A n -> Vector A (S n).

Notation "'VEC' n" := (fun A => Vector A n) (at level 3).

(** ** Functor instance *)
(******************************************************************************)
Fixpoint map_Vector (n : nat) {A B : Type} (f : A -> B) (v : Vector A n) : Vector B n :=
  match v in Vector _ n return Vector B n with
  | Vnil _(*=A*) => Vnil B
  | Vcons _(*=A*) a(*:A*) m(*n = S m*) rest =>
      Vcons B (f a) m (map_Vector m f rest)
  end.

Instance Map_Vector (n : nat) : Map (VEC n) := @map_Vector n.

Lemma fun_map_id_Vector : forall (n : nat) (A : Type), map (VEC n) id = (@id (VEC n A)).
Proof.
  intros.
  ext v.
  induction v.
  - reflexivity.
  - cbn. unfold id. fequal. apply IHv.
Qed.

Lemma fun_map_map_Vector : forall (n : nat) (A B C : Type) (f : A -> B) (g : B -> C),
    map (VEC n) g ∘ map (VEC n) f = map (VEC n) (g ∘ f).
Proof.
  intros.
  ext v.
  induction v.
  - reflexivity.
  - cbn. unfold id. fequal. apply IHv.
Qed.

#[export] Instance Functor_Vector (n : nat) : Functor (VEC n) :=
  {| fun_map_id := fun_map_id_Vector n;
    fun_map_map := fun_map_map_Vector n;
  |}.

(** ** Applicative instance *)
(******************************************************************************)
Fixpoint dist_Vector (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
  {A : Type} (v : Vector (G A) n) : G (Vector A n) :=
  match v in Vector _ n return G (Vector A n) with
  | Vnil _(*=A*) => pure G (Vnil A)
  | Vcons _(*=A*) a(*:FA*) m(*n = S m*) rest =>
      pure G (fun a => Vcons A a m) <⋆> a <⋆> dist_Vector m G rest
  end.

Instance Dist_Vector (n : nat) : ApplicativeDist (VEC n) := @dist_Vector n.


Tactic Notation "cleanup_Vector" :=
  repeat (change (map_Vector ?n (A := ?x) (B := ?y)) with (map (VEC n) (A := x) (B := y)) +
          change (dist_Vector ?n ?G (A := ?x)) with (dist (VEC n) G (A := x))).

Tactic Notation "cleanup_Vector_*" :=
  repeat ((change (map_Vector ?n (A := ?x) (B := ?y)) with (map (VEC n) (A := x) (B := y)) in *) ||
          change (dist_Vector ?n ?G (A := ?x)) with (dist (VEC n) G (A := x)) in *).

Lemma dist_natural_Vector (n : nat) :
  forall (G : Type -> Type) (H1 : Map G)
    (H2 : Pure G) (H3 : Mult G),
    Applicative G -> Natural (F := (VEC n ∘ G)) (G := (G ∘ VEC n)) (@dist_Vector n G _ _ _).
Proof.
  intros. constructor; try typeclasses eauto.
  intros. unfold_ops @Map_compose. unfold compose at 3 7.
  ext v. induction v.
  - cbn. compose near (Vnil A).
    apply (app_pure_natural G).
  - cbn.
    (* LHS *)
    rewrite (map_ap).
    rewrite (map_ap).
    rewrite (app_pure_natural G).
    (* RHS *)
    cleanup_Vector_*.
    rewrite <- IHv.
    rewrite <- (ap_map).
    rewrite <- (ap_map).
    rewrite (map_ap).
    compose near (pure G (fun a0 : B => Vcons B a0 n)).
    rewrite (fun_map_map (F := G)).
    rewrite (app_pure_natural G).
    reflexivity.
Qed.

Lemma dist_morph_Vector (n : nat) :
  forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Map G2) (H5 : Pure G2)
    (H6 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ -> forall A : Type, dist (VEC n) G2 ∘ map (VEC n) (ϕ A) = ϕ (VEC n A) ∘ dist (VEC n) G1.
Proof.
  intros. unfold compose at 1 2.
  ext v. induction v.
  - cbn. rewrite (appmor_pure G1 G2). reflexivity.
  - cbn. cleanup_Vector.
    (* LHS *)
    rewrite IHv.
    inversion H.
    (* RHS *)
    rewrite (ap_morphism_1).
    rewrite (ap_morphism_1).
    rewrite (appmor_pure).
    reflexivity.
Qed.

Lemma dist_unit_Vector (n : nat) : forall A : Type, dist (A := A) (VEC n) (fun A : Type => A) = id.
Proof.
  intros. ext v. induction v.
  - cbn. reflexivity.
  - cbn. cleanup_Vector.
    (* LHS *)
    rewrite IHv.
    reflexivity.
Qed.

Lemma dist_linear_Vector (n : nat) :
  forall (G1 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H3 : Mult G1),
    Applicative G1 ->
    forall (G2 : Type -> Type) (H5 : Map G2) (H6 : Pure G2) (H7 : Mult G2),
      Applicative G2 ->
      forall A : Type, dist (A := A) (VEC n) (G1 ∘ G2) = map G1 (dist (VEC n) G2) ∘ dist (VEC n) G1.
Proof.
  intros. unfold compose at 4.
  ext v. induction v.
  - cbn. unfold_ops @Pure_compose.
    rewrite (app_pure_natural G1).
    reflexivity.
  - cbn. cleanup_Vector.
    (* LHS *)
    rewrite IHv.
    unfold_ops @Pure_compose.
    rewrite (ap_compose2 G2 G1).
    rewrite (ap_compose2 G2 G1).
    rewrite <- (ap_map (G := G1)).
    rewrite (map_ap (G := G1)).
    rewrite (map_ap (G := G1)).
    compose near (pure G1 (pure G2 (fun a0 : A => Vcons A a0 n))).
    rewrite (fun_map_map (F := G1)).
    compose near (pure G1 (pure G2 (fun a0 : A => Vcons A a0 n))).
    rewrite (fun_map_map (F := G1)).
    rewrite (app_pure_natural G1).
    (* RHS *)
    rewrite (map_ap (G := G1)).
    rewrite (map_ap (G := G1)).
    rewrite (app_pure_natural G1).
    reflexivity.
Qed.

#[export] Instance TraversableFunctor_Vector (n : nat) : TraversableFunctor (VEC n) :=
  {| dist_natural := dist_natural_Vector n;
    dist_morph := dist_morph_Vector n;
    dist_unit := dist_unit_Vector n;
    dist_linear := dist_linear_Vector n;
  |}.
