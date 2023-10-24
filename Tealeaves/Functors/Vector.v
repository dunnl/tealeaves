From Tealeaves Require Export
  Functors.Batch
  Classes.Categorical.Applicative
  Classes.Categorical.TraversableFunctor.

From Tealeaves Require Import
  Adapters.CategoricalToKleisli.TraversableFunctor.

#[local] Generalizable Variables ϕ T G A M F.

Import Applicative.Notations.

(*
(** * Vectors *)
(******************************************************************************)
Inductive Vector (A : Type) : forall (n : nat), Type :=
| Vnil : Vector A 0
| Vcons : A -> forall (n : nat), Vector A n -> Vector A (S n).
 *)

Notation "'VEC' n" := (fun A => Vector.t A n) (at level 3).

Definition unone {A : Type} : Vector.t A 1 -> A.
Proof.
  intros v. remember 1. induction v.
  - inversion Heqn.
  - assumption.
Defined.

(** ** Functor instance *)
(******************************************************************************)
Fixpoint map_Vector (n : nat) {A B : Type} (f : A -> B) (v : VEC n A) : VEC n B :=
  match v in Vector.t _ n return Vector.t B n with
  | Vector.nil _(*=A*) => Vector.nil B
  | Vector.cons _(*=A*) a(*:A*) m(*n = S m*) rest =>
      Vector.cons B (f a) m (map_Vector m f rest)
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
  {A : Type} (v : VEC n (G A)) : G (VEC n A) :=
  match v in Vector.t _ n return G (Vector.t A n) with
  | Vector.nil _(*=A*) => pure G (Vector.nil A)
  | Vector.cons _(*=A*) a(*:FA*) m(*n = S m*) rest =>
      pure G (fun a => Vector.cons A a m) <⋆> a <⋆> dist_Vector m G rest
  end.

#[export] Instance Dist_Vector (n : nat) : ApplicativeDist (VEC n) := @dist_Vector n.

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
  - cbn. compose near (Vector.nil A).
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
    compose near (pure G (fun a0 : B => Vector.cons B a0 n)).
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
    compose near (pure G1 (pure G2 (fun a0 : A => Vector.cons A a0 n))).
    rewrite (fun_map_map (F := G1)).
    compose near (pure G1 (pure G2 (fun a0 : A => Vector.cons A a0 n))).
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

(** * Batch to Vector *)
(******************************************************************************)

Inductive KStore A B C :=
  { length : nat;
    contents : VEC length A;
    build : VEC length B -> C;
  }.

Definition kstore {A B : Type} : A -> KStore A B B :=
  fun a => Build_KStore A B B 1 (Vector.cons A a 0 (Vector.nil A)) unone.

(** ** Functor instance *)
(******************************************************************************)
Section map.

  Context
    {A B : Type}.

  Definition map_KStore : forall (C D : Type) (f : C -> D),
      KStore A B C -> KStore A B D.
  Proof.
    intros. destruct X.
    econstructor. eassumption.
    intros. apply f. auto.
  Defined.

  #[export] Instance Map_KStore : Map (KStore A B) := map_KStore.

  Lemma map_id_KStore : forall (C : Type),
      map (KStore A B) (@id C) = @id (KStore A B C).
  Proof.
    intros. ext k. destruct k as [len contents make].
    reflexivity.

  Qed.
  Lemma map_map_KStore : forall (C D E : Type) (f : C -> D) (g : D -> E),
      map (KStore A B) g ∘ map (KStore A B) f = map (KStore A B) (g ∘ f).
  Proof.
    intros. ext k. destruct k as [len contents make].
    reflexivity.
  Qed.

  #[export] Instance Functor_KStore : Functor (KStore A B) :=
    {| fun_map_id := @map_id_KStore;
      fun_map_map := @map_map_KStore;
    |}.

End map.

(** ** Applicative instance *)
(******************************************************************************)
Definition pure_KStore : forall (A B C : Type), C -> KStore A B C.
Proof.
  intros.
  apply (Build_KStore _ _ _ 0).
  apply Vector.nil.
  intros _; apply X.
Defined.

#[export] Instance Pure_KStore (A B : Type) : Pure (KStore A B) := pure_KStore A B.

Definition mult_KStore : forall (A B C D : Type), KStore A B C * KStore A B D -> KStore A B (C * D).
Proof.
  introv [k1 k2].
  destruct k1.
  destruct k2.
  apply (Build_KStore A B (C * D) (length0 + length1)).
  apply Vector.append; eauto.
  intro t.
  apply (VectorDef.splitat length0) in t.
  destruct t as [tc td].
  split; auto.
Defined.

#[export] Instance Mult_KStore (A B : Type) : Mult (KStore A B) := mult_KStore A B.

#[export] Instance Applicative_KStore : forall (A B : Type), Applicative (KStore A B). Admitted.

(** * Batch to KStore *)
(******************************************************************************)
Section batch_to.

  Context (A B C : Type).

  Definition toVector : Batch A B C -> @sigT nat (Vector.t A).
  Proof.
    intros b.
    induction b.
    - exists 0. apply Vector.nil.
    - destruct IHb as [n contents].
      exists (S n). apply Vector.cons. assumption.
      assumption.
  Defined.

  Definition toMake : Batch A B C -> @sigT nat (fun n => Vector.t B n -> C).
  Proof.
    intros b.
    induction b.
    - exists 0. intros _. assumption.
    - destruct IHb as [n mk].
      exists (S n). intro v.
      remember (S n). destruct v.
      + inversion Heqn0.
      + inversion Heqn0; subst.
        apply mk.
        assumption.
        assumption.
  Qed.

  Definition toBoth : Batch A B C -> @sigT nat (fun n => VEC n A * (VEC n B -> C)).
  Proof.
    intros b.
    induction b.
    - exists 0. split. apply Vector.nil. auto.
    - destruct IHb as [n [contents mk]].
      exists (S n). split.
      + apply Vector.cons. assumption. assumption.
      + intro v. apply Vector.uncons in v. destruct v.
        apply mk; auto.
  Defined.

  Definition toKStore_manual : Batch A B C -> KStore A B C.
  Proof.
    intros b.
    destruct (toBoth b) as [len [contents mk]].
    econstructor; eassumption.
  Defined.

  About runBatch.

  Definition toKStore : Batch A B C -> KStore A B C.
  Proof.
    eapply (runBatch kstore C).
  Defined.

End batch_to.

(** Properties of vectors *)
(******************************************************************************)
Lemma toNil {B : Type} : forall (b : Vector.t B 0), b = Vector.nil B.
Proof.
  intros.
  apply (Vector.case0 (A := B) (fun v : Vector.t B 0 => v = Vector.nil B)).
  reflexivity.
Qed.

(** * Cata for <<KStore>> *)
(******************************************************************************)
Section cata.

  Context
    (A B : Type).

  Definition cata `{Mult F} `{Map F} `{Pure F} : forall (f : A -> F B) C, KStore A B C -> F C.
  Proof.
    intros f C [len contents make].
    pose (x :=traverse (Traverse := ToKleisli.Traverse_dist _) (VEC len) F f contents).
    apply (map F make x).
  Defined.

  Import ToKleisli.

  #[local] Instance Natural_cata : forall `{Applicative F} (f : A -> F B), Natural (cata f).
  Proof.
    constructor; try typeclasses eauto.
    intros. ext k.
    unfold compose. destruct k.
    cbn. compose near ((traverse (VEC length0) F f contents0)) on left.
    rewrite (fun_map_map (F := F)).
    reflexivity.
  Qed.

  Context
    `{ApplicativeMorphism F G ϕ}.

  Lemma cata_kstore : forall C, cata kstore C = @id (KStore A B C).
  Proof.
    intros C. ext k. destruct k as [len contents make].
    unfold id.
    assert (lemma : traverse VEC len (KStore A B) kstore contents =
              {| length := len; contents := contents; build := (@id _) |}).
    { clear. induction contents.
      - cbn. unfold_ops @Pure_KStore.
        unfold pure_KStore. fequal.
        ext b. rewrite toNil. reflexivity.
      - cbn.
        change_left (pure (KStore A B) (fun a : B => Vector.cons B a n) <⋆> kstore h <⋆> traverse VEC n (KStore A B) kstore contents0 ).
        rename h into a.
        rewrite IHcontents.
        unfold kstore.
        unfold ap.
        unfold_ops @Mult_KStore @Pure_KStore.
        unfold mult_KStore, pure_KStore.
        cbn.
        fequal.
        ext X.
        rewrite Vector.eta.
        reflexivity.
    }
    cbn.
    rewrite lemma.
    reflexivity.
  Qed.

  Lemma cata_appmor : forall (f : A -> F B) C, ϕ C ∘ cata f C = cata (ϕ B ∘ f) C.
  Proof.
    intros. ext k. inversion H2. unfold compose. induction k.
    cbn. rewrite appmor_natural.
    compose near (contents0).
    rewrite (trf_traverse_morphism (T := VEC length0)).
    reflexivity.
  Qed.

End cata.

(** ** <<KStore>> to <<Batch>> *)
(******************************************************************************)
Section toBatch.

  Context (A B : Type).

  Definition toBatch : forall (C : Type), KStore A B C -> Batch A B C
    := cata A B batch.

  Definition toBatch_manual : forall (C : Type), KStore A B C -> Batch A B C.
  Proof.
    intros C k.
    destruct k as [len contents make].
    generalize dependent C.
    induction len.
    - intros C make.
      pose (c := make (Vector.nil B)).
      exact (Done c).
    - intros.
      apply Vector.uncons in contents.
      destruct contents as [a rest].
      specialize (IHlen rest (B -> C)).
      apply Step.
      + apply IHlen.
        intros. apply make. constructor; assumption.
      + assumption.
  Defined.

  Definition toBatch_manual2 : forall C, KStore A B C -> Batch A B C.
    intros C k.
    destruct k as [len contents make].
    generalize dependent C.
    induction contents as [| a n rest IHrest].
    - intros C make.
      exact (Done (make (Vector.nil B))).
    - intros C make.
      apply Step.
      apply IHrest.
      intros restB b.
      apply make.
      apply Vector.cons.
      assumption.
      assumption.
      assumption.
  Defined.

End toBatch.

(* ISOS *)
Section isos.

  Context (A B C : Type).

  Goal forall (k : KStore A B C), k = toKStore A B C (toBatch A B C k).
  Proof.
    intros.
    unfold toBatch.
    unfold toKStore.
    compose near k.
    rewrite (cata_appmor _ _ _).
    Check (runBatch kstore B ∘ batch).
    replace (runBatch kstore B ∘ batch) with (kstore (B := B) (A := A)).
    rewrite (cata_kstore A B). reflexivity.
    Fail rewrite (runBatch_batch).
  Admitted.


  Goal forall (k : KStore A B C), k = toKStore_manual A B C (toBatch_manual A B C k).
  Proof.
    intros k.
    destruct k.
    destruct length0.
    - cbn.
      rewrite (toNil contents0).
      fequal.
      ext b. rewrite (toNil b).
      reflexivity.
    - cbn.
      unfold toKStore_manual.
      cbn.
      unfold Batch_rect.
      cbn.
      unfold nat_rect.
  Abort.


  Goal forall (k : KStore A B C), k = toKStore_manual A B C (toBatch_manual2 A B C k).
    intros.
    destruct k.
    cbn. induction contents0.
    cbn.
    + fequal. ext b. fequal.
      apply toNil.
    + cbn. cbv.
  cbv.

End isos.
