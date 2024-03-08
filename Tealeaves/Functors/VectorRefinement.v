From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.TraversableFunctor.

From Coq Require Import
  Logic.ProofIrrelevance.

#[local] Generalizable Variables ϕ T G A M F.

Import Applicative.Notations.

Definition Vector (n: nat) (A: Type) : Type :=
  {l : list A | length l = n}.
Lemma Vector_eq_eq: forall (A: Type) (n: nat) (l1 l2 : list A)
                   (p1 : length l1 = n)
                   (p2 : length l2 = n),
    (l1 = l2) =
      (exist (fun l => length l = n) l1 p1 = exist _ l2 p2).
Proof.
  intros.
  propext.
  + intros. subst.
    fequal.
    apply proof_irrelevance.
  + intros.
    inversion H.
    reflexivity.
Qed.

Lemma Vector_eq: forall (A: Type) (n: nat)
                      (v1 v2: Vector n A),
    proj1_sig v1 = proj1_sig v2 ->
    v1 = v2.
Proof.
  intros.
  destruct v1.
  destruct v2.
  cbn in H.
  erewrite Vector_eq_eq in H.
  eassumption.
Defined.

Section sec.
Context (A: Type).

Definition to_list {n:nat}: Vector n A -> list A.
Proof.
  intros. apply proj1_sig in X. assumption.
Defined.

Definition decide_length: forall (n: nat) (l: list A),
    {length l = n} + { length l = n -> False}.
Proof.
  intros.
  remember (Nat.eqb (length l) n) as b.
  symmetry in Heqb.
  destruct b.
  - left.
    apply (PeanoNat.Nat.eqb_eq (length l) n).
    assumption.
  - right.
    apply (PeanoNat.Nat.eqb_neq (length l) n).
    assumption.
Defined.

Definition artificial_surjection {n:nat} (x: Vector n A):
  list A -> Vector n A :=
  fun l =>
    match (decide_length n l) with
    | left Heq => (exist _ l Heq)
    | right _ => x
    end.

Lemma to_list_length: forall (n:nat) (x: Vector n A),
    length (to_list x) = n.
Proof.
  intros.
  destruct x.
  assumption.
Qed.

Lemma artificial_iso {n:nat}(x: Vector n A):
    artificial_surjection x ∘ to_list = id.
Proof.
  intros.
  ext v.
  unfold compose.
  unfold artificial_surjection.
  destruct v as [lv Heq].
  cbn.
  assert (decide_length n lv = left Heq).
  { unfold decide_length.
    admit. }
  rewrite H.
  reflexivity.
Admitted.

Lemma Vector_pres_inj {n:nat} (v: Vector n A) `{Functor F}:
  forall (x y: F (Vector n A)),
    map to_list x = map to_list y ->
    x = y.
Proof.
  introv Heq.
  assert (map (artificial_surjection v) (map to_list x)
          = map (artificial_surjection v) (map to_list y)).
  { now rewrite Heq. }
  generalize H0.
  compose near x.
  compose near y.
  rewrite (fun_map_map).
  rewrite artificial_iso.
  rewrite fun_map_id.
  unfold id.
  auto.
Qed.

End sec.

Definition vunone {A : Type} : Vector 1 A -> A.
Proof.
  intros v.
  destruct v.
  destruct x.
  - inversion e.
  - cbn in e.
    destruct x.
    + exact a.
    + inversion e.
Defined.

Definition vnil {A}: {l : list A | length l = 0} :=
  exist _ nil eq_refl.

Definition vcons (n:nat) {A}:
  A ->
  {l : list A | length l = n} ->
  {l : list A | length l = S n}.
Proof.
  introv a v.
  destruct v.
  rewrite <- e.
  exact (exist _ (cons a x) eq_refl).
Defined.

Definition vuncons (n:nat) {A}:
  {l: list A | length l = S n} ->
  A * {l:list A | length l = n}.
Proof.
  intros.
  destruct X.
  generalize dependent n.
  induction x; intros.
  - inversion e.
  - cbn in *.
    inversion e.
    split.
    apply a.
    exists x. reflexivity.
Defined.

From Tealeaves Require Import Functors.List.

Lemma map_preserve_length:
  forall (A B: Type) (f: A -> B) (l: list A),
    length (map f l) = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - cbn.
    rewrite <- IHl.
    reflexivity.
Qed.

Print eq_trans.
(** ** Functor instance *)
(******************************************************************************)
Definition map_Vector (n : nat) {A B : Type} (f : A -> B)
                      (v : Vector n A): Vector n B :=
  match v with
  | exist _ l p => exist _ (map (F := list) f l)
                        (eq_trans (map_preserve_length A B f l) p)
  end.

#[export] Instance Map_Vector (n: nat) : Map (Vector n) := @map_Vector n.

Lemma fun_map_id_Vector : forall (n : nat) (A : Type),
    map (F := Vector n) id = @id (Vector n A).
Proof.
  intros.
  ext [l Heq].
  apply Vector_eq.
  cbn.
  now rewrite fun_map_id.
Qed.

Lemma fun_map_map_Vector : forall (n : nat) (A B C : Type) (f : A -> B) (g : B -> C),
    map (F := Vector n) g ∘ map (F := Vector n) f = map (F := Vector n) (g ∘ f).
Proof.
  intros.
  ext [l Heq].
  apply Vector_eq.
  cbn. compose near l on left.
  now rewrite fun_map_map.
Qed.

#[export] Instance Functor_Vector (n : nat) : Functor (Vector n) :=
  {| fun_map_id := fun_map_id_Vector n;
    fun_map_map := fun_map_map_Vector n;
  |}.

(** ** Traversable instance *)
(******************************************************************************)
Definition traverse_Vector
             (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
             {A B : Type} (f : A -> G B)
             (v : Vector n A) : G (Vector n B).
Proof.
  destruct v as [l Heq].
  generalize dependent n.
  induction l.
  - intros n Heq. exact (pure (exist _ nil Heq)).
  - intros n Heq.
    cbn in Heq.
    unfold Vector in *.
    rewrite <- Heq.
    specialize (IHl (length l) eq_refl).
    apply (pure (vcons (length l)) <⋆> (f a) <⋆> IHl).
Defined.

 Definition traverse_Vector_manual
 (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
 {A B : Type} (f : A -> G B)
 (v : Vector n A) : G (Vector n B).

 Proof.
   unfold Vector in *.
   destruct v as [l Heq].
   induction l.
   - subst. exact (pure (exist _ nil eq_refl)).
   - destruct n.
     + cbn in Heq. false.
     + inversion Heq.
 Abort.

 Definition traverse_Vector_manual
 (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
 {A B : Type} (f : A -> G B)
 (v : Vector n A) : G (Vector n B).

 Proof.
   unfold Vector in *.
   destruct v as [l Heq].
   symmetry in Heq.
   subst.
 Abort.

 #[local] Instance Trav_Vec {n}: Traverse (Vector n) := traverse_Vector n.

 Lemma traverse_Vector_projT1:
   forall (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
     {A B : Type} (f : A -> G B)
     `{! Applicative G}
     (nonempty : Vector n B)
     (v : Vector n A),
     map (F := G)
             (@proj1_sig (list B) (fun l => length l = n))
             (traverse (T := Vector n) f v) =
       traverse f (proj1_sig v).
 Proof.
   intros.
   dup. {
     Check (Vector_pres_inj A v).
     Check (traverse (T := Vector n) f v).
     Check (Vector_pres_inj B nonempty).
     Check (Vector_pres_inj B nonempty) (traverse (T := Vector n) f v).
   }
   destruct v.
   generalize dependent n.
   induction x; intros.
   - cbn.
     rewrite <- pure_appmor_1.
     cbn.
     reflexivity.
   - cbn.
     cbn.
     destruct e.
     cbn.
     specialize (IHx (length x) eq_refl).
     cbn in IHx.
     unfold eq_rect.
     rewrite <- IHx.
     rewrite map_ap.
     rewrite map_ap.
     rewrite app_pure_natural.
     rewrite <- ap_map.
     rewrite map_ap.
     rewrite app_pure_natural.
     fequal.
     fequal.
     fequal.
     ext b.
     cbn.
     unfold compose, precompose.
     ext l.
     cbn.
     destruct l.
     cbn.
     destruct e.
     reflexivity.
 Qed.

 Lemma traverse_Vector_rw2:
   forall (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
     {A B : Type} (f : A -> G B)
     (v : Vector n A) (a : A) (l: list A)
     (p : length (a :: l) = n),
     traverse f (exist _ (a :: l) p) =
       traverse f (exist _ (a :: l) p).
 Proof.
   intros.
   Check (pure (vcons (length l)) <⋆> f a <⋆>
            (traverse f (exist _ l _))).
 Abort.

Lemma Vector_trav_eq_eq:
  forall (A: Type) (n: nat) (l1 l2 : list A)
    (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {B : Type} (f : A -> G B)
    (p1 : length l1 = n)
    (p2 : length l2 = n),
    (traverse f l1 = traverse f l2) <->
      traverse f (exist (fun l => length l = n) l1 p1) =
        traverse f (exist _ l2 p2).
Proof.
  dup.
  { intros.
    assert (length l1 = length l2).
    now subst.
    subst.
    rewrite p2 in H2.
    split.
    2: admit.
    intros Heq.
    subst.
    destruct l1.
    assert (l2 = nil).
    { cbn in p2. destruct l2; now inverts p2. }
    subst.
    rewrite (UIP_refl _ _ p2).
    reflexivity.
    admit.
  }
  intros.
  generalize dependent n.
  destruct l1; intros n p1 p2.
  - induction l2.
    2:{ cbn in p1. subst. inversion p2. }
    split.
    + intros. cbn.
      fequal.
      fequal.
      apply proof_irrelevance.
    + reflexivity.
  - generalize dependent n.
    induction l2; intros n p1 p2.
    1:{ cbn in p2. subst. inversion p2. }
    cbn in p1, p2.
    split.
    + intros.
      cbn.
      cbn.
Admitted.

Lemma Vector_trav_eq: forall
    (A: Type) (n: nat)
    (v1 v2: Vector n A)
    (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {B : Type} (f : A -> G B),
    traverse f (proj1_sig v1) = traverse f (proj1_sig v2) ->
    traverse f v1 = traverse f v2.
Proof.
  intros.
  destruct v1.
  destruct v2.
  cbn in H.
  erewrite <- Vector_trav_eq_eq.
  exact H2.
Defined.


#[local] Instance TF_Vec {n}: TraversableFunctor (Vector n).
Proof.
  constructor.
  - intros.
    ext [l Heq].
    generalize dependent n.
    induction l; intros n Heq.
    + apply Vector_eq.
      reflexivity.
    + cbn in *.
      cbn.
      specialize (IHl _ eq_refl).
      rewrite (IHl).
      cbn.
      rewrite <- Heq.
      reflexivity.
  - intros.
    ext [l Heq].
    generalize dependent n.
    unfold compose.
    intros.
    About Vector_eq.
    eapply Vector_eq.
    induction l; intros n Heq.
    + cbn.
      rewrite <- pure_appmor_1.
      cbn.
      reflexivity.
    + cbn.
      rewrite map_pure.
      apply Vector_eq.
      reflexivity.
    + cbn in *.
      cbn.
      specialize (IHl _ eq_refl).
      rewrite (IHl).
      cbn.
      rewrite <- Heq.
      reflexivity.
    cbn.
    subst.
    cbn.
  unfold Vector.
  pose (t := traverse (T := list) f l).
  induction l.
  - exist (

  - Check traverse (T := list) f x.

  match v in Vector.t _ n return G (Vector.t A n) with
  | Vector.nil _(*=A*) => pure (F := G) (Vector.nil A)
  | Vector.cons _(*=A*) a(*:FA*) m(*n = S m*) rest =>
      pure (F := G) (Basics.flip (fun a => Vector.cons A a m))
      <⋆> dist_Vector m G rest
      <⋆> a
      (*
      pure (F := G) (fun a => Vector.cons A a m) <⋆> a <⋆> dist_Vector m G rest
       *)
  end.

#[export] Instance Dist_Vector (n : nat):
  ApplicativeDist (Vector n) := @dist_Vector n.

Tactic Notation "cleanup_Vector" :=
  repeat (change (map_Vector ?n (A := ?x) (B := ?y))
           with (map (F := Vector n) (A := x) (B := y)) +
                  change (dist_Vector ?n ?G (A := ?x))
             with (dist (Vector n) G (A := x))).

Tactic Notation "cleanup_Vector_*" :=
  repeat ((change (map_Vector ?n (A := ?x) (B := ?y))
            with (map (F := Vector n) (A := x) (B := y)) in *) ||
                   change (dist_Vector ?n ?G (A := ?x))
              with (dist (Vector n) G (A := x)) in *).

Lemma dist_natural_Vector (n : nat) :
  forall (G : Type -> Type) (H1 : Map G)
    (H2 : Pure G) (H3 : Mult G),
    Applicative G -> Natural (F := (Vector n ∘ G)) (G := (G ∘ Vector n)) (@dist_Vector n G _ _ _).
Proof.
  intros. constructor; try typeclasses eauto.
  intros. unfold_ops @Map_compose. unfold compose at 3 7.
  ext v. induction v.
  - cbn. compose near (Vector.nil A).
    apply (app_pure_natural (G := G)).
  - cbn.
    (* LHS *)
    rewrite (map_ap).
    rewrite (map_ap).
    rewrite (app_pure_natural (G := G)).
    (* RHS *)
    cleanup_Vector_*.
    rewrite <- IHv.
    rewrite <- (ap_map).
    rewrite <- (ap_map).
    rewrite (map_ap).
    compose near (pure (F := G) (Basics.flip (fun a0 : B => Vector.cons B a0 n))).
    rewrite (fun_map_map (F := G)).
    rewrite (app_pure_natural).
    reflexivity.
Qed.

Lemma dist_morph_Vector (n : nat) :
  forall (G1 G2 : Type -> Type) (H1 : Map G1) (H3 : Mult G1) (H2 : Pure G1) (H4 : Map G2)
    (H6 : Mult G2) (H5 : Pure G2) (ϕ : forall A : Type, G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ -> forall A : Type,
      dist (Vector n) G2 ∘ map (F := Vector n) (ϕ A) = ϕ (Vector n A) ∘ dist (Vector n) G1.
Proof.
  intros. unfold compose at 1 2.
  ext v. induction v.
  - cbn. rewrite (appmor_pure (F := G1) (G := G2)). reflexivity.
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

Lemma dist_unit_Vector (n : nat) : forall A : Type, dist (A := A) (Vector n) (fun A : Type => A) = id.
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
      forall A : Type, dist (A := A) (Vector n) (G1 ∘ G2) = map (F := G1) (dist (Vector n) G2) ∘ dist (Vector n) G1.
Proof.
  intros. unfold compose at 4.
  ext v. induction v.
  - cbn. unfold_ops @Pure_compose.
    rewrite (app_pure_natural (G := G1)).
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
    compose near (pure (F := G1) (pure (F := G2)
                                       (Basics.flip (fun a0 : A => Vector.cons A a0 n)))).
    rewrite (fun_map_map (F := G1)).
    compose near (pure (F := G1) (pure (F := G2)
                                       (Basics.flip (fun a0 : A => Vector.cons A a0 n)))).
    rewrite (fun_map_map (F := G1)).
    rewrite (app_pure_natural (G := G1)).
    (* RHS *)
    rewrite (map_ap (G := G1)).
    rewrite (app_pure_natural (G := G1)).
    reflexivity.
Qed.

#[export] Instance TraversableFunctor_Vector (n : nat):
  Categorical.TraversableFunctor.TraversableFunctor (Vector n) :=
  {| dist_natural := dist_natural_Vector n;
    dist_morph := dist_morph_Vector n;
    dist_unit := dist_unit_Vector n;
    dist_linear := dist_linear_Vector n;
  |}.

#[export] Instance Traverse_Vector (n : nat): Traverse (Vector n) :=
  Adapters.CategoricalToKleisli.TraversableFunctor.ToKleisli.Traverse_dist (Vector n).


#[export] Instance KleisliTraversableFunctor_Vector (n : nat):
  Kleisli.TraversableFunctor.TraversableFunctor (Vector n) :=
  Adapters.CategoricalToKleisli.TraversableFunctor.ToKleisli.TraversableFunctor_instance_0.

Require Import Functors.Batch.

Import Batch.Notations.

(** * Deconstructing <<Batch A B C>> into shape and contents *)
(******************************************************************************)
Section deconstruction.

  #[local] Arguments Done {A B C}%type_scope _.
  #[local] Arguments Step {A B C}%type_scope _.

  Context {A B: Type}.

  Fixpoint Batch_to_contents {C} (b: Batch A B C):
    Vector (length_Batch b) A :=
    match b return (Vector (length_Batch b) A) with
    | Done c => vnil
    | Step rest a => vcons (length_Batch rest) a (Batch_to_contents rest)
    end.

  #[program] Fixpoint Batch_to_makeFn {C} (b: Batch A B C):
    Vector (length_Batch b) B -> C :=
    match b return (Vector (length_Batch b) B -> C) with
    | Done c =>
        const c
    | Step rest a =>
        fun (v: Vector (S (length_Batch rest)) B) =>
          (_ (Batch_to_makeFn rest))
    end.

  Next Obligation.
    destruct (vuncons _ v).
    apply x.
    exact s. assumption.
  Defined.

  Lemma Batch_to_contents_rw2: forall {C} (b: Batch A B (B -> C)) (a: A),
      Batch_to_contents (b ⧆ a) =
        Vector.cons A a (length_Batch b) (Batch_to_contents b).
  Proof.
    reflexivity.
  Qed.

  Lemma Batch_to_makeFn_rw2: forall {C} (a: A) (b: Batch A B (B -> C)),
      Batch_to_makeFn (b ⧆ a) =
        fun (v:Vector.t B (S (length_Batch b))) =>
          match (Vector.uncons v) with
          | (b', v') => Batch_to_makeFn b v' b'
          end.
  Proof.
    reflexivity.
  Qed.

  Lemma runBatch_repr `{Applicative G} {C}: forall (f: A -> G B) (b: Batch A B C),
      runBatch G f C b =
      pure G (Batch_to_makeFn b) <⋆>
                traverse (T := Vector (length_Batch b)) f (Batch_to_contents b).
  Proof.
    intros.
    induction b.
    - cbn.
      rewrite ap2.
      reflexivity.
    - rewrite runBatch_rw2.
      rewrite Batch_to_contents_rw2.
      rewrite Batch_to_makeFn_rw2.
      cbn.
      rewrite <- ap4.
      rewrite ap2.
      rewrite <- ap4.
      rewrite ap2.
      rewrite ap2.
      rewrite IHb.
      reflexivity.
  Qed.

End deconstruction.












