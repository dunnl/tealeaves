From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.TraversableFunctor
  Functors.Batch.

From Coq Require Import
  Logic.ProofIrrelevance.

#[local] Generalizable Variables ϕ T G A M F.

Import Applicative.Notations.

Lemma S_uncons: forall (n m: nat),
    S n = S m -> n = m.
Proof.
  now inversion 1.
Defined.

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

Lemma length_uncons: forall `(a: A) (l: list A) n,
    length (a :: l) = S n -> length l = n.
Proof.
  now inversion 1.
Qed.

Definition Vector (n: nat) (A: Type) : Type :=
  {l : list A | length l = n}.

Lemma Vector_eq_iff:
  forall (A: Type) (n: nat) (l1 l2 : list A)
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
  erewrite Vector_eq_iff in H.
  eassumption.
Defined.

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
  destruct v as [vlist vlen].
  apply (exist (fun l => length l = S n) (cons a vlist)).
  cbn. fequal. assumption.
Defined.

Lemma Vector_nil_eq:
  forall (A: Type)
    (v: Vector 0 A),
    v = vnil.
Proof.
  intros.
  destruct v as [vlist vlen].
  unfold vnil.
  apply Vector_eq.
  cbn.
  rewrite <- List.length_zero_iff_nil.
  assumption.
Qed.

Lemma list_cons_eq:
  forall (A: Type) (n: nat)
    (v: list A) (vlen: length v = S n),
    exists (a: A) (v': list A),
    v = cons a v'.
Proof.
Admitted.

Lemma proj_vcons: forall (n: nat) `(a: A) (v: Vector n A),
    proj1_sig (vcons n a v) = cons a (proj1_sig v).
Proof.
  intros.
  destruct v as [vlist vlen].
  destruct vlen.
  reflexivity.
Qed.

Lemma Vector_cons_eq:
  forall (A: Type) (n: nat)
    (v: Vector (S n) A),
  exists (a: A) (v': Vector n A),
    v = vcons n a v'.
Proof.
  intros.
  destruct v as [vlist vlen].
  assert (exists a l, vlist = cons a l).
  { eapply list_cons_eq. eassumption. }
  destruct H as [a [l veq]].
  assert (length l = n).
  { subst. now inversion vlen. }
  { exists a.
    exists (exist (fun l => length l = n) l H).
    apply Vector_eq.
    rewrite proj_vcons.
    cbn.
    assumption.
  }
Qed.

Lemma Vector_cons_eq':
  forall (A: Type) (n: nat)
    (v: Vector (S n) A),
    {p: A * Vector n A | v = vcons n (fst p) (snd p)}.
Proof.
  intros.
  destruct v as [vlist vlen].
  destruct vlist.
  - inversion vlen.
  - pose (length_uncons a vlist n vlen).
    apply (exist _ (a, exist (fun l => length l = n) vlist e)).
    cbn.
    fequal.
    apply proof_irrelevance.
Qed.

Lemma Vector_induction:
  forall (A: Type) (P: forall m, Vector m A -> Prop)
    (IHnil: P 0 (vnil))
    (IHcons:
      forall a m (v: Vector m A), P m v -> P (S m) (vcons m a v)),
  forall m (v: Vector m A), P m v.
Proof.
  intros.
  induction m.
  + rewrite Vector_nil_eq. assumption.
  + destruct (Vector_cons_eq A m v)
      as [a [v' rest]].
    rewrite rest.
    apply IHcons.
    apply IHm.
Qed.


Lemma Vector_induction2:
  forall (A: Type) (P: forall m, Vector m A -> Vector m A -> Prop)
    (IHnil: P 0 vnil vnil)
    (IHcons:
      forall m (a1 a2: A) (v1 v2: Vector m A),
        P m v1 v2 ->
        P (S m) (vcons m a1 v1) (vcons m a2 v2)),
  forall m (v1 v2: Vector m A), P m v1 v2.
Proof.
  intros.
  induction m.
  + rewrite Vector_nil_eq.
    rewrite (Vector_nil_eq _ v1).
    assumption.
  + destruct (Vector_cons_eq A m v1)
      as [a1 [v1' rest1]].
    destruct (Vector_cons_eq A m v2)
      as [a2 [v2' rest2]].
    rewrite rest1.
    rewrite rest2.
    apply IHcons.
    apply IHm.
Qed.

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

Definition vuncons_hd (n:nat) {A}:
  {l: list A | length l = S n} ->
  A.
Proof.
  intros.
  destruct X.
  destruct x.
  - false.
  - exact a.
Defined.

Definition vuncons_tl (n:nat) {A}:
  {l: list A | length l = S n} ->
  {l: list A | length l = n}.
Proof.
  intros.
  destruct X.
  destruct x.
  - false.
  - cbn in e.
    exists x. now inversion e.
Defined.

Lemma vuncons_surj (n:nat) {A} (v : {l: list A | length l = S n}):
  vuncons n v = (vuncons_hd n v , vuncons_tl n v).
Proof.
  intros.
  destruct v.
  induction x.
  - false.
  - cbn.
    inversion e.
    symmetry in H0.
    subst.
    cbn in e.
    assert (e = eq_refl).
    { apply proof_irrelevance. }
    rewrite H.
    cbn.
    reflexivity.
Qed.

Lemma vuncons_surj2 (n:nat) {A} (v : {l: list A | length l = S n}):
  v = vcons n (vuncons_hd n v) (vuncons_tl n v).
Proof.
  intros.
  destruct v.
  induction x.
  - false.
  - cbn. fequal.
    apply proof_irrelevance.
Qed.

Lemma vuncons_surj_hd (n:nat) {A} (a: A) (v : {l: list A | length l = n}):
  a = vuncons_hd n (vcons n a v).
Proof.
  destruct v.
  reflexivity.
Qed.

Lemma vuncons_surj_tl (n:nat) {A} (a: A) (v : {l: list A | length l = n}):
  v = vuncons_tl n (vcons n a v).
Proof.
  destruct v.
  apply Vector_eq.
  cbn.
  reflexivity.
Qed.

Definition vuncons2 (n:nat) {A}:
  Vector (S n) A ->
  A * Vector n A.
Proof.
  apply vuncons.
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

(** ** Batch *)

(*
Definition Batch_to_Vector1 {A B C}:
  forall (b: Batch A B C) (n: nat) (Heq: length_Batch b = n),
    Vector n A.
Proof.
  intros.
  generalize dependent n.
  induction b.
  - cbn. intros. subst. apply vnil.
  - intros.
    destruct n.
    + inversion Heq.
    + inversion Heq.
      apply vcons.
      * exact a.
      * apply IHb.
        reflexivity.
Defined.

Lemma Batch_to_Vector_rw1 {A B C c} (Heq: length_Batch (@Done A B C c) = 0):
  Batch_to_Vector1 (@Done A B C c) 0 Heq =
    vnil.
Proof.
  rewrite (UIP_refl _ _ Heq).
  reflexivity.
Qed.
*)

(*
Lemma Batch_to_Vector_rw2 {A B C} n (b: Batch A B (B -> C)) a (Heq: length_Batch `(Step b a) = S n):
  Batch_to_Vector1 (Step b a) (S n) Heq =
    vcons n a (Batch_to_Vector1 b n (S_uncons _ _ Heq)).
Proof.
  Set Printing All.
  cbn in Heq.
  pose Heq. symmetry in e.
  rewrite e.
  change_left ((@Batch_to_Vector A B C (@Step A B C b a) ((S (@length_Batch A B (forall _ : B, C) b))) eq_refl)).
  r (S n) with (S (@length_Batch A B (forall _ : B, C) b)) .
  rewrite <- Heq.
  pose (S_uncons _ _ Heq).
  rewrite <- e at 1.
  rewrite (UIP_refl _ _ Heq).
  reflexivity.
Qed.
 *)

(*
Definition Batch_to_Vector2 {A B C}:
  forall (b: Batch A B C), Vector (length_Batch b) A.
Proof.
  intros.
  induction b.
  - cbn.
    apply vnil.
  - cbn.
    apply vcons;
      assumption.
Defined.
 *)

Fixpoint Batch_to_Vector2 {A B C} (b: Batch A B C):
  Vector (length_Batch b) A :=
  match b return Vector (length_Batch b) A with
  | Done c => vnil
  | Step b a => vcons (length_Batch b) a (Batch_to_Vector2 b)
  end.

Lemma Batch_to_Vector2_rw1 {A B C c}:
  Batch_to_Vector2 (@Done A B C c) = vnil.
Proof.
  reflexivity.
Qed.

Lemma Batch_to_Vector2_rw2 {A B C} (b: Batch A B (B -> C)) a:
  Batch_to_Vector2 (Step b a) =
    vcons (length_Batch b) a (Batch_to_Vector2 b).
Proof.
  reflexivity.
Qed.

Fixpoint Batch_to_Make2 {A B C} (b: Batch A B C):
  Vector (length_Batch b) B -> C :=
  match b return Vector (length_Batch b) B -> C with
  | Done c => const c
  | Step b a =>
      fun v =>
        let (p, q) := (vuncons2 (length_Batch b) v)
        in Batch_to_Make2 b q p
  end.

Lemma Batch_to_Make2_rw1 {A B C c}:
  Batch_to_Make2 (@Done A B C c) = const c.
Proof.
  reflexivity.
Qed.

Lemma Batch_to_Make2_rw2 {A B C} (b: Batch A B (B -> C)) a:
  Batch_to_Make2 (Step b a) =
    fun v => Batch_to_Make2 b
                         (vuncons_tl (length_Batch b) v)
                         (vuncons_hd (length_Batch b) v).
Proof.
  cbn.
  ext v.
  rewrite vuncons_surj.
  reflexivity.
Qed.

Lemma Batch_repr {A C}:
  forall (b: Batch A A C),
    Batch_to_Make2 b (Batch_to_Vector2 b) = extract_Batch b.
Proof.
  intros.
  induction b.
  - reflexivity.
  - cbn.
    rewrite <- IHb.
    assert (forall q, vuncons2 (length_Batch b) (vcons (length_Batch b) a q) = (a, q)).
    { intros q.
      unfold vcons.
      unfold vuncons2.
      rewrite vuncons_surj.
      fequal.
      + destruct q.
        cbn.
        reflexivity.
      + destruct q.
        apply Vector_eq.
        cbn.
        reflexivity.
    }
    rewrite H.
    reflexivity.
Qed.

(*
Definition Batch_to_Make {A B C}:
  forall (b: Batch A B C) (n: nat) (Heq: length_Batch b = n),
    Vector n B -> C.
Proof.
  intros.
  generalize dependent n.
  induction b.
  - intros. apply c.
  - intros.
    destruct n.
    + inversion Heq.
    + inversion Heq.
      destruct (Vector_cons_eq' B n X) as [[b' v] rest].
      eapply IHb.
      eassumption.
      assumption.
      assumption.
Defined.

Lemma Batch_repr {A C}:
  forall (b: Batch A A C) (n: nat) (Heq: length_Batch b = n),
    Batch_to_Make b n Heq (Batch_to_Vector b n Heq) = extract_Batch b.
Proof.
  intros.
  generalize dependent n.
  induction b.
  - intros.
    reflexivity.
  - intros.
    destruct n.
    + inversion Heq.
    + inversion Heq.
      specialize (IHb n H0).
      cbn. rewrite <- IHb.
      subst. cbn in Heq.
      assert (Heq = eq_refl).
      admit.
      subst.
      cbn.
      cbn.
      fequal.
      destruct Heq.
      rewrite <- H0 in Heq.
      fequal.
      fequal.
      destruct Heq.
    cbv.
  induction b.
*)

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
    apply (pure (F := G) (Basics.flip (vcons (length l))) <⋆> IHl <⋆> f a).
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


  (*
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
   *)

 Lemma traverse_Vector_rw2:
   forall (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
     {A B : Type} (f : A -> G B)
     (a : A) (l: list A)
     (p : length (a :: l) = S n),
     traverse f (exist _ (a :: l) p) =
       pure (Basics.flip (vcons n)) <⋆> traverse f (exist (fun l => length l = n) l (length_uncons a l n p)) <⋆> f a.
 Proof.
   intros.
   assert (n = length l).
   inversion p.
   subst.
   cbn in p.
   reflexivity.
   subst.
   cbn in p.
   assert (p = eq_refl).
   apply proof_irrelevance.
   rewrite H2 at 1.
   cbn.
   subst.
   cbn.
   fequal.
   fequal.
   fequal.
   apply proof_irrelevance.
 Qed.

 Lemma traverse_Vector_vcons:
   forall (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
     {A B : Type} (f : A -> G B)
     (v : Vector n A) (a : A),
     traverse f (vcons n a v) =
       pure (Basics.flip (vcons n)) <⋆> traverse f v <⋆> f a.
 Proof.
   intros.
   unfold vcons.
   destruct v.
   rewrite traverse_Vector_rw2.
   fequal.
   fequal.
   fequal.
   fequal.
   apply proof_irrelevance.
 Qed.


Lemma runBatch_repr {A B C} `{Applicative G}:
  forall (b: Batch A B C) (f: A -> G B),
  map (F := G) (Batch_to_Make2 b) (traverse (T := Vector (length_Batch b)) f (Batch_to_Vector2 b)) =
        runBatch G f _ b.
Proof.
  intros.
  induction b.
  - cbn.
    rewrite app_pure_natural.
    reflexivity.
  - cbn.
    rewrite traverse_Vector_vcons.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- IHb.
    cbn.
    rewrite map_to_ap.
    fequal.
    fequal.
    fequal.
    unfold compose, Basics.flip.
    ext v.
    ext b'.
    rewrite vuncons_surj.
    fequal.
    + symmetry.
      apply vuncons_surj_tl.
    + symmetry.
      apply vuncons_surj_hd.
Qed.


Require Import

          Classes.Coalgebraic.TraversableFunctor
          Adapters.KleisliToCoalgebraic.TraversableFunctor.

Section deconstruction.

  Context
    `{Kleisli.TraversableFunctor.TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  Definition toContents {A B} (t: T A):
    Vector (length_Batch (toBatch (A' := B) t)) A :=
    Batch_to_Vector2 (toBatch t).

  Definition toMake {A} (t: T A) B:
    Vector (length_Batch (toBatch (A' := B) t)) B -> (T B) :=
    Batch_to_Make2 (toBatch t).

  Definition plength: forall {A}, T A -> nat :=
    fun A => traverse (B := False) (G := const nat) (fun _ => 1).

  Lemma plength_eq_length: forall {A} (t: T A),
      plength t = length_Batch (toBatch (A' := False) t).
  Proof.
    intros.
    unfold plength.
    rewrite traverse_through_runBatch.
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn.
      rewrite IHb.
      unfold_ops @NaturalNumbers.Monoid_op_plus.
      lia.
  Qed.

  Lemma plength_eq_length': forall {A} {B} (t: T A),
      plength t = length_Batch (toBatch (A' := B) t).
  Proof.
    intros.
    unfold plength.
    rewrite traverse_through_runBatch.
    unfold compose.
  Admitted.

  Lemma toMake_toContents {A} (t: T A):
    toMake t A (toContents t) = t.
  Proof.
    unfold toMake.
    unfold toContents.
    rewrite Batch_repr.
    compose near t on left.
    rewrite trf_extract.
    reflexivity.
  Qed.

  (*
  Lemma toMake_shape : forall A (t: T A) B,
      toMake t B = toMake (map (F := T) (const tt) t) B.
*)


  Lemma traverse_repr {A} (t: T A) {B} `{Applicative G} `(f: A -> G B):
    traverse f t =
      map (toMake t B) (traverse f (toContents t)).
  Proof.
    rewrite traverse_through_runBatch.
    unfold compose.
    rewrite <- VectorRefinement.runBatch_repr.
    reflexivity.
  Qed.

  Lemma unnamed: forall `(t: T A) B,
      mapsnd_Batch B unit (const tt) (toBatch (A' := unit) t) =
        mapsnd_Batch B unit (const tt) (toBatch (A' := unit) t).
  Proof.
    intros.
    Check map (const tt) (mapsnd_Batch B unit (const tt) (toBatch (A' := unit) t)).
  Abort.

  Section constant_applicatives.

    Context
      `{Monoid M}.

    Lemma traverse_const1: forall {A : Type} (B : Type) `(f : A -> M),
        traverse (G := const M) (B := False) f =
          traverse (G := const M) (B := B) f.
    Proof.
      intros.
      change_left (map (F := const M) (A := T False)
                     (B := T B) (map (F := T) (A := False) (B := B) exfalso)
                     ∘ traverse (T := T) (G := const M)
                     (B := False) (f : A -> const M False)).
      rewrite (map_traverse (G1 := const M)).
      reflexivity.
    Qed.

    Lemma traverse_const2: forall {A : Type} (f : A -> M) (fake1 fake2 : Type),
        traverse (G := const M) (B := fake1) f =
          traverse (G := const M) (B := fake2) f.
    Proof.
      intros.
      rewrite <- (traverse_const1 fake1).
      rewrite -> (traverse_const1 fake2).
      reflexivity.
    Qed.

  End constant_applicatives.

  Lemma unnamed: forall `(t: T A) B C,
      length_Batch (toBatch (A' := B) t) =
        length_Batch (toBatch (A' := C) t).
  Proof.
    intros.
    rewrite length_Batch_spec.
    rewrite length_Batch_spec.
    compose near t on left.
    compose near t on right.
    rewrite <- traverse_through_runBatch.
    rewrite <- traverse_through_runBatch.
    rewrite (traverse_const2 _ B C).
    reflexivity.
  Qed.

  Goal forall `{Applicative G} A B C (t: T A) v1  (f: B -> G C),
      traverse f (toMake t B v1) =
        traverse f (toMake t B v1).
    intros.
    Check  (traverse (T := Vector (length_Batch (toBatch t))) f v1).
    About toBatch.
    (* G (Vector (length_Batch (toBatch t)) C) *)
    Check  map (F := G) (toMake t C).
    (*  G (Vector (length_Batch (toBatch t)) C) -> G (T C) *)
    Fail Check map (F := G) (toMake t C)
              (traverse (G := G) (T := Vector (length_Batch (toBatch t))) f v1).
  Abort.

  Goal forall A (t: T A) B v1,
      plength (toMake t B v1) = length_Batch (toBatch (A' := B) t).
  Proof.
    intros.
    unfold plength.
    unfold toMake.
    destruct (toBatch (A' := B) t).
  Abort.

  Goal forall A (t: T A) B v,
      plength (toMake t B v) = plength t.
  Proof.
    intros.
    rewrite <- (toMake_toContents t) at 2.
    rewrite plength_eq_length.
    rewrite plength_eq_length.
    Search length_Batch toBatch.
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

Lemma Vector_trav_eq_correct: forall
    (A: Type) (n: nat)
    (v1 v2: Vector n A)
    (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {B : Type} (f : A -> G B),
    traverse f (proj1_sig v1) = traverse f (proj1_sig v2) ->
    traverse f v1 = traverse f v2.
Proof.
  introv Heq.
  About Vector_induction2.
  pose (Vector_induction2 A (fun m v1 v2 =>
                               traverse f (proj1_sig v1) = traverse f (proj1_sig v2) ->
                               traverse f v1 = traverse f v2)).
  apply e; clear e.
  - reflexivity.
  - intros m a1 a2 v1' v2' Heq' Heq''.
    rewrite traverse_Vector_vcons.
    rewrite traverse_Vector_vcons.
    rewrite proj_vcons in Heq''.
    rewrite proj_vcons in Heq''.
    cbn in Heq''.
    assert (traverse f v1' = traverse f v2').
    fequal.
    + fequal. admit.
Abort.

#[local] Instance TF_Vec {n}: TraversableFunctor (Vector n).
Proof.
  constructor.
  - intros.
    ext v.
    unfold id at 2.
    specialize (Vector_induction A (fun m v' => traverse (G := fun A => A) id v' = v')).
    intros.
    apply H.
    + reflexivity.
    + intros a m w heq.
      rewrite traverse_Vector_vcons.
      rewrite heq.
      reflexivity.
  -
Admitted.


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












