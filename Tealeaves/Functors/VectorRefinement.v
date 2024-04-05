From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.TraversableFunctor
  Functors.Batch.

From Coq Require Import
  Logic.ProofIrrelevance.

#[local] Generalizable Variables ϕ T G A M F n m.

Import Applicative.Notations.

(** * Random lemmas *)
(******************************************************************************)
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

Lemma list_cons_eq:
  forall (A: Type) (n: nat)
    (v: list A) (vlen: length v = S n),
    exists (a: A) (v': list A),
    v = cons a v'.
Proof.
  intros.
  destruct v.
  - inversion vlen.
  - exists a v. reflexivity.
Qed.

(** * Refinement-style vectors *)
(******************************************************************************)
Definition Vector (n: nat) (A: Type) : Type :=
  {l : list A | length l = n}.

Definition coerce_Vector_length: forall {A: Type} (n m: nat) (Heq: n = m),
    Vector n A -> Vector m A.
Proof.
  introv heq [v pf].
  exists v. now subst.
Defined.

Lemma coerce_Vector_contents: forall {A: Type} (n m: nat) (Heq: n = m) (v: Vector n A),
    proj1_sig v = proj1_sig (coerce_Vector_length n m Heq v).
Proof.
  intros ? n m Heq [v pf].
  reflexivity.
Qed.

(** ** Basic properties vectors *)
(******************************************************************************)
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

Lemma Vector_eq:
  forall (A: Type) (n: nat)
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

(** ** Derived constructors *)
(******************************************************************************)
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
  assert (vlist = @nil A).
  { rewrite <- (List.length_zero_iff_nil vlist).
    assumption. }
  subst.
  apply Vector_eq.
  reflexivity.
Qed.

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

(** ** Induction *)
(******************************************************************************)
Lemma Vector_induction:
  forall (A: Type) (P: forall m, Vector m A -> Prop)
    (IHnil: P 0 vnil)
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

Lemma Vector_induction_alt:
  forall (m: nat) (A: Type) (P: forall m, Vector m A -> Prop)
    (IHnil: P 0 vnil)
    (IHcons:
      forall a m (v: Vector m A), P m v -> P (S m) (vcons m a v)),
  forall (v: Vector m A), P m v.
Proof.
  intros.
  apply Vector_induction; eauto.
Qed.

Lemma Vector_induction2:
  forall (A: Type) (m : nat) (P: forall m, Vector m A -> Vector m A -> Prop)
    (IHnil: P 0 vnil vnil)
    (IHcons:
      forall m (a1 a2: A) (v1 v2: Vector m A),
        P m v1 v2 ->
        P (S m) (vcons m a1 v1) (vcons m a2 v2)),
  forall (v1 v2: Vector m A), P m v1 v2.
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

(** ** Inversion *)
(******************************************************************************)
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

(** ** to_list *)
(******************************************************************************)
Section sec.

  Context (A: Type).

  Definition to_list {n:nat}: Vector n A -> list A.
  Proof.
    intros. apply proj1_sig in X. assumption.
  Defined.

  Lemma to_list_vnil:
    to_list vnil = @nil A.
  Proof.
    reflexivity.
  Qed.

  Lemma to_list_vcons {a} {n} {v: Vector n A}:
    to_list (vcons _ a v) = a :: to_list v.
  Proof.
    destruct v.
    unfold vcons.
    reflexivity.
  Qed.

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

  Lemma artificial_surjection_inv n (x:Vector n A) (l:list A) (Heq: length l = n):
    proj1_sig (artificial_surjection x l) = l.
  Proof.
    unfold artificial_surjection.
    assert (decide_length n l = left Heq).
    { destruct (decide_length n l).
      + fequal. apply proof_irrelevance.
      + contradiction.
    }
    rewrite H.
    reflexivity.
  Qed.

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
    destruct v.
    apply Vector_eq.
    rewrite artificial_surjection_inv.
    - reflexivity.
    - rewrite to_list_length.
      reflexivity.
  Qed.

  Lemma functors_preserve_inj `{Functor F}:
    forall {A B: Type} (f: A -> B) (g: B -> A)
      (Hinv: g ∘ f = id) (a1 a2: F A),
      map f a1 = map f a2 -> a1 = a2.
  Proof.
    introv Hinv Heq.
    change (id a1 = id a2).
    rewrite <- (fun_map_id (F := F)).
    rewrite <- Hinv.
    rewrite <- (fun_map_map (F := F)).
    unfold compose.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma functors_preserve_inj2 `{Functor F}:
    forall {A B: Type} (f: A -> B) (a1 a2: F A),
    (exists g: B -> A, g ∘ f = id) ->
      map f a1 = map f a2 -> a1 = a2.
  Proof.
    introv Hinv. destruct Hinv.
    eapply functors_preserve_inj.
    eassumption.
  Qed.

  Lemma functors_preserve_inj4 `{Applicative F}:
    forall {A1 A2 B: Type} (f: A1 -> A2 -> B) (a1 a2: F A1) (a1' a2': F A2),
    (exists g: B -> A1 * A2, (forall x y, (compose g ∘ f) x y = (x, y))) ->
    pure f <⋆> a1 <⋆> a1'
    = pure f <⋆> a2 <⋆> a2'
    -> a1 = a2 /\ a1' = a2'.
  Proof.
    introv Hinv Heq.
    enough (cut: (a1, a1') = (a2, a2')).
    { inversion cut. now subst. }
    change (id (a1, a1') = (a2, a2')).
    assert (a1 ⊗ a1' = a2 ⊗ a2' -> (a1, a1') = (a2, a2')).
    { intro eq_mult.
      assert (map fst (a1 ⊗ a1') =
                map fst (a2 ⊗ a2'))
               by now rewrite eq_mult.
      assert (map snd (a1 ⊗ a1') =
                map snd (a2 ⊗ a2'))
        by now rewrite eq_mult.
      assert (map (F := F) (fun x => (fst x, snd x)) (a1 ⊗ a1') =
                map (fun x => (fst x, snd x)) (a2 ⊗ a2')).
      { rewrite eq_mult. reflexivity. }
  Abort.

  Lemma functors_preserve_inj3 `{Applicative F}:
    forall {A B: Type} (f: A -> B) (a1 a2: F A),
    (exists g: B -> A, g ∘ f = id) ->
    pure f <⋆> a1 = pure f <⋆> a2 -> a1 = a2.
  Proof.
    introv Hinv.
    rewrite <- map_to_ap.
    rewrite <- map_to_ap.
    apply functors_preserve_inj2.
    assumption.
  Qed.

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
  | exist _ l p =>
      exist _ (map (F := list) f l)
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


Definition traverse_Vector_alt
             (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
             {A B : Type} (f : A -> G B)
             (v : Vector n A) : G (Vector n B).
Proof.
  unfold Vector in *.
  destruct v as [l Heq].
  generalize dependent n.
  induction l; intros n Heq.
  - apply pure.
    subst.
    cbn.
    apply vnil.
  - cbn in Heq.
    assert (n = S (n - 1)).
    { lia. }
    rewrite H2.
    apply ((ap G) ∘ ap G (pure (vcons (n - 1))) (A := B)).
    + apply f. assumption.
    + apply IHl.
      lia.
Defined.

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

#[export] Instance Traverse_Vector {n}: Traverse (Vector n) := traverse_Vector n.


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

Lemma traverse_Vector_rw1:
  forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {A B : Type} (f : A -> G B),
    traverse f vnil = pure vnil.
Proof.
  intros.
  reflexivity.
Qed.

Lemma traverse_Vector_rw2:
  forall (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {A B : Type} (f : A -> G B)
    (a : A) (l: list A)
    (p : length (a :: l) = S n),
    traverse f (exist _ (a :: l) p) =
      pure (Basics.flip (vcons n)) <⋆>
        traverse f (exist (fun l => length l = n) l (length_uncons a l n p)) <⋆> f a.
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

Lemma traverse_Vector_id `{v : Vector n A}:
  traverse (G := fun A => A) id v = v.
Proof.
  induction v using Vector_induction_alt.
  - rewrite traverse_Vector_rw1.
    reflexivity.
  - rewrite traverse_Vector_vcons.
    rewrite IHv.
    reflexivity.
Qed.

Lemma trf_traverse_traverse_Vector:
  forall (G1 : Type -> Type)
    (H0 : Map G1) (H1 : Pure G1)
    (H2 : Mult G1),
    Applicative G1 ->
    forall (G2 : Type -> Type)
      (H4 : Map G2) (H5 : Pure G2)
      (H6 : Mult G2),
      Applicative G2 ->
      forall (A B C : Type) (g : B -> G2 C) (f : A -> G1 B),
      forall `{v : Vector n A},
        (map (traverse (G := G2) g) ∘ traverse (G := G1) f) v =
          traverse (T := Vector n) (G := G1 ∘ G2) (kc2 g f) v.
Proof.
  intros.
  unfold compose at 1.
  induction v using Vector_induction_alt.
  - do 2 rewrite traverse_Vector_rw1.
    rewrite app_pure_natural.
    rewrite traverse_Vector_rw1.
    reflexivity.
  - rewrite traverse_Vector_vcons.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite traverse_Vector_vcons.
    rewrite <- IHv.
    rewrite (ap_compose2 G2 G1).
    rewrite (ap_compose2 G2 G1).
    unfold_ops @Pure_compose.
    repeat rewrite map_ap;
      rewrite (app_pure_natural (G := G1));
      rewrite <- ap_map;
      repeat rewrite map_ap;
      rewrite (app_pure_natural (G := G1)).
    rewrite app_pure_natural.
    unfold kc2.
    unfold compose at 4.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite (app_pure_natural (G := G1)).
    { repeat fequal.
      ext w z.
      unfold compose, precompose.
      unfold Basics.flip.
      fold (Vector m C).
      rewrite traverse_Vector_vcons.
      reflexivity.
    }
Qed.

Lemma trf_traverse_morphism_Vector :
  forall (G1 G2 : Type -> Type)
    (H0 : Map G1) (H1 : Mult G1)
    (H2 : Pure G1) (H3 : Map G2)
    (H4 : Mult G2) (H5 : Pure G2)
    (ϕ : forall A : Type, G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ ->
    forall (A B : Type) (f : A -> G1 B),
    forall `{v : Vector n A},
      ϕ (_ B) (traverse f v) = traverse (ϕ B ∘ f) v.
Proof.
  intros.
  induction v using Vector_induction_alt.
  - do 2 rewrite traverse_Vector_rw1.
    rewrite appmor_pure.
    reflexivity.
  - rewrite traverse_Vector_vcons.
    rewrite traverse_Vector_vcons.
    inversion H.
    rewrite <- appmor_pure.
    rewrite <- IHv.
    unfold compose at 1.
    do 2 rewrite ap_morphism_1.
    reflexivity.
Qed.

#[export] Instance TraversableFunctor_Vector {n:nat}:
  TraversableFunctor (Vector n).
Proof.
  constructor.
  - intros.
    apply functional_extensionality.
    intros.
    apply traverse_Vector_id.
  - intros.
    apply functional_extensionality.
    intros.
    apply trf_traverse_traverse_Vector; auto.
  - intros.
    apply functional_extensionality.
    intros.
    apply trf_traverse_morphism_Vector.
    auto.
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
