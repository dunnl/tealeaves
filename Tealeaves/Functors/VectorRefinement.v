From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.TraversableFunctor
  Functors.Batch.

From Coq Require Import
  Logic.ProofIrrelevance.

#[local] Generalizable Variables ϕ T G A B C D M F n m v.

Import Applicative.Notations.

(** * Random lemmas *)
(******************************************************************************)
Lemma S_uncons: `{S n = S m -> n = m}.
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

Definition zero_not_S {n} {anything}:
  0 = S n -> anything :=
  fun pf => match pf with
         | eq_refl =>
             let false : False :=
               eq_ind 0 (fun e : nat => match e with
                           | 0 => True
                           | S _ => False
                           end) I (S n) pf
             in (False_rect anything false)
         end.

(*
Definition length_nil_not_S {n A} {anything}:
  length (@nil A) = S n -> anything := zero_not_S.
*)

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

Definition list_uncons {n A} (l: list A) (vlen: length l = S n):
  A * list A :=
  match l return (length l = S n -> A * list A) with
  | nil => zero_not_S
  | cons a rest => fun vlen => (a, rest)
  end vlen.

Definition list_hd {n A} :=
  fun (l: list A) (vlen: length l = S n) =>
  fst (list_uncons l vlen).

Definition list_tl {n A} :=
  fun (l: list A) (vlen: length l = S n) =>
    snd (list_uncons l vlen).

Lemma list_hd_proof_irrelevance
        {n m A}
        (l: list A)
        (vlen1: length l = S n)
        (vlen2: length l = S m):
  list_hd l vlen1 = list_hd l vlen2.
Proof.
  induction l.
  - inversion vlen1.
  - reflexivity.
Qed.

Lemma list_tl_proof_irrelevance
        {n m A}
        (l: list A)
        (vlen1: length l = S n)
        (vlen2: length l = S m):
  list_tl l vlen1 = list_tl l vlen2.
Proof.
  induction l.
  - inversion vlen1.
  - reflexivity.
Qed.

(*
Lemma list_hd_proof_irrelevance_rw2
        {n A}
        (l1 l2: list A)
        (Heq: l1 = l2)
        (vlen1: length l1 = S n)
        (vlen2: length l2 = S n):
  list_hd l1 vlen1 = list_hd l2 vlen2.
Proof.
  subst.
  apply list_hd_proof_irrelevance1.
Qed.
 *)

Import EqNotations.

Lemma list_hd_proof_irrelevance_rw
        {n A}
        {l1 l2: list A}
        (Heq: l1 = l2)
        {vlen: length l1 = S n}:
  list_hd l1 vlen = list_hd l2 (rew [fun l1 => length l1 = S n] Heq in vlen).
Proof.
  subst.
  apply list_hd_proof_irrelevance.
Qed.

Lemma list_tl_proof_irrelevance_rw
        {n A}
        {l1 l2: list A}
        (Heq: l1 = l2)
        {vlen: length l1 = S n}:
  list_tl l1 vlen = list_tl l2 (rew [fun l1 => length l1 = S n] Heq in vlen).
Proof.
  subst.
  apply list_tl_proof_irrelevance.
Qed.

Lemma list_surjective_pairing `(l: list A) `(vlen: length l = S n):
  list_uncons l vlen = (list_hd l vlen, list_tl l vlen).
Proof.
  destruct l.
  - inversion vlen.
  - reflexivity.
Qed.

Lemma list_surjective_pairing2 `(l: list A) `(vlen: length l = S n):
  l = cons (list_hd l vlen) (list_tl l vlen).
Proof.
  destruct l.
  - inversion vlen.
  - reflexivity.
Qed.

Lemma list_tl_length `(l: list A) `(vlen: length l = S n):
  length (list_tl l vlen) = n.
Proof.
  destruct l.
  - inversion vlen.
  - cbn. now inversion vlen.
Qed.

(** * Refinement-style vectors *)
(******************************************************************************)
Definition Vector (n: nat) (A: Type) : Type :=
  {l : list A | length l = n}.

Definition coerce_Vector_length:
  forall {A: Type} `(Heq: n = m),
    Vector n A -> Vector m A.
Proof.
  introv heq [v pf].
  exists v. now subst.
Defined.

Lemma coerce_Vector_contents:
  forall {A: Type} `(Heq: n = m) (v: Vector n A),
    proj1_sig v = proj1_sig (coerce_Vector_length Heq v).
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
      (exist (fun l => length l = n) l1 p1 =
         exist (fun l => length l = n) l2 p2).
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

Lemma Vector_coerce_eq:
  forall {A: Type} `(Heq: m = n)
    (v1: Vector n A)
    (v2: Vector m A),
    proj1_sig v1 = proj1_sig v2 ->
    v1 = coerce_Vector_length Heq v2.
Proof.
  intros.
  apply Vector_eq.
  rewrite H.
  rewrite (coerce_Vector_contents Heq).
  reflexivity.
Defined.

(** ** Derived constructors *)
(******************************************************************************)
Definition vnil {A}: Vector 0 A :=
  exist (fun l => length l = 0) nil eq_refl.

Definition vcons (n:nat) {A}:
  A ->
  Vector n A ->
  Vector (S n) A.
Proof.
  introv a v.
  destruct v as [vlist vlen].
  apply (exist (fun l => length l = S n) (cons a vlist)).
  cbn. fequal. assumption.
Defined.

Lemma Vector_nil_eq:
  forall `(v: Vector 0 A),
    v = vnil.
Proof.
  intros.
  destruct v as [vlist vlen].
  assert (vlist = @nil A) by
    now rewrite (List.length_zero_iff_nil vlist) in vlen.
  subst.
  apply Vector_eq.
  reflexivity.
Qed.

Lemma proj_vnil: forall `(v: Vector 0 A),
    proj1_sig v = nil.
Proof.
  intros.
  rewrite (Vector_nil_eq v).
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
    rewrite (Vector_nil_eq v1).
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
(*
Definition vuncons {n A}: Vector (S n) A ->
  A * Vector n A.
Proof.
  intros [vlist vlen].
  generalize dependent n.
  induction vlist; intros n vlen.
  - inversion vlen.
  - cbn in *.
    inversion vlen.
    split.
    + exact a.
    + exists vlist. reflexivity.
Defined.
*)

Definition Vector_uncons {n A} (v: Vector (S n) A):
  A * Vector n A :=
  let (vlist, vlen) := v in
  match vlist return (length vlist = S n -> A * Vector n A) with
  | nil => zero_not_S
  | cons a rest => fun vlen => (a, exist _ rest (S_uncons vlen))
  end vlen.

Definition Vector_hd {n A}:
  Vector (S n) A -> A :=
  fst ∘ Vector_uncons.

Definition Vector_tl {n A}:
  Vector (S n) A -> Vector n A :=
  snd ∘ Vector_uncons.

Lemma Vector_list_hd: forall `(v: Vector (S n) A),
    Vector_hd v = list_hd (proj1_sig v) (proj2_sig v).
Proof.
  intros.
  destruct v as [vlist vlen].
  destruct vlist.
  - inversion vlen.
  - reflexivity.
Qed.

Lemma proj_Vector_tl: forall `(v: Vector (S n) A),
    proj1_sig (Vector_tl v) = list_tl (proj1_sig v) (proj2_sig v).
Proof.
  intros.
  destruct v as [vlist vlen].
  destruct vlist.
  - inversion vlen.
  - reflexivity.
Qed.

Lemma Vector_list_tl: forall `(v: Vector (S n) A),
    Vector_tl v = exist (fun l : list A => length l = n)
                        (list_tl (proj1_sig v) (proj2_sig v))
                        (list_tl_length (proj1_sig v) (proj2_sig v)).
Proof.
  intros.
  destruct v as [vlist vlen].
  apply Vector_eq.
  rewrite proj_Vector_tl.
  reflexivity.
Qed.

Lemma Vector_surjective_pairing `{v: Vector (S n) A}:
  Vector_uncons v = (Vector_hd v , Vector_tl v).
Proof.
  destruct v as [vlist vlen].
  unfold Vector_hd, Vector_tl.
  unfold compose.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Lemma Vector_surjective_pairing2 `{v: Vector (S n) A}:
  v = vcons n (Vector_hd v) (Vector_tl v).
Proof.
  destruct v as [vlist vlen].
  apply Vector_eq.
  rewrite proj_vcons.
  cbn.
  rewrite Vector_list_hd.
  rewrite Vector_list_tl.
  cbn.
  apply list_surjective_pairing2.
Qed.

Lemma Vector_hd_vcons {n A a} (v: Vector n A):
  Vector_hd (vcons n a v) = a.
Proof.
  destruct v.
  reflexivity.
Qed.

Lemma Vector_tl_vcons {n A a} (v: Vector n A):
  Vector_tl (vcons n a v) = v.
Proof.
  destruct v.
  apply Vector_eq.
  cbn.
  reflexivity.
Qed.

Definition vunone {A : Type} : Vector 1 A -> A :=
  Vector_hd.

(** ** Similarity *)
(******************************************************************************)
(*
  Definition Vector_sim {n A}:
    Vector n A -> Vector n A -> Prop :=
    fun v1 v2 => proj1_sig v1 = proj1_sig v2.
 *)


From Coq Require Import RelationClasses.


Definition Vector_sim {n m A}:
  Vector n A -> Vector m A -> Prop :=
  fun v1 v2 => proj1_sig v1 = proj1_sig v2.

Infix "=vec=" := (Vector_sim) (at level 30).

Lemma symmetric_Vector_sim
        `{v1: Vector n A}
        `{v2: Vector m A}:
  Vector_sim v1 v2 <->
    Vector_sim v2 v1.
  split; symmetry; assumption.
Qed.

Ltac vec_symmetry :=
  rewrite symmetric_Vector_sim.

#[export] Instance Reflexive_Vector_sim {n A}:
  Reflexive (@Vector_sim n n A).
Proof.
  unfold Reflexive. reflexivity.
Qed.

Lemma coerce_Vector_compose
        {n m p: nat}
        `{v: Vector n A} (Heq1: n = m) (Heq2: m = p):
  coerce_Vector_length Heq2 (coerce_Vector_length Heq1 v) =
    coerce_Vector_length (eq_trans Heq1 Heq2) v.
Proof.
  destruct v as [vlist vlen].
  unfold coerce_Vector_length.
  fequal.
  destruct Heq1.
  cbn.
  fequal.
  now rewrite eq_trans_refl_l.
  destruct Heq2.
  subst.
  cbn.
  reflexivity.
Qed.

Lemma Vector_coerce_sim {n m} `{v: Vector n A}:
  forall (Heq: n = m),
    Vector_sim (coerce_Vector_length Heq v) v.
Proof.
  intros.
  unfold Vector_sim.
  rewrite (coerce_Vector_contents Heq).
  reflexivity.
Qed.

Lemma Vector_sim_eq1 {n A} (v1 v2: Vector n A):
  Vector_sim v1 v2 -> v1 = v2.
Proof.
  intro hyp.
  apply Vector_eq.
  apply hyp.
Qed.

Lemma Vector_hd_sim {n m A}
                    {v1: Vector (S n) A}
                    {v2: Vector (S m) A}:
    Vector_sim v1 v2 ->
    Vector_hd v1 = Vector_hd v2.
Proof.
  intro Hsim.
  rewrite Vector_list_hd.
  rewrite Vector_list_hd.
  unfold Vector_sim in Hsim.
  rewrite (list_hd_proof_irrelevance_rw Hsim).
  apply list_hd_proof_irrelevance.
Qed.

Lemma Vector_tl_sim {n m A}
                    {v1: Vector (S n) A}
                    {v2: Vector (S m) A}:
    Vector_sim v1 v2 ->
    Vector_sim (Vector_tl v1) (Vector_tl v2).
Proof.
  intro Hsim.
  unfold Vector_sim in *.
  rewrite proj_Vector_tl.
  rewrite proj_Vector_tl.
  rewrite (list_tl_proof_irrelevance_rw Hsim).
  apply list_tl_proof_irrelevance.
Qed.

Corollary Vector_tl_coerce_sim {n m A}
                               {v: Vector (S n) A}
                               {Heq: S n = S m}:
  Vector_sim (Vector_tl v) (Vector_tl (coerce_Vector_length Heq v)).
Proof.
  apply Vector_tl_sim.
  vec_symmetry.
  apply Vector_coerce_sim.
Qed.

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

Fixpoint Batch_contents `(b: Batch A B C):
  Vector (length_Batch b) A :=
  match b with
  | Done c => vnil
  | Step b a => vcons (length_Batch b) a (Batch_contents b)
  end.

Fixpoint Batch_make `(b: Batch A B C):
  Vector (length_Batch b) B -> C :=
  match b return Vector (length_Batch b) B -> C with
  | Done c => fun v => c
  | Step b a => fun v =>
        Batch_make b (Vector_tl v) (Vector_hd v)
        (*
        let (hd, tl) := Vector_uncons v
        in Batch_make b tl hd
        *)
  end.

Fixpoint Batch_replace_contents
           `(b: Batch A B C)
           `(v: Vector (length_Batch b) A')
           : Batch A' B C :=
  match b return (Vector (length_Batch b) A' -> Batch A' B C) with
  | Done c => fun v => Done c
  | Step rest a =>
      fun v => Step (Batch_replace_contents rest (Vector_tl v))
           (Vector_hd v)
  end v.

Section Batch.

  Section rw.
    Context {A B C: Type}.

    Implicit Types (a: A) (b: Batch A B (B -> C)) (c: C).

    Lemma Batch_contents_rw1 {c}:
      Batch_contents (@Done A B C c) = vnil.
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_contents_rw2 {b a}:
      Batch_contents (Step b a) =
        vcons (length_Batch b) a (Batch_contents b).
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_make_rw1 {c}:
      Batch_make (@Done A B C c) = const c.
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_make_rw2 {b a}:
      Batch_make (Step b a) =
        fun v => Batch_make b (Vector_tl v) (Vector_hd v).
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_replace_rw1 {c} `{v: Vector _ A'}:
      Batch_replace_contents (@Done A B C c) v = Done c.
    Proof.
      reflexivity.
    Qed.

    Lemma Batch_replace_rw2 {b a} `{v: Vector _ A'}:
      Batch_replace_contents (Step b a) v =
        Step (Batch_replace_contents b (Vector_tl v)) (Vector_hd v).
    Proof.
      reflexivity.
    Qed.

  End rw.

  Lemma Batch_make_sim
          `(b: Batch A B C)
          `{v1: Vector (length_Batch b) B}
          `{v2: Vector (length_Batch b) B}
      (Hsim: Vector_sim v1 v2):
    Batch_make b v1 = Batch_make b v2.
  Proof.
    induction b.
    - reflexivity.
    - rewrite Batch_make_rw2.
      rewrite (IHb _ _ (Vector_tl_sim Hsim)).
      rewrite (Vector_hd_sim Hsim).
      reflexivity.
  Qed.

  Lemma Batch_make_sim'
          `(b1: Batch A B C)
          `(b2: Batch A B C)
          `{v1: Vector (length_Batch b1) B}
          `{v2: Vector (length_Batch b2) B}
          (Heq: b1 = b2)
      (Hsim: Vector_sim v1 v2):
    Batch_make b1 v1 = Batch_make b2 v2.
  Proof.
    subst.
    now apply Batch_make_sim.
  Qed.

  Lemma Batch_make_sim''
          `(b1: Batch A B C)
          `(b2: Batch A B C)
          `{v1: Vector (length_Batch b1) B}
          (Heq: b1 = b2):
    Batch_make b1 v1 =
      Batch_make b2 (rew [fun b => Vector (length_Batch b) B]
                     Heq in v1).
  Proof.
    subst.
    now apply Batch_make_sim.
  Qed.

  Lemma Batch_make_compose `(b: Batch A B C) `(f: C -> D)
                           `(Hsim: v1 =vec= v2):
    f (Batch_make b v1) =
      Batch_make (map (F := Batch A B) f b) v2.
  Proof.
    generalize dependent v2.
    generalize dependent v1.
    generalize dependent D.
    induction b as [C c | C rest IHrest].
    - reflexivity.
    - intros D f v1 v2 Hsim.
      change (map f (Step rest a)) with
        (Step (map (compose f) rest) a) in *.
      cbn in v2, v1.
      do 2 rewrite Batch_make_rw2.
      replace (Vector_hd v2) with (Vector_hd v1) at 1.
      2: { apply Vector_hd_sim. assumption. }
      change_left ((evalAt (Vector_hd v1) ∘ compose f)
                     (Batch_make rest (Vector_tl v1))).
      change_right (evalAt (Vector_hd v1)
                           (Batch_make (map (compose f) rest) (Vector_tl v2))).
      specialize (IHrest _ (compose f)).
      unfold compose at 1.
      fequal.
      assert (tl_sim: (Vector_tl v1) =vec= (Vector_tl v2)).
      { apply Vector_tl_sim. assumption. }
      specialize (IHrest (Vector_tl v1) (Vector_tl v2) tl_sim).
      rewrite IHrest.
      reflexivity.
  Qed.

  Lemma Batch_make_compose_rw1 `(b: Batch A B C) `(f: C -> D) v:
    f (Batch_make b v) =
      Batch_make (map (F := Batch A B) f b)
                 (coerce_Vector_length (batch_length_map _ _) v).
  Proof.
    rewrite (Batch_make_compose b f
                                (v1 := v)
                                (v2 :=coerce_Vector_length (batch_length_map _ _) v)).
    reflexivity.
    vec_symmetry.
    apply Vector_coerce_sim.
  Qed.

  Lemma Batch_make_compose_rw2 `(b: Batch A B C) `(f: C -> D) v:
    Batch_make (map (F := Batch A B) f b) v =
      f (Batch_make b (coerce_Vector_length (eq_sym (batch_length_map _ _)) v)).
  Proof.
    rewrite (Batch_make_compose_rw1 b f).
    apply Batch_make_sim.
    vec_symmetry.
    rewrite coerce_Vector_compose.
    apply Vector_coerce_sim.
  Qed.

  Context {A A' B C: Type}.

  (* get-put?? *)
  Lemma Batch_make_contents:
    forall (b: Batch A A C),
      Batch_make b (Batch_contents b) = extract_Batch b.
  Proof.
    intros.
    induction b.
    - reflexivity.
    - rewrite Batch_make_rw2.
      rewrite Batch_contents_rw2.
      rewrite Vector_tl_vcons.
      rewrite Vector_hd_vcons.
      rewrite IHb.
      reflexivity.
  Qed.

  (* get-put?? *)
  Lemma Batch_contents_make:
    forall (b: Batch A B C),
      Batch_contents (Batch_make b v) = extract_Batch b.
  Proof.
    intros.
    induction b.
    - reflexivity.
    - rewrite Batch_make_rw2.
      rewrite Batch_contents_rw2.
      rewrite Vector_tl_vcons.
      rewrite Vector_hd_vcons.
      rewrite IHb.
      reflexivity.
  Qed.

  (* /put-get *)

  Lemma length_replace_contents:
    forall {A B C: Type} (b: Batch A B C) `(v: Vector _ A'),
    length_Batch b = length_Batch (Batch_replace_contents b v).
  Proof.
    intros.
    clear A B C.
    rename A0 into A, B0 into B, C0 into C.
    induction b.
    - reflexivity.
    - cbn. fequal.
      apply (IHb (Vector_tl v)).
  Qed.

  Ltac solve_vector_length :=
    match goal with
    | |- ?v =vec= coerce_Vector_length ?e ?v =>
        vec_symmetry;
        apply Vector_coerce_sim
    | |- Vector_hd ?v = Vector_hd ?w =>
        apply Vector_hd_sim;
        solve_vector_length
    end.

  Lemma Batch_replace_contents0:
    forall (b: Batch A B C) v,
      Batch_contents (Batch_replace_contents b v) =
        coerce_Vector_length (length_replace_contents b v) v.
  Proof.
    intros.
    generalize (length_replace_contents b v).
    intros e.
    induction b.
    - cbn. symmetry.
      cbn in v.
      apply Vector_nil_eq.
    - cbn in *.
      rewrite Vector_surjective_pairing2.
      fequal.
      + solve_vector_length.
      + specialize (IHb (Vector_tl v) (S_uncons e)).
        assert (H: coerce_Vector_length (S_uncons e) (Vector_tl v) =
                  Vector_tl (coerce_Vector_length e v)).
        { apply Vector_eq.
          rewrite <- coerce_Vector_contents.
          apply Vector_tl_sim.
          solve_vector_length.
        }
        rewrite <- H.
        assumption.
  Qed.

  Lemma Batch_replace_contents1:
    forall (b: Batch A B C),
      Batch_replace_contents b (Batch_contents b) = b.
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn.
      rewrite Vector_tl_vcons.
      rewrite Vector_hd_vcons.
      rewrite IHb.
      reflexivity.
  Qed.

  (* TODO Move me *)
  Lemma length_cojoin_Batch:
    forall {A B C} (b: Batch A B C),
      length_Batch b = length_Batch (cojoin_Batch (B := A') b).
  Proof.
    induction b.
    - reflexivity.
    - cbn. fequal.
      rewrite IHb.
      rewrite <- batch_length_map.
      reflexivity.
  Qed.

  Lemma Batch_replace_contents2:
    forall (b: Batch A B C) (v: Vector (length_Batch b) A'),
      Batch_replace_contents b v =
        Batch_make (cojoin_Batch b (B := A'))
                   (coerce_Vector_length (length_cojoin_Batch b) v).
  Proof.
    intros.
    generalize (length_cojoin_Batch b).
    intros e.
    induction b.
    - reflexivity.
    - rewrite Batch_replace_rw2.
      pose (cojoin_Batch_rw1 A A' B C b a).
      change (cojoin_Batch (Step b a))
        with (Step (map (@Step A' B C) (cojoin_Batch b)) a).
      rewrite Batch_make_rw2.
      replace (Vector_hd (coerce_Vector_length e v))
        with (Vector_hd v) at 1.
      2:{ erewrite Vector_hd_sim. reflexivity.
          vec_symmetry.
          apply Vector_coerce_sim. }
      rewrite Batch_make_compose_rw2.
      fequal.
      specialize (IHb (Vector_tl v)).
      specialize (IHb (length_cojoin_Batch b)).
      rewrite IHb.
      apply Batch_make_sim.
      {
        unfold Vector_sim.
        rewrite <- coerce_Vector_contents.
        rewrite <- coerce_Vector_contents.
        apply Vector_tl_coerce_sim.
      }
  Qed.

  Lemma Batch_replace_contents3:
    forall (b: Batch A B C) (v: Vector (length_Batch b) A'),
      Batch_make (Batch_replace_contents b v) =
        (fun v' => Batch_make (B := B) b
                            (coerce_Vector_length
                               (eq_sym (length_replace_contents b v)) v')).
  Proof.
    intros.
    ext v'.
    generalize (eq_sym (length_replace_contents b v)).
    intro e.
    induction b.
    - reflexivity.
    - cbn.
      specialize (IHb (Vector_tl v)).
      specialize (IHb (Vector_tl v')).
      specialize (IHb (eq_sym (length_replace_contents b (Vector_tl v)))).

      replace (Vector_hd (coerce_Vector_length e v'))
        with (Vector_hd v') at 1.
      Set Keyed Unification.
      rewrite IHb.
      Unset Keyed Unification.
      fequal.
      { apply Vector_eq.
        rewrite <- coerce_Vector_contents.
        apply Vector_tl_coerce_sim.
      }
      solve_vector_length.
  Qed.

  (*
  Lemma Batch_make_cojoin:
    forall (b: Batch A B C) (v: Vector (length_Batch b) B),
      Batch_make (cojoin_Batch (B := B) b) = b.

  Lemma Batch_repr:
    forall (b: Batch A A C) v,
      Batch_contents (Batch_make b v) = v.

  Fixpoint cojoin_Batch {A B C D : Type} (b : Batch A C D) :
    Batch A B (Batch B C D)
   *)

  (* put-get?? *)
  (*
  Lemma Batch_repr:
    forall (b: Batch A A C) v,
      Batch_contents (Batch_make b v) = v.
  Proof.
    intros.
    induction b.
    - reflexivity.
    - rewrite Batch_make_rw2.
      rewrite Batch_contents_rw2.
      rewrite Vector_tl_vcons.
      rewrite Vector_hd_vcons.
      rewrite IHb.
      reflexivity.
  Qed.
*)

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

End Batch.

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
    map (F := G) (Batch_make b)
        (traverse (T := Vector (length_Batch b)) f (Batch_contents b)) =
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
    rewrite Vector_tl_vcons.
    rewrite Vector_hd_vcons.
    reflexivity.
Qed.
