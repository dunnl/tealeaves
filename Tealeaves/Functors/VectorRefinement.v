From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.TraversableFunctor
  Classes.Categorical.ShapelyFunctor
  Functors.Batch.

From Coq Require Import
  Logic.ProofIrrelevance.

#[local] Generalizable Variables ϕ T G A B C D M F n m p v.

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

Definition decide_length {A}: forall (n: nat) (l: list A),
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

(* TODO Move me *)
Lemma length_cojoin_Batch:
  forall {A A' B C} (b: Batch A B C),
    length_Batch b = length_Batch (cojoin_Batch (B := A') b).
Proof.
  induction b.
  - reflexivity.
  - cbn. fequal.
    rewrite IHb.
    rewrite <- batch_length_map.
    reflexivity.
Qed.

(** * Un-con-sing non-empty lists *)
(******************************************************************************)
Lemma list_uncons_exists:
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

Definition list_uncons_sigma {n A} (l: list A) (vlen: length l = S n):
  A * {l : list A | length l = n} :=
  match l return (length l = S n -> A * {l: list A | length l = n}) with
  | nil => zero_not_S
  | cons hd tl => fun vlen => (hd, exist _ tl (S_uncons vlen))
  end vlen.

Definition list_uncons_sigma2 {n A} (l: list A) (vlen: length l = S n):
  {p: A * list A | l = uncurry cons p} :=
  match l return (length l = S n -> {p: A * list A | l = uncurry cons p}) with
  | nil => zero_not_S
  | cons hd tl => fun vlen => exist _ (hd, tl) eq_refl
  end vlen.

(** ** Total list head and tail functions for non-empty lists *)
(******************************************************************************)
Definition list_hd {n A} :=
  fun (l: list A) (vlen: length l = S n) =>
  fst (list_uncons l vlen).

Definition list_tl {n A} :=
  fun (l: list A) (vlen: length l = S n) =>
    snd (list_uncons l vlen).

(** *** Proof independence and rewriting laws *)
(******************************************************************************)
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

Import EqNotations.

(** Rewrite a [list_hd] subterm by pushing a type coercion into the
    length proof *)
Lemma list_hd_rw
        {n A}
        {l1 l2: list A}
        (Heq: l1 = l2)
        {vlen: length l1 = S n}:
  list_hd l1 vlen = list_hd l2 (rew [fun l1 => length l1 = S n] Heq in vlen).
Proof.
  subst.
  apply list_hd_proof_irrelevance.
Qed.

(** Rewrite a [list_tl] subterm by pushing a type coercion into the
    length proof *)
Lemma list_tl_rw
        {n A}
        {l1 l2: list A}
        (Heq: l1 = l2)
        {vlen: length l1 = S n}:
  list_tl l1 vlen = list_tl l2 (rew [fun l1 => length l1 = S n] Heq in vlen).
Proof.
  subst.
  apply list_tl_proof_irrelevance.
Qed.

Lemma list_tl_length `(l: list A) `(vlen: length l = S n):
  length (list_tl l vlen) = n.
Proof.
  destruct l.
  - inversion vlen.
  - cbn. now inversion vlen.
Qed.

(** *** Surjective pairing properties *)
(******************************************************************************)
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

#[global] Notation "'coerce' Hlen 'in' V" :=
  (coerce_Vector_length Hlen V)
    (at level 10, V at level 10).

#[global] Notation "'precoerce' Hlen 'in' F" :=
  (F ○ coerce_Vector_length Hlen)
    (at level 10, F at level 20).

Lemma coerce_Vector_contents:
  forall {A: Type} `(Heq: n = m) (v: Vector n A),
    proj1_sig v = proj1_sig (coerce_Vector_length Heq v).
Proof.
  intros ? n m Heq [v pf].
  reflexivity.
Qed.

Lemma coerce_Vector_eq_refl:
  forall {A: Type} {n} (v: Vector n A),
    coerce eq_refl in v = v.
Proof.
  intros.
  destruct v.
  destruct e.
  reflexivity.
Qed.

Lemma coerce_Vector_compose
        {n m p: nat} `{v: Vector n A}
        (Heq1: n = m)
        (Heq2: m = p):
  coerce_Vector_length Heq2 (coerce_Vector_length Heq1 v) =
    coerce_Vector_length (eq_trans Heq1 Heq2) v.
Proof.
  destruct Heq1.
  destruct Heq2.
  destruct v as [vlist vlen].
  destruct vlen.
  reflexivity.
Qed.

Lemma coerce_Vector_eq_sym:
  forall {A: Type} {n m} (v: Vector n A)
    (Heq: n = m),
    v = coerce (eq_sym Heq) in coerce Heq in v.
Proof.
  intros.
  rewrite coerce_Vector_compose.
  rewrite eq_trans_sym_inv_r.
  rewrite coerce_Vector_eq_refl.
  reflexivity.
Qed.

(** ** Similarity *)
(******************************************************************************)
From Coq Require Import RelationClasses.

Definition Vector_sim {n m A}:
  Vector n A -> Vector m A -> Prop :=
  fun v1 v2 => proj1_sig v1 = proj1_sig v2.

Infix "~~" := (Vector_sim) (at level 30).

(* Without <<n = m>>, functions with <<n <> m>> are related which is
awkward and blocks transitivity. >> *)
Definition Vector_fun_sim {n m A B}:
  (Vector n A -> B) -> (Vector m A -> B) -> Prop :=
  fun f1 f2 => n = m /\ forall v1 v2, v1 ~~ v2 ->
                     f1 v1 = f2 v2.

Infix "~!~" := (Vector_fun_sim) (at level 30).

Definition Vector_fun_indep {n A B} (f: Vector n A -> B)
  : Prop := f ~!~ f.

Lemma Vector_fun_sim_eq
        {n m A B} {v1: Vector n A} {v2: Vector m A}
        {f: Vector n A -> B} {g: Vector m A -> B}:
  f ~!~ g ->
  v1 ~~ v2 ->
  f v1 = g v2.
Proof.
  introv Hfsim Hsim.
  destruct Hfsim as [Heq Hfsim].
  auto.
Qed.

Lemma Vector_fun_indep_eq
        {n A B} {v1: Vector n A} {v2: Vector n A}
        {f: Vector n A -> B} (Hind: f ~!~f):
  v1 ~~ v2 ->
  f v1 = f v2.
Proof.
  now apply Vector_fun_sim_eq.
Qed.

Lemma Vector_sim_length:
  forall {A: Type} {n m: nat}
    (v1: Vector n A)
    (v2: Vector m A),
    v1 ~~ v2 -> n = m.
Proof.
  intros.
  destruct v1.
  destruct v2.
  unfold Vector_sim in H.
  cbn in H.
  subst.
  reflexivity.
Qed.

(** *** Relation properties *)
(******************************************************************************)

(** **** Reflexivity *)
(******************************************************************************)
#[export] Instance Reflexive_Vector_sim {n A}:
  Reflexive (@Vector_sim n n A).
Proof.
  unfold Reflexive. reflexivity.
Qed.

(* You need proof irrelevance to prove reflexivity *)
#[export] Instance Reflexive_Vector_fun_sim {n A B}:
  Reflexive (@Vector_fun_sim n n A B).
Proof.
  unfold Reflexive. intro f.
Abort.

(** **** Symmetry *)
(******************************************************************************)
(* We cannot instantiate <<Symmetric>> because ~~ is parameterized by
n and m. *)
Lemma symmetric_Vector_sim
        `{v1: Vector n A}
        `{v2: Vector m A}:
  v1 ~~ v2 <->
    v2 ~~ v1.
Proof.
  split; symmetry; assumption.
Qed.

Ltac vec_symmetry :=
  rewrite symmetric_Vector_sim.

Lemma symmetric_Vector_fun_sim
        `{f1: Vector n A -> B}
        `{f2: Vector m A -> B}:
  f1 ~!~ f2 <->
    f2 ~!~ f1.
Proof.
  unfold Vector_fun_sim.
  (*
  split; intros.
  - symmetry. apply H. now vec_symmetry.
  - symmetry. apply H. now vec_symmetry.
  *)
  split; intros [H1 H2]; split; try congruence; subst.
  - symmetry. apply H2; auto. now vec_symmetry.
  - symmetry. apply H2; auto. now vec_symmetry.
Qed.

Ltac vec_fun_symmetry :=
  rewrite symmetric_Vector_fun_sim.

(** *** Transitivity *)
(******************************************************************************)
(* We cannot instantiate <<Transitive>> because ~~ is parameterized by
n and m. *)
Lemma transitive_Vector_sim
        `{v1: Vector n A}
        `{v2: Vector m A}
        `{v3: Vector p A}:
  v1 ~~ v2 -> v2 ~~ v3 -> v1 ~~ v3.
Proof.
  congruence.
Qed.

Lemma transitive_Vector_fun_sim
        `{f1: Vector n A -> B}
        `{f2: Vector m A -> B}
        `{f3: Vector p A -> B}:
  f1 ~!~ f2 ->
  f2 ~!~ f3 ->
  f1 ~!~ f3.
Proof.
  intros.
  unfold Vector_fun_sim in *.
  intuition.
  destruct H1.
  transitivity (f2 v1).
  - apply H2. reflexivity.
  - apply H3. assumption.
Qed.

(** *** Length coercions *)
(******************************************************************************)
Lemma Vector_coerce_sim_l {n m} `{v: Vector n A} (Heq: n = m):
    coerce Heq in v ~~ v.
Proof.
  unfold Vector_sim.
  rewrite (coerce_Vector_contents Heq).
  reflexivity.
Qed.

Lemma Vector_coerce_sim_r {n m} `{v: Vector n A} (Heq: n = m):
  v ~~ coerce Heq in v.
Proof.
  vec_symmetry.
  apply Vector_coerce_sim_l.
Qed.

(* Tactics *)
Lemma Vector_coerce_sim_l'
        {n m p} `{w: Vector p A} `{v: Vector n A} (Heq: n = m):
  v ~~ w ->
  coerce Heq in v ~~ w.
Proof.
  apply transitive_Vector_sim.
  apply Vector_coerce_sim_l.
Qed.

Lemma Vector_coerce_sim_r'
        {n m p} `{w: Vector p A} `{v: Vector n A} (Heq: n = m):
  w ~~ v ->
  w ~~ coerce Heq in v.
Proof.
  intro.
  vec_symmetry.
  eapply transitive_Vector_sim.
  apply Vector_coerce_sim_l.
  now vec_symmetry.
Qed.

Lemma Vector_coerce_fun_sim_l
        {n m A B} {f: Vector n A -> B}:
  forall (Heq: m = n),
    f ~!~ f ->
    (f ○ coerce_Vector_length Heq) ~!~ f.
Proof.
  unfold Vector_fun_sim.
  intros Heq. destruct Heq.
  split.
  - reflexivity.
  - intros v1 v2.
    rewrite coerce_Vector_eq_refl.
    apply H.
Qed.

Lemma Vector_coerce_fun_sim_r
        {n m A B} {f: Vector n A -> B}:
  forall (Heq: m = n),
    f ~!~ f ->
    f ~!~ (f ○ coerce_Vector_length Heq).
Proof.
  intros.
  vec_fun_symmetry.
  now apply Vector_coerce_fun_sim_l.
Qed.

Lemma Vector_coerce_fun_sim_l'
        {n m p A B}
        {f: Vector n A -> B} {g: Vector m A -> B}:
  forall (Heq: p = n),
    f ~!~ g ->
    (f ○ coerce_Vector_length Heq) ~!~ g.
Proof.
  unfold Vector_fun_sim.
  intros Heq1 [Heq2 Hfsim].
  split.
  - congruence.
  - intros v1 v2 Hsim.
    apply Hfsim.
    destruct Heq1.
    now rewrite coerce_Vector_eq_refl.
Qed.

Lemma Vector_coerce_fun_sim_r'
        {n m p A B}
        {f: Vector n A -> B} {g: Vector m A -> B}:
  forall (Heq: p = n),
    g ~!~ f ->
    g ~!~ (f ○ coerce_Vector_length Heq).
Proof.
  intros.
  vec_fun_symmetry.
  apply Vector_coerce_fun_sim_l'.
  now vec_fun_symmetry.
Qed.

(** ** Notions of equality assuming proof-irrelevance axiom *)
(******************************************************************************)
Lemma Vector_eq_list_eq:
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

(** Proof irrelevance implies similarity entails equality *)
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
  erewrite Vector_eq_list_eq in H.
  eassumption.
Defined.

Lemma Vector_sim_eq {n A} (v1 v2: Vector n A):
  v1 ~~ v2 -> v1 = v2.
Proof.
  apply Vector_eq.
Qed.

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

(** *** Projecting the smart constructors *)
(******************************************************************************)
Lemma proj_vnil: forall `(v: Vector 0 A),
    proj1_sig v = nil.
Proof.
  intros.
  destruct v as [v vlen].
  cbn.
  now apply List.length_zero_iff_nil.
Qed.

Lemma proj_vcons: forall (n: nat) `(a: A) (v: Vector n A),
    proj1_sig (vcons n a v) = cons a (proj1_sig v).
Proof.
  intros.
  destruct v as [vlist vlen].
  destruct vlen.
  reflexivity.
Qed.

Lemma vcons_sim
        {n m:nat} `{a:A}
        `{v1: Vector n A}
        `{v2: Vector m A}:
        v1 ~~ v2 ->
      vcons n a v1 ~~ vcons m a v2.
Proof.
  intros.
  unfold Vector_sim in *.
  do 2 rewrite proj_vcons.
  now rewrite H.
Qed.

(*
Instance vcons_resp:
  forall a n m, n = m ->
           vcons n a ~!~ vcons m a.
*)

(* This is better for rewriting *)
Lemma vcons_sim'
        {n:nat} `{a:A}
        `{v1: Vector n A}
        `{v2: Vector n A}:
        v1 ~~ v2 ->
      vcons n a v1 = vcons n a v2.
Proof.
  intros.
  fequal.
  now apply Vector_eq.
Qed.

Definition vcons_resp:
  forall `(a:A) n,
    Vector_fun_indep (vcons n a).
Proof.
  intros.
  unfold Vector_fun_indep; split.
  - reflexivity.
  - intros. auto using vcons_sim'.
Qed.

(** ** Inversion/un-consing non-empty vectors *)
(******************************************************************************)
Section inversion.

  Section heads_tails.

    Context {A: Type} {n: nat}.

    Implicit Type (v: Vector (S n) A).

    (* Un-nil-ing *)
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

    Lemma Vector_uncons_exists:
      forall v, exists (a: A) (v': Vector n A),
        v = vcons n a v'.
    Proof.
      intros.
      destruct v as [vlist vlen].
      specialize (list_uncons_exists _ _ _ vlen).
      intros [vhd [vtl v_eq]].
      subst.
      exists vhd.
      exists (exist (fun l => length l = n) vtl (S_uncons vlen)).
      cbn.
      fequal.
      cbn in *.
      apply proof_irrelevance.
    Qed.

    Lemma Vector_uncons_inform:
      forall v, {p: A * Vector n A | v = vcons n (fst p) (snd p)}.
    Proof.
      intros.
      destruct v as [vlist vlen].
      destruct (list_uncons_sigma2 vlist vlen) as [[vhd vtl] veq].
      subst.
      cbn in vlen.
      exists (vhd, (exist (fun l => length l = n)) vtl (S_uncons vlen)).
      cbn.
      fequal.
      apply proof_irrelevance.
    Defined.

    Definition Vector_uncons {n A} (v: Vector (S n) A):
      A * Vector n A :=
      let (vlist, vlen) := v in
      match vlist return (length vlist = S n -> A * Vector n A) with
      | nil => zero_not_S
      | cons a rest => fun vlen => (a, exist _ rest (S_uncons vlen))
      end vlen.

    Lemma Vector_uncons_inform1 (v: Vector (S n) A):
      Vector_uncons v = proj1_sig (Vector_uncons_inform v).
    Proof.
      destruct v as [vlist vlen].
      destruct vlist.
      - inversion vlen.
      - cbn. reflexivity.
    Qed.

    Definition Vector_hd:
      Vector (S n) A -> A :=
      fst ∘ Vector_uncons.

    Definition Vector_tl:
      Vector (S n) A -> Vector n A :=
      snd ∘ Vector_uncons.

    Lemma Vector_list_hd (v: Vector (S n) A):
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

    Lemma Vector_hd_vcons {a} {v: Vector n A}:
      Vector_hd (vcons n a v) = a.
    Proof.
      destruct v.
      reflexivity.
    Qed.

    Lemma Vector_tl_vcons {a} {v: Vector n A}:
      Vector_tl (vcons n a v) = v.
    Proof.
      destruct v.
      cbn.
      fequal.
      apply proof_irrelevance.
    Qed.

  End heads_tails.

  Definition vunone {A}: Vector 1 A -> A :=
    @Vector_hd A 0.

  Lemma Vector_hd_sim {n m A}
                      {v1: Vector (S n) A}
                      {v2: Vector (S m) A}:
    v1 ~~ v2 ->
    Vector_hd v1 = Vector_hd v2.
  Proof.
    intro Hsim.
    rewrite Vector_list_hd.
    rewrite Vector_list_hd.
    unfold Vector_sim in Hsim.
    rewrite (list_hd_rw Hsim).
    apply list_hd_proof_irrelevance.
  Qed.

  Lemma Vector_tl_sim {n m A}
                      {v1: Vector (S n) A}
                      {v2: Vector (S m) A}:
    v1 ~~ v2 ->
    Vector_tl v1 ~~ Vector_tl v2.
  Proof.
    intro Hsim.
    unfold Vector_sim in *.
    rewrite proj_Vector_tl.
    rewrite proj_Vector_tl.
    rewrite (list_tl_rw Hsim).
    apply list_tl_proof_irrelevance.
  Qed.


  Corollary Vector_hd_coerce_eq
              {n m A}
              {v: Vector (S n) A}
              {Heq: S n = S m}:
    Vector_hd v = Vector_hd (coerce_Vector_length Heq v).
  Proof.
    apply Vector_hd_sim.
    apply Vector_coerce_sim_r.
  Qed.

  Corollary Vector_tl_coerce_sim
              {n m A}
              {v: Vector (S n) A}
              {Heq: S n = S m}:
    Vector_tl v ~~ Vector_tl (coerce_Vector_length Heq v).
  Proof.
    apply Vector_tl_sim.
    apply Vector_coerce_sim_r.
  Qed.

End inversion.

Ltac vector_sim :=
  repeat (match goal with
          | |- ?v ~~ coerce ?Heq in ?v =>
              apply Vector_coerce_sim_r
          | |- coerce ?Heq in ?v ~~ ?v =>
              apply Vector_coerce_sim_l
          | |- ?v ~~ coerce ?Heq in ?w =>
              apply Vector_coerce_sim_r'
          | |- coerce ?Heq in ?w ~~ ?v =>
              apply Vector_coerce_sim_l'
          | |- Vector_tl ?v ~~ Vector_tl ?w =>
              apply Vector_tl_sim
          | |- ?v ~!~ precoerce ?Heq in ?v =>
              apply Vector_coerce_fun_sim_r
          | |- precoerce ?Heq in ?v ~~ ?v =>
              apply Vector_coerce_fun_sim_l
          | |- ?v ~~ precoerce ?Heq in ?w =>
              apply Vector_coerce_fun_sim_r'
          | |- precoerce ?Heq in ?w ~~ ?v =>
              apply Vector_coerce_fun_sim_l'
          | |- _ => reflexivity
          | |- _ => assumption
          end).

(** ** Induction *)
(******************************************************************************)
Lemma Vector_induction_core:
  forall (A: Type)
    (P: forall m, Vector m A -> Prop)
    (IHnil: P 0 vnil)
    (IHcons:
      forall a m (v: Vector m A), P m v -> P (S m) (vcons m a v)),
  forall m (v: Vector m A), P m v.
Proof.
  intros.
  induction m.
  + rewrite Vector_nil_eq. assumption.
  + destruct (Vector_uncons_inform v) as [[vhd vtl] veq].
    subst. auto.
Qed.

Lemma Vector_induction:
  forall (m: nat) (A: Type) (P: forall m, Vector m A -> Prop)
    (IHnil: P 0 vnil)
    (IHcons:
      forall a m (v: Vector m A), P m v -> P (S m) (vcons m a v)),
  forall (v: Vector m A), P m v.
Proof.
  intros; apply Vector_induction_core; auto.
Qed.

(** *** Simultaneous induction on vectors of similar length *)
(******************************************************************************)
Lemma Vector_induction2_core:
  forall (A: Type)
    (P: forall m, Vector m A -> Vector m A -> Prop)
    (IHnil: P 0 vnil vnil)
    (IHcons:
      forall m (a1 a2: A) (v1 v2: Vector m A),
        P m v1 v2 ->
        P (S m) (vcons m a1 v1) (vcons m a2 v2)),
  forall (m : nat) (v1 v2: Vector m A), P m v1 v2.
Proof.
  intros.
  induction m.
  + rewrite Vector_nil_eq.
    rewrite (Vector_nil_eq v1).
    assumption.
  + destruct (Vector_uncons_inform v1) as
      [[v1hd v1tl] v1eq].
    destruct (Vector_uncons_inform v2) as
      [[v2hd v2tl] v2eq].
    subst; cbn; auto.
Qed.

Lemma Vector_induction2:
  forall (A: Type) (m n : nat)
    (P: forall m n, Vector m A -> Vector n A -> Prop)
    (IHnil: P 0 0 vnil vnil)
    (IHcons:
      forall m n (a1 a2: A) (v1: Vector m A) (v2: Vector n A),
        P m n v1 v2 ->
        P (S m) (S n) (vcons m a1 v1) (vcons n a2 v2)),
  forall (v1: Vector m A) (v2: Vector n A),
    n = m -> P m n v1 v2.
Proof.
  intros.
  subst.
  apply (Vector_induction2_core A (fun m => P m m)).
  assumption.
  auto.
Qed.

(** ** Misc *)
(******************************************************************************)
Fixpoint Vector_repeat
           (n: nat) {A: Type} (a : A): Vector n A :=
  match n with
  | 0 => vnil
  | S m => vcons m a (Vector_repeat m a)
  end.

Definition Vector_tt (n: nat): Vector n unit :=
  Vector_repeat n tt.

(** ** to_list *)
(******************************************************************************)
Section sec.

  Context (A: Type).

  Definition to_list {n:nat}: Vector n A -> list A :=
    @proj1_sig (list A) _.

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

(** * Functor instance *)
(******************************************************************************)
Definition map_Vector
             (n : nat) {A B : Type} (f : A -> B)
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

(** ** Traversable instance *)
(******************************************************************************)
Definition traverse_Vector_core
             {G} `{Map G} `{Pure G} `{Mult G}
             {A B : Type} (f : A -> G B)
             (vlist : list A) `(vlen : length vlist = n) : G (Vector n B) :=
      (fix go (vl : list A) n : length vl = n -> G (Vector n B) :=
         match vl
               return length vl = n -> G (Vector n B)
         with
         | nil =>
             fun vlen =>
               pure (F := G) (exist _ nil vlen)
         | cons a rest =>
             fun vlen =>
               match n return
                     length (a :: rest) = n -> G (Vector n B)
               with
               | O => fun vlen' => zero_not_S (eq_sym vlen')
               | S m =>
                   fun vlen' =>
                     pure (@vcons m B) <⋆> f a <⋆> go rest m (S_uncons vlen')
               end vlen
         end) vlist n vlen.

Definition traverse_Vector
             (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
             {A B : Type} (f : A -> G B)
             (v : Vector n A) : G (Vector n B) :=
  match v with
  | exist _ vlist vlen =>
      traverse_Vector_core f vlist vlen
  end.

#[export] Instance Traverse_Vector {n}: Traverse (Vector n)
  := traverse_Vector n.

Lemma traverse_Vector_rw
  (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          {A B : Type} (f : A -> G B)
          (a: A) (l: list A) (pf: length (a :: l) = n):
    traverse f (exist (fun l => length l = n) (a :: l) pf) =
      traverse f (exist (fun l => length l = n) (a :: l) pf).
Proof.
  cbn.
Abort.

 Lemma traverse_Vector_contents:
   forall (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
     {A B : Type} (f : A -> G B)
     `{! Applicative G}
     (v : Vector n A),
     map (F := G)
             (@proj1_sig (list B) (fun l => length l = n))
             (traverse (T := Vector n) f v) =
       traverse f (proj1_sig v).
 Proof.
   intros.
   destruct v as [vlist vlen].
   generalize dependent n.
   induction vlist; intros n vlen.
   - cbn. rewrite app_pure_natural. reflexivity.
   - cbn. destruct n.
     + false.
     + cbn in IHvlist.
       rewrite <- (IHvlist n (S_uncons vlen)).
       rewrite map_ap.
       rewrite map_ap.
       rewrite app_pure_natural.
       rewrite <- ap_map.
       rewrite map_ap.
       rewrite app_pure_natural.
       fequal.
       fequal.
       fequal.
       ext b vb.
       unfold compose, precompose.
       rewrite proj_vcons.
       reflexivity.
 Qed.

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
      pure (vcons n) <⋆> f a <⋆>
        traverse f (exist (fun l => length l = n) l (S_uncons p)).
Proof.
  intros.
  reflexivity.
Qed.

Lemma traverse_Vector_vcons:
  forall (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {A B : Type} (f : A -> G B)
    (v : Vector n A) (a : A),
    traverse f (vcons n a v) =
      pure (vcons n) <⋆> f a <⋆> traverse f v.
Proof.
  intros.
  destruct v.
  unfold vcons.
  rewrite traverse_Vector_rw2.
  fequal.
  fequal.
  fequal.
  apply proof_irrelevance.
Qed.

Lemma traverse_Vector_coerce:
  forall (n m : nat) `{Applicative G}
    {A B : Type} (f : A -> G B)
    (Heq: n = m) (v : Vector n A),
    traverse f v = map (F := G) (fun v => coerce (eq_sym Heq) in v)
                       (traverse f (coerce Heq in v) : G (Vector m B)).
Proof.
  intros.
  subst.
  replace (fun v0 : Vector m B => coerce eq_sym eq_refl in v0)
    with (@id (Vector m B)).
  rewrite (fun_map_id).
  replace (coerce eq_refl in v) with v.
  reflexivity.
  - destruct v.
    destruct e.
    reflexivity.
  - ext w.
    destruct w.
    destruct e.
    reflexivity.
Qed.


Lemma traverse_Vector_indep:
  forall (n : nat) `{Applicative G}
    {A B : Type} (f : A -> G B),
    @Vector_fun_indep n A (G (Vector n B)) (traverse f).
Proof.
  intros.
  unfold Vector_fun_indep.
  split.
  - reflexivity.
  - intros.
    pose (Ind:= Vector_induction2_core A
                                       (fun x v1 v2 =>
                                          v1 ~~ v2 ->
                                     traverse (G := G) (T := Vector x) f v1 =
                                       traverse (G := G) (T := Vector x) f v2)).
    apply Ind.
    + reflexivity.
    + clear.
      intros n a1 a2 v1 v2 Hsim Heq.
      assert (Hsim_: a1 = a2 /\ v1 ~~ v2).
      { unfold Vector_sim in Heq.
        do 2 rewrite proj_vcons in Heq.
        inversion Heq.
        auto. }
      destruct Hsim_ as [Ha Hcons].
      inversion Ha.
      do 2 rewrite traverse_Vector_vcons.
      rewrite (Hsim Hcons).
      reflexivity.
    + assumption.
Qed.

(*
Lemma traverse_Vector_rw2:
  forall (n : nat) (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {A B : Type} (f : A -> G B)
    (a : A) (l: list A)
    (p : length (a :: l) = S n),
    traverse f (exist _ (a :: l) p) =
      pure (Basics.flip (vcons n)) <⋆>
        traverse f (exist (fun l => length l = n) l (S_uncons p)) <⋆> f a.
Proof.
  intros.
  cbn.
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
 *)

Lemma traverse_Vector_id `{v : Vector n A}:
  traverse (G := fun A => A) id v = v.
Proof.
  induction v using Vector_induction.
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
  induction v using Vector_induction.
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
    unfold compose at 5.
    rewrite <- ap_map.
    rewrite (app_pure_natural (G := G1)).
    { repeat fequal.
      ext w z.
      unfold compose, precompose.
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
  induction v using Vector_induction.
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

(** ** Batch *)
(******************************************************************************)

(** Extract the contents of <<Batch>> as a vector *)
Fixpoint Batch_contents `(b: Batch A B C):
  Vector (length_Batch b) A :=
  match b with
  | Done c => vnil
  | Step b a => vcons (length_Batch b) a (Batch_contents b)
  end.

(** Obtain the build function of <<Batch>>. Note that
 <<Batch_make b v>> in general has type <<C>>, not another <<Batch>>.
 That is, this is not <<make>> in the sense of <<put>> *)
Fixpoint Batch_make `(b: Batch A B C):
  Vector (length_Batch b) B -> C :=
  match b return Vector (length_Batch b) B -> C with
  | Done c => fun v => c
  | Step b a => fun v =>
        Batch_make b (Vector_tl v) (Vector_hd v)
  end.

(** This is <<make>> in the sense of <<put>>. *)
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

  (** ** Lemmas for <<Batch_make>> *)
  (******************************************************************************)
  Section Batch_make.

    (*
    Lemma Batch_length_ind:
      forall (A1 A2 B : Type)
        (P : forall C : Type,
            Batch A1 B C ->
            Batch A2 B C ->
            Prop)
        (IHdone: forall (C : Type) (c : C), P C (Done c) (Done c))
        (IHstep: forall (C : Type)
                   (b1 : Batch A1 B (B -> C))
                   (b2 : Batch A2 B (B -> C)),
            P (B -> C) b1 b2 ->
            forall (a1 : A1) (a2: A2)
              (Hlen: length_Batch (Step b1 a1) = length_Batch (Step b2 a2)),
              P C (Step b1 a1) (Step b2 a2)),
      forall (C : Type) (b1: Batch A1 B C) (b2: Batch A2 B C)
        (Hlen: length_Batch b1 = length_Batch b2), P C b1 b2.
    Proof.
      intros.
      induction b1.
      - induction b2.
        +
        + false.
      - induction b2.
        + false.
        + apply IHstep.
          * apply IHb1.
            now inversion Hlen.
          * apply Hlen.
    Qed.
    *)

    Lemma Batch_shape_ind:
      forall (A1 A2 B : Type)
        (P : forall C : Type,
            Batch A1 B C ->
            Batch A2 B C ->
            Prop)
        (IHdone: forall (C : Type) (c : C), P C (Done c) (Done c))
        (IHstep: forall (C : Type)
                   (b1 : Batch A1 B (B -> C))
                   (b2 : Batch A2 B (B -> C)),
            P (B -> C) b1 b2 ->
            forall (a1 : A1) (a2: A2)
              (Hshape: shape (Step b1 a1) = shape (Step b2 a2)),
              P C (Step b1 a1) (Step b2 a2)),
      forall (C : Type) (b1: Batch A1 B C) (b2: Batch A2 B C)
        (Hshape: shape b1 = shape b2), P C b1 b2.
    Proof.
      intros.
      induction b1.
      - induction b2.
        + now inversion Hshape.
        + false.
      - induction b2.
        + false.
        + apply IHstep.
          * apply IHb1.
            now inversion Hshape.
          * apply Hshape.
    Qed.

    (* Equivalence of shape is equivalent to
       saying the <<Batch>> values have the same length
       and the same make function *)
    Lemma length_Batch_shape:
      forall `(b1: Batch A1 B C)
        `(b2: Batch A2 B C),
        shape b1 = shape b2 ->
        length_Batch b1 = length_Batch b2.
    Proof.
      introv Hshape.
      induction b1.
      - destruct b2.
        + now inversion Hshape.
        + false.
      - destruct b2.
        + false.
        + cbn. fequal.
          apply IHb1.
          now inversion Hshape.
    Qed.

    Lemma Batch_make_shape:
      forall `(b1: Batch A B C) `(b2: Batch A' B C),
        shape b1 = shape b2 ->
        Batch_make b1 ~!~ Batch_make b2.
    Proof.
      intros.
      apply (@Batch_shape_ind
               A A' B
               (fun C b1 b2 => Batch_make b1 ~!~ Batch_make b2)).
      - clear. intros.
        split; auto.
      - clear. introv Hsim; introv Hshape.
        do 2 rewrite Batch_make_rw2.
        unfold Vector_fun_sim.
        split.
        + apply length_Batch_shape. assumption.
        + introv Hsim'.
          rewrite (Vector_hd_sim Hsim').
          enough (Batch_make b1 (Vector_tl v1) =
                    Batch_make b2 (Vector_tl v2)).
          { rewrite H. reflexivity. }
          apply Vector_fun_sim_eq.
          assumption.
          apply Vector_tl_sim.
          assumption.
      - assumption.
    Qed.

    (* This is true, but to prove it we need more lemmas *)
    Lemma Batch_make_shape_rev:
      forall `(b1: Batch A B C) `(b2: Batch A' B C),
        Batch_make b1 ~!~ Batch_make b2 ->
          shape b1 = shape b2.
    Proof.
    Abort.

    Lemma Batch_replace_shape {A'}:
      forall `(b1: Batch A1 B C) `(b2: Batch A2 B C),
        shape b1 = shape b2 ->
        Batch_replace_contents (A' := A') b1
          ~!~ Batch_replace_contents (A' := A') b2.
    Proof.
      intros.
      apply (@Batch_shape_ind
               _ _ _
               (fun C b1 b2 => Batch_replace_contents b1 ~!~ Batch_replace_contents b2)). 3:auto. all:clear.
      - intros. split. reflexivity. reflexivity.
      - intros. split.
        + auto using length_Batch_shape.
        + introv Hsim.
          cbn.
          fequal.
          apply H.
          now apply Vector_tl_sim.
          now apply Vector_hd_sim.
    Qed.

    Lemma shape_spec:
      forall `(b: Batch A B C),
        shape b =
          Batch_replace_contents b (Vector_tt (length_Batch b)).
    Proof.
      intros.
      induction b.
      - reflexivity.
      - cbn.
        rewrite Vector_tl_vcons.
        rewrite Vector_hd_vcons.
        fequal.
        apply IHb.
    Qed.

    Lemma Batch_make_sim1
            `(b: Batch A B C)
            `{v1: Vector (length_Batch b) B}
            `{v2: Vector (length_Batch b) B}
            (Hsim: v1 ~~ v2):
      Batch_make b v1 = Batch_make b v2.
    Proof.
      induction b.
      - reflexivity.
      - rewrite Batch_make_rw2.
        rewrite (IHb _ _ (Vector_tl_sim Hsim)).
        rewrite (Vector_hd_sim Hsim).
        reflexivity.
    Qed.

    (* This sort of lemma is very useful when the complexity of expression
     <<v1>> and <<v2>> obstructs tactics like <<rewrite>> *)
    Lemma Batch_make_sim2
            `(b1: Batch A B C)
            `(b2: Batch A B C)
            `{v1: Vector (length_Batch b1) B}
            `{v2: Vector (length_Batch b2) B}
            (Heq: b1 = b2)
            (Hsim: Vector_sim v1 v2):
      Batch_make b1 v1 = Batch_make b2 v2.
    Proof.
      now (subst; apply Batch_make_sim1).
    Qed.

    Lemma Batch_make_sim3
            `(b1: Batch A1 B C)
            `(b2: Batch A2 B C)
            `{v1: Vector (length_Batch b1) B}
            `{v2: Vector (length_Batch b2) B}
            (Heq: shape b1 = shape b2)
            (Hsim: v1 ~~ v2):
      Batch_make b1 v1 = Batch_make b2 v2.
    Proof.
      apply Vector_fun_sim_eq.
      apply Batch_make_shape.
      auto. assumption.
    Qed.

    Lemma Batch_make_coerce
            `(b: Batch A B C)
            `{v1: Vector (length_Batch b) B}
            `{v2: Vector n B}
            (Heq: n = length_Batch b):
                v1 ~~ v2 ->
      Batch_make b v1 = Batch_make b (coerce Heq in v2).
    Proof.
      subst.
      intros.
      apply Batch_make_sim1.
      rewrite coerce_Vector_eq_refl.
      assumption.
    Qed.

    (** Rewrite the <<Batch>> argument to an equal one by
      coercing the length proof in the vector. *)
    Lemma Batch_make_rw
            `(b1: Batch A B C)
            `(b2: Batch A B C)
            `{v1: Vector (length_Batch b1) B}
            (Heq: b1 = b2):
      Batch_make b1 v1 =
        Batch_make b2 (rew [fun b => Vector (length_Batch b) B]
                           Heq in v1).
    Proof.
      now (subst; apply Batch_make_sim1).
    Qed.

    Lemma Batch_make_compose `(b: Batch A B C) `(f: C -> D)
                             `(Hsim: v1 ~~ v2):
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
        rewrite <- (Vector_hd_sim Hsim).
        change_left ((f ∘ Batch_make rest (Vector_tl v1)) (Vector_hd v1)).
        specialize (IHrest _ (compose f)).
        rewrite (IHrest (Vector_tl v1) (Vector_tl v2) (Vector_tl_sim Hsim)).
        reflexivity.
    Qed.

    Lemma Batch_make_compose_rw1 `(b: Batch A B C) `(f: C -> D) v:
      f (Batch_make b v) =
        Batch_make (map (F := Batch A B) f b)
                   (coerce_Vector_length (batch_length_map _ _) v).
    Proof.
      now rewrite (
              Batch_make_compose
                b f
                (v1 := v)
                (v2 :=coerce_Vector_length (batch_length_map _ _) v)
            ) by vector_sim.
    Qed.

    Lemma Batch_make_compose_rw2 `(b: Batch A B C) `(f: C -> D) v:
      Batch_make (map (F := Batch A B) f b) v =
        f (Batch_make b (coerce_Vector_length (eq_sym (batch_length_map _ _)) v)).
    Proof.
      rewrite (Batch_make_compose_rw1 b f).
      apply Batch_make_sim1.
      vector_sim.
    Qed.

    Lemma Batch_replace_sim1
            `(b: Batch A B C)
            `{v1: Vector (length_Batch b) A'}
            `{v2: Vector (length_Batch b) A'}
            (Hsim: v1 ~~ v2):
      Batch_replace_contents b v1 = Batch_replace_contents b v2.
    Proof.
      induction b.
      - reflexivity.
      - do 2 rewrite Batch_replace_rw2.
        rewrite (IHb _ _ (Vector_tl_sim Hsim)).
        rewrite (Vector_hd_sim Hsim).
        reflexivity.
    Qed.

    Lemma Batch_replace_sim2
            `(b1: Batch A B C)
            `(b2: Batch A B C)
            `{v1: Vector (length_Batch b1) A'}
            `{v2: Vector (length_Batch b2) A'}
            (Heq: b1 = b2)
            (Hsim: Vector_sim v1 v2):
      Batch_replace_contents b1 v1 = Batch_replace_contents b2 v2.
    Proof.
      now (subst; apply Batch_replace_sim1).
    Qed.

    Lemma Batch_replace_sim3
            `(b1: Batch A1 B C)
            `(b2: Batch A2 B C)
            `{v1: Vector (length_Batch b1) A'}
            `{v2: Vector (length_Batch b2) A'}
            (Heq: shape b1 = shape b2)
            (Hsim: v1 ~~ v2):
      Batch_replace_contents b1 v1 = Batch_replace_contents b2 v2.
    Proof.
      apply Vector_fun_sim_eq;
        auto using Batch_replace_shape.
    Qed.

  End Batch_make.

  Lemma length_replace_contents:
    forall {A B C: Type} (b: Batch A B C) `(v: Vector _ A'),
      length_Batch b = length_Batch (Batch_replace_contents b v).
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn. fequal.
      apply (IHb (Vector_tl v)).
  Qed.

  Lemma Batch_shape_replace_contents:
    forall {A A' B C: Type} (b: Batch A B C) `(v: Vector _ A'),
      shape b = shape (Batch_replace_contents b v).
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn. fequal.
      apply (IHb (Vector_tl v)).
  Qed.

  Section lens_laws.

    Context {A A' B C: Type}.

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

    Lemma Batch_get_put:
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

    Lemma Batch_put_get:
      forall (b: Batch A B C) (v: Vector _ A'),
        Batch_contents (Batch_replace_contents b v) =
          coerce length_replace_contents b v in v.
    Proof.
      intros.
      generalize (length_replace_contents b v).
      intros Heq.
      induction b.
      - cbn. symmetry.
        apply Vector_nil_eq.
      - cbn in *.
        rewrite Vector_surjective_pairing2.
        rewrite <- (Vector_hd_coerce_eq (Heq := Heq) (v := v)).
        specialize (IHb (Vector_tl v) (S_uncons Heq)).
        fold (@length_Batch A B).
        (* ^^ I have no idea why this got expanded but it blocks rewriting *)
        rewrite IHb.
        fequal.
        apply Vector_sim_eq.
        vector_sim.
    Qed.

    Lemma Batch_put_make:
      forall (b: Batch A B C),
        Batch_replace_contents b =
          precoerce (length_cojoin_Batch b)
                   in Batch_make (cojoin_Batch b (B := A')).
    Proof.
      intros b. ext v.
      generalize (length_cojoin_Batch (A' := A') b).
      intros Heq.
      induction b.
      - reflexivity.
      - rewrite Batch_replace_rw2.
        cbn.
        rewrite Batch_make_compose_rw2.
        rewrite <- (Vector_hd_coerce_eq (Heq := Heq)).
        fequal.
        specialize (IHb (Vector_tl v) (length_cojoin_Batch b)).
        rewrite IHb.
        apply Batch_make_sim1.
        vector_sim.
    Qed.

    Lemma Batch_make_replace_contents:
      forall (b: Batch A B C) (v: Vector (length_Batch b) A'),
        Batch_make (Batch_replace_contents b v) =
          precoerce (eq_sym (length_replace_contents b v))
        in (Batch_make (B := B) b).
    Proof.
      intros.
      ext v'.
      generalize (eq_sym (length_replace_contents b v)).
      intro e.
      induction b.
      - reflexivity.
      - cbn.
        specialize (IHb (Vector_tl v) (Vector_tl v')).
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
        apply Vector_hd_coerce_eq.
    Qed.

  End lens_laws.

  Section length_shape.

    Context {A A' B C: Type}.


    Lemma Batch_make_shape_rev:
      forall `(b1: Batch A B C) `(b2: Batch A' B C),
        Batch_make b1 ~!~ Batch_make b2 ->
          shape b1 = shape b2.
    Proof.
      intros.
      unfold Vector_fun_sim in *.
      destruct H as [Hlen Hsim].
      induction b1.
      - destruct b2.
        * cbn in *.
          specialize (Hsim vnil vnil ltac:(reflexivity)).
          now inversion Hsim.
        * false.
      - destruct b2.
        + false.
        + cbn. fequal. apply IHb1.
          * now inversion Hlen.
          * intros v1 v2 Vsim.
            ext b.
            assert (Vsim': vcons _ b v1 ~~ vcons _ b v2).
            now apply vcons_sim.
            specialize (Hsim _ _ Vsim').
            cbn in Hsim.
            do 2 rewrite Vector_tl_vcons in Hsim.
            do 2 rewrite Vector_hd_vcons in Hsim.
            assumption.
    Qed.

    Corollary Batch_make_shape_iff:
      forall `(b1: Batch A B C) `(b2: Batch A' B C),
        shape b1 = shape b2 <->
          Batch_make b1 ~!~ Batch_make b2.
    Proof.
      intros.
      split; auto using Batch_make_shape,
        Batch_make_shape_rev.
    Qed.

    Lemma Batch_make_replace_sim:
      forall `(b1: Batch A B C) `(b2: Batch A' B C) {A''},
      Batch_make b1 ~!~ Batch_make b2 ->
      Batch_replace_contents (A' := A'') b1 ~!~ Batch_replace_contents b2.
    Proof.
      intros.
      rewrite <- Batch_make_shape_iff in H.
      apply (Batch_shape_ind
               A A' B
               (fun C b1 b2 =>
                  @Batch_replace_contents
                    A B C b1 A''
                    ~!~ @Batch_replace_contents
                    A' B C b2 A'')); try assumption; clear.
      - intros. split.
        + reflexivity.
        + intros v1 v2 Hsim.
          reflexivity.
      - intros. split.
        + auto using length_Batch_shape.
        + intros. cbn.
          fequal.
          * destruct H as [Hlen Hsim].
            apply Hsim.
            now apply Vector_tl_sim.
          * now apply Vector_hd_sim.
    Qed.

  End length_shape.

  Section spec.

    Lemma Batch_eq_iff:
      forall `(b1: Batch A B C) `(b2: Batch A B C),
        b1 = b2 <->
          Batch_make b1 ~!~ Batch_make b2 /\
            Batch_contents b1 ~~ Batch_contents b2.
    Proof.
      intros. split.
      - intros; subst. split.
        2: reflexivity.
        unfold Vector_fun_sim.
        split; try reflexivity.
        introv Hsim.
        auto using Batch_make_sim1.
      - intros [Hmake Hcontents].
        rewrite <- (Batch_get_put b1).
        rewrite <- (Batch_get_put b2).
        apply Batch_replace_sim3.
        now apply Batch_make_shape_rev.
        assumption.
    Qed.

    From Tealeaves.Functors Require Import Backwards.

    Lemma forwards_ap `{Applicative G}:
      forall {A B: Type} (f: (Backwards G) (A -> B)) (a : (Backwards G) A),
        forwards (f <⋆> a) =
          ap G (map (F := G) (fun a => evalAt (A := A) a (B := B))
                    (forwards a)) (forwards f).
    Proof.
      intros.
      cbn.
      unfold ap.
      rewrite (app_mult_natural_l G).
      compose near (forwards a ⊗ forwards f).
      do 2 rewrite (fun_map_map).
      fequal.
      now ext [p q].
    Qed.

    Lemma runBatch_repr1 `{Applicative G}:
      forall `(b: Batch A B C) (f: A -> G B),
        map (F := G) (Batch_make b)
            (traverse (T := Vector (length_Batch b)) f (Batch_contents b)) =
          forwards (runBatch (Backwards G) (mkBackwards ∘ f) _ b).
    Proof.
      intros.
      induction b.
      - cbn.
        rewrite app_pure_natural.
        reflexivity.
      - rewrite Batch_contents_rw2.
        unfold length_Batch at 2. (* hidden *)
        rewrite traverse_Vector_vcons.
        rewrite runBatch_rw2.
        rewrite forwards_ap.
        rewrite map_ap.
        rewrite map_ap.
        rewrite app_pure_natural.
        rewrite <- IHb.
        rewrite map_to_ap.
        rewrite <- ap_map.
        rewrite map_ap.
        rewrite app_pure_natural.
        fequal.
        fequal.
        fequal.
        ext b' v'.
        unfold compose, precompose, evalAt.
        cbn.
        rewrite Vector_tl_vcons.
        rewrite Vector_hd_vcons.
        reflexivity.
    Qed.

    Lemma runBatch_repr2 `{Applicative G}:
      forall `(b: Batch A B C) (f: A -> G B),
        runBatch G f _ b =
          map (F := G) (Batch_make b)
              (forwards (traverse (G := (Backwards G))
                                  (T := Vector (length_Batch b))
                                  (mkBackwards ∘ f)
                                  (Batch_contents b))).
    Proof.
      intros.
      symmetry.
      change_left
        (forwards
           (map (F := Backwards G) (Batch_make b)
                (traverse (G := Backwards G) (mkBackwards ∘ f) (Batch_contents b)))).
      rewrite runBatch_repr1.
      rewrite runBatch_spec.
      rewrite runBatch_spec.
      change_left
        (map (F := G) extract_Batch
             (forwards (
                  forwards (
                      traverse (G := Backwards (Backwards G))
                               (mkBackwards ∘ (mkBackwards ∘ f)) b)))).
      rewrite traverse_double_backwards.
      reflexivity.
    Qed.

  End spec.

End Batch.
