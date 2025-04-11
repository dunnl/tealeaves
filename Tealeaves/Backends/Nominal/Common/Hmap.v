From Tealeaves Require Export
  Functors.List_Telescoping_General
  Functors.List.

#[local] Open Scope list_scope.

Import List.ListNotations.
Import Monoid.Notations.
Import ContainerFunctor.Notations.

(** * The <<hmap>> Operation *)
(**********************************************************************)
(* Fold over a list of A's where each A has the prefix of the list so far *)
Fixpoint hmap {A B: Type}
  (f: list B * A -> B)
  (l: list A): list B :=
  match l with
  | nil => nil
  | cons a rest =>
      f ([], a) :: hmap (f ⦿ [f ([], a)]) rest
  end.

(** ** Rewriting Rules for <<hmap>> *)
(**********************************************************************)
Section rw.

  Context {A B: Type}.

  Section basic.

    Context (f: list B * A -> B).

    Lemma hmap_nil:
      hmap f nil = nil.
    Proof.
      reflexivity.
    Qed.

    Lemma hmap_cons {a l}:
      hmap f (a :: l) =
        f ([], a) :: hmap (f ⦿ [f ([], a)]) l.
    Proof.
      cbn.
      reflexivity.
    Qed.

    Lemma hmap_one {a}:
      hmap f ([a]) =
        [f ([], a)].
    Proof.
      cbn.
      reflexivity.
    Qed.

  End basic.

  Lemma hmap_app {l1 l2: list A}:
    forall (f: list B * A -> B),
      hmap f (l1 ++ l2) =
        hmap f l1 ++
          hmap (f ⦿ hmap f l1) l2.
  Proof.
    induction l1 as [|a l1 IHl1]; intros.
    - cbn. change (f ⦿ []) with (f ⦿ Ƶ).
      now rewrite preincr_zero.
    - rewrite <- List.app_comm_cons.
      rewrite hmap_cons.
      rewrite hmap_cons.
      rewrite IHl1.
      rewrite <- List.app_comm_cons.
      rewrite preincr_preincr.
      reflexivity.
  Qed.

  (* Tailored for use when the list is a nominal binding context decomposition *)
  Lemma hmap_decompose {l1 l2: list A} {a: A}:
    forall (f: list B * A -> B),
      hmap f (l1 ++ [a] ++ l2) =
        hmap f l1 ++
          [f (hmap f l1, a)] ++
          hmap (f ⦿ (hmap f l1 ++ [f (hmap f l1, a)])) l2.
  Proof.
    intros.
    rewrite hmap_app.
    rewrite hmap_app.
    rewrite hmap_one.
    rewrite preincr_preincr.
    unfold preincr, incr, compose.
    unfold_ops @Monoid_op_list.
    rewrite List.app_nil_r.
    reflexivity.
  Qed.

End rw.

(** ** Preservation of <<length>> *)
(**********************************************************************)
Lemma length_hmap {A B}: forall (l: list A) (f: list B * A -> B),
    length (hmap f l) = length l.
Proof.
  intros.
  generalize dependent f.
  induction l; intros.
  - reflexivity.
  - cbn. fequal.
    apply IHl.
Qed.

(** ** An Induction Rule for <<hmap>> *)
(**********************************************************************)
Section induction.

  Import Theory.TraversableFunctor.

  Context
    {A B: Type}
    {f: list B * A -> B}
    (P: B -> Prop).

  Section Forall.

    Context
      (Hbase: forall (a: A), P (f (nil, a)))
      (Hstep: forall (a: A) (h: list B),
      Forall P h -> P (f (h, a))).

    Lemma hmap_ind_Forall: forall (l: list A),
        Forall P (hmap f l).
    Proof.
      intro l.
      induction l as [| a rest IHrest] using List.rev_ind.
      - reflexivity.
      - rewrite hmap_app.
        rewrite TraversableFunctor.forall_iff.
        rewrite TraversableFunctor.forall_iff in IHrest.
        intro b.
        rewrite element_of_list_app.
        intros [Case1| Case2].
        + auto.
        + rewrite hmap_one in Case2.
          rewrite element_of_list_one in Case2.
          subst.
          apply Hstep.
          change (@nil B) with (Ƶ: list B).
          rewrite monoid_id_r.
          rewrite TraversableFunctor.forall_iff.
          assumption.
    Qed.

  End Forall.

  Section elementwise.

    Context
      (Hbase: forall (a: A), P (f (nil, a)))
      (Hstep: forall (a: A) (h: list B),
      (forall (b: B), b ∈ h -> P b) -> P (f (h, a))).

    Lemma hmap_ind: forall (l: list A),
      forall (b: B), b ∈ hmap f l -> P b.
    Proof.
      intro l.
      rewrite <- TraversableFunctor.forall_iff.
      apply hmap_ind_Forall.
      intros; apply Hstep.
      rewrite TraversableFunctor.forall_iff in H.
      assumption.
    Qed.

  End elementwise.

End induction.

(** * Relating History to the Prefix: <<hadapt>> *)
(**********************************************************************)
Definition hadapt {A B: Type} (f: list B * A -> B): list A * A -> B :=
  fun '(prefix, a) => f (hmap f prefix, a).

(** ** Rewriting Rules *)
(**********************************************************************)
Section relate_history_prefix.

  Context {A B: Type} (f: list B * A -> B).

  (** *** Spec for <<scons>> *)
  (**********************************************************************)
  Lemma hadapt_app_one_spec: forall (l: list A) (a: A),
      hmap f (l ++ [a]) =
        hmap f l ++ [hadapt f (l, a)].
  Proof.
    intros.
    rewrite hmap_app.
    fequal.
    rewrite hmap_one.
    unfold preincr, incr, compose.
    change (@nil B) with (Ƶ: list B) at 1.
    rewrite monoid_id_r.
    fequal.
  Qed.

  (** *** Spec for <<list>> Operations *)
  (**********************************************************************)
  Lemma hadapt_nil: forall (a: A),
    hadapt f (nil, a) = f (nil, a).
  Proof.
    reflexivity.
  Qed.

  Lemma hadapt_cons {a l x}:
    hadapt f (a :: l, x) =
      f (f ([], a) :: hmap (f ⦿ [f ([], a)]) l, x).
  Proof.
    reflexivity.
  Qed.

  Lemma hadapt_app {l1 l2 x}:
    hadapt f (l1 ++ l2, x) =
      f (hmap f l1 ++ hmap (f ⦿ hmap f l1) l2, x).
  Proof.
    cbn.
    rewrite hmap_app.
    reflexivity.
  Qed.

  Lemma hadapt_one {a x}:
    hadapt f ([a], x) =
      f ([f ([], a)], x).
  Proof.
    cbn.
    reflexivity.
  Qed.

End relate_history_prefix.

(** ** Rewriting Rules *)
(**********************************************************************)
Lemma hadapt_spec {A B: Type} (f: list B * A -> B):
  mapd_list_prefix (hadapt f) =
    hmap f.
Proof.
  ext l.
  generalize dependent f.
  induction l; intros.
  - cbn.
    reflexivity.
  - rewrite mapd_list_prefix_rw_cons.
    rewrite hmap_cons.
    rewrite hadapt_nil.
    rewrite <- IHl.
    fequal.
    fequal.
    ext [w a'].
    cbn.
    reflexivity.
Qed.

(** * Folding with context AND history *)
(**********************************************************************)
Fixpoint fold_with_ctx_history_rec {A B: Type}
  (f: list B * list A * A -> B)
  (hist: list B) (ctx: list A)

  (l: list A): list B :=
  match l with
  | nil => nil
  | cons a rest =>
      f (hist, ctx, a) ::
        fold_with_ctx_history_rec f (hist ++ [f (hist, ctx, a)]) (ctx ++ [a]) rest
  end.

Definition fold_with_ctx_history {A B: Type}
  (f: list B * list A * A -> B)
  (l: list A): list B :=
  fold_with_ctx_history_rec f [] [] l.

Section rw.

  Context {A B: Type}.

  Section basic.

    Context (f: list B * list A * A -> B).

    Lemma fold_with_ctx_history_nil_rec: forall hist ctx,
        fold_with_ctx_history_rec f hist ctx nil = nil.
    Proof.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_cons {a l}:
      fold_with_ctx_history f (a :: l) =
        f ([], [], a) :: fold_with_ctx_history_rec f [f ([], [], a)] [a] l.
    Proof.
      cbn.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_one_rec {hist ctx a}:
      fold_with_ctx_history_rec f hist ctx ([a]) =
        [f (hist, ctx, a)].
    Proof.
      cbn.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_nil:
      fold_with_ctx_history f nil = nil.
    Proof.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_cons_rec {hist ctx a l}:
      fold_with_ctx_history_rec f hist ctx (a :: l) =
        f (hist, ctx, a) :: fold_with_ctx_history_rec f (hist ++ [f (hist, ctx, a)]) (ctx ++ [a]) l.
    Proof.
      cbn.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_one {a}:
      fold_with_ctx_history f ([a]) =
        [f ([], [], a)].
    Proof.
      cbn.
      reflexivity.
    Qed.

  End basic.

  Lemma fold_with_ctx_history_app_rec {l1 l2: list A}:
    forall (f: list B * list A * A -> B) hist ctx,
      fold_with_ctx_history_rec f hist ctx (l1 ++ l2) =
        fold_with_ctx_history_rec f hist ctx l1 ++
          fold_with_ctx_history_rec f (hist ++ fold_with_ctx_history_rec f hist ctx l1) (ctx ++ l1) l2.
  Proof.
    induction l1 as [|a l1 IHl1]; intros.
    - cbn.
      do 2 rewrite List.app_nil_r.
      reflexivity.
    - rewrite <- List.app_comm_cons.
      rewrite fold_with_ctx_history_cons_rec.
      rewrite fold_with_ctx_history_cons_rec.
      rewrite IHl1.
      rewrite <- List.app_comm_cons.
      repeat rewrite <- List.app_assoc.
      reflexivity.
  Qed.

  Lemma fold_with_ctx_history_app {l1 l2: list A}:
    forall (f: list B * list A * A -> B),
      fold_with_ctx_history f (l1 ++ l2) =
        fold_with_ctx_history f l1 ++
          fold_with_ctx_history_rec f (fold_with_ctx_history_rec f [] [] l1) l1 l2.
  Proof.
    intros. unfold fold_with_ctx_history.
    rewrite fold_with_ctx_history_app_rec.
    rewrite List.app_nil_l.
    rewrite List.app_nil_l.
    reflexivity.
  Qed.

End rw.
