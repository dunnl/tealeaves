From Tealeaves Require Export
     Util.Prelude
     Util.EqDec_eq LN.Atom LN.AtomSet LN.Leaf
     Classes.SetlikeMonad.

From Multisorted Require Export
     Classes.DecoratedMonad
     Classes.ListableMonad.

Import Monoid.Notations.
Import LN.AtomSet.Notations.
Import Classes.SetlikeFunctor.Notations.
Import Tealeaves.Classes.SetlikeFunctor.Notations.
Import Multisorted.Classes.SetlikeFunctor.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.
#[local] Open Scope set_scope.

(** * Operations for locally nameless *)
(******************************************************************************)

(** ** Local operations *)
(******************************************************************************)
Section local_operations.

  Context
    `{Index}
    `{MReturn T}.

  Implicit Types (x : atom) (k : K).

  Definition free_loc : leaf -> list atom :=
    fun l => match l with
          | Fr x => cons x List.nil
          | _ => List.nil
          end.

  Definition subst_loc k x (u : T k leaf) : leaf -> T k leaf :=
    fun l => match l with
          | Fr y => if x == y then u else mret T k (Fr y)
          | Bd n => mret T k (Bd n)
          end.

  Definition open_loc k (u : T k leaf) : Row nat * leaf -> T k leaf :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => mret T k (Fr x)
            | Bd n => match Nat.compare n (w k) with
                     | Gt => mret T k (Bd (n - 1))
                     | Eq => u
                     | Lt => mret T k (Bd n)
                     end
            end
          end.

  Definition is_opened : nat * leaf -> Prop :=
    fun p =>
      match p with
      | (ctx, l) =>
        match l with
        | Fr y => False
        | Bd n => n = ctx
        end
      end.

  Definition close_loc k x : Row nat * leaf -> leaf :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr y => if x == y then Bd (w k) else Fr y
            | Bd n => match Nat.compare n (w k) with
                    | Gt => Bd (S n)
                    | Eq => Bd (S n)
                    | Lt => Bd n
                    end
            end
          end.

  (** The argument <<n>> is appended the context---to define local
      closure we will take <<n = 0>>, but we can also consider more
      notions like ``local closure within a gap of 1 binder,'' which
      is useful for backend reasoning. **)
  Definition is_bound_or_free k (gap : nat) : Row nat * leaf -> Prop :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => True
            | Bd n => n < w k ● gap
            end
          end.

End local_operations.

(** ** Lifted operations *)
(******************************************************************************)
Section LocallyNamelessOperations.

  Context
    (F : Type -> Type)
    `{DecoratedMultisortedModule
        (Row nat) (mn_op := Monoid_op_Row) (mn_unit := Monoid_unit_Row)
        F T}
  `{! Tomlist F} `{! forall k, Tomlist (T k)} `{! ListableMultisortedModule F T}.

  Definition open k (u : T k leaf) : F leaf -> F leaf  :=
    bindkd F k (open_loc k u).

  Definition close k x : F leaf -> F leaf :=
    fmapkd F k (close_loc k x).

  Definition subst k x (u : T k leaf) : F leaf -> F leaf :=
    bindk F k (subst_loc k x u).

  Definition free : K -> F leaf -> list atom :=
    fun k t => bind list free_loc (tolistk F k t).

  (** Derived operation *)
  Definition freeset : K -> F leaf -> AtomSet.t :=
    fun k t => LN.AtomSet.atoms (free k t).

  Definition locally_closed_gap k (gap : nat) : F leaf -> Prop :=
    fun t => forall w l, (k, (w, l)) ∈md t -> is_bound_or_free k gap (w, l).

  Definition locally_closed k : F leaf -> Prop :=
    locally_closed_gap k 0.

  Definition scoped : K -> F leaf -> AtomSet.t -> Prop :=
    fun k t γ => freeset k t ⊆ γ.

End LocallyNamelessOperations.

Module Notations.

  Notation "t '{ k | x ~> u }" := (subst _ k x u t) (at level 35).
  Notation "t '( k | u )" := (open _ k u t) (at level 35).
  Notation "'[ k | x ] t" := (close _ k x t) (at level 35).
  Notation "( x , y , z )" := (pair x (pair y z)) : tealeaves_multi_scope.

End Notations.

(** * Immediate properties of the operations *)
(******************************************************************************)
Section LocallyNameless.

  Section test_notations.

    Import Notations.

    Context
    (F : Type -> Type)
    `{DecoratedMultisortedModule
        (Row nat) (mn_op := Monoid_op_Row) (mn_unit := Monoid_unit_Row)
        F T}
    `{! Tomlist F} `{! forall k, Tomlist (T k)} `{! ListableMultisortedModule F T}.

    Context
      (k j : K)
      (t1 : T k leaf)
      (t2 : T j leaf)
      (u : F leaf)
      (x : atom)
      (n : nat).

    Check u '{ k | x ~> t1}.
    Check u '(k | t1).
    Check '[k | x] u.

    Check u '{j | x ~> t2}.
    Check u '(j | t2).
    Check '[j | x] u.

    Fail Check u '{j | x ~> t1}.
    Fail Check u '(j | t1).

  End test_notations.

  Import Notations.

  Context
    (F : Type -> Type)
    `{DecoratedMultisortedModule
        (Row nat) (mn_op := Monoid_op_Row) (mn_unit := Monoid_unit_Row)
        F T}
  `{! Tomlist F} `{! forall k, Tomlist (T k)} `{! ListableMultisortedModule F T}.

  Implicit Types (l : leaf) (n : Row nat) (t : F leaf) (x : atom).

  (** ** Identity and equality lemmas for operations *)
  (******************************************************************************)
  Lemma open_eq : forall k t u1 u2,
      (forall w l, (k, (w, l)) ∈md t -> open_loc k u1 (w, l) = open_loc k u2 (w, l)) ->
      t '(k | u1) = t '(k | u2).
  Proof.
    intros. unfold open.
    now apply (bindkd_respectful F T).
  Qed.

  Lemma open_id : forall k t u,
      (forall w l, (k, (w, l)) ∈md t -> open_loc k u (w, l) = mret T k l) ->
      t '(k | u) = t.
  Proof.
    intros. unfold open.
    now apply (bindkd_respectful_id F T).
  Qed.

  Lemma subst_eq : forall k t x u1 u2,
      (forall l, (k, l) ∈m t -> subst_loc k x u1 l = subst_loc k x u2 l) ->
      t '{k | x ~> u1} = t '{k | x ~> u2}.
  Proof.
    intros. unfold subst.
    now apply (setlike_bindk_respectful F T).
  Qed.

  Lemma subst_id : forall k t x u,
      (forall l, (k, l) ∈m t -> subst_loc k x u l = mret T k l) ->
      t '{k | x ~> u} = t.
  Proof.
    intros. unfold subst.
    now apply (setlike_bindk_respectful_id F T).
  Qed.

  Lemma close_eq : forall k t x y,
      (forall w l, (k, (w, l)) ∈md t -> close_loc k x (w, l) = close_loc k y (w, l)) ->
      '[k | x] t = '[k | y] t.
  Proof.
    intros. unfold close.
    now apply (fmapkd_respectful F).
  Qed.

  Lemma close_id : forall k t x,
      (forall w l, (k, (w, l)) ∈md t -> close_loc k x (w, l) = l) ->
      '[k | x] t = t.
  Proof.
    intros. unfold close.
    now apply (fmapkd_respectful_id F).
  Qed.

  (** ** Context-sensitive leaf analysis of operations *)
  (******************************************************************************)

  (** *** Opening *)
  (******************************************************************************)
  Lemma inr_open_iff_eq : forall k l n u t,
      (k, (n, l)) ∈md t '(k | u) <-> exists l1 n1 n2,
        (k, (n1, l1)) ∈md t /\ (k, (n2, l)) ∈md open_loc k u (n1, l1) /\ n = n1 ● n2.
  Proof.
    intros. unfold open.
    now rewrite (ind_bindkd_iff_eq F T k).
  Qed.

  Lemma inr_open_iff_neq : forall k j l n u t,
      k <> j ->
      (k, (n, l)) ∈md t '(j | u) <-> (k, (n, l)) ∈md t \/ exists l1 n1 n2,
          (j, (n1, l1)) ∈md t /\ (k, (n2, l)) ∈md open_loc j u (n1, l1) /\ n = n1 ● n2.
  Proof.
    intros. unfold open.
    now rewrite (ind_bindkd_iff_neq F T j k).
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma inr_close_iff_eq : forall k l n x t,
      (k, (n, l)) ∈md '[k | x] t <-> exists l1,
        (k, (n, l1)) ∈md t /\ close_loc k x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite (ind_fmapkd_iff_eq F).
  Qed.

  Lemma ind_close_iff_neq : forall k j l n x t,
      j <> k ->
      (k, (n, l)) ∈md '[j | x] t <-> (k, (n, l)) ∈md t.
  Proof.
    intros. unfold close.
    now rewrite (ind_fmapkd_iff_neq F).
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma ind_subst_iff_eq : forall k n l u t x,
      (k, (n, l)) ∈md t '{k | x ~> u} <-> exists l1 n1 n2,
        (k, (n1, l1)) ∈md t /\ (k, (n2, l)) ∈md subst_loc k x u l1 /\ n = n1 ● n2.
  Proof.
    intros. unfold subst.
    now rewrite (ind_bindk_iff_eq F T k).
  Qed.

  Lemma ind_subst_iff_neq : forall k j n l u t x,
      k <> j ->
      (k, (n, l)) ∈md t '{j | x ~> u} <-> (k, (n, l)) ∈md t \/ exists l1 n1 n2,
        (j, (n1, l1)) ∈md t /\ (k, (n2, l)) ∈md subst_loc j x u l1 /\ n = n1 ● n2.
  Proof.
    intros. unfold subst.
    now rewrite (ind_bindk_iff_neq F T).
  Qed.

  (** ** Context-agnostic leaf analysis of operations *)
  (******************************************************************************)

  (** *** Opening *)
  (******************************************************************************)
  Lemma in_open_iff_eq : forall k l u t,
      (k, l) ∈m t '(k | u) <-> exists l1 n1,
        (k, (n1, l1)) ∈md t /\ (k, l) ∈m open_loc k u (n1, l1).
  Proof.
    intros. unfold open.
    now rewrite (in_bindkd_iff_eq F T k).
  Qed.

  Lemma in_open_iff_neq : forall k j l u t,
      k <> j ->
      (k, l) ∈m t '(j | u) <-> (k, l) ∈m t \/ exists l1 n1,
          (j, (n1, l1)) ∈md t /\ (k, l) ∈m open_loc j u (n1, l1).
  Proof.
    intros. unfold open.
    now rewrite (in_bindkd_iff_neq F T k j).
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma in_close_iff_eq : forall k l x t,
      (k, l) ∈m '[k | x] t <-> exists n l1,
        (k, (n, l1)) ∈md t /\ close_loc k x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite (in_fmapkd_iff_eq F).
  Qed.

  Lemma in_close_iff_neq : forall k j l x t,
      k <> j ->
      (k, l) ∈m '[j | x] t <-> (k, l) ∈m t.
  Proof.
    intros. unfold close.
    now rewrite (in_fmapkd_iff_neq F).
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma in_subst_iff_eq : forall k l u t x,
      (k, l) ∈m t '{k | x ~> u} <-> exists l1,
        (k, l1) ∈m t /\ (k, l) ∈m subst_loc k x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (in_bindk_iff_eq F T t k).
  Qed.

  Lemma in_subst_iff_neq : forall k j l u t x,
      j <> k ->
      (k, l) ∈m t '{j | x ~> u} <-> (k, l) ∈m t \/ exists l1,
        (j, l1) ∈m t /\ (k, l) ∈m subst_loc j x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (in_bindk_iff_neq F T).
  Qed.

  (** ** Properties of free variables *)
  (******************************************************************************)

  (** *** Specifications for [free] and [freeset] *)
  (******************************************************************************)
  Theorem in_free_iff : forall (k : K) (t : F leaf) (x : atom),
      x ∈ free F k t <-> (k, Fr x) ∈m t.
  Proof.
    intros. unfold free. rewrite (in_bind_iff list). split.
    - intros [l [lin xin]]. rewrite (in_tolistk_iff) in lin.
      destruct l as [a|n].
      + cbv in xin. destruct xin as [?|[]].
        subst. now rewrite in_iff_in_mlist.
      + cbv in xin. destruct xin as [].
    - intros. exists (Fr x). rewrite (in_tolistk_iff).
      rewrite <- (in_iff_in_mlist). split; [assumption| ].
      cbv. now left.
  Qed.

  Theorem in_free_iff_T : forall (k j : K) (t : T j leaf) (x : atom),
      x ∈ free (T j) k t <-> (k, Fr x) ∈m t.
  Proof.
    intros. unfold free. rewrite (in_bind_iff list). split.
    - intros [l [lin xin]]. rewrite (in_tolistk_iff) in lin.
      destruct l as [a|n].
      + cbv in xin. destruct xin as [?|[]].
        subst. now rewrite in_iff_in_mlist.
      + cbv in xin. destruct xin as [].
    - intros. exists (Fr x). rewrite (in_tolistk_iff).
      rewrite <- (in_iff_in_mlist). split; [assumption| ].
      cbv. now left.
  Qed.

  Theorem free_iff_freeset : forall (k : K) (t : F leaf) (x : atom),
      x ∈ free F k t <-> x ∈@ freeset F k t.
  Proof.
    intros. unfold freeset. rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  Theorem free_iff_freeset_T : forall (k j : K) (t : T j leaf) (x : atom),
      x ∈ free (T j) k t <-> x ∈@ freeset (T j) k t.
  Proof.
    intros. unfold freeset. rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  (** *** Opening *)
  (******************************************************************************)
  Local Notation "x @ < k , w > ∈ t" :=
    (tomsetd _ t (k, (w, x))) (k at level 5, w at level 5, at level 50) : tealeaves_multi_scope.

  Lemma free_open_iff_eq : forall k u t x,
      x ∈ free F k (t '(k | u)) <-> exists l1 w,
        l1 @ <k, w> ∈ t /\ x ∈ free (T k) k (open_loc k u (w, l1)).
  Proof.
    intros. rewrite in_free_iff. setoid_rewrite in_free_iff_T.
    now rewrite in_open_iff_eq.
  Qed.

  Lemma free_open_iff_neq : forall k j u t x,
      k <> j ->
      x ∈ free F j (t '(k | u)) <-> x ∈ free F j t \/ exists l1 w,
          (k, (w, l1)) ∈md t /\ x ∈ free (T k) j (open_loc k u (w, l1)).
  Proof.
    intros. rewrite 2(in_free_iff). setoid_rewrite in_free_iff_T.
    now rewrite in_open_iff_neq; auto.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma free_close_iff_eq : forall k t x y,
      y ∈ free F k ('[k | x] t) <-> exists w l1,
        l1 @ <k, w> ∈ t /\ close_loc k x (w, l1) = Fr y.
  Proof.
    intros. rewrite in_free_iff.
    now rewrite in_close_iff_eq.
  Qed.

  Lemma free_close_iff_neq : forall k j t x,
      k <> j ->
      x ∈ free F j ('[k | x] t) <-> x ∈ free F j t.
  Proof.
    intros. rewrite 2(in_free_iff).
    now rewrite in_close_iff_neq; auto.
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma free_subst_iff_eq : forall k u t x y,
      y ∈ free F k (t '{k | x ~> u}) <-> exists l1,
        (k, l1) ∈m t /\ y ∈ free (T k) k (subst_loc k x u l1).
  Proof.
    intros. rewrite (in_free_iff). setoid_rewrite (in_free_iff_T).
    now rewrite (in_subst_iff_eq).
  Qed.

  Lemma free_subst_iff_neq : forall j k u t x y,
      k <> j ->
      y ∈ free F j (t '{k | x ~> u}) <-> y ∈ free F j t \/ exists l1,
        (k, l1) ∈m t /\ y ∈ free (T k) j (subst_loc k x u l1).
  Proof.
    intros. rewrite 2(in_free_iff). setoid_rewrite (in_free_iff_T).
    now rewrite (in_subst_iff_neq); auto.
  Qed.

End LocallyNameless.
