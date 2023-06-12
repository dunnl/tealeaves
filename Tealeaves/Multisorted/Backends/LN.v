From Tealeaves Require Export
  Classes.EqDec_eq
  Categories.TypeFamilies
  Backends.LN.Atom
  Backends.LN.AtomSet
  Multisorted.Classes.DTM
  Classes.Traversable.Monad. (* bind for lists *)

From Tealeaves Require Import Classes.Kleisli.Monad.
From Tealeaves Require Import Classes.Kleisli.Traversable.Functor.
From Tealeaves Require Import Classes.Kleisli.Traversable.Monad.
From Tealeaves Require Import Classes.Kleisli.Decorated.Functor.
From Tealeaves Require Import Classes.Kleisli.Decorated.Monad.
From Tealeaves Require Import Classes.Kleisli.DT.Functor.
From Tealeaves Require Import Classes.Kleisli.DT.Monad.

Import Multisorted.Classes.DTM.Notations.
Import Multisorted.Classes.DTM.Notations2.
Import Multisorted.Classes.DTM.Notations3.
Import Categories.TypeFamilies.Notations.
Import Classes.Setlike.Functor.Notations.
Import Monoid.Notations.
Import List.ListNotations.
Import LN.AtomSet.Notations.

#[local] Open Scope nat_scope. (* Let <<x + y>> be addition, not sum type. *)
#[local] Generalizable Variables T.

(** * Binders contexts **)
(** We assume that binder contexts are lists of tagged values of type
    <<unit>>, which are just tags themselves. *)
(******************************************************************************)
Section operations_on_context.

  Context
    `{Index}.

  Fixpoint countk (j : K) (l : list K) : nat :=
    match l with
    | nil => 0
    | cons k rest =>
      (if j == k then 1 else 0) + countk j rest
    end.

  Lemma countk_nil : forall j, countk j nil = 0.
  Proof.
    easy.
  Qed.

  Lemma countk_one_eq : forall j, countk j [j] = 1.
  Proof.
    intros. cbn. compare values j and j.
  Qed.

  Lemma countk_one_neq : forall j k, j <> k -> countk j [k] = 0.
  Proof.
    intros. cbn. compare values j and k.
  Qed.

  Lemma countk_cons_eq : forall j l, countk j (j :: l) = S (countk j l).
  Proof.
    intros. cbn. compare values j and j.
  Qed.

  Lemma countk_cons_neq : forall j k l, j <> k -> countk j (k :: l) = countk j l.
  Proof.
    intros. cbn. compare values j and k.
  Qed.

  Lemma countk_app : forall j l1 l2, countk j (l1 ++ l2) = countk j l1 + countk j l2.
  Proof.
    intros. induction l1.
    - easy.
    - cbn. compare values j and a.
      now rewrite IHl1.
  Qed.

End operations_on_context.

(** * Locally nameless variables *)
(******************************************************************************)
Inductive LN :=
| Fr : atom -> LN
| Bd : nat -> LN.

Theorem eq_dec_LN : forall l1 l2 : LN, {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
  - compare values a and a0; auto.
  - compare values n and n0; auto.
Qed.

#[export] Instance EqDec_LN : EquivDec.EqDec LN eq := eq_dec_LN.

Lemma compare_to_atom : forall x l (P : LN -> Prop),
    P (Fr x) ->
    (forall a : atom, a <> x -> P (Fr a)) ->
    (forall n : nat, P (Bd n)) ->
    P l.
Proof.
  introv case1 case2 case3. destruct l.
  - destruct_eq_args x a. auto.
  - auto.
Qed.

Tactic Notation "compare" constr(l) "to" "atom" constr(x) :=
  (induction l using (compare_to_atom x)).

(** * Syntax operations for locally nameless *)
(******************************************************************************)

(** ** Local operations *)
(******************************************************************************)
Section local_operations.

  Context
    `{Index}
    `{MReturn T}.

  Implicit Types (x : atom) (k : K).

  Definition free_loc : LN -> list atom :=
    fun l => match l with
          | Fr x => cons x List.nil
          | _ => List.nil
          end.

  Definition subst_loc k x (u : T k LN) : LN -> T k LN :=
    fun l => match l with
          | Fr y =>
            if x == y then u else mret T k (Fr y)
          | Bd n =>
            mret T k (Bd n)
          end.

  Definition open_loc k (u : T k LN) : list K * LN -> T k LN :=
    fun '(w, l) =>
      match l with
      | Fr x => mret T k (Fr x)
      | Bd n =>
        match Nat.compare n (countk k w) with
        | Gt => mret T k (Bd (n - 1))
        | Eq => u
        | Lt => mret T k (Bd n)
        end
      end.

  Definition is_opened : list K * (K * LN) -> Prop :=
    fun '(w, (k, l)) =>
      match l with
      | Fr y => False
      | Bd n => n = countk k w
      end.

  Definition close_loc k x : list K * LN -> LN :=
    fun '(w, l) =>
      match l with
      | Fr y =>
        if x == y then Bd (countk k w) else Fr y
      | Bd n =>
        match Nat.compare n (countk k w) with
        | Gt => Bd (S n)
        | Eq => Bd (S n)
        | Lt => Bd n
        end
      end.

  (** To define local closure we will take <<n = 0>>, but we can also
      consider more notions like ``local closure within a gap of 1
      binder,'' which is useful for backend reasoning. **)
  Definition is_bound_or_free k (gap : nat) : list K * LN -> Prop :=
    fun '(w, l) =>
      match l with
      | Fr x => True
      | Bd n => n < (countk k w) + gap
      end.

End local_operations.

(** ** Lifted operations *)
(******************************************************************************)
Section LocallyNamelessOperations.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Definition open k (u : T k LN) : S LN -> S LN  :=
    kbindd S k (open_loc k u).

  Definition close k x : S LN -> S LN :=
    kfmapd S k (close_loc k x).

  Definition subst k x (u : T k LN) : S LN -> S LN :=
    kbind S k (subst_loc k x u).

  Definition free : K -> S LN -> list atom :=
    fun k t => bind list free_loc (toklist S k t).

  Definition locally_closed_gap k (gap : nat) : S LN -> Prop :=
    fun t => forall (w : list K) (l : LN),
        (w, (k, l)) ∈md t -> is_bound_or_free k gap (w, l).

  Definition locally_closed k : S LN -> Prop :=
    locally_closed_gap k 0.

  Definition freeset : K -> S LN -> AtomSet.t :=
    fun k t => LN.AtomSet.atoms (free k t).

  Definition scoped : K -> S LN -> AtomSet.t -> Prop :=
    fun k t γ => freeset k t ⊆ γ.

End LocallyNamelessOperations.

(** ** Notations for operations *)
(******************************************************************************)
Module Notations.

  Notation "t '{ k | x ~> u }" := (subst _ k x u t) (at level 35).
  Notation "t '( k | u )" := (open _ k u t) (at level 35).
  Notation "'[ k | x ] t" := (close _ k x t) (at level 35).
  Notation "( x , y , z )" := (pair x (pair y z)) : tealeaves_multi_scope.

End Notations.

Section test_notations.

  Import Notations.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Context
    (k j : K)
    (t1 : T k LN)
    (t2 : T j LN)
    (u : S LN)
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

(*|
############################################################
Multisorted locally nameless infrastructure
############################################################
|*)

(*|
---------------------------------------
Basic properties of operations
---------------------------------------
|*)
Section operations_specifications.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Implicit Types (l : LN) (w : list K) (t : S LN) (x : atom).

  (** ** Identity and equality lemmas for operations *)
  (******************************************************************************)

  (** *** For [open] *)
  (******************************************************************************)
  Lemma open_eq : forall k t (u1 u2 : T k LN),
      (forall (w : list K) (l : LN), (w, (k, l)) ∈md t -> open_loc k u1 (w, l) = open_loc k u2 (w, l)) ->
      t '(k | u1) = t '(k | u2).
  Proof.
    introv hyp. unfold open. apply kbindd_respectful. auto.
  Qed.

  Lemma open_id : forall k t u,
      (forall w l, (w, (k, l)) ∈md t -> open_loc k u (w, l) = mret T k l) ->
      t '(k | u) = t.
  Proof.
    intros. unfold open.
    now apply (kbindd_respectful_id k).
  Qed.

  (** *** For [subst] *)
  (******************************************************************************)
  Lemma subst_eq : forall k t x u1 u2,
      (forall l, (k, l) ∈m t -> subst_loc k x u1 l = subst_loc k x u2 l) ->
      t '{k | x ~> u1} = t '{k | x ~> u2}.
  Proof.
    introv hyp. unfold subst. apply kbind_respectful. auto.
  Qed.

  Lemma subst_id : forall k t x u,
      (forall l, (k, l) ∈m t -> subst_loc k x u l = mret T k l) ->
      t '{k | x ~> u} = t.
  Proof.
    intros. unfold subst.
    now apply kbind_respectful_id.
  Qed.

  (** *** For [close] *)
  (******************************************************************************)
  Lemma close_eq : forall k t x y,
      (forall w l, (w, (k, l)) ∈md t -> close_loc k x (w, l) = close_loc k y (w, l)) ->
      '[k | x] t = '[k | y] t.
  Proof.
    intros. unfold close.
    now apply (kfmapd_respectful).
  Qed.

  Lemma close_id : forall k t x,
      (forall w l, (w, (k, l)) ∈md t -> close_loc k x (w, l) = l) ->
      '[k | x] t = t.
  Proof.
    intros. unfold close.
    now apply (kfmapd_respectful_id).
  Qed.

  (** ** Context-sensitive LN analysis of operations *)
  (******************************************************************************)

  (** *** For [open] *)
  (******************************************************************************)
  Lemma ind_open_iff_eq : forall k l w u t,
      (w, (k, l)) ∈md t '(k | u) <-> exists w1 w2 l1,
        (w1, (k, l1)) ∈md t /\ (w2, (k, l)) ∈md open_loc k u (w1, l1) /\ w = w1 ● w2.
  Proof.
    intros. unfold open.
    now rewrite (ind_kbindd_eq_iff S).
  Qed.

  Lemma ind_open_neq_iff : forall k j l w u t,
      k <> j ->
      (w, (k, l)) ∈md t '(j | u) <-> (w, (k, l)) ∈md t \/ exists w1 w2 l1,
          (w1, (j, l1)) ∈md t /\ (w2, (k, l)) ∈md open_loc j u (w1, l1) /\ w = w1 ● w2.
  Proof.
    intros. unfold open.
    now rewrite (ind_kbindd_neq_iff S); auto.
  Qed.

  (** *** For [close] *)
  (******************************************************************************)
  Lemma ind_close_iff_eq : forall k l w x t,
      (w, (k, l)) ∈md '[k | x] t <-> exists l1,
        (w, (k, l1)) ∈md t /\ l = close_loc k x (w, l1).
  Proof.
    intros. unfold close.
    rewrite (ind_kfmapd_eq_iff S).
    easy.
  Qed.

  Lemma ind_close_neq_iff : forall k j l w x t,
      j <> k ->
      (w, (k, l)) ∈md '[j | x] t <-> (w, (k, l)) ∈md t.
  Proof.
    intros. unfold close.
    now rewrite (ind_kfmapd_neq_iff S).
  Qed.

  (** *** For [subst] *)
  (******************************************************************************)
  Lemma ind_subst_iff_eq : forall k w l u t x,
      (w, (k, l)) ∈md t '{k | x ~> u} <-> exists w1 w2 l1,
        (w1, (k, l1)) ∈md t /\ (w2, (k, l)) ∈md subst_loc k x u l1 /\ w = w1 ● w2.
  Proof.
    intros. unfold subst.
    now rewrite (ind_kbind_eq_iff S).
  Qed.

  Lemma ind_subst_neq_iff : forall k j w l u t x,
      k <> j ->
      (w, (k, l)) ∈md t '{j | x ~> u} <-> (w, (k, l)) ∈md t \/ exists w1 w2 l1,
        (w1, (j, l1)) ∈md t /\ (w2, (k, l)) ∈md subst_loc j x u l1 /\ w = w1 ● w2.
  Proof.
    intros. unfold subst.
    now rewrite (ind_kbind_neq_iff S); auto.
  Qed.

  (** ** Context-agnostic LN analysis of operations *)
  (******************************************************************************)

  (** *** For [open] *)
  (******************************************************************************)
  Lemma in_open_eq_iff : forall k l u t,
      (k, l) ∈m t '(k | u) <-> exists w1 l1,
        (w1, (k, l1)) ∈md t /\ (k, l) ∈m open_loc k u (w1, l1).
  Proof.
    intros. unfold open.
    now rewrite (in_kbindd_eq_iff S).
  Qed.

  Lemma in_open_neq_iff : forall k j l u t,
      k <> j ->
      (k, l) ∈m t '(j | u) <-> (k, l) ∈m t \/ exists w1 l1,
          (w1, (j, l1)) ∈md t /\ (k, l) ∈m open_loc j u (w1, l1).
  Proof.
    intros. unfold open.
    now rewrite (in_kbindd_neq_iff S); auto.
  Qed.

  (** *** For [close] *)
  (******************************************************************************)
  Lemma in_close_eq_iff : forall k l x t,
      (k, l) ∈m '[k | x] t <-> exists w l1,
        (w, (k, l1)) ∈md t /\ l = close_loc k x (w, l1).
  Proof.
    intros. unfold close.
    now rewrite (in_kfmapd_eq_iff S).
  Qed.

  Lemma in_close_neq_iff : forall k j l x t,
      k <> j ->
      (k, l) ∈m '[j | x] t <-> (k, l) ∈m t.
  Proof.
    intros. unfold close.
    now rewrite (in_kfmapd_neq_iff S); auto.
  Qed.

  (** *** For [subst] *)
  (******************************************************************************)
  Lemma in_subst_eq_iff : forall k l u t x,
      (k, l) ∈m t '{k | x ~> u} <-> exists l1,
        (k, l1) ∈m t /\ (k, l) ∈m subst_loc k x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (in_kbind_eq_iff S).
  Qed.

  Lemma in_subst_neq_iff : forall k j l u t x,
      j <> k ->
      (k, l) ∈m t '{j | x ~> u} <-> (k, l) ∈m t \/ exists l1,
          (j, l1) ∈m t /\ (k, l) ∈m subst_loc j x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (in_kbind_neq_iff S).
  Qed.

End operations_specifications.


(** * Specifications for <<free>> *)
(******************************************************************************)
Section operations_specifications.

  (** ** Characterizations for [free] and [freeset] *)
  (******************************************************************************)
  Section characterize_free.

    Context
      (S : Type -> Type)
      `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
      `{! DTM (list K) T}.

    Theorem in_free_iff : forall (k : K) (t : S LN) (x : atom),
        x ∈ free S k t <-> (k, Fr x) ∈m t.
    Proof.
      intros. unfold free. rewrite in_bind_list_iff. split.
      - intros [l [lin xin]]. rewrite <- (in_iff_in_toklist) in lin.
        destruct l as [a|n].
        + cbv in xin. destruct xin as [?|[]].
          subst. assumption.
        + cbv in xin. destruct xin as [].
      - intros. exists (Fr x). rewrite <- (in_iff_in_toklist).
        split; [assumption| ].
        cbv. now left.
    Qed.

    Corollary free_iff_freeset : forall (k : K) (t : S LN) (x : atom),
        x ∈ free S k t <-> x ∈@ freeset S k t.
    Proof.
      intros. unfold freeset. rewrite <- in_atoms_iff.
      reflexivity.
    Qed.

  End characterize_free.

  (** ** [free] variables after <<open>>/<<close>>/<<subst>> *)
  (******************************************************************************)
  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  (** *** After [open] *)
  (******************************************************************************)
  Lemma free_open_eq_iff : forall k u t x,
      x ∈ free S k (t '(k | u)) <-> exists w l1,
        (w, (k, l1)) ∈md t /\ x ∈ free (T k) k (open_loc k u (w, l1)).
  Proof.
    intros. rewrite in_free_iff.
    setoid_rewrite in_free_iff.
    now rewrite in_open_eq_iff.
  Qed.

  Lemma free_open_neq_iff : forall k j u t x,
      k <> j ->
      x ∈ free S j (t '(k | u)) <-> x ∈ free S j t \/ exists w l1,
          (w, (k, l1)) ∈md t /\ x ∈ free (T k) j (open_loc k u (w, l1)).
  Proof.
    intros. rewrite 2(in_free_iff). setoid_rewrite in_free_iff.
    now rewrite in_open_neq_iff; auto.
  Qed.

  (** *** After [close] *)
  (******************************************************************************)
  Lemma free_close_eq_iff : forall k t x y,
      y ∈ free S k ('[k | x] t) <-> exists w l1,
        (w, (k, l1)) ∈md t /\ Fr y = close_loc k x (w, l1).
  Proof.
    intros. rewrite (in_free_iff S).
    now rewrite (in_close_eq_iff S).
  Qed.

  Lemma free_close_neq_iff : forall k j t x,
      k <> j ->
      x ∈ free S j ('[k | x] t) <-> x ∈ free S j t.
  Proof.
    intros. rewrite 2(in_free_iff).
    now rewrite (in_close_neq_iff S); auto.
  Qed.

  (** *** For [subst] *)
  (******************************************************************************)
  Lemma free_subst_eq_iff : forall k u t x y,
      y ∈ free S k (t '{k | x ~> u}) <-> exists l1,
        (k, l1) ∈m t /\ y ∈ free (T k) k (subst_loc k x u l1).
  Proof.
    intros. rewrite (in_free_iff). setoid_rewrite (in_free_iff (T k)).
    now rewrite (in_subst_eq_iff S).
  Qed.

  Lemma free_subst_neq_iff : forall j k u t x y,
      k <> j ->
      y ∈ free S j (t '{k | x ~> u}) <-> y ∈ free S j t \/ exists l1,
        (k, l1) ∈m t /\ y ∈ free (T k) j (subst_loc k x u l1).
  Proof.
    intros. rewrite 2(in_free_iff). setoid_rewrite (in_free_iff (T k)).
    now rewrite (in_subst_neq_iff); auto.
  Qed.

End operations_specifications.

(** * Lemmas for local reasoning *)
(** The following lemmas govern the behavior of the <<*_loc>> operations of
      the locally nameless library. These are put into a hint database
      <<tea_local>> to use with <<autorewrite>>. Since <<autorewrite>> tries the
      first unifying lemma (even if this generates absurd side conditions), we
      use <<Hint Rewrite ... using ...>> clauses and typically prefer
      <<autorewrite*>>, which only uses hints whose side conditions are
      discharged by the associated tactic. *)
(******************************************************************************)
Create HintDb tea_local.

Section locally_nameless_local.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Implicit Types (l : LN) (w : list K) (t : S LN) (x : atom) (j k : K) (n : nat).

  (** ** Lemmas for proving (in)equalities between leaves *)
  (******************************************************************************)
  Lemma Fr_injective : forall (x y : atom),
      (Fr x = Fr y) <-> (x = y).
  Proof.
    intros. split; intro hyp.
    now injection hyp. now subst.
  Qed.

  Lemma Fr_injective_not_iff : forall (x y : atom),
      (Fr x <> Fr y) <-> (x <> y).
  Proof.
    intros. split; intro hyp; contradict hyp.
    now subst. now injection hyp.
  Qed.

  Lemma Fr_injective_not : forall (x y : atom),
      x <> y -> ~ (Fr x = Fr y).
  Proof.
    intros. now rewrite Fr_injective.
  Qed.

  Lemma B_neq_Fr : forall n x,
      (Bd n = Fr x) = False.
  Proof.
    introv. propext. discriminate. contradiction.
  Qed.

  Lemma prod_K_not_iff : forall (k : K) A (x y : A),
      ((k, x) <> (k, y)) <-> (x <> y).
  Proof.
    intros. split; intro hyp; contradict hyp.
    now subst. now injection hyp.
  Qed.

  Lemma ninf_in_neq : forall k x l (t : S LN),
      ~ x ∈ free S k t ->
      (k, l) ∈m t -> Fr x <> l.
  Proof.
    introv hyp1 hyp2.
    rewrite in_free_iff in hyp1. destruct l.
    - injection. intros; subst.
      contradiction.
    - discriminate.
  Qed.

  Lemma neq_symmetry : forall X (x y : X),
      (x <> y) = (y <> x).
  Proof.
    intros. propext; intro hyp; contradict hyp; congruence.
  Qed.

  (** ** [subst_loc] *)
  (******************************************************************************)
  Lemma subst_loc_eq : forall k u x,
      subst_loc k x u (Fr x) = u.
  Proof.
    intros. cbn. now compare values x and x.
  Qed.

  Lemma subst_loc_neq : forall k u x y,
      y <> x ->
      subst_loc k x u (Fr y) = mret T k (Fr y).
  Proof.
    intros. cbn. now compare values x and y.
  Qed.

  Lemma subst_loc_b : forall k u x n,
      subst_loc k x u (Bd n) = mret T k (Bd n).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_loc_fr_neq : forall k u l x,
      Fr x <> l ->
      subst_loc k x u l = mret T k l.
  Proof.
    introv neq. unfold subst_loc.
    destruct l as [a|?]; [compare values x and a | reflexivity].
  Qed.

  Lemma subst_in_mret_eq : forall k x l u,
      (mret T k l) '{k | x ~> u} = subst_loc k x u l.
  Proof.
    intros. unfold subst.
    now rewrite kbind_comp_mret_eq.
  Qed.

  Lemma subst_in_mret_neq : forall k j x l u,
      j <> k ->
      (mret T k l) '{j | x ~> u} = mret T k l.
  Proof.
    intros. unfold subst.
    now rewrite kbind_comp_mret_neq.
  Qed.

  (** ** [open_loc] *)
  (******************************************************************************)
  Lemma open_loc_lt : forall k u w n,
      n < countk k w ->
      open_loc k u (w, Bd n) = mret T k (Bd n).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and (countk k w).
  Qed.

  Lemma open_loc_gt : forall k u n w,
      n > countk k w ->
      open_loc k u (w, Bd n) = mret T k (Bd (n - 1)).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and (countk k w).
  Qed.

  Lemma open_loc_eq : forall k w u,
      open_loc k u (w, Bd (countk k w)) = u.
  Proof.
    introv. unfold open_loc. compare naturals (countk k w) and (countk k w).
  Qed.

  Lemma open_loc_atom : forall k u w x,
      open_loc k u (w, Fr x) = mret T k (Fr x).
  Proof.
    reflexivity.
  Qed.

End locally_nameless_local.

(** ** Tactics for local reasoning *)
(******************************************************************************)
Tactic Notation "unfold_monoid" :=
  repeat unfold monoid_op, Monoid_op_list, Monoid_op_list,
  monoid_unit, Monoid_unit_list, Monoid_unit_list in *.

#[export] Hint Rewrite @prod_K_not_iff : tea_local.

(** Rewrite rules for expressions of the form <<x ∈ mret T y>> *)
#[export] Hint Rewrite
     @in_mret_iff @in_mret_eq_iff
     @ind_mret_iff @ind_mret_eq_iff using typeclasses eauto : tea_local.

(** Rewrite rules for simplifying expressions involving equalities between leaves *)
#[export] Hint Rewrite
     Fr_injective Fr_injective_not_iff B_neq_Fr : tea_local.

(** Solve goals of the form <<Fr x <> Fr y>> by using <<x <> y>> *)
#[export] Hint Resolve
 Fr_injective_not : tea_local.

#[export] Hint Rewrite
     @subst_loc_eq @subst_in_mret_eq
     using typeclasses eauto : tea_local.
#[export] Hint Rewrite
     @subst_loc_neq @subst_loc_b @subst_loc_fr_neq @subst_in_mret_neq
     using first [ typeclasses eauto | auto ] : tea_local.
#[export] Hint Rewrite
     @open_loc_lt @open_loc_gt
     using first [ typeclasses eauto | auto ] : tea_local.
#[export] Hint Rewrite
     @open_loc_eq @open_loc_atom
     using typeclasses eauto : tea_local.

Tactic Notation "simpl_local" := (autorewrite* with tea_local).

(** * Metatheory for the <<subst>> operation *)
(******************************************************************************)
Section subst_metatheory.

  Section fix_dtm.

    Context
      (S : Type -> Type)
      `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
      `{! DTM (list K) T}.

    Implicit Types
             (k : K) (j : K)
             (l : LN) (p : LN)
             (x : atom) (t : S LN)
             (w : list K) (n : nat).

    (** ** LN analysis with contexts *)
    (******************************************************************************)
    Lemma ind_subst_loc_iff : forall k l w j p u x,
        (w, (j, p)) ∈md subst_loc k x u l <->
        l <> Fr x /\ k = j /\ w = Ƶ /\ l = p \/ (* l is not replaced *)
        l = Fr x /\ (w, (j, p)) ∈md u. (* l is replaced *)
    Proof.
      introv. compare l to atom x.
      - rewrite subst_loc_eq.
        clear; firstorder.
      - rewrite subst_loc_neq; auto.
        rewrite ind_mret_iff.
        rewrite Fr_injective.
        firstorder.
      - rewrite subst_loc_b.
        rewrite ind_mret_iff.
        rewrite B_neq_Fr.
        firstorder.
    Qed.

    Corollary ind_subst_loc_iff_eq : forall k l w p u x,
        (w, (k, p)) ∈md subst_loc k x u l <->
        l <> Fr x /\ w = Ƶ /\ l = p \/
        l = Fr x /\ (w, (k, p)) ∈md u.
    Proof.
      introv. rewrite ind_subst_loc_iff. clear. firstorder.
    Qed.

    Corollary ind_subst_loc_iff_neq : forall k l w j p u x,
        k <> j ->
        (w, (j, p)) ∈md subst_loc k x u l <->
        l = Fr x /\ (w, (j, p)) ∈md u.
    Proof.
      introv neq. rewrite ind_subst_loc_iff. intuition.
    Qed.

    Theorem ind_subst_iff : forall k j w t u l x,
        (* <<l>> occurs in the result of a <<subst>> IFF *)
        (w, j, l) ∈md t '{k | x ~> u} <->
        (* <<l>> is an occurrence in <<t>> not of the same sort as the <<subst>> OR *)
        k <> j /\ (w, j, l) ∈md t \/
        (* <<l>> is an occurrence of the same sort but not an occurrence of <<x>> OR *)
        k = j /\ (w, k, l) ∈md t /\ l <> Fr x \/
        (* <<x>> occurs and <<l>> is the any LN in a substituted <<u>> *)
        exists w1 w2 : list K, (w1, k, Fr x) ∈md t /\ (w2, j, l) ∈md u /\ w = w1 ● w2.
    Proof with auto.
      intros. compare values k and j.
      - rewrite (ind_subst_iff_eq S). setoid_rewrite (ind_subst_loc_iff_eq j).
        split.
        + intros [l' [n1 [n2 conditions]]].
          right. destruct conditions as [c1 [[c2|c2] c3]].
          { subst. left. destructs c2; subst.
            rewrite monoid_id_l. auto. }
          { subst. right. destructs c2; subst. eauto. }
        + intros [[contra ?] | [ [? [in_t neq]] | hyp ] ].
          { contradiction. }
          { exists w (Ƶ : list K) l. rewrite monoid_id_l. split... }
          { destruct hyp as [w1 [w2 ?]]. exists w1 w2 (Fr x). intuition. }
      - rewrite (ind_subst_neq_iff S)... split.
        + intros [? | [n1 [n2 [p [in_t in_local]]]]]...
          rewrite (ind_subst_loc_iff_neq k) in in_local...
          right. right. exists n1 n2. destruct in_local as [[? ?] ?]; subst...
        + intros [[? ?] | [[? ?] | [w1 [w2 rest]]]].
          { auto. }
          { contradiction. }
          { right. exists w1 w2 (Fr x). simpl_local... }
    Qed.

    Corollary ind_subst_iff_eq' : forall k w t u l x,
        (w, k, l) ∈md t '{k | x ~> u} <->
        (w, k, l) ∈md t /\ l <> Fr x \/
        exists w1 w2 : list K, (w1, k, Fr x) ∈md t /\ (w2, k, l) ∈md u /\ w = w1 ● w2.
    Proof.
      intros. rewrite ind_subst_iff. intuition.
    Qed.

    Corollary ind_subst_iff_neq' : forall k j w t u l x,
        k <> j ->
        (w, j, l) ∈md t '{k | x ~> u} <->
        (w, j, l) ∈md t \/
        exists w1 w2 : list K, (w1, k, Fr x) ∈md t /\ (w2, j, l) ∈md u /\ w = w1 ● w2.
    Proof.
      intros. rewrite ind_subst_iff. intuition.
    Qed.

    (** ** LN analysis without contexts *)
    (******************************************************************************)
    Lemma in_subst_loc_iff : forall k l j p u x,
        (j, p) ∈m subst_loc k x u l <->
        l <> Fr x /\ k = j /\ l = p \/
        l = Fr x /\ (j, p) ∈m u.
    Proof.
      introv. compare l to atom x; autorewrite* with tea_local; intuition.
    Qed.

    Corollary in_subst_loc_iff_eq : forall k l p u x,
        (k, p) ∈m subst_loc k x u l <->
        l <> Fr x /\ l = p \/
        l = Fr x /\ (k, p) ∈m u.
    Proof.
      introv. rewrite in_subst_loc_iff; intuition.
    Qed.

    Corollary in_subst_loc_iff_neq : forall k l j p u x,
        k <> j ->
        (j, p) ∈m subst_loc k x u l <->
        l = Fr x /\ (j, p) ∈m u.
    Proof.
      introv neq. rewrite in_subst_loc_iff. intuition.
    Qed.

    Theorem in_subst_iff : forall k j t u l x,
        (* <<l>> occurs in the result of a <<subst>> IFF *)
        (j, l) ∈m t '{k | x ~> u} <->
        (* <<l>> is an occurrence in <<t>> not of the same sort as the <<subst>> OR *)
        k <> j /\ (j, l) ∈m t \/
        (* <<l>> is an occurrence of the same sort but not an occurrence of <<x>> OR *)
        k = j /\ (k, l) ∈m t /\ l <> Fr x \/
        (* <<x>> occurs and <<l>> is the any LN in a substituted <<u>> *)
        (k, Fr x) ∈m t /\ (j, l) ∈m u.
    Proof with auto.
      intros. destruct_eq_args k j.
      - rewrite (in_subst_eq_iff S).
        setoid_rewrite (in_subst_loc_iff_eq). split.
        + intros [? [?  in_sub]].
          destruct in_sub as [[? heq] | [heq ?]]; subst...
        + intros [[contra ?] | [ [? [in_t neq]] | ? ] ].
          { contradiction.  }
          { exists l... }
          { exists (Fr x). intuition. }
      - rewrite (in_subst_neq_iff S); auto. split.
        + intros [? | [p [in_t in_local]] ]; auto.
          rewrite in_subst_loc_iff_neq in in_local; auto.
          destruct in_local as [? ?]; subst. auto.
        + intros [[? ?] | [[? ?] | ?]].
          { auto. }
          { contradiction. }
          { right. exists (Fr x). simpl_local... }
    Qed.

    Corollary in_subst_iff_eq : forall k t u l x,
        (k, l) ∈m t '{k | x ~> u} <->
        (k, l) ∈m t /\ l <> Fr x \/
        (k, Fr x) ∈m t /\ (k, l) ∈m u.
    Proof with auto.
      intros. rewrite in_subst_iff. intuition.
    Qed.

    Corollary in_subst_iff_neq : forall k j t u l x,
        k <> j ->
        (j, l) ∈m t '{k | x ~> u} <->
        (j, l) ∈m t \/
        (k, Fr x) ∈m t /\ (j, l) ∈m u.
    Proof with auto.
      intros. rewrite in_subst_iff. intuition.
    Qed.

    (** ** Free variables after substitution *)
    (******************************************************************************)
    Corollary in_free_subst_iff_eq : forall t k u x y,
        y ∈ free S k (t '{k | x ~> u}) <->
        y ∈ free S k t /\ y <> x \/ x ∈ free S k t /\ y ∈ free (T k) k u.
    Proof.
      intros. repeat rewrite (in_free_iff).
      rewrite in_subst_iff_eq. now simpl_local.
    Qed.

    Corollary in_freeset_subst_iff_eq : forall t k u x y,
        y ∈@ freeset S k (t '{k | x ~> u}) <->
        y ∈@ freeset S k t /\ y <> x \/
        x ∈@ freeset S k t /\ y ∈@ freeset (T k) k u.
    Proof.
      intros. repeat rewrite <- (free_iff_freeset).
      apply in_free_subst_iff_eq.
    Qed.

    Corollary in_free_subst_iff_neq : forall t k j u x y,
        k <> j ->
        y ∈ free S j (t '{k | x ~> u}) <->
        y ∈ free S j t \/ x ∈ free S k t /\ y ∈ free (T k) j u.
    Proof.
      intros. repeat rewrite (in_free_iff).
      rewrite in_subst_iff_neq; auto. reflexivity.
    Qed.

    Corollary in_freeset_subst_iff_neq : forall t k j u x y,
        k <> j ->
        y ∈@ freeset S j (t '{k | x ~> u}) <->
        y ∈@ freeset S j t \/
        x ∈@ freeset S k t /\ y ∈@ freeset (T k) j u.
    Proof.
      intros. repeat rewrite <- (free_iff_freeset).
      auto using in_free_subst_iff_neq.
    Qed.

    (** ** Upper and lower bounds for leaves after substitution *)
    (******************************************************************************)
    Corollary in_subst_upper : forall k j t u l x,
        (j, l) ∈m t '{k | x ~> u} ->
        (j, l) ∈m t /\ (j, l) <> (k, Fr x) \/ (j, l) ∈m u.
    Proof with auto.
      introv hin. rewrite in_subst_iff in hin.
      destruct hin as [[hyp1 hyp2] | [hyp | hyp] ].
      - left. split; [assumption |]. injection...
      - destructs hyp. subst. left.
        split; [assumption |]. injection...
      - intuition.
    Qed.

    Corollary in_subst_upper_eq : forall k t u l x,
        (k, l) ∈m t '{k | x ~> u} ->
        (k, l) ∈m t /\ l <> Fr x \/ (k, l) ∈m u.
    Proof.
      introv hyp. apply in_subst_upper in hyp.
      autorewrite* with tea_local in hyp.
      intuition.
    Qed.

    Corollary in_subst_upper_neq : forall k j t u l x,
        k <> j ->
        (j, l) ∈m t '{k | x ~> u} ->
        (j, l) ∈m t \/ (j, l) ∈m u.
    Proof.
      introv neq hyp. apply in_subst_upper in hyp.
      intuition.
    Qed.

    Corollary in_free_subst_upper : forall k j t u x y,
        y ∈ free S j (t '{k | x ~> u}) ->
        (y ∈ free S j t /\ j <> k) \/ (y ∈ free S k t /\ y <> x /\ k = j) \/ y ∈ free (T k) j u.
    Proof.
      setoid_rewrite (in_free_iff). introv hyp.
      apply in_subst_upper in hyp.
      destruct hyp as [hyp | hyp].
      - destruct hyp. compare values j and k.
        + right. left. splits; auto.
          intro contra; subst; contradiction.
        + auto.
      - eauto using in_subst_upper.
    Qed.

    Corollary in_free_subst_upper_eq : forall k t u x y,
        y ∈ free S k (t '{k | x ~> u}) ->
        (y ∈ free S k t /\ y <> x) \/ y ∈ free (T k) k u.
    Proof.
      introv hyp. apply in_free_subst_upper in hyp.
      intuition.
    Qed.

    Corollary in_free_subst_upper_neq : forall k j t u x y,
        k <> j ->
        y ∈ free S j (t '{k | x ~> u}) ->
        y ∈ free S j t \/ y ∈ free (T k) j u.
    Proof.
      introv neq hyp. apply in_free_subst_upper in hyp.
      intuition.
    Qed.

    Corollary freeset_subst_upper : forall k j t u x y,
        y ∈@ freeset S j (t '{k | x ~> u}) ->
        k = j /\ y ∈@ (freeset S k t \\ {{x}} ∪ freeset (T k) j u) \/
        k <> j /\ y ∈@ (freeset S j t ∪ freeset (T k) j u).
    Proof.
      setoid_rewrite AtomSet.union_spec.
      setoid_rewrite AtomSet.diff_spec.
      setoid_rewrite <- free_iff_freeset.
      introv hyp. apply in_free_subst_upper in hyp.
      compare values j and k.
      + left. destruct hyp as [hyp | [hyp | hyp]].
        { split; auto. intuition. }
        { split; auto. left. split. intuition. fsetdec. }
        { split; auto. }
      + right. split; auto. destruct hyp as [hyp | [hyp | hyp]].
        { intuition. }
        { intuition. }
        { intuition. }
    Qed.

    Corollary freeset_subst_upper_eq : forall k t u x,
        freeset S k (t '{k | x ~> u}) ⊆
                (freeset S k t \\ {{x}} ∪ freeset (T k) k u).
    Proof.
      intros. intros a hyp. apply freeset_subst_upper in hyp.
      intuition.
    Qed.

    Corollary scoped_subst_eq : forall t k (u : T k LN) x γ1 γ2,
        scoped S k t γ1 ->
        scoped (T k) k u γ2 ->
        scoped S k (t '{k | x ~> u}) (γ1 \\ {{x}} ∪ γ2).
    Proof.
      introv St Su. unfold scoped in *.
      etransitivity. apply freeset_subst_upper_eq. fsetdec.
    Qed.

    Corollary freeset_subst_upper_neq : forall k j t u x,
        k <> j ->
        freeset S j (t '{k | x ~> u}) ⊆
                (freeset S j t ∪ freeset (T k) j u).
    Proof.
      intros. intros a hyp. apply freeset_subst_upper in hyp.
      intuition.
    Qed.

    Corollary scoped_subst_neq : forall t j k u x γ1 γ2,
        j <> k ->
        scoped S k t γ1 ->
        scoped (T j) k u γ2 ->
        scoped S k (t '{j | x ~> u}) (γ1 ∪ γ2).
    Proof.
      introv St Su. unfold scoped in *.
      etransitivity. apply freeset_subst_upper_neq; assumption.
      fsetdec.
    Qed.

    Corollary in_subst_lower_eq : forall t k u l x,
        (k, l) ∈m t /\ l <> Fr x ->
        (k, l) ∈m t '{k | x ~> u}.
    Proof with auto.
      intros; rewrite in_subst_iff...
    Qed.

    Corollary in_subst_lower_neq : forall t k j u l x,
        k <> j ->
        (j, l) ∈m t ->
        (j, l) ∈m t '{k | x ~> u}.
    Proof with auto.
      intros; rewrite in_subst_iff...
    Qed.

    Corollary in_free_subst_lower_eq : forall t k (u : T k LN) x y,
        y ∈ free S k t /\ y <> x ->
        y ∈ free S k (t '{k | x ~> u}).
    Proof.
      setoid_rewrite (in_free_iff). intros.
      apply in_subst_lower_eq. now simpl_local.
    Qed.

    Corollary in_free_subst_lower_neq : forall t k j u x y,
        k <> j ->
        y ∈ free S j t ->
        y ∈ free S j (t '{k | x ~> u}).
    Proof.
      setoid_rewrite (in_free_iff). intros.
      now apply in_subst_lower_neq.
    Qed.

    Corollary freeset_subst_lower_eq : forall t k (u : T k LN) x,
        freeset S k t \\ {{ x }} ⊆ freeset S k (t '{k | x ~> u}).
    Proof.
      introv. intro a. rewrite AtomSet.diff_spec.
      do 2 rewrite <- (free_iff_freeset).
      intros [? ?]. apply in_free_subst_lower_eq.
      intuition.
    Qed.

    Corollary freeset_subst_lower_eq_alt : forall t k (u : T k LN) x,
        freeset S k t ⊆ freeset S k (t '{k | x ~> u}) ∪ {{ x }}.
    Proof.
      introv. intro a. rewrite AtomSet.union_spec.
      do 2 rewrite <- (free_iff_freeset).
      destruct_eq_args a x.
      - right. fsetdec.
      - left. auto using in_free_subst_lower_eq.
    Qed.

    Corollary freeset_subst_lower_neq : forall t k j u x,
        k <> j ->
        freeset S j t ⊆
                freeset S j (t '{k | x ~> u}).
    Proof.
      introv neq. intro a.
      do 2 rewrite <- (free_iff_freeset).
      now apply in_free_subst_lower_neq.
    Qed.

    (** ** Substitution of fresh variables *)
    (******************************************************************************)
    Theorem subst_fresh : forall t k x u,
        ~ x ∈ free S k t ->
        t '{k | x ~> u} = t.
    Proof.
      intros. apply (subst_id S). intros.
      assert (Fr x <> l).
      eapply (ninf_in_neq S); eauto.
      now simpl_local.
    Qed.

    Corollary subst_fresh_set : forall t k x u,
        ~ x ∈@ freeset S k t ->
        t '{k | x ~> u} = t.
    Proof.
      setoid_rewrite <- free_iff_freeset. apply subst_fresh.
    Qed.

    Theorem free_subst_fresh : forall t k j u x,
        ~ x ∈ free S k t ->
        free S j (t '{k | x ~> u}) = free S j t.
    Proof with auto.
      introv fresh. replace (t '{k | x ~> u}) with t...
      rewrite subst_fresh...
    Qed.

    Corollary free_subst_fresh_eq : forall t k u x,
        ~ x ∈ free S k t ->
        free S k (t '{k | x ~> u}) = free S k t.
    Proof.
      introv fresh. replace (t '{k | x ~> u}) with t; auto.
      now rewrite subst_fresh.
    Qed.

    Corollary freeset_subst_fresh : forall t k j u x,
        ~ x ∈@ freeset S k t ->
        freeset S j (t '{k | x ~> u}) [=] freeset S j t.
    Proof.
      introv fresh. intro y.
      rewrite <- ?(free_iff_freeset) in *.
      now rewrite free_subst_fresh.
    Qed.

    Corollary freeset_subst_fresh_eq : forall t k u x,
        ~ x ∈@ freeset S k t ->
        freeset S k (t '{k | x ~> u}) [=] freeset S k t.
    Proof.
      intros. apply freeset_subst_fresh; auto.
    Qed.

  End fix_dtm.

  (** ** Composing substitutions *)
  (******************************************************************************)
  Section fix_dtm.

    Context
      (S : Type -> Type)
      `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
      `{! DTM (list K) T}.

    Implicit Types
             (k : K) (j : K)
             (l : LN) (p : LN)
             (x : atom) (t : S LN)
             (w : list K) (n : nat).

    Lemma subst_subst_neq_loc : forall j k1 k2 (u1 : T k1 LN) (u2 : T k2 LN) (x1 x2 : atom),
        k1 <> k2 ->
        ~ x1 ∈ free (T k2) k1 u2 ->
        subst (T j) k2 x2 u2 ∘ btg T k1 (subst_loc k1 x1 u1) j =
        subst (T j) k1 x1 (subst (T k1) k2 x2 u2 u1) ∘ btg T k2 (subst_loc k2 x2 u2) j.
    Proof with easy.
      intros. ext l. unfold compose. compare j to both of { k1 k2 }.
      - do 2 simpl_tgt_fallback.
        simpl_local.
        compare l to atom x1.
        + rewrite 2(subst_loc_eq)...
        + rewrite subst_loc_neq; auto. now simpl_local.
        + rewrite subst_loc_b. now simpl_local.
      - simpl_tgt. simpl_local. compare l to atom x2.
        + simpl_local. rewrite (subst_fresh (T k2))...
        + simpl_local...
        + simpl_local...
      - simpl_tgt_fallback. now do 2 (rewrite subst_in_mret_neq; auto).
    Qed.

    Theorem subst_subst_neq : forall k1 k2 u1 u2 t (x1 x2 : atom),
        k1 <> k2 ->
        ~ x1 ∈ free (T k2) k1 u2 ->
        t '{k1 | x1 ~> u1} '{k2 | x2 ~> u2} =
        t '{k2 | x2 ~> u2} '{k1 | x1 ~> u1 '{k2 | x2 ~> u2} }.
    Proof.
      intros. unfold subst.
      compose near t on left.
      compose near t on right.
      unfold kbind. rewrite 2(mbind_mbind S).
      fequal. ext j. now apply subst_subst_neq_loc.
    Qed.

    Lemma subst_subst_eq_local : forall k u1 u2 x1 x2,
        ~ x1 ∈ free (T k) k u2 ->
        x1 <> x2 ->
        subst (T k) k x2 u2 ∘ subst_loc k x1 u1 =
        subst (T k) k x1 (subst (T k) k x2 u2 u1) ∘ subst_loc k x2 u2.
    Proof with auto.
      intros. ext l. unfold compose. compare l to atom x1.
      - rewrite subst_loc_eq, subst_loc_neq,
        subst_in_mret_eq, subst_loc_eq...
      - rewrite subst_loc_neq...
        compare values x2 and a.
        + rewrite subst_in_mret_eq, subst_loc_eq, (subst_fresh (T k))...
        + rewrite subst_loc_neq, 2(subst_in_mret_eq), 2(subst_loc_neq)...
      - rewrite 2(subst_loc_b), 2(subst_in_mret_eq), 2(subst_loc_b)...
    Qed.

    Theorem subst_subst_eq : forall k u1 u2 t x1 x2,
        ~ x1 ∈ free (T k) k u2 ->
        x1 <> x2 ->
        t '{k | x1 ~> u1} '{k | x2 ~> u2} =
        t '{k | x2 ~> u2} '{k | x1 ~> u1 '{k | x2 ~> u2} }.
    Proof with auto.
      intros. unfold subst.
      compose near t.
      rewrite 2(kbind_kbind S).
      fequal. now apply subst_subst_eq_local.
    Qed.

    (** ** Commuting two substitutions *)
    (******************************************************************************)
    Corollary subst_subst_comm_eq : forall k u1 u2 t x1 x2,
        x1 <> x2 ->
        ~ x1 ∈ free (T k) k u2 ->
        ~ x2 ∈ free (T k) k u1 ->
        t '{k | x1 ~> u1} '{k | x2 ~> u2} =
        t '{k | x2 ~> u2} '{k | x1 ~> u1}.
    Proof.
      intros. rewrite subst_subst_eq; auto.
      rewrite (subst_fresh (T k)); auto.
    Qed.

    Corollary subst_subst_comm_neq : forall k1 k2 u1 u2 t x1 x2,
        k1 <> k2 ->
        ~ x1 ∈ free (T k2) k1 u2 ->
        ~ x2 ∈ free (T k1) k2 u1 ->
        t '{k1 | x1 ~> u1} '{k2 | x2 ~> u2} =
        t '{k2 | x2 ~> u2} '{k1 | x1 ~> u1}.
    Proof.
      intros. rewrite subst_subst_neq; auto.
      rewrite (subst_fresh (T k1)); auto.
    Qed.

    (** ** Local closure is preserved by substitution *)
    (******************************************************************************)
    Theorem subst_lc_eq : forall k u t x,
        locally_closed S k t ->
        locally_closed (T k) k u ->
        locally_closed S k (subst S k x u t).
    Proof.
      unfold locally_closed. introv lct lcu hin.
      rewrite (ind_subst_iff_eq' S) in hin.
      destruct hin as [[? ?] | [n1 [n2 [h1 [h2 h3]]]]].
      - auto.
      - subst. specialize (lcu n2 l h2).
        unfold is_bound_or_free in *.
        destruct l; auto. unfold_monoid.
        rewrite countk_app. lia.
    Qed.

    Theorem subst_lc_neq : forall k j u t x,
        k <> j ->
        locally_closed S j t ->
        locally_closed (T k) j u ->
        locally_closed S j (subst S k x u t).
    Proof.
      unfold locally_closed. introv neq lct lcu hin.
      rewrite (ind_subst_iff_neq' S) in hin; auto.
      destruct hin as [? | [n1 [n2 [h1 [h2 h3]]]]].
      - auto.
      - subst. specialize (lcu n2 l h2).
        unfold is_bound_or_free in *.
        destruct l; auto. unfold_monoid.
        rewrite countk_app. lia.
    Qed.

    (** ** Decompose substitution into closing/opening *)
    (******************************************************************************)
    Lemma subst_spec_local : forall k u w l x,
        subst_loc k x u l =
        open_loc k u (w, (close_loc k x) (w, l)).
    Proof.
      introv. compare l to atom x; autorewrite* with tea_local.
      - cbn. compare values x and x. unfold id.
        compare naturals (countk k w) and (countk k w).
      - cbn. compare values x and a. (* todo fix fragile names *)
      - cbn. unfold id. compare naturals n and (countk k w).
        compare naturals (Datatypes.S (countk k w)) and (countk k w).
        now compare naturals (Datatypes.S n) and (countk k w).
    Qed.

    Theorem subst_spec : forall k x u t,
        t '{k | x ~> u} = ('[k | x] t) '(k | u).
    Proof.
      intros. compose near t on right.
      unfold open, close, subst.
      rewrite (kbindd_kfmapd S).
      symmetry. apply (kbindd_respectful_kbind k).
      symmetry. apply subst_spec_local.
    Qed.

    (** ** Substitution when <<u>> is a LN **)
    (******************************************************************************)
    Definition subst_loc_LN k x (u : LN) : LN -> LN :=
      fun l => match l with
            | Fr y => if x == y then u else Fr y
            | Bd n => Bd n
            end.

    Theorem subst_by_LN_spec : forall k x l,
        subst S k x (mret T k l) = kfmap S k (subst_loc_LN k x l).
    Proof.
      intros. unfold subst. ext t.
      apply kbind_respectful_kfmap.
      intros l' Hin. destruct l'.
      - cbn. compare values x and a.
      - reflexivity.
    Qed.

    (** ** Substitution by the same variable is the identity *)
    (******************************************************************************)
    Theorem subst_same : forall t k x,
        t '{k | x ~> mret T k (Fr x)} = t.
    Proof.
      intros. apply (subst_id S).
      intros. compare l to atom x; now simpl_local.
    Qed.

  End fix_dtm.

End subst_metatheory.

(** ** Metatheory for <<close>> *)
(******************************************************************************)
Section close_metatheory.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Implicit Types
           (k : K) (j : K)
           (l : LN) (p : LN)
           (x : atom) (t : S LN)
           (w : list K) (n : nat).

  (** ** Free variables after variable closing *)
  (******************************************************************************)
  Lemma in_free_close_iff_loc_1 : forall k w l t x  y,
      (w, k, l) ∈md t ->
      Fr y = close_loc k x (w, l) ->
      (k, Fr y) ∈m t /\ x <> y.
  Proof.
    introv lin heq. destruct l as [la | ln].
    - cbn in heq. destruct_eq_args x la.
      inverts heq. now apply (DTM.ind_implies_in S) in lin.
    - cbn in heq. compare_nats_args ln (countk k w); discriminate.
  Qed.

  Lemma in_free_close_iff_loc_2 : forall t k x y,
      x <> y ->
      (k, Fr y) ∈m t ->
      exists w l, (w, k, l) ∈md t /\ Fr y = close_loc k x (w, l).
  Proof.
    introv neq yin. apply (DTM.ind_iff_in S) in yin. destruct yin as [w yin].
    exists w. exists (Fr y). cbn. compare values x and y.
  Qed.

  Theorem in_free_close_iff : forall k t x y,
      y ∈ free S k ('[k | x] t) <-> y ∈ free S k t /\ x <> y.
  Proof.
    introv. rewrite (free_close_eq_iff S).
    rewrite (in_free_iff). split.
    - introv [? [? [? ?] ] ]. eauto using in_free_close_iff_loc_1.
    - intros [? ?]. eauto using in_free_close_iff_loc_2.
  Qed.

  Corollary in_free_close_iff_1 : forall k t x y,
      y <> x ->
      y ∈ free S k ('[k | x] t) <-> y ∈ free S k t.
  Proof.
    intros. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary freeset_close : forall k t x,
      freeset S k ('[k | x] t) [=] freeset S k t \\ {{ x }}.
  Proof.
    introv. intro a. rewrite AtomSet.diff_spec.
    rewrite <- 2(free_iff_freeset). rewrite in_free_close_iff.
    fsetdec.
  Qed.

  Corollary nin_free_close : forall k t x,
      ~ (x ∈ free S k ('[k | x] t)).
  Proof.
    introv. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary nin_freeset_close : forall k t x,
      ~ (x ∈@ freeset S k ('[k | x] t)).
  Proof.
    introv. rewrite <- free_iff_freeset. apply nin_free_close.
  Qed.

  (** ** Variable closing and local closure *)
  (******************************************************************************)
  Theorem close_lc_eq : forall k t x,
      locally_closed S k t ->
      locally_closed_gap S k 1 (close S k x t).
  Proof.
    unfold locally_closed. introv lct hin.
    rewrite (ind_close_iff_eq S) in hin.
    destruct hin as [l1 [? ?]]. compare l1 to atom x; subst.
    - cbn. compare values x and x. unfold_monoid; lia.
    - cbn. compare values x and a.
    - cbn. compare naturals n and (countk k w).
      + specialize (lct w (Bd (countk k w)) ltac:(assumption)).
        cbn in lct. now unfold_monoid; lia.
      + specialize (lct w (Bd n) ltac:(assumption)).
        cbn in lct. now unfold_monoid; lia.
  Qed.

  Theorem close_lc_neq : forall k j t x,
      k <> j ->
      locally_closed S j t ->
      locally_closed S j (close S k x t).
  Proof.
    unfold locally_closed. introv neq lct hin.
    rewrite (ind_close_neq_iff S) in hin; auto.
  Qed.

End close_metatheory.

(** ** Metatheory for <<open>> *)
(******************************************************************************)
Section open_metatheory.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Implicit Types
           (k : K) (j : K)
           (l : LN) (p : LN)
           (x : atom) (t : S LN)
           (w : list K) (n : nat).

  (** ** Upper and lower bounds on free variables after opening *)
  (******************************************************************************)
  Lemma free_open_upper_local : forall t k j (u : T k LN) w l x,
      (k, l) ∈m t ->
      x ∈ free (T k) j (open_loc k u (w, l)) ->
      k = j /\ l = Fr x /\ x ∈ free S j t \/
      x ∈ free (T k) j u.
  Proof with auto.
    introv lin xin. rewrite in_free_iff in xin.
    rewrite 2(in_free_iff). destruct l as [y | n].
    - left. autorewrite with tea_local in xin. inverts xin...
    - right. cbn in xin. compare naturals n and (countk k w).
      { contradict xin. simpl_local. intuition. }
      { assumption. }
      { contradict xin. simpl_local. intuition. }
  Qed.

  Corollary free_open_upper_local_eq : forall t k (u : T k LN) w l x,
      (k, l) ∈m t ->
      x ∈ free (T k) k (open_loc k u (w, l)) ->
      x ∈ free S k t \/ x ∈ free (T k) k u.
  Proof.
    introv lin xin.
    apply free_open_upper_local
      with (t:=t) in xin; auto.
    intuition.
  Qed.

  Corollary free_open_upper_local_neq : forall t k j (u : T k LN) w l x,
      k <> j ->
      (k, l) ∈m t ->
      x ∈ free (T k) j (open_loc k u (w, l)) ->
      x ∈ free (T k) j u.
  Proof.
    introv neq lin xin.
    apply free_open_upper_local
      with (t:=t) in xin; auto.
    intuition.
  Qed.

  Theorem free_open_upper : forall t k j (u : T k LN) x,
      x ∈ free S j (t '(k | u)) ->
      x ∈ free S j t \/ x ∈ free (T k) j u.
  Proof.
    introv xin. compare values j and k.
    - rewrite (free_open_eq_iff S) in xin.
      destruct xin as [w [l [hin ?]]].
      eapply (DTM.ind_implies_in S) in hin.
      eauto using free_open_upper_local_eq.
    - rewrite (free_open_neq_iff S) in xin; auto.
      destruct xin as  [? |  [w [l [hin ?]]]].
      auto. apply (DTM.ind_implies_in S) in hin.
      right. eauto using free_open_upper_local_neq.
  Qed.

  Corollary freeset_open_upper : forall t k j (u : T k LN),
      freeset S j (t '(k | u)) ⊆ freeset S j t ∪ freeset (T k) j u.
  Proof.
    intros. intro a. rewrite AtomSet.union_spec.
    repeat rewrite <- (free_iff_freeset).
    auto using free_open_upper.
  Qed.

  Corollary free_open_upper_eq : forall t k (u : T k LN) x,
      x ∈ free S k (t '(k | u)) ->
      x ∈ free S k t \/ x ∈ free (T k) k u.
  Proof.
    intros. auto using free_open_upper.
  Qed.

  Corollary freeset_open_upper_eq : forall t k (u : T k LN),
      freeset S k (t '(k | u)) ⊆ freeset S k t ∪ freeset (T k) k u.
  Proof.
    intros. apply freeset_open_upper.
  Qed.

  Theorem free_open_lower : forall t k j u x,
      x ∈ free S j t ->
      x ∈ free S j (t '(k | u)).
  Proof.
    introv xin. compare values j and k.
    - rewrite (in_free_iff) in xin.
      rewrite (DTM.ind_iff_in S) in xin.
      destruct xin as [w xin].
      rewrite (free_open_eq_iff S).
      setoid_rewrite (in_free_iff).
      exists w (Fr x). now autorewrite with tea_local.
    - rewrite (free_open_neq_iff S); auto.
  Qed.

  Theorem free_open_lower_eq : forall t k u x,
      x ∈ free S k t ->
      x ∈ free S k (t '(k | u)).
  Proof.
    intros. auto using free_open_lower.
  Qed.

  Corollary freeset_open_lower : forall t k j u,
      freeset S j t ⊆ freeset S j (t '(k | u)).
  Proof.
    intros. intro a. rewrite <- 2(free_iff_freeset).
    apply free_open_lower.
  Qed.

  Corollary freeset_open_lower_eq : forall t k u,
      freeset S k t ⊆ freeset S k (t '(k | u)).
  Proof.
    intros. apply freeset_open_lower.
  Qed.

  (** ** Opening a locally closed term is the identity *)
  (**************************************************************************)
  Lemma open_lc_local : forall k (u : T k LN) w l,
      is_bound_or_free k 0 (w, l) ->
      open_loc k u (w, l) = mret T k l.
  Proof.
    introv hyp. destruct l as [a | n].
    - reflexivity.
    - cbn in *. compare naturals n and (countk k w); unfold_monoid; lia.
  Qed.

  Lemma open_lc : forall k t u,
      locally_closed S k t ->
      t '(k | u) = t.
  Proof.
    introv lc. apply (open_id S). introv lin.
    specialize (lc _ _ lin).
    destruct l; auto using open_lc_local.
  Qed.

  (** ** Opening followed by substitution *)
  (**************************************************************************)
  Lemma subst_open_eq_loc : forall k u1 u2 x,
      locally_closed (T k) k u2 ->
      subst (T k) k x u2 ∘ open_loc k u1 =
      open_loc k (u1 '{k | x ~> u2}) ⋆kdm (subst_loc k x u2 ∘ snd).
  Proof.
    introv lcu2. ext [w l]. unfold compose_kdm.
    unfold compose. compare l to atom x.
    - cbn. simpl_local. compare values x and x.
      symmetry. apply kbindd_respectful_id. intros ? [?|?] hin.
      + trivial.
      + specialize (lcu2 _ _ hin). cbn in lcu2. cbn. unfold_monoid.
        rewrite countk_app.
        compare naturals n and (countk k w + countk k w0).
    - cbn. simpl_local. compare values x and a.
      now rewrite (kbindd_comp_mret_eq).
    (* <<< TODO standardize this lemma *)
    - cbn. rewrite (kbindd_comp_mret_eq).
      compare naturals n and (countk k w); cbn; simpl_local.
      + rewrite monoid_id_l. compare naturals n and (countk k w).
      + rewrite monoid_id_l. cbn. compare naturals (countk k w) and (countk k w).
      + rewrite monoid_id_l. cbn. compare naturals n and (countk k w).
  Qed.

  Theorem subst_open_eq :  forall k u1 u2 t x,
      locally_closed (T k) k u2 ->
      t '(k | u1) '{k | x ~> u2} =
      t '{k | x ~> u2} '(k | u1 '{k | x ~> u2}).
  Proof.
    introv lc. compose near t.
    unfold open, subst at 1 3.
    rewrite (kbind_kbindd S), (kbindd_kbind S).
    fequal. apply subst_open_eq_loc; auto.
  Qed.

  Theorem subst_open_neq_loc :  forall k1 k2 (u1 : T k1 LN) (u2 : T k2 LN) (x : atom),
      k1 <> k2 ->
      locally_closed (T k2) k1 u2 ->
      (btgd T k2 (subst_loc k2 x u2 ∘ extract (prod (list K)))) ⋆dm btgd T k1 (open_loc k1 u1) =
      (btgd T k1 (open_loc k1 (mbind (T k1) (btg T k2 (subst_loc k2 x u2)) u1))) ⋆dm (btg T k2 (subst_loc k2 x u2) ◻ const (extract (prod (list K)))).
  Proof.
    intros. ext k [w a]. unfold compose_dm.
    replace (btgd T k2 (subst_loc k2 x u2 ∘ extract (prod (list K))) ◻ const (incr w))
      with  (btgd T k2 (subst_loc k2 x u2 ∘ extract (prod (list K)))).
    2:{ ext j [w' a']. cbn. compare values j and k2. }
    change ((btg T k2 (subst_loc k2 x u2) k ∘ const (extract (prod (list K))) k) (w, a))
      with (btg T k2 (subst_loc k2 x u2) k a).
    compare values k and k1.
    - simpl_tgt. compose near a on right.
      rewrite (mbindd_comp_mret k1). simpl_tgt.
      unfold const. destruct a as [y | n].
      { cbn. compose near (Fr y) on left.
        rewrite (mbindd_comp_mret k1). now simpl_tgt. }
      { cbn. simpl_monoid. compare naturals n and (countk k1 w).
        - compose near (Bd n) on left. rewrite (mbindd_comp_mret k1).
          simpl_tgt. reflexivity.
        - rewrite mbind_to_mbindd. fequal. ext j.
          compare values j and k2; now simpl_tgt.
        - compose near (Bd (n - 1)) on left.
          rewrite (mbindd_comp_mret k1). now simpl_tgt. }
    - compare values k and k2.
      { simpl_tgt. unfold compose. cbn. compose near a on left.
        rewrite (mbindd_comp_mret k2). simpl_tgt. compare a to atom x.
        - { rewrite subst_loc_eq. unfold compose. rewrite subst_loc_eq.
            symmetry. apply mbindd_respectful_id. introv Hin.
            compare values k and k1.
            + simpl_tgt. destruct a.
              * reflexivity.
              * cbn. unfold locally_closed, locally_closed_gap, is_bound_or_free in H2.
                specialize (H2 w0 (Bd n) Hin). cbn in H2.
                compare naturals n and (countk k1 (w ● w0)).
                { contradict H2. unfold_monoid. rewrite countk_app. lia. }
                { contradict ineqp. unfold_monoid. rewrite countk_app. lia. }
            + now simpl_tgt. }
        - rewrite subst_loc_fr_neq. 2:{ autorewrite with tea_local; auto. }
          compose near (Fr a) on right. rewrite (mbindd_comp_mret k2).
          simpl_tgt. cbn. compare values x and a.
        - cbn.
          compose near (Bd n) on right. rewrite (mbindd_comp_mret k2).
          now simpl_tgt. }
      { simpl_tgt. unfold compose. cbn. compose near a.
        do 2 rewrite (mbindd_comp_mret k). now simpl_tgt_fallback. }
  Qed.

  Theorem subst_open_neq :  forall k1 k2 (u1 : T k1 LN) (u2 : T k2 LN) (x : atom) (t : S LN),
      k1 <> k2 ->
      locally_closed (T k2) k1 u2 ->
      t '(k1 | u1) '{k2 | x ~> u2} =
      t '{k2 | x ~> u2} '(k1 | u1 '{k2 | x ~> u2}).
  Proof.
    introv neq lc. compose near t.
    unfold subst, open. unfold kbind, kbindd.
    rewrite (mbind_to_mbindd S), (mbindd_mbindd S).
    rewrite (mbindd_mbindd S). fequal.
    pose (lemma := subst_open_neq_loc).
    unfold compose_dm in lemma. setoid_rewrite <- lemma; auto.
    ext k [w a]. fequal. ext j [w' a']. compare values j and k2.
    + rewrite btgd_eq, btg_eq. cbn. reflexivity.
    + rewrite btgd_neq, btg_neq; auto.
  Qed.

  (** ** Decompose opening into variable opening followed by substitution *)
  (**************************************************************************)
  Lemma open_spec_eq_loc : forall k u x w l,
      l <> Fr x ->
      (subst (T k) k x u ∘ open_loc k (mret T k (Fr x))) (w, l) =
      open_loc k u (w, l).
  Proof.
    introv neq. unfold compose. compare l to atom x.
    - contradiction.
    - cbn. rewrite subst_in_mret_eq, subst_loc_fr_neq.
      trivial. intuition.
    - cbn. compare naturals n and (countk k w).
      now rewrite subst_in_mret_eq.
      now rewrite subst_in_mret_eq, subst_loc_eq.
      now rewrite subst_in_mret_eq, subst_loc_b.
  Qed.

  (* This theorem would be easy to prove with [subst_open_eq], but
   applying that theorem would introduce a local closure hypothesis
   for <<u>> that is not actually required for our purposes. *)
  Theorem open_spec_eq : forall k u t x,
      ~ x ∈@ freeset S k t ->
      t '(k | u) = t '(k | mret T k (Fr x)) '{k | x ~> u}.
  Proof.
    introv fresh. compose near t on right.
    unfold subst, open. rewrite (kbind_kbindd S).
    apply (kbindd_respectful). introv Hin.
    assert (a <> Fr x).
    { apply (DTM.ind_implies_in S) in Hin.
      rewrite <- free_iff_freeset in fresh.
      eapply ninf_in_neq in fresh; eauto. }
    now rewrite <- (open_spec_eq_loc k u x).
  Qed.

  (** ** Opening by a variable, followed by non-equal substitution *)
  (**************************************************************************)
  Lemma subst_open_var_loc : forall k u x y,
      x <> y ->
      locally_closed (T k) k u ->
      subst (T k) k x u ∘ open_loc k (mret T k (Fr y)) =
      open_loc k (mret T k (Fr y)) ⋆kdm (subst_loc k x u ∘ extract (prod (list K))).
  Proof with auto.
    introv neq lc. rewrite subst_open_eq_loc...
    simpl_local. reflexivity.
  Qed.

  Theorem subst_open_var : forall k u t x y,
      x <> y ->
      locally_closed (T k) k u ->
      t '(k | mret T k (Fr y)) '{k | x ~> u} =
      t '{k | x ~> u} '(k | mret T k (Fr y)).
  Proof.
    introv neq lc. compose near t.
    unfold open, subst.
    rewrite (kbind_kbindd S), (kbindd_kbind S).
    fequal. apply subst_open_var_loc; auto.
  Qed.

  (** ** Closing, followed by opening *)
  (**************************************************************************)
  Lemma open_close_loc : forall k x w l,
      (open_loc k (mret T k (Fr x)) ∘ cobind (prod (list K))
                (close_loc k x)) (w, l) = mret T k l.
  Proof.
    intros. cbn. unfold id. compare l to atom x.
    - compare values x and x. compare naturals (countk k w) and (countk k w).
    - compare values x and a.
    - compare naturals n and (countk k w).
      compare naturals (Datatypes.S (countk k w)) and (countk k w).
      compare naturals (Datatypes.S n) and (countk k w).
  Qed.

  Theorem open_close : forall k x t,
      ('[k | x] t) '(k | mret T k (Fr x)) = t.
  Proof.
    intros. compose near t on left.
    unfold open, close.
    rewrite (kbindd_kfmapd S).
    apply (kbindd_respectful_id); intros.
    apply open_close_loc.
  Qed.

  (** ** Opening by a LN reduces to an [kfmapd] *)
  (**************************************************************************)
  Definition open_LN_loc k (u : LN) : list K * LN -> LN :=
    fun wl =>
      match wl with
      | (w, l) =>
        match l with
        | Fr x => Fr x
        | Bd n =>
          match Nat.compare n (countk k w) with
          | Gt => Bd (n - 1)
          | Eq => u
          | Lt => Bd n
          end
        end
      end.

  Lemma open_by_LN_spec : forall k l,
      open S k (mret T k l) = kfmapd S k (open_LN_loc k l).
  Proof.
    intros. unfold open. ext t.
    apply (kbindd_respectful_kfmapd).
    intros w l' l'in. destruct l'.
    - reflexivity.
    - cbn. compare naturals n and (countk k w).
  Qed.

  (** ** Opening, followed by closing *)
  (**************************************************************************)
  Lemma close_open_local : forall k x w l,
      l <> Fr x ->
      (close_loc k x ∘ cobind (prod (list K))
                 (open_LN_loc k (Fr x))) (w, l) = l.
  Proof.
    introv neq. cbn. unfold id. compare l to atom x.
    - contradiction.
    - unfold compose; cbn. now compare values x and a.
    - unfold compose; cbn.
      compare naturals n and (countk k w). compare values x and x.
      compare naturals (n - 1) and (countk k w).
  Qed.

  Theorem close_open : forall k x t,
      ~ x ∈ free S k t ->
      '[k | x] (t '(k | mret T k (Fr x))) = t.
  Proof.
    introv fresh. compose near t on left.
    rewrite open_by_LN_spec. unfold close.
    rewrite (kfmapd_kfmapd S).
    apply (kfmapd_respectful_id).
    intros w l lin.
    assert (l <> Fr x).
    { rewrite neq_symmetry. apply (DTM.ind_implies_in) in lin.
      eapply (ninf_in_neq S). eassumption. auto. }
    now apply close_open_local.
  Qed.

  (** ** Opening and local closure *)
  (**************************************************************************)
  Lemma open_lc_gap_eq_1 : forall k n t u,
      locally_closed (T k) k u ->
      locally_closed_gap S k n t ->
      locally_closed_gap S k (n - 1) (t '(k | u)).
  Proof.
    unfold locally_closed_gap.
    introv lcu lct Hin. rewrite (ind_open_iff_eq S) in Hin.
    destruct Hin as [w1 [w2 [l1 [h1 [h2 h3]]]]].
    destruct l1.
    - cbn in h2. rewrite ind_mret_eq_iff in h2.
      destruct h2; subst. cbn. trivial.
    - specialize (lct _ _ h1). cbn in h2. compare naturals n0 and (countk k w1).
      + rewrite ind_mret_eq_iff in h2; destruct h2; subst.
        cbn. unfold_monoid. List.simpl_list. lia.
      + specialize (lcu w2 l h2). unfold is_bound_or_free in *.
        destruct l; [trivial|]. unfold_monoid. rewrite countk_app. lia.
      + rewrite ind_mret_eq_iff in h2. destruct h2; subst.
        unfold is_bound_or_free in *. unfold_monoid. List.simpl_list. lia.
  Qed.

  Lemma open_lc_gap_eq_2 : forall k n t u,
      n > 0 ->
      locally_closed (T k) k u ->
      locally_closed_gap S k (n - 1) (t '(k | u)) ->
      locally_closed_gap S k n t.
  Proof.
    unfold locally_closed_gap.
    introv ngt lcu lct Hin. setoid_rewrite (ind_open_iff_eq S) in lct.
    destruct l.
    - cbv. trivial.
    - compare naturals n0 and (countk k w).
      + specialize (lct w (Bd n0)).
        lapply lct.
        { cbn; unfold_monoid; lia. }
        { exists w (Ƶ : list K) (Bd n0).
          split; auto. cbn. compare naturals n0 and (countk k w).
          rewrite ind_mret_eq_iff. now simpl_monoid. }
      + cbn. unfold_monoid; lia.
      + cbn. specialize (lct w (Bd (n0 - 1))).
        lapply lct.
        { cbn; unfold_monoid; lia. }
        { exists w (Ƶ : list K) (Bd n0).
          split; auto. cbn. compare naturals n0 and (countk k w).
          rewrite ind_mret_eq_iff. now simpl_monoid. }
  Qed.

  Theorem open_lc_gap_eq_iff : forall k n t u,
      n > 0 ->
      locally_closed (T k) k u ->
      locally_closed_gap S k n t <->
      locally_closed_gap S k (n - 1) (t '(k | u)).
  Proof.
    intros; intuition (eauto using open_lc_gap_eq_1, open_lc_gap_eq_2).
  Qed.

  Corollary open_lc_gap_eq_var : forall k n t x,
      n > 0 ->
      locally_closed_gap S k n t <->
      locally_closed_gap S k (n - 1) (t '(k | mret T k (Fr x))).
  Proof.
    intros. apply open_lc_gap_eq_iff. auto.
    intros w l hin. rewrite ind_mret_eq_iff in hin.
    destruct hin; subst. cbv. trivial.
  Qed.

  Corollary open_lc_gap_eq_iff_1 : forall k t u,
      locally_closed (T k) k u ->
      locally_closed_gap S k 1 t <->
      locally_closed S k (t '(k | u)).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_iff; auto.
    reflexivity.
  Qed.

  Corollary open_lc_gap_eq_var_1 : forall k t x,
      locally_closed_gap S k 1 t <->
      locally_closed S k (t '(k | mret T k (Fr x))).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_var; auto.
    reflexivity.
  Qed.

  Lemma open_lc_gap_neq_1 : forall k j n t u,
      k <> j ->
      locally_closed (T j) k u ->
      locally_closed_gap S k n t ->
      locally_closed_gap S k n (t '(j | u)).
  Proof.
    unfold locally_closed_gap.
    introv neq lcu lct Hin.
    rewrite (ind_open_neq_iff S) in Hin; auto.
    destruct Hin as [Hin | Hin].
    - auto.
    - destruct Hin as [w1 [w2 [l1 [in_t [in_open ?]]]]].
      subst. destruct l1.
      + cbn in in_open. rewrite ind_mret_iff in in_open.
        false. intuition.
      + destruct l.
        { cbn. trivial. }
        { cbn. cbn in in_open.
          compare naturals n0 and (countk j w1).
          - rewrite ind_mret_iff in in_open. false; intuition.
          - specialize (lcu _ _ in_open).
            unfold is_bound_or_free in lcu. unfold_monoid.
            rewrite countk_app. lia.
          - rewrite ind_mret_iff in in_open. false; intuition.
        }
  Qed.

  Lemma open_lc_gap_neq_2 : forall k j n t u,
      k <> j ->
      locally_closed (T j) k u ->
      locally_closed_gap S k n (t '(j | u)) ->
      locally_closed_gap S k n t.
  Proof.
    unfold locally_closed_gap.
    introv neq lcu lct Hin.
    destruct l.
    + cbn. auto.
    + specialize (lct w (Bd n0)).
      apply lct. rewrite (ind_open_neq_iff S); auto.
  Qed.

  Theorem open_lc_gap_neq_iff : forall k j n t u,
      k <> j ->
      locally_closed (T j) k u ->
      locally_closed_gap S k n t <->
      locally_closed_gap S k n (t '(j | u)).
  Proof.
    intros. intuition (eauto using open_lc_gap_neq_1, open_lc_gap_neq_2).
  Qed.

  Corollary open_lc_gap_neq_var : forall k j t x,
      k <> j ->
      locally_closed S k t <->
      locally_closed S k (t '(j | mret T j (Fr x))).
  Proof.
    intros. unfold locally_closed.
    rewrite open_lc_gap_neq_iff; eauto.
    reflexivity. unfold locally_closed, locally_closed_gap.
    setoid_rewrite ind_mret_iff. intuition.
  Qed.

End open_metatheory.
