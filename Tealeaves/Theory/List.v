From Tealeaves Require Export
  Theory.Traversable.Monad
  Functors.List.

From Coq Require Import
  Sorting.Permutation.

Import List.ListNotations.
Import Monoid.Notations.
Import Sets.Notations.
Import Applicative.Notations.

Create HintDb tea_list.

#[local] Generalizable Variables M A B G ϕ.
#[local] Arguments bindt T {U}%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(*
(** * [list] is set-like *)
(** A [list] can be reduced to a [set] by discarding the ordering, or more
    concretely by applying [List.In]. This makes [list] into a quantifiable
    monad. The lemmas involved in proving this fact form a key step in proving
    that all listables are quantifiable, below. *)
(******************************************************************************)
#[export] Instance El_list : El list :=
  fun (A : Type) (l : list A) (a : A) => List.In a l.

#[local] Arguments el F%function_scope {El} {A}%type_scope.
*)

#[local] Arguments el F%function_scope {El} {A}%type_scope _ _.

(** ** Rewriting lemmas for <<toset>>\<<∈>>*)
(******************************************************************************)
Lemma toset_list_nil : forall A, el list (@nil A) = ∅.
Proof.
  reflexivity.
Qed.

Lemma toset_list_cons : forall A (x : A) (xs : list A),
    el list (x :: xs) = {{x}} ∪ el list xs.
Proof.
  intros. cbn.
  unfold_ops @Monoid_op_set.
  unfold_ops @Pure_const.
  unfold_ops @Map_const.
  unfold compose.
  solve_basic_set.
Qed.

Lemma toset_list_one : forall A (a : A), el list [ a ] = ret set A a.
Proof.
  intros. ext b; propext; cbv; intuition.
Qed.

Lemma toset_list_ret : forall A (a : A), el list (ret list A a) = ret set A a.
Proof.
  intros. ext b; propext; cbv; intuition.
Qed.

Lemma toset_list_app : forall A (l1 l2 : list A),
    el list (l1 ++ l2) = el list l1 ∪ el list l2.
Proof.
  intros. ext b.
  unfold_ops @Toset_Traverse.
Admitted.

#[export] Hint Rewrite toset_list_nil toset_list_cons
     toset_list_one toset_list_ret toset_list_app : tea_list.

Import Sets.ElNotations.

Lemma in_list_nil {A} : forall (p : A), p ∈ @nil A <-> False.
Proof.
  reflexivity.
Qed.

Lemma in_list_cons {A} : forall (a1 a2 : A) (xs : list A),
    a1 ∈ (a2 :: xs) <-> a1 = a2 \/ a1 ∈ xs.
Proof.
  intros; simpl_list. unfold_set. intuition congruence.
Qed.

Lemma in_list_one {A} (a1 a2 : A) : a1 ∈ [ a2 ] <-> a1 = a2.
Proof.
  intros. simpl_list. simpl_set. intuition congruence.
Qed.

Lemma in_list_ret {A} (a1 a2 : A) : a1 ∈ ret list A a2 <-> a1 = a2.
Proof.
  intros. simpl_list. intuition.
Qed.

Lemma in_list_app {A} : forall (a : A) (xs ys : list A),
    a ∈ (xs ++ ys) <-> a ∈ xs \/ a ∈ ys.
Proof.
  intros. simpl_list. simpl_set. reflexivity.
Qed.

#[export] Hint Rewrite @in_list_nil @in_list_cons
     @in_list_one @in_list_ret @in_list_app : tea_list.

Theorem perm_set_eq : forall {A} {l1 l2 : list A},
    Permutation l1 l2 -> (forall a, a ∈ l1 <-> a ∈ l2).
Proof.
  introv perm. induction perm; firstorder.
Qed.

(** ** [toset] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_toset_list (A : Type) : Monoid_Morphism (el list (A := A)) :=
  {| monmor_unit := @toset_list_nil A;
     monmor_op := @toset_list_app A;
  |}.

(** ** Respectfulness conditions *)
(******************************************************************************)
#[export] Instance Natural_toset_list: Natural (@el list _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold compose. ext l. induction l.
  - simpl_list.
    simpl_set.
    autorewrite with tea_set.
    reflexivity.
  - simpl_list.
    simpl_set.
    now rewrite IHl.
Qed.

Theorem map_rigidly_respectful_list : forall A B (f g : A -> B) (l : list A),
    (forall (a : A), a ∈ l -> f a = g a) <-> map list f l = map list g l.
Proof.
  intros. induction l.
  - simpl_list. setoid_rewrite set_in_empty. tauto.
  - simpl_list. setoid_rewrite set_in_add.
    setoid_rewrite set_in_ret.
    destruct IHl. split.
    + intro; fequal; auto.
    + injection 1; intuition (subst; auto).
Qed.

Corollary map_respectful_list : forall A B (l : list A) (f g : A -> B),
    (forall (a : A), a ∈ l -> f a = g a) -> map list f l = map list g l.
Proof.
  intros. now rewrite <- map_rigidly_respectful_list.
Qed.
