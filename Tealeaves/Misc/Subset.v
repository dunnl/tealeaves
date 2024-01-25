From Tealeaves Require Import
  Classes.Monoid
  Classes.Functor.

#[local] Generalizable Variables A B.

(** * Subsets *)
(******************************************************************************)
#[local] Notation "( -> B )" := (fun A => A -> B) (at level 50).
#[local] Notation "'subset'" := ((-> Prop)).

(** ** Operations *)
(******************************************************************************)
Definition subset_one {A} : A -> subset A := eq.

Definition subset_empty {A} : subset A :=
  const False.

Definition subset_add {A} : subset A -> subset A -> subset A :=
  fun x y p => x p \/ y p.

(** ** Notations and tactics *)
(******************************************************************************)
Module Notations.
  Notation "∅" := subset_empty : tealeaves_scope.
  Notation "{{ x }}" := (subset_one x) : tealeaves_scope.
  Infix "∪" := subset_add (at level 61, left associativity) : tealeaves_scope.
  Notation "( -> B )" := (fun A => A -> B) (at level 50) : tealeaves_scope.
  Notation "'subset'" := ((-> Prop)) : tealeaves_scope.
End Notations.

Import Notations.

Tactic Notation "simpl_subset" := (autorewrite with tea_set).
Tactic Notation "simpl_subset" "in" hyp(H) := (autorewrite with tea_set H).
Tactic Notation "simpl_subset" "in" "*" := (autorewrite with tea_set in *).

Ltac unfold_subset :=
  unfold subset_empty; unfold subset_add; unfold const.

Ltac solve_basic_subset :=
  unfold transparent tcs; unfold_subset; unfold compose; try setext;
  first [tauto | firstorder (subst; (solve auto + eauto)) ].

(** ** Subset monoid instance *)
(******************************************************************************)
Section subset_monoid.

  Context
    {A : Type}.

  Implicit Types (s t : subset A) (a : A).

  Definition subset_add_nil_l : forall s, s ∪ ∅ = s :=
    ltac:(solve_basic_subset).
  Definition subset_add_nil_r : forall s, ∅ ∪ s = s :=
    ltac:(solve_basic_subset).
  Definition subset_add_assoc : forall s t u, s ∪ t ∪ u = s ∪ (t ∪ u) :=
    ltac:(solve_basic_subset).
  Definition subset_add_comm : forall s t, s ∪ t = t ∪ s :=
    ltac:(solve_basic_subset).

  Definition subset_in_empty : forall a, ∅ a = False
    := ltac:(solve_basic_subset).
  Definition subset_in_add : forall s t a, (s ∪ t) a = (s a \/ t a)
    := ltac:(solve_basic_subset).

End subset_monoid.

#[export] Hint Rewrite @subset_add_nil_l @subset_add_nil_r
     @subset_add_assoc @subset_in_empty @subset_in_add : tea_set.

#[export] Instance Monoid_op_subset {A} : Monoid_op (subset A) := @subset_add A.

#[export] Instance Monoid_unit_subset {A} : Monoid_unit (subset A) := subset_empty.

#[export, program] Instance Monoid_subset {A} :
  @Monoid (subset A) (@Monoid_op_subset A) (@Monoid_unit_subset A).

Solve Obligations with (intros; unfold transparent tcs; solve_basic_subset).

(** * The <<subset>> functor *)
(******************************************************************************)

(** ** Functor instance *)
(******************************************************************************)
#[export] Instance Map_subset : Map subset :=
  fun A B f s b => exists (a : A), s a /\ f a = b.

(** *** Rewriting rules *)
(******************************************************************************)
Definition map_set_nil `{f : A -> B} :
  map f ∅ = ∅ := ltac:(solve_basic_subset).

Lemma map_set_one `{f : A -> B} {a : A} :
  map f {{ a }} = {{ f a }}.
Proof.
  ext b. propext.
  - intros [a' [Hin Heq]].
    cbv in Hin; subst.
    solve_basic_subset.
  - cbv. intro; subst.
    eauto.
Qed.

Definition map_set_add `{f : A -> B} {x y} :
  map f (x ∪ y) = map f x ∪ map f y
  := ltac:(solve_basic_subset).

#[export] Hint Rewrite
  @map_set_nil  @map_set_one  @map_set_add
  : tea_set.

(** *** Functor laws *)
(******************************************************************************)
Lemma map_subset_id : forall (A : Type), map id = id (A := subset A).
Proof.
  intros. ext s a.
  cbv. propext.
  - intros [a' [Hin Heq]]. now subst.
  - intros H. eauto.
Qed.

Lemma map_subset_compose : forall (A B C : Type) (f : A -> B) (g : B -> C),
    map g ∘ map f = map (F := subset) (g ∘ f).
Proof.
  intros. ext s c.
  unfold compose. cbv.
  propext.
  - intros [b [[a [Hina Heqa]] Heq]].
    exists a. rewrite Heqa. eauto.
  - intros [a [Hin Heq]]. eauto.
Qed.

#[export] Instance Functor_subset : Functor subset :=
  {| fun_map_id := map_subset_id;
     fun_map_map := map_subset_compose;
  |}.
