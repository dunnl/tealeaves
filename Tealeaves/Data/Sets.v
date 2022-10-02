From Tealeaves Require Import
  Util.Prelude
  Classes.Monoid.

#[local] Generalizable Variables A B.

(** * Sets *)
(******************************************************************************)
#[local] Notation "( -> B )" := (fun A => A -> B) (at level 50).
#[local] Notation "'set'" := ((-> Prop)).

(** ** Operations *)
(******************************************************************************)
Definition set_one {A} : A -> set A := eq.

Definition set_empty {A} : set A :=
  const False.

Definition set_add {A} : set A -> set A -> set A :=
  fun x y p => x p \/ y p.

(** ** Notations and tactics *)
(******************************************************************************)
Module Notations.
  Notation "∅" := set_empty : tealeaves_scope.
  Notation "{{ x }}" := (set_one x) : tealeaves_scope.
  Infix "∪" := set_add (at level 61, left associativity) : tealeaves_scope.
  Notation "( -> B )" := (fun A => A -> B) (at level 50) : tealeaves_scope.
  Notation "'set'" := ((-> Prop)) : tealeaves_scope.
End Notations.

Import Notations.

Create HintDb tea_set.
Tactic Notation "simpl_set" := (autorewrite with tea_set).
Tactic Notation "simpl_set" "in" hyp(H) := (autorewrite with tea_set H).
Tactic Notation "simpl_set" "in" "*" := (autorewrite with tea_set in *).

Ltac unfold_set :=
  unfold set_empty; unfold set_add; unfold const.

Ltac solve_basic_set :=
  unfold transparent tcs; unfold_set; unfold compose; try setext;
  first [tauto | firstorder (subst; (solve auto + eauto)) ].

(** ** Set monoid instance *)
(******************************************************************************)
Section set_monoid.

  Context
    {A : Type}.

  Implicit Types (s t : set A) (a : A).

  Definition set_add_nil_l : forall s, s ∪ ∅ = s :=
    ltac:(solve_basic_set).
  Definition set_add_nil_r : forall s, ∅ ∪ s = s :=
    ltac:(solve_basic_set).
  Definition set_add_assoc : forall s t u, s ∪ t ∪ u = s ∪ (t ∪ u) :=
    ltac:(solve_basic_set).
  Definition set_add_comm : forall s t, s ∪ t = t ∪ s :=
    ltac:(solve_basic_set).

  Definition set_in_empty : forall a, ∅ a = False
    := ltac:(solve_basic_set).
  Definition set_in_add : forall s t a, (s ∪ t) a = (s a \/ t a)
    := ltac:(solve_basic_set).

End set_monoid.

#[export] Hint Rewrite @set_add_nil_l @set_add_nil_r
     @set_add_assoc @set_in_empty @set_in_add : tea_set.

#[export] Instance Monoid_op_set {A} : Monoid_op (set A) := @set_add A.

#[export] Instance Monoid_unit_set {A} : Monoid_unit (set A) := set_empty.

#[export, program] Instance Monoid_set {A} :
  @Monoid (set A) (@Monoid_op_set A) (@Monoid_unit_set A).

Solve Obligations with (intros; unfold transparent tcs; solve_basic_set).
