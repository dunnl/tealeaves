From Tealeaves Require Import
  Classes.Monoid
  Misc.Prop.

#[local] Generalizable Variables A B.

(** * Subsets *)
(******************************************************************************)
#[local] Notation "( -> B )" := (fun A => A -> B) (at level 50).
#[local] Notation "'subset'" := ((-> Prop)).

(** ** Operations *)
(******************************************************************************)
Definition subset_one {A}: A -> subset A := eq.

Definition subset_empty {A}: subset A :=
  const False.

Definition subset_add {A}: subset A -> subset A -> subset A :=
  fun x y p => x p \/ y p.

(** ** Notations and tactics *)
(******************************************************************************)
Module Notations.
  Notation "∅" := subset_empty: tealeaves_scope.
  Notation "{{ x }}" := (subset_one x): tealeaves_scope.
  Infix "∪" := subset_add (at level 61, left associativity): tealeaves_scope.
  Notation "( -> B )" := (fun A => A -> B) (at level 50): tealeaves_scope.
  Notation "'subset'" := ((-> Prop)): tealeaves_scope.
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
    {A: Type}.

  Implicit Types (s t: subset A) (a: A).

  Definition subset_add_nil_l: forall s, s ∪ ∅ = s :=
    ltac:(solve_basic_subset).
  Definition subset_add_nil_r: forall s, ∅ ∪ s = s :=
    ltac:(solve_basic_subset).
  Definition subset_add_assoc: forall s t u, s ∪ t ∪ u = s ∪ (t ∪ u) :=
    ltac:(solve_basic_subset).
  Definition subset_add_comm: forall s t, s ∪ t = t ∪ s :=
    ltac:(solve_basic_subset).

  Definition subset_in_empty: forall a, ∅ a = False
    := ltac:(solve_basic_subset).
  Definition subset_in_add: forall s t a, (s ∪ t) a = (s a \/ t a)
    := ltac:(solve_basic_subset).

End subset_monoid.

#[export] Hint Rewrite @subset_add_nil_l @subset_add_nil_r
     @subset_add_assoc @subset_in_empty @subset_in_add: tea_set.

#[export] Instance Monoid_op_subset {A}: Monoid_op (subset A) := @subset_add A.

#[export] Instance Monoid_unit_subset {A}: Monoid_unit (subset A) := subset_empty.

#[export, program] Instance Monoid_subset {A} :
  @Monoid (subset A) (@Monoid_op_subset A) (@Monoid_unit_subset A).

Solve Obligations with (intros; unfold transparent tcs; solve_basic_subset).

(** *** Querying for an element is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_el {A: Type} (a: A) :
  @Monoid_Morphism (subset A) Prop
    (@Monoid_op_subset A) (@Monoid_unit_subset A)
    (Monoid_op_or) (Monoid_unit_false)
    (evalAt a).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - reflexivity.
  - reflexivity.
Qed.
