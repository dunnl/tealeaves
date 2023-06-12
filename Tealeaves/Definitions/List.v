From Tealeaves Require Import
  Classes.Monoid
  Classes.Functor.

Import List.ListNotations.
Import Monoid.Notations.
Open Scope list_scope.

#[local] Generalizable Variables A B M.

(** * [list] monoid *)
(******************************************************************************)
#[export] Instance Monoid_op_list {A} : Monoid_op (list A) := @app A.

#[export] Instance Monoid_unit_list {A} : Monoid_unit (list A) := nil.

#[export, program] Instance Monoid_list {A} :
  @Monoid (list A) (@Monoid_op_list A) (@Monoid_unit_list A).

Solve Obligations with (intros; unfold transparent tcs; auto with datatypes).

(** * Folding over lists *)
(******************************************************************************)
Fixpoint fold `{op : Monoid_op M} `{unit : Monoid_unit M} (l : list M) : M :=
  match l with
  | nil => Ƶ
  | cons x l' => x ● fold l'
  end.

(** ** Rewriting lemmas for [fold] *)
(******************************************************************************)
Section fold_rewriting_lemmas.

  Context
    `{Monoid M}.

  Lemma fold_nil : fold (@nil M) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_cons : forall (m : M) (l : list M),
      fold (m :: l) = m ● fold l.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_one : forall (m : M), fold [ m ] = m.
  Proof.
    intro. cbn. now simpl_monoid.
  Qed.

  Lemma fold_app : forall (l1 l2 : list M),
      fold (l1 ++ l2) = fold l1 ● fold l2.
  Proof.
    intros l1 ?. induction l1 as [| ? ? IHl].
    - cbn. now simpl_monoid.
    - cbn. rewrite IHl. now simpl_monoid.
  Qed.

End fold_rewriting_lemmas.

(** * Filtering lists *)
(******************************************************************************)
Fixpoint filter `(P : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons a rest =>
    if P a then a :: filter P rest else filter P rest
  end.

(** ** Folding a list is a monoid homomorphism *)
(** <<fold : list M -> M>> is homomorphism of monoids. *)
(******************************************************************************)
#[export] Instance Monmor_fold `{Monoid M} : Monoid_Morphism fold :=
  {| monmor_unit := fold_nil;
     monmor_op := fold_app |}.

(** ** Rewriting lemmas for [filter] *)
(******************************************************************************)
Section filter_lemmas.

  Context
    `(P : A -> bool).

  Lemma filter_nil :
    filter P nil = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_cons : forall (a : A) (l : list A),
      filter P (a :: l) = if P a then a :: filter P l else filter P l.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_one : forall (a : A),
      filter P [a] = if P a then [a] else nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_app : forall (l1 l2 : list A),
      filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
  Proof.
    intros. induction l1.
    - reflexivity.
    - cbn. rewrite IHl1. now destruct (P a).
  Qed.

End filter_lemmas.

#[export] Hint Rewrite @filter_nil @filter_cons @filter_app @filter_one : tea_list.
