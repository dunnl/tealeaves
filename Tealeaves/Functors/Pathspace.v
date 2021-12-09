(** This file defines the pathspace functor which maps a type <<A>> to
    the set of proofs of equality between any two terms of <<A>>. *)

From Tealeaves Require Export
     Classes.Applicative.

#[local] Open Scope tealeaves_scope.

(** * Pathspace applicative functor *)
(******************************************************************************)
Inductive PathSpace (A : Type) : Type :=
| path : forall (x y : A), x = y -> PathSpace A.

Instance Fmap_Path : Fmap PathSpace :=
  fun A B (f : A -> B) '(@path _ x y p)
  => @path _ (f x) (f y) (ltac:(subst; auto)).

#[program] Instance Path_End : Functor PathSpace.

Solve All Obligations with
    (intros; ext [? ?]; now destruct e).

Instance Pure_Path : Pure PathSpace :=
  fun (A : Type) (a : A) => @path A a a eq_refl.

Instance Path_Mult : Mult PathSpace :=
  ltac:(refine (fun A B '(@path _ a1 a2 eqa, @path _ b1 b2 eqb) =>
                  @path _ (a1, b1) (a2, b2) _); subst; reflexivity).

#[program] Instance App_Path : Applicative PathSpace.

Solve All Obligations with
    (intros; now repeat (match goal with
                         | x : PathSpace ?A |- _ =>
                           destruct x; subst end)).
