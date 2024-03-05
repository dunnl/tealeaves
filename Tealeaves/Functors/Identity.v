From Tealeaves Require Export
  Classes.Functor.

(** * The identity functor *)
(******************************************************************************)
#[export] Instance Map_I : Map (fun A => A) :=
  fun (A B : Type) (f : A -> B) => f.

#[program, export] Instance Functor_I : Functor (fun A => A).

Next Obligation.
  unfold_ops @Map_I.
  unfold Proper.
  intros f g.
  auto.
Qed.

Next Obligation.
  unfold_ops @Map_I.
  cbv.
  auto.
Qed.

Next Obligation.
  unfold_ops @Map_I.
  intros x y Heq.
  unfold compose.
  rewrite Heq.
  reflexivity.
Qed.
