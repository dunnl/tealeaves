From Tealeaves Require Export
  Classes.Algebraic.Monad.

#[local] Generalizable Variables T.

(** * The identity monad *)
(******************************************************************************)
#[export] Instance Return_I : Return (fun A => A) := (fun A (a : A) => a).

#[export] Instance Join_I : Join (fun A => A) := (fun A (a : A) => a).

#[export, program] Instance Monad_I : Monad (fun A => A).

Solve All Obligations with
  (constructor; try typeclasses eauto; intros; now ext t).

(** * Miscellaneous properties *)
(******************************************************************************)
Section tensor_laws.

  Context
    `{Monad T}
    {W : Type}.

  Theorem strength_return  {A B} (a : A) (b : B) :
    strength T (b, ret T a) = ret T (b, a).
  Proof.
    unfold strength. compose near a on left.
    change (@compose ?B) with (@compose ((fun A => A) B)).
    now rewrite natural.
  Qed.

End tensor_laws.
