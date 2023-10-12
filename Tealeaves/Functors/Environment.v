From Tealeaves Require Export
  Misc.Product
  Misc.Strength
  Classes.Comonoid
  Classes.Kleisli.Comonad.

Import Product.Notations.

(** * Environment comonad (a/k/a "Reader") *)
(******************************************************************************)

(** ** Kleisli instance *)
(******************************************************************************)
Section with_E.

  Context
    (E : Type).

  #[export] Instance Extract_env : Extract (E ×) :=
    fun A '(e, a) => a.

  #[export] Instance Cobind_env : Cobind (E ×) :=
    fun A B (f : E * A -> B) '(e, a) => (e, f (e, a)).

  #[export, program] Instance KleisliComonad_prod : Kleisli.Comonad.Comonad (E ×).

  Solve All Obligations with (introv; now ext [? ?]).

  #[export] Instance Map_Env : Map (E ×) :=
    Comonad.DerivedInstances.Map_Cobind (E ×).

  #[export] Instance Functor_Env : Functor (E ×) :=
    Comonad.DerivedInstances.Functor_Comonad (E ×).

  Lemma map_to_cobind : forall A B (f : A -> B),
      map (E ×) f = cobind (E ×) (f ∘ extract (E ×) A).
  Proof.
    reflexivity.
  Qed.

End with_E.
