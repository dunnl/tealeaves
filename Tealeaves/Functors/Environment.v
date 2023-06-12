From Tealeaves Require Export
  Definitions.Product
  Definitions.Strength
  Classes.Comonoid
  Classes.Comonad.

Import Product.Notations.
Import Strength.Notations.

(** * Environment comonad (a/k/a "Reader" or "co-Reader") *)
(******************************************************************************)
Section comonad.

  Context
    (E : Type).

  #[export] Instance Extract_env : Extract (E ×) :=
    fun A '(e, a) => a.

  #[export] Instance Cobind_env : Cobind (E ×) :=
    fun A B (f : E * A -> B) '(e, a) => (e, f (e, a)).

  #[export, program] Instance Comonad_prod : Comonad (E ×).

  Solve All Obligations with (introv; now ext [? ?]).

End comonad.

#[export] Instance Map_Env (E : Type) : Map (E ×) :=
  Comonad.DerivedInstances.Map_Cobind (E ×).

#[export] Instance Functor_Env (E : Type) : Functor (E ×) :=
  Comonad.DerivedInstances.Functor_Comonad (E ×).

Lemma map_to_cobind {E} : forall A B (f : A -> B),
    map (E ×) f = cobind (E ×) A B (f ∘ extract (E ×) A).
Proof.
  reflexivity.
Qed.
