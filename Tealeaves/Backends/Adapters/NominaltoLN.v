From Tealeaves Require Import
  Classes.Kleisli.DecoratedFunctorPoly
  Backends.Nominal.Common.Binding
  Backends.LN.LN.

(** * Nominal to Locally Translation *)
(********************************************************************)
Section with_DTM.

  Context
    {T: Type -> Type -> Type}.

  Definition binding_to_ln: Binding -> LN :=
    fun b =>
      match b with
      | Bound prefix var postfix =>
          Bd (length postfix)
      | Unbound context var =>
          Fr var
      end.

  Definition nomToLN_loc:
    list name * name -> LN.
  Proof.
    intros [ctx x].
    exact (binding_to_ln (get_binding ctx x)).
  Defined.

  Definition nomToLN `{MapdPoly T}:
    T name name -> T unit LN :=
    mapdp (T := T) (const tt) nomToLN_loc.

End with_DTM.
