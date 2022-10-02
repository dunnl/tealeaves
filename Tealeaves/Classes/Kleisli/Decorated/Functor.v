From Tealeaves Require Export
  Classes.Algebraic.Comonad
  Functors.Environment.

Import Product.Notations.

(** * Operation <<fmapdt>> *)
(******************************************************************************)
Section operations.

  Context
    (E : Type)
    (F : Type -> Type).

  Class Fmapd :=
    fmapd : forall {A B : Type} (f : E * A -> B), F A -> F B.

End operations.

Arguments fmapd {E}%type_scope F%function_scope {Fmapd} {A B}%type_scope f%function_scope _.

(** ** Typeclass *)
(******************************************************************************)
Section class.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Fmapd E T}.

  Class DecoratedFunctor :=
    { dfun_fmapd1 : forall (A : Type),
        fmapd T (extract (E ×)) = @id (T A);
      dfun_fmapd2 : forall (A B C : Type) (g : E * B -> C) (f : E * A -> B),
        fmapd T g ∘ fmapd T f = fmapd T (g ∘ cobind (E ×) f);
    }.

End class.

