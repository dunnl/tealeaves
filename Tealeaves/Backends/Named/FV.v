From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Kleisli.Theory.DecoratedTraversableFunctor
  Backends.Named.Common.

Import List.ListNotations.

(** * Free Variables *)
(**********************************************************************)
Section FV.

  Context
    (T: Type -> Type)
    `{Mapdt (list name) T}.

  Definition FV_loc: list name * name -> list name :=
    fun '(ctx, x) => if get_binding ctx x then @nil name else [x].

  Definition FV: T name -> list name :=
    foldMapd FV_loc.

End FV.
