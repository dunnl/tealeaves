From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.List_Telescoping_General
  Backends.Named.Names
  Backends.Named.Named
  Functors.Constant
  Functors.Subset.

Import Subset.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import List.ListNotations.
Import Product.Notations.
Import ContainerFunctor.Notations.

Section alt.

  Context
    {T: Type -> Type -> Type}
    `{forall W, Return (T W)}
    `{Substitute T T}.

  Import DecoratedTraversableMonadPoly.DerivedOperations.

  Section rename_local.

    Context (conflicts: list name).
    (* X is the var being substituted, fv_u is FV u *)
    Context (x: name) (fv_u: list name) (u: T name name).

    (* Given a substitution of x by u, encode the logic of what happens at <<current>> if <<history>> is the set of names
     given to the binders so far *)
    Definition rename_binder_local_history:
      list name * name -> name :=
      fun '(history, b) =>
        if x == b
        then b
        else if SmartAtom.name_inb b (fv_u)
             then fresh (conflicts ++ history ++ [b])
             else b.

    Definition ctx_to_history: list name -> list name :=
      fold_with_history rename_binder_local_history.


    (* Name a binder to something else during substitution *)
    Definition rename_binder_local:
      list name * name -> name :=
      fun '(ctx, b) =>
        if SmartAtom.name_inb x ctx (* Halt substitution early *)
        then b
        else if x == b (* Else check if halt now *)
             then b
             else if SmartAtom.name_inb b fv_u (* Else check if need to rename *)
             then (rename_binder_local_history (ctx_to_history ctx, b))
             else b.

    Definition subst_local:
      list name * name -> T name name :=
      fun '(ctx, v) =>
        if SmartAtom.name_inb x ctx (* Halt substitution early *)
        then ret (T := T name) v
        else
               match (get_binding ctx v) with
               | Unbound _ =>
                   if v == x
                   then u
                   else ret (T := T name) v
               | Bound prefix _ _ =>
                   if v == x
                   then ret (T := T name) v
                   else if SmartAtom.name_inb v (FV T u)
                        then ret (T := T name) (rename_binder_local_history (prefix, v))
                        else ret (T := T name) v
               end.

    Definition subst_top
      (t: T name name): T name name :=
      substitute (G := fun A => A) (U := T)
        rename_binder_local
        subst_local t.

  End rename_local.

  Definition subst
    (x: name) (u: T name name)
    (t: T name name): T name name :=
    subst_top (FV T t ++ FV T u) x (FV T u) u t.

End alt.
