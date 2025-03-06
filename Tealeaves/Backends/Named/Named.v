From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.List_Telescoping_General
  Backends.Common.Names
  Backends.Named.Common
  Functors.Constant
  Functors.Subset.

Import Subset.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import List.ListNotations.
Import Product.Notations.
Import ContainerFunctor.Notations.

(** * Fully named syntax *)
(**********************************************************************)

(** ** Variable freshness *)
(**********************************************************************)
(* Given the history of output names so far, decide the name of this binder *)
Definition hf_loc: list name * name -> name :=
  fun '(history, current) =>
    if Name.name_inb current history
    then fresh history
    else current.

Definition hf: list name -> list name := fold_with_history hf_loc.
Section examples.

  Compute hf_loc ([], 1).
  Compute hf_loc ([1], 0).
  Compute hf_loc ([1], 1).
  Compute hf_loc ([1; 2], 1).
  Compute hf_loc ([0; 1; 2], 1).

  Compute hf nil = nil.
  Compute hf [0].
  Compute hf [1].
  Compute hf [1; 2].
  Compute hf [1; 2; 3].
  Compute hf [1; 2; 3; 4].
  Compute hf [0; 0].
  Compute hf [1; 0].
  Compute hf [0; 1; 0].
  Compute hf [0; 1; 0; 1].
  Compute hf [0; 1; 0; 1; 0; 1].
  Compute hf [0; 1; 3; 1; 0; 1].

End examples.

(** ** Localized operations *)
(**********************************************************************)
Section named_local_operations.

  Context
    {T: Type -> Type -> Type}
    `{forall W, Return (T W)}.

  Definition FV_loc: list name * name -> list name :=
    fun '(ctx, x) => if get_binding ctx x then @nil name else [x].

  Definition deconflict_binder_local (conflicts: list name):
    list name * name -> name :=
    hf_loc ⦿ conflicts.

  Definition subst_local
    (conflicts: list name)
    (looking_for: name)
    (u: T name name):
    list name * name -> T name name :=
    fun '(context, var) =>
      match (get_binding context var) with
      | Unbound _ _ =>
          if var == looking_for
          then u
          else ret (T := T name) var
      | Bound prefix _ _ =>
          ret (T := T name) (hf_loc (conflicts ++ prefix, var))
      end.

End named_local_operations.

(** ** Localized operations *)
(**********************************************************************)
From Tealeaves Require Import
  Classes.Categorical.DecoratedTraversableMonadPoly
  Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly.

Section named_local_operations.

  Context
    (T: Type -> Type -> Type)
    `{MapdtPoly T}.

  Definition FV: T name name -> list name :=
    mapdtp
      (T := T)
      (A1 := name) (B1 := name)
      (A2 := False) (B2 := False)
      (G := const (list name))
      (const (@nil name))
      FV_loc.

  Context
    `{forall W, Return (T W)}
    `{Substitute T T}.

  Definition subst_conflicts (top_conflicts: list name)
    (x: name) (u: T name name):
    T name name -> T name name :=
    substitute (G := fun A => A) (U := T)
      (deconflict_binder_local top_conflicts)
      (subst_local top_conflicts x u).

  Definition subst (x: name) (u: T name name)
    (t: T name name): T name name :=
    subst_conflicts (FV t ++ FV u) x u t.

End named_local_operations.
