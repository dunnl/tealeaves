From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.List_Telescoping_General
  Backends.Named.Names
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

(** ** General operations on lists *)
(**********************************************************************)

(* Fold over a list of A's where each A has the prefix of the list so far *)
Fixpoint fold_with_history {A B: Type}
  (f: list B * A -> B)
  (l: list A): list B :=
  match l with
  | nil => nil
  | cons a rest =>
      f ([], a) :: fold_with_history (f ⦿ [f ([], a)]) rest
  end.

(** ** Variable freshness *)
(**********************************************************************)
(* Given the history of output names so far, decide the name of this binder *)
Definition hf_loc: list name * name -> name :=
  fun '(history, current) =>
    if SmartAtom.name_inb current history
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

(*
  Goal hf nil = nil. reflexivity. Qed.
  Goal hf [1] = [1]. cbv. reflexivity. Qed.
  Goal hf [1 ; 2] = [1 ; 2]. reflexivity. Qed.
  Goal hf [1 ; 2 ; 3] = [1 ; 2 ; 3]. reflexivity. Qed.

  Goal hf [1 ; 1 ] = [1 ; 2 ]. reflexivity. Qed.
  Goal hf [1 ; 1 ; 1 ] = [1 ; 2 ; 3 ]. reflexivity. Qed.
  Goal hf [1 ; 2 ; 1] = [1 ; 2 ; 3]. reflexivity. Qed.
  Goal hf [1 ; 3 ; 8] = [1 ; 2 ; 3]. reflexivity. Qed.
  Goal hf [1 ; 4 ; 6] = [1 ; 2 ; 3]. reflexivity. Qed.
  Goal hf [1 ; 4 ; 6 ; 4] = [1 ; 2 ; 3 ; 4]. reflexivity. Qed.
  Goal hf [1 ; 4 ; 6 ; 4 ; 9 ; 10] = [1 ; 2 ; 3 ; 4; 5; 6]. reflexivity. Qed.
  Goal hf [1 ; 4 ; 8 ; 8 ] = [1 ; 2 ; 3 ; 4 ]. reflexivity. Qed.
 *)

End examples.

(** ** The logic of binding *)
(**********************************************************************)
Inductive Binding: Type :=
  Bound: list name -> name -> list name -> Binding
| Unbound: list name -> Binding.

Fixpoint get_binding_rec (discarded: list name)  (l: list name) (looking_for: name): Binding :=
  match l with
  | nil => Unbound discarded
  | cons y ys =>
      if looking_for == y
      then Bound discarded y ys
      else get_binding_rec (discarded ++ [y]) ys looking_for
  end.

Definition get_binding: list name -> name -> Binding :=
  get_binding_rec [].

Section examples.

  Compute get_binding nil 1.
  Compute get_binding nil 2.
  Compute get_binding [1] 1.
  Compute get_binding [2] 1.
  Compute get_binding [1] 2.
  Compute get_binding [2] 2.
  Compute get_binding [1; 2] 1.
  Compute get_binding [1; 2] 2.

  Compute get_binding [1; 2] 1.
  Compute get_binding [1; 2] 2.
  Compute get_binding [1; 2] 3.
  Compute get_binding [1; 2; 3] 1.
  Compute get_binding [1; 2; 3] 2.
  Compute get_binding [1; 2; 3] 3.

End examples.

(** ** Localized operations *)
(**********************************************************************)
Section named_local_operations.

  Context
    {T: Type -> Type -> Type}
    `{forall W, Return (T W)}.


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
      | Unbound _ =>
          if var == looking_for
          then u
          else ret (T := T name) var
      | Bound prefix _ _ =>
          ret (T := T name) (hf_loc (conflicts ++ prefix, var))
      end.

  Definition alpha_equiv_local:
    list name * name -> list name * name -> Prop :=
    fun '(ctx0, nm0) '(ctx1, nm1) =>
      match (get_binding ctx0 nm0, get_binding ctx1 nm1) with
      | (Bound prefix0 _ _, Bound prefix1 _ _) =>
          if length prefix0 == length prefix1
          then True
          else False
      | _ => False
      end.

End named_local_operations.

(** ** Localized operations *)
(**********************************************************************)
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
      (fun '(ctx, x) => if get_binding ctx x then @nil name else [x]).

  Definition alpha:
    T name name -> T name name -> Prop.
  Admitted.

  Import DecoratedTraversableMonadPoly.DerivedOperations.

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
