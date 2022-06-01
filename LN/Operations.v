From Tealeaves Require Import
     Util.Prelude Util.EqDec_eq
     LN.Atom LN.AtomSet LN.Leaf
     Classes.DecoratedTraversableModule.

Import DecoratedTraversableMonad.Notations.
Import LN.AtomSet.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope set_scope.

(** * Operations for locally nameless *)
(******************************************************************************)

(** ** Local operations *)
(******************************************************************************)
Section locally_nameless_local_operations.

  Context
    `{Return T}.

  Definition free_loc : leaf -> list atom :=
    fun l => match l with
          | Fr x => cons x List.nil
          | _ => List.nil
          end.

  Definition subst_loc (x : atom) (u : T leaf) : leaf -> T leaf :=
    fun l => match l with
          | Fr y => if x == y then u else ret T (Fr y)
          | Bd n => ret T (Bd n)
          end.

  Definition open_loc (u : T leaf) : nat * leaf -> T leaf :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => ret T (Fr x)
            | Bd n =>
              match Nat.compare n w with
              | Gt => ret T (Bd (n - 1))
              | Eq => u
              | Lt => ret T (Bd n)
              end
            end
          end.

  Definition is_opened : nat * leaf -> Prop :=
    fun p =>
      match p with
      | (ctx, l) =>
        match l with
        | Fr y => False
        | Bd n => n = ctx
        end
      end.

  Definition close_loc (x : atom ) : nat * leaf -> leaf :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr y => if x == y then Bd w else Fr y
            | Bd n =>
              match Nat.compare n w with
              | Gt => Bd (S n)
              | Eq => Bd (S n)
              | Lt => Bd n
              end
            end
          end.

  (** The argument <<n>> is appended the context---to define local
      closure we will take <<n = 0>>, but we can also consider more
      notions like ``local closure within a gap of 1 binder,'' which
      is useful for backend reasoning. **)
  Definition is_bound_or_free (gap : nat) : nat * leaf -> Prop :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => True
            | Bd n => n < w ● gap
            end
          end.

End locally_nameless_local_operations.

(** ** Lifted operations *)
(******************************************************************************)
Section locally_nameless_operations.

  Context
    (F : Type -> Type)
    `{DecoratedTraversableModule nat F T}.

  Definition open (u : T leaf) : F leaf -> F leaf  :=
    subd F (open_loc u).

  Definition close x : F leaf -> F leaf :=
    fmapd F (close_loc x).

  Definition subst x (u : T leaf) : F leaf -> F leaf :=
    sub F (subst_loc x u).

  Definition free : F leaf -> list atom :=
    fun t => bind list free_loc (tolist F t).

  Definition freeset : F leaf -> AtomSet.t :=
    fun t => LN.AtomSet.atoms (free t).

  Definition locally_closed_gap (gap : nat) : F leaf -> Prop :=
    fun t => forall w l, (w, l) ∈d t -> is_bound_or_free gap (w, l).

  Definition locally_closed : F leaf -> Prop :=
    locally_closed_gap 0.

  Definition scoped : F leaf -> AtomSet.t -> Prop :=
    fun t γ => freeset t ⊆ γ.

End locally_nameless_operations.

(** ** Notations *)
(******************************************************************************)
Module Notations.
  Notation "t '{ x ~> u }" := (subst _ x u t) (at level 35).
  Notation "t '( u )" := (open _ u t) (at level 35).
  Notation "'[ x ] t" := (close _ x t) (at level 35).
End Notations.

Section test_notations.

  Import Notations.

  Context
    `{DecoratedTraversableModule nat F T}.

  Context
    (t : T leaf)
    (u : F leaf)
    (x : atom)
    (n : nat).

  Check u '{x ~> t}.
  Check u '(t).
  Check '[ x ] u.

End test_notations.
