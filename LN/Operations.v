From Tealeaves Require Import
  LN.Atom LN.AtomSet LN.Leaf
  Theory.Kleisli.DT.Monad
  Theory.List.Kleisli
  Data.Natural.

Import Monoid.Notations.
Import DT.Monad.Notations.
Import LN.AtomSet.Notations.
Import DT.Monad.DerivedInstances.Operations.

#[local] Generalizable Variable T.

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
    (T : Type -> Type)
    `{DT.Monad.Monad nat T}.

  Definition open (u : T leaf) : T leaf -> T leaf  :=
    bindd T (open_loc u).

  Definition close x : T leaf -> T leaf :=
    fmapd T (close_loc x).

  Definition subst x (u : T leaf) : T leaf -> T leaf :=
    bind T (subst_loc x u).

  Definition free : T leaf -> list atom :=
    fun t => bind list free_loc (tolist T t).

  Definition freeset : T leaf -> AtomSet.t :=
    fun t => LN.AtomSet.atoms (free t).

  Definition locally_closed_gap (gap : nat) : T leaf -> Prop :=
    fun t => forall w l, (w, l) ∈d t -> is_bound_or_free gap (w, l).

  Definition locally_closed : T leaf -> Prop :=
    locally_closed_gap 0.

  Definition scoped : T leaf -> AtomSet.t -> Prop :=
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
    `{DT.Monad.Monad nat T}.

  Context
    (t : T leaf)
    (u : T leaf)
    (x : atom)
    (n : nat).

  Check u '{x ~> t}.
  Check u '(t).
  Check '[ x ] u.

End test_notations.
