From Tealeaves Require Export
     Util.Prelude
     Util.EqDec_eq LN.Atom LN.AtomSet LN.Leaf.

From Multisorted Require Import
     Classes.DTM
     Theory.DTMContainer.

Import LN.AtomSet.Notations.
Import Multisorted.Theory.DTMContainer.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.
#[local] Open Scope set_scope.

(** * Operations for locally nameless *)
(******************************************************************************)

(** ** Local operations *)
(******************************************************************************)
Section local_operations.

  Context
    `{Index}
    `{MReturn T}.

  Implicit Types (x : atom) (k : K).

  Definition free_loc : leaf -> list atom :=
    fun l => match l with
          | Fr x => cons x List.nil
          | _ => List.nil
          end.

  Definition subst_loc k x (u : T k leaf) : leaf -> T k leaf :=
    fun l => match l with
          | Fr y => if x == y then u else mret T k (Fr y)
          | Bd n => mret T k (Bd n)
          end.

  Fixpoint countk (j : K) (l : list K) : nat :=
    match l with
    | nil => 0
    | cons k rest =>
      (if j == k then 1 else 0) + countk j rest
    end.

  Definition open_loc k (u : T k leaf) : list K * leaf -> T k leaf :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => mret T k (Fr x)
            | Bd n => match Nat.compare n (countk k w) with
                     | Gt => mret T k (Bd (n - 1))
                     | Eq => u
                     | Lt => mret T k (Bd n)
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

  Definition close_loc k x : list K * leaf -> leaf :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr y => if x == y then Bd (countk k w) else Fr y
            | Bd n => match Nat.compare n (countk k w) with
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
  Definition is_bound_or_free k (gap : nat) : list K * leaf -> Prop :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => True
            | Bd n => n < (countk k w) + gap
            end
          end.

End local_operations.

(** ** Lifted operations *)
(******************************************************************************)
Section LocallyNamelessOperations.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Definition open k (u : T k leaf) : S leaf -> S leaf  :=
    kbindd S k (open_loc k u).

  Definition close k x : S leaf -> S leaf :=
    kfmapd S k (close_loc k x).

  Definition subst k x (u : T k leaf) : S leaf -> S leaf :=
    kbind S k (subst_loc k x u).

  Definition free : K -> S leaf -> list atom :=
    fun k t => bind list free_loc (toklist S k t).

  (** Derived operations *)
  Definition freeset : K -> S leaf -> AtomSet.t :=
    fun k t => LN.AtomSet.atoms (free k t).

  Definition locally_closed_gap k (gap : nat) : S leaf -> Prop :=
    fun t => forall (w : list K) (l : leaf),
        (w, (k, l)) ∈md t -> is_bound_or_free k gap (w, l).

  Definition locally_closed k : S leaf -> Prop :=
    locally_closed_gap k 0.

  Definition scoped : K -> S leaf -> AtomSet.t -> Prop :=
    fun k t γ => freeset k t ⊆ γ.

End LocallyNamelessOperations.

Module Notations.

  Notation "t '{ k | x ~> u }" := (subst _ k x u t) (at level 35).
  Notation "t '( k | u )" := (open _ k u t) (at level 35).
  Notation "'[ k | x ] t" := (close _ k x t) (at level 35).
  Notation "( x , y , z )" := (pair x (pair y z)) : tealeaves_multi_scope.

End Notations.

Section test_notations.

  Import Notations.

  Context
    (S : Type -> Type)
    `{DTPreModule (list K) S T (mn_op := Monoid_op_list) (mn_unit := Monoid_unit_list)}
    `{! DTM (list K) T}.

  Context
    (k j : K)
    (t1 : T k leaf)
    (t2 : T j leaf)
    (u : S leaf)
    (x : atom)
    (n : nat).

  Check u '{ k | x ~> t1}.
  Check u '(k | t1).
  Check '[k | x] u.

  Check u '{j | x ~> t2}.
  Check u '(j | t2).
  Check '[j | x] u.

  Fail Check u '{j | x ~> t1}.
  Fail Check u '(j | t1).

End test_notations.
