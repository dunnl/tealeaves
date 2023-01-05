From Tealeaves Require Import
  Util.Prelude
  Classes.Kleisli.DT.Monad
  Theory.Kleisli.DT.Monad.DerivedInstances
  Theory.Kleisli.Monad.ToApplicative
  Theory.Kleisli.DT.Monad.Container
  Functors.Maybe
  Data.Natural.

From Coq Require Import
  Init.Datatypes
  Lists.List.

Import Theory.Kleisli.DT.Functor.Container.Notations.
Import Monoid.Notations.
Import DT.Monad.Notations.

#[local] Generalizable Variables W T.

(** * Operations for locally nameless *)
(******************************************************************************)

Inductive Db : Type :=
| MkDb : nat -> nat -> Db.

(** ** Local operations *)
(******************************************************************************)
Section locally_nameless_local_operations.

  Context
    `{Return T}.

  Definition open_loc (u : list (T Db)) : list nat * Db -> option (T Db)  :=
    fun p => match p with
          | (context, MkDb index1 index2) =>
              match Nat.compare (length context) index1 with
              | Gt => Some (ret T (MkDb (index1 - 1) index2))
              | Eq => nth_error u index2
              | Lt => Some (ret T (MkDb index1 index2))
              end
          end.

  Definition variable_bound : list nat * Db -> Prop :=
    fun '(context, MkDb index1 index2) =>
      match fmap option (fun i => Nat.leb index2 i) (nth_error context index1) with
      | Some true => True
      | Some false => False
      | None => False
      end.


  Definition variable_bound_level : nat -> list nat * Db -> bool :=
    fun tolerance '(context, MkDb index1 index2) =>
      orb (Nat.leb index1 (length (context) + tolerance))
        (match fmap option (fun i => Nat.leb index2 i) (nth_error context index1) with
         | Some true => true
         | Some false => false
         | None => false
         end).

  Definition closed_loc : list nat * Db -> Prop :=
    fun p => match p with
          | (context, MkDb index1 index2) =>
              match fmap option (fun i => Nat.leb index2 i) (nth_error context index1) with
              | Some true => True
              | Some false => False
              | None => False
              end
          end.

  Definition open_loc_safe (u : list (T Db)) (context : list nat)
    (db :  Db) (H_safe : variable_bound_level 1 (context, db) = true) : T Db.
  Proof.
    unfold variable_bound_level in H_safe.
    destruct db as [index1 index2]. destruct H_safe.
                  fun p => match p with
                        | (context, MkDb index1 index2) =>
                            match Nat.compare (length context) index1 with
                            | Gt => Some (ret T (MkDb (index1 - 1) index2))
                            | Eq => nth_error u index2
                            | Lt => Some (ret T (MkDb index1 index2))
                            end
                        end.

End locally_nameless_local_operations.

Import DT.Monad.DerivedInstances.Operations.
Import DT.Monad.DerivedInstances.Instances.

(** ** Lifted operations *)
(******************************************************************************)
Section locally_nameless_operations.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad (list nat) T}.

  Definition open (u : list (T Db)) : T Db -> option (T Db)  :=
    binddt T option (open_loc (T := T) u).

  Definition closed : T Db -> Prop :=
    fun t => forall β db, (β, db) ∈d t -> closed_loc (β, db).

  Section test.

    Context
      (t : T Db)
      (u : list (T Db)).

    Hypothesis (H_closed : closed t).

    Goal open u t = Some t.
    Proof.
      intros. unfold open.
      change (Some t) with (pure option t).
      unfold closed in H_closed.
    Abort.

    Goal open u t = Some t.
      intros. unfold open.
      rewrite (binddt_to_runBatch T).
      change (Some t) with (Some (id t)).
      rewrite <- (kdtm_binddt1 (list nat) T).
      rewrite (binddt_to_runBatch T).
      induction (iterate_dm T Db t).
      - reflexivity.
      - cbn. rewrite IHb. clear IHb.
        destruct x as [context db].
        destruct db as [index1 index2].
        unfold compose.
        cbn. compare naturals (length context) and index1.
        + Search nth_error length.
        unfold compose. cbn.
        cbn.
        cbn.
    Abort.

End locally_nameless_operations.

