From Tealeaves Require Export
     Classes.Monad.

#[local] Open Scope tealeaves_scope.

(** * State monad *)
(******************************************************************************)
Inductive State (S A : Type) :=
| mkState : (S -> S * A) -> State S A.

Arguments mkState {S A}%type_scope _.

Section state_monad.

  Context
    {S : Type}.

  Definition runState {A} : State S A -> S -> S * A :=
    fun st s => match st with
             | mkState run => run s
             end.

  Definition runStateValue {A} : State S A -> S -> A :=
    fun st s => snd (runState st s).

  Definition runStateState {A} : State S A -> S -> S :=
    fun st s => fst (runState st s).

  #[global] Instance Fmap_State : Fmap (State S) :=
    fun A B (f : A -> B) (st : State S A) =>
      match st with
      | mkState r =>
        mkState (fun s => match (r s) with (s', a) => (s', f a) end)
      end.

  #[global] Instance Functor_State : Functor (State S).
  Proof.
    constructor; try typeclasses eauto.
    - intros. ext [st]. unfold id.
      cbn. fequal. ext s. now destruct (st s).
    - intros. ext [st]. unfold compose.
      cbn. fequal. ext s. now destruct (st s).
  Qed.

  #[global] Instance Return_State : Return (State S) :=
    fun A (a : A) => mkState (fun s => (s, a)).

  #[global] Instance Join_State : Join (State S) :=
    fun A (st : State S (State S A)) =>
      match st with
      | mkState r =>
        mkState (fun s => match (r s) with (s', st') => runState st' s' end)
      end.

  Instance Natural_ret : Natural (@ret (State S) _).
  Proof.
    ltac:(constructor; try typeclasses eauto).
    reflexivity.
  Qed.

  Instance Natural_join : Natural (@join (State S) _).
  Proof.
    ltac:(constructor; try typeclasses eauto).
    intros. ext [st]. cbn. fequal.
    ext s. destruct (st s); cbn. now (destruct s1).
  Qed.

  #[global] Instance Monad_State : Monad (State S).
  Proof.
    constructor; try typeclasses eauto.
    - intros. ext [st]. unfold id.
      cbn. fequal. ext s. now destruct (st s).
    - intros. now (ext [st]).
    - intros. ext [st]. unfold compose; cbn.
      fequal. ext s. destruct (st s). now (destruct s1).
  Qed.

End state_monad.
