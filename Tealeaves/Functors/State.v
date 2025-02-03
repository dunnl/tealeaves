From Tealeaves Require Export
  Classes.Kleisli.Monad.

(** * State Monad *)
(**********************************************************************)
Inductive State (S A: Type) :=
| mkState: (S -> S * A) -> State S A.

Arguments mkState {S A}%type_scope _.

Section state_monad.

  Context
    {S: Type}.

  Definition runState {A}: State S A -> S -> S * A :=
    fun st s => match st with
             | mkState run => run s
             end.

  Definition runStateValue {A}: State S A -> S -> A :=
    fun st s => snd (runState st s).

  Definition runStateState {A}: State S A -> S -> S :=
    fun st s => fst (runState st s).

  (** ** Functor Instance *)
  (********************************************************************)
  #[export] Instance Map_State: Map (State S) :=
    fun A B (f: A -> B) (st: State S A) =>
      match st with
      | mkState r =>
          mkState (fun s => match (r s) with (s', a) => (s', f a) end)
      end.

  #[export] Instance Functor_State: Functor (State S).
  Proof.
    constructor; try typeclasses eauto.
    - intros. ext [st]. unfold id.
      cbn. fequal. ext s. now destruct (st s).
    - intros. ext [st]. unfold compose.
      cbn. fequal. ext s. now destruct (st s).
  Qed.

  (** ** Monad Instance (Kleisli) *)
  (********************************************************************)
  #[export] Instance Return_State: Return (State S) :=
    fun A (a: A) => mkState (fun s => (s, a)).

  #[export] Instance Bind_State: Bind (State S) (State S) :=
    fun A B (f: A -> State S B) (st1: State S A) =>
      match st1 with
      | mkState action =>
          mkState
            (fun s => match (action s) with
                     (s', a) => runState (f a) s'
                   end)
      end.

  #[export] Instance Monad_State: Monad (State S).
  Proof.
    constructor.
    - intros. ext a. cbv.
      now destruct (f a).
    - constructor.
      + intros. ext s.
        cbv. destruct s.
        fequal. ext s. now destruct (p s).
      + intros. ext s.
        cbv. destruct s. fequal.
        ext s. destruct (p s).
        now destruct (f a).
  Qed.

  (** ** Monad Instance (Categorical) *)
  (* TODO *)
  (********************************************************************)
(*
  #[export] Instance Join_State: Join (State S) :=
  fun A (st: State S (State S A)) =>
  match st with
  | mkState r =>
  mkState (fun s => match (r s) with (s', st') => runState st' s' end)
  end.

  Instance Natural_ret: Natural (@ret (State S) _).
  Proof.
  ltac:(constructor; try typeclasses eauto).
  reflexivity.
  Qed.

  Instance Natural_join: Natural (@join (State S) _).
  Proof.
  ltac:(constructor; try typeclasses eauto).
  intros. ext [st]. cbn. fequal.
  ext s. destruct (st s); cbn. now (destruct s1).
  Qed.

  #[export] Instance Monad_State: Monad (State S).
  Proof.
  constructor; try typeclasses eauto.
  - intros. now (ext [st]).
  - intros. ext [st]. unfold id.
  cbn. fequal. ext s. now destruct (st s).
  - intros. ext [st]. unfold compose; cbn.
  fequal. ext s. destruct (st s). now (destruct s1).
  Qed.
 *)

End state_monad.
