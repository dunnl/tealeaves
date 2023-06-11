From Tealeaves Require Export
  Classes.Kleisli.

(** * [option] monad *)
(******************************************************************************)
(*
Inductive Maybe (A : Type) :=
| Just : A -> Maybe A
| None : Maybe A.

Arguments Just {A}%type_scope _.
Arguments None {A}%type_scope.
*)

#[export] Instance Map_option : Map option :=
  fun A B (f : A -> B) (m : option A) =>
    match m with
    | Some a => Some (f a)
    | None => None
    end.

#[export] Instance Functor_option : Functor option.
Proof.
  constructor.
  - intros. now ext [|].
  - intros. now ext [|].
Qed.

#[export] Instance Return_option : Return option :=
  fun A => Some.

(*
#[export] Instance Join_option : Join option :=
  fun A (m : option (option A)) =>
    match m with
    | Some m' => m'
    | None => None
    end.

#[export] Instance: Natural (@ret option _).
Proof.
  constructor; try typeclasses eauto.
  reflexivity.
Qed.

#[export] Instance: Natural (@join option _).
Proof.
  constructor; try typeclasses eauto.
  intros. now ext [[|]|].
Qed.

#[export] Instance Monad_option : Monad option.
Proof.
  constructor; try typeclasses eauto.
  - intros. now ext [|].
  - intros. now ext [|].
  - intros. now ext [|].
Qed.
*)
