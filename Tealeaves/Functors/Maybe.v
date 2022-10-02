From Tealeaves Require Export
  Classes.Algebraic.Monad.

(** * Maybe monad *)
(******************************************************************************)
Inductive Maybe (A : Type) :=
| Just : A -> Maybe A
| None : Maybe A.

Arguments Just {A}%type_scope _.
Arguments None {A}%type_scope.

#[export] Instance Fmap_Maybe : Fmap Maybe :=
  fun A B (f : A -> B) (m : Maybe A) =>
    match m with
    | Just a => Just (f a)
    | None => None
    end.

#[export] Instance Functor_Maybe : Functor Maybe.
Proof.
  constructor.
  - intros. now ext [|].
  - intros. now ext [|].
Qed.

#[export] Instance Return_Maybe : Return Maybe :=
  fun A => Just.

#[export] Instance Join_Maybe : Join Maybe :=
  fun A (m : Maybe (Maybe A)) =>
    match m with
    | Just m' => m'
    | None => None
    end.

#[export] Instance: Natural (@ret Maybe _).
Proof.
  constructor; try typeclasses eauto.
  reflexivity.
Qed.

#[export] Instance: Natural (@join Maybe _).
Proof.
  constructor; try typeclasses eauto.
  intros. now ext [[|]|].
Qed.

#[export] Instance Monad_Maybe : Monad Maybe.
Proof.
  constructor; try typeclasses eauto.
  - intros. now ext [|].
  - intros. now ext [|].
  - intros. now ext [|].
Qed.
