From Tealeaves Require Export
  Classes.Kleisli.Monad
  Classes.Categorical.Applicative.

(** * The [option] Monad *)
(**********************************************************************)
(*
  Inductive Maybe (A: Type) :=
  | Just: A -> Maybe A
  | None: Maybe A.

  Arguments Just {A}%type_scope _.
  Arguments None {A}%type_scope.
 *)

(** ** Functor Instance *)
(**********************************************************************)
#[export] Instance Map_option: Map option :=
  fun A B (f: A -> B) (m: option A) =>
    match m with
    | Some a => Some (f a)
    | None => None
    end.

#[export] Instance Functor_option: Functor option.
Proof.
  constructor.
  - intros. now ext [|].
  - intros. now ext [|].
Qed.

(** ** Applicative Instance *)
(**********************************************************************)
#[export] Instance Pure_option: Pure option :=
  @Some.

#[export] Instance Mult_option: Mult option.
Proof.
  hnf.
  intros A B [[a|] [b|]].
  - exact (Some (a, b)).
  - exact None.
  - exact None.
  - exact None.
Defined.

#[export] Instance Applicative_option: Applicative option.
Proof.
  constructor; try typeclasses eauto.
  - reflexivity.
  - destruct x as [x|];
      destruct y as [y|];
      reflexivity.
  - destruct x as [x|];
      destruct y as [y|];
      destruct z as [z|];
      reflexivity.
  - destruct x as [x|]; reflexivity.
  - destruct x as [x|]; reflexivity.
  - reflexivity.
Qed.


(** ** Monad Instance *)
(**********************************************************************)
(*
  #[export] Instance Return_option: Return option :=
  @Some.

  #[export] Instance Join_option: Join option :=
  fun A (m: option (option A)) =>
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

  #[export] Instance Monad_option: Monad option.
  Proof.
  constructor; try typeclasses eauto.
  - intros. now ext [|].
  - intros. now ext [|].
  - intros. now ext [|].
  Qed.
 *)
