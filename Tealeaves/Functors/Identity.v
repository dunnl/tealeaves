From Tealeaves Require Export
  Classes.Functor.

(** * The Identity Functor *)
(**********************************************************************)
#[export] Instance Map_I: Map (fun A => A) :=
  fun (A B: Type) (f: A -> B) => f.

#[program, export] Instance Functor_I: Functor (fun A => A).
