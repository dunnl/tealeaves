From Tealeaves Require Export
  Classes.Categorical.Applicative.

Import Applicative.Notations.

#[local] Generalizable Variables F.

(** * The <<Backwards>> idiom *)
(******************************************************************************)
Section Backwards.

  Record Backwards (F : Type -> Type) A :=
    { forwards : F A }.

  Context
    `{Applicative F}.

  #[export] Instance Map_Backwards : Map (Backwards F) :=
    fun A B f '(Build_Backwards _ _ x) => {| forwards := map F f x |}.

  #[export] Instance Pure_Backwards : Pure (Backwards F) :=
    fun A a => Build_Backwards _ _ (pure F a).

  Definition swap {A B} : B * A -> A * B :=
    fun '(b, a) => (a, b).

  Definition mult_Backwards {A B} : Backwards F A -> Backwards F B -> Backwards F (A * B) :=
    fun ba bb => Build_Backwards F _ (map F swap (forwards _ _ bb ⊗ forwards _ _ ba)).

  #[export] Instance Mult_Backwards : Mult (Backwards F) :=
    fun A B '(x, y) => mult_Backwards x y.

  (* TODO Finish proving <<Backwards>> is an applicative.
     We do not need this right now. *)
  (*
  #[export, program] Instance Applicative_Backwards : Applicative (Backwards F).
   *)

End Backwards.
