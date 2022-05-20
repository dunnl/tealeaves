From Tealeaves Require Export
     Classes.Applicative.

Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

(** * The <<Backwards>> idiom *)
(******************************************************************************)
Section Backwards.

  Record Backwards (F : Type -> Type) A :=
    { forwards : F A }.

  Context
    `{Applicative F}.

  #[global] Instance Fmap_Backwards : Fmap (Backwards F) :=
    fun A B f '(Build_Backwards _ _ x) => {| forwards := fmap F f x |}.

  #[global] Instance Pure_Backwards : Pure (Backwards F) :=
    fun A a => Build_Backwards _ _ (pure F a).

  Definition swap {A B} : B * A -> A * B :=
    fun '(b, a) => (a, b).

  Definition mult_Backwards {A B} : Backwards F A -> Backwards F B -> Backwards F (A * B) :=
    fun ba bb => Build_Backwards F _ (fmap F swap (forwards _ _ bb ⊗ forwards _ _ ba)).

  #[global] Instance Mult_Backwards : Mult (Backwards F) :=
    fun A B '(x, y) => mult_Backwards x y.

  (* TODO We do not need this right now
  #[global, program] Instance Applicative_Backwards : Applicative (Backwards F).
   *)

End Backwards.
