From Tealeaves Require Export
     Classes.Functor.

Import Functor.Notations.
#[local] Open Scope tealeaves_scope.

(** * Parameterized comonads *)
(******************************************************************************)
Section ParameterizedComonad_operations.

  Context
    (W : Type -> Type -> Type -> Type).

  Class Extract :=
    extract : forall A, W A A ⇒ (fun X => X).

  Class Cojoin :=
    cojoin : forall A B C, W A C ⇒ W A B ∘ W B C.

End ParameterizedComonad_operations.

Section Comonad.

  Context
    `(W : Type -> Type -> Type -> Type)
    `{forall A B, Fmap (W A B)}
    `{Cojoin W}
    `{Extract W}.

  Class ParameterizedComonad :=
    { com_functor :> forall A B, Functor (W A B);
      com_extract_cojoin :
        `((extract W A _) ∘ cojoin W A A B X = @id (W A B X));
      com_fmap_extract_cojoin :
        `(fmap (W A B) (extract W B _) ∘ cojoin W A B B X = @id (W A B X));
    }.

End Comonad.

Arguments cojoin _%function_scope {Cojoin} {A}%type_scope.
Arguments extract _%function_scope {Extract} {A}%type_scope.
