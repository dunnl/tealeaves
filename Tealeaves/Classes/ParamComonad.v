From Tealeaves Require Export
     Classes.Functor.

Import Functor.Notations.
#[local] Open Scope tealeaves_scope.

(** * Parameterized comonads *)
(******************************************************************************)
Section ParameterizedComonad_operations.

  Context
    (W : Type -> Type -> Type -> Type).

  Class PExtract :=
    pextract : forall A, W A A ⇒ (fun X => X).

  Class PCojoin :=
    pcojoin : forall A B C, W A C ⇒ W A B ∘ W B C.

End ParameterizedComonad_operations.

Section ParameterizedComonad_typeclass.

  Context
    `(W : Type -> Type -> Type -> Type)
    `{forall A B, Fmap (W A B)}
    `{PCojoin W}
    `{PExtract W}.

  Class ParameterizedComonad :=
    { pcom_functor :> forall A B, Functor (W A B);
      pcom_extract_cojoin :
        `((pextract W A _) ∘ pcojoin W A A B X = @id (W A B X));
      pcom_fmap_extract_cojoin :
        `(fmap (W A B) (pextract W B X) ∘ pcojoin W A B B X = @id (W A B X));
      pcom_cojoin_cojoin :
        `(pcojoin W A B C (W C D X) ∘ pcojoin W A C D X =
         fmap (W A B) (pcojoin W B C D X) ∘ pcojoin W A B D X);
    }.

End ParameterizedComonad_typeclass.

Arguments pcojoin _%function_scope {PCojoin} {A}%type_scope.
Arguments pextract _%function_scope {PExtract} {A}%type_scope.
