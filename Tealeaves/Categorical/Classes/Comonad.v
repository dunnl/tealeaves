From Tealeaves Require Export
  Classes.Functor
  Functors.Identity
  Functors.Compose
  Classes.Kleisli (Extract, extract).

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

(** * Comonads *)
(******************************************************************************)
Section comonad.

  Context
    (W : Type -> Type).

  Class Cojoin :=
    cojoin : W ⇒ W ∘ W.

  Context
    `{Map W}
    `{Cojoin}
    `{Extract W}.

  Class Comonad :=
    { com_functor :> Functor W;
      com_extract_natural :> Natural (extract W);
      com_cojoin_natural :> Natural (cojoin);
      com_extract_cojoin :
      `(extract W (W A) ∘ cojoin A = @id (W A));
      com_map_extr_cojoin :
      `(map W (W A) A (extract W A) ∘ cojoin A = @id (W A));
      com_cojoin_cojoin :
      `(cojoin (W A) ∘ cojoin A = map W (W A) (W (W A)) (cojoin A) ∘ cojoin A);
    }.

End comonad.

Arguments cojoin _%function_scope {Cojoin} {A}%type_scope.
Arguments extract _%function_scope {Extract} {A}%type_scope.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'coμ'" := (cojoin) : tealeaves_scope.
  (*Notation "'coη'" := (extract) : tealeaves_scope.*)
End Notations.
