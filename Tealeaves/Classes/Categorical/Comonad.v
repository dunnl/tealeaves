From Tealeaves Require Export
  Classes.Functor
  Functors.Identity
  Functors.Compose.

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

(** * Comonads *)
(**********************************************************************)

(** ** Operations <<cojoin>> and <<extract>> *)
(**********************************************************************)
Class Extract (W: Type -> Type) :=
  extract: W ⇒ (fun A => A).
Class Cojoin (W: Type -> Type) :=
  cojoin: W ⇒ W ∘ W.

#[global] Arguments extract {W}%function_scope {Extract} {A}%type_scope.
#[global] Arguments cojoin {W}%function_scope {Cojoin} {A}%type_scope.

(** ** Typeclass *)
(**********************************************************************)
Class Comonad (W: Type -> Type)
  `{Map_W: Map W}
  `{Cojoin_W: Cojoin W}
  `{Extract_W: Extract W} :=
  { com_functor :> Functor W;
    com_extract_natural :> Natural (@extract W _);
    com_cojoin_natural :> Natural (@cojoin W _);
    com_extract_cojoin:
    `(extract (A := W A) ∘ cojoin (A := A) = @id (W A));
    com_map_extr_cojoin:
    `(map (F := W) (extract (A := A)) ∘ cojoin (A := A) = @id (W A));
    com_cojoin_cojoin:
    `(cojoin (A := W A) ∘ cojoin (A := A) =
        map (F := W) (cojoin (A := A)) ∘ cojoin (A := A));
  }.

(** * Notations *)
(**********************************************************************)
Module Notations.
  Notation "'coμ'" := cojoin: tealeaves_scope.
End Notations.
