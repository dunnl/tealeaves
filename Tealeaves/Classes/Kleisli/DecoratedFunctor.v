From Tealeaves Require Export
  Functors.Early.Reader
  Classes.Kleisli.Comonad.

Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables E T.

(** * Decorated functors *)
(******************************************************************************)

(** ** <<Mapd>> operation *)
(******************************************************************************)
Class Mapd (E: Type) (T: Type -> Type) :=
  mapd: forall (A B: Type), (E * A -> B) -> T A -> T B.

#[global] Arguments mapd {E}%type_scope {T}%function_scope
  {Mapd} {A B}%type_scope _%function_scope _.

(** Kleisli composition is [kc4] as for comonads *)

(** ** Typeclasses *)
(******************************************************************************)
Class DecoratedFunctor (E: Type) (T: Type -> Type) `{Mapd E T} :=
  { kdf_mapd1: forall (A: Type),
      mapd (extract (A := A)) = @id (T A);
    kdf_mapd2: forall (A B C: Type) (g: E * B -> C) (f: E * A -> B),
      mapd g ∘ mapd f = mapd (g ⋆4 f);
  }.

(** ** Decoration-preserving natural transformations *)
(******************************************************************************)
Class DecoratedHom
  (E: Type) (T1 T2: Type -> Type)
  (ϕ: forall A: Type, T1 A -> T2 A)
  `{Mapd E T1} `{Mapd E T2} :=
  { dhom_natural:
    forall (A B: Type) (f: E * A -> B), mapd f ∘ ϕ A = ϕ B ∘ mapd f;
  }.
