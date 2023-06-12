(** This file defines typeclasses *)
From Tealeaves Require Export
  Prelude
  Classes.Applicative
  Classes.Monoid
  Classes.Functor.

#[local] Generalizable Variables F G A B W T U ϕ.

Import Product.Notations.
Import Monoid.Notations.
Import Functor.Notations.
Import Monoid.Notations.
Import Product.Notations.

Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

(** * Operational typeclasses for DTM hierarchy *)
(******************************************************************************)
Section operations.

  Context
    (M : Type)
    (T : Type -> Type)
    (U : Type -> Type).

    Class Return :=
      ret : (fun A => A) ⇒ T.

    Class Traverse := traverse :
        forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (A -> G B) -> T A -> G (T B).

    Class Mapd := mapd :
        forall (A B : Type),
          (M * A -> B) -> T A -> T B.

    Class Mapdt := mapdt :
        forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (M * A -> G B) -> T A -> G (T B).

    Class Bind :=
      bind : forall (A B : Type), (A -> T B) -> U A -> U B.

    Class Bindd := bindd :
        forall (A B : Type),
          (M * A -> T B) -> U A -> U B.

    Class Bindt := bindt :
        forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (A -> G (T B)) -> U A -> G (U B).

    Class Binddt := binddt :
        forall (G : Type -> Type)
          `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (M * A -> G (T B)) -> U A -> G (U B).

End operations.

#[export] Instance Extract_env {E : Type} : Extract (E ×) :=
  fun A '(e, a) => a.

#[export] Instance Cobind_env {E : Type} : Cobind (E ×) :=
  fun A B (f : E * A -> B) '(e, a) => (e, f (e, a)).

(** * Kleisli-style typeclasses for structured functors *)
(******************************************************************************)


(** ** Decorated monad *)
(******************************************************************************)



(** ** Decorated traversable functor *)
(******************************************************************************)


(** ** Decorated traversable monad *)
(******************************************************************************)
