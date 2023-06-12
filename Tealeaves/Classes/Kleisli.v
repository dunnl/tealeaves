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
Section kc.

  Context
    (E : Type).

  Definition kc6
    {A B C}
    (G1 G2 : Type -> Type)
    `{Map G1} `{Pure G1} `{Mult G1}
    `{Map G2} `{Pure G2} `{Mult G2} :
    (E * B -> G2 C) ->
    (E * A -> G1 B) ->
    (E * A -> G1 (G2 C)) :=
    fun g f => map G1 (E * B) (G2 C) g ∘ strength G1 ∘ cobind (prod E) A (G1 B) f.

End kc.

#[local] Infix "⋆6" := (kc6 _ _ _) (at level 60) : tealeaves_scope.

Section class.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Mapdt E T}.

  Class DecoratedTraversableFunctor :=
    { kdtfun_mapdt1 : forall (A : Type),
        mapdt E T (fun A => A) A A (extract (E ×) A) = @id (T A);
      kdtfun_mapdt2 : forall (G1 G2 : Type -> Type)
                        `{Applicative G1} `{Applicative G2}
                        (A B C : Type)
                        `(g : E * B -> G2 C) `(f : E * A -> G1 B),
        map G1 (T B) (G2 (T C)) (mapdt E T G2 B C g) ∘ mapdt E T G1 A B f = mapdt E T (G1 ∘ G2) A C (g ⋆6 f);
      kdtfun_morph : forall `{ApplicativeMorphism G1 G2 ϕ} `(f : E * A -> G1 B),
        mapdt E T G2 A B (ϕ B ∘ f) = ϕ (T B) ∘ mapdt E T G1 A B f;
    }.

End class.

(** ** Decorated traversable monad *)
(******************************************************************************)
