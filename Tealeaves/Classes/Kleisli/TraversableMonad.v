From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.Monad.

#[local] Generalizable Variables U T G A B C D ϕ M f.
(** * Traversable monad *)
(******************************************************************************)

(** ** [bindt] operation *)
(******************************************************************************)
Class Bindt (T: Type -> Type) (U: Type -> Type) :=
  bindt: forall (G : Type -> Type) `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G}
           (A B : Type), (A -> G (T B)) -> U A -> G (U B).

#[global] Arguments bindt {T U}%function_scope {Bindt} {G}%function_scope
  {Map_G Pure_G Mult_G} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc3
  `{Bindt T T}
  {A B C: Type}
  {G1 G2: Type -> Type}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2}:
  (B -> G2 (T C)) ->
  (A -> G1 (T B)) ->
  (A -> G1 (G2 (T C))) :=
  fun g f => map (F := G1) (bindt g) ∘ f.

#[local] Infix "⋆3" := (kc3) (at level 60): tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class TraversableRightPreModule (T: Type -> Type) (U: Type -> Type)
  `{Return_T: Return T}
  `{Bindt_TT: Bindt T T}
  `{Bindt_TU: Bindt T U} :=
  { ktm_bindt1: forall (A: Type),
      bindt (U := U) (G := fun A => A) (ret (T := T)) = @id (U A);
    ktm_bindt2:
    forall `{Applicative G1} `{Applicative G2} (A B C: Type)
      (g: B -> G2 (T C)) (f: A -> G1 (T B)),
      map (F := G1) (bindt g) ∘ bindt (U := U) f =
        bindt (U := U) (kc3 (G1 := G1) (G2 := G2) g f);
    ktm_morph:
    forall `{morphism: ApplicativeMorphism G1 G2 ϕ}
      (A B: Type) `(f: A -> G1 (T B)),
      ϕ (U B) ∘ bindt (U := U) f = bindt (ϕ (T B) ∘ f);
  }.

Class TraversableMonad (T: Type -> Type)
  `{Return_T: Return T}
  `{Bindt_T: Bindt T T} :=
  { ktm_bindt0: forall `{Applicative G} (A B: Type) (f: A -> G (T B)),
      bindt f ∘ ret = f;
    ktm_premod :> TraversableRightPreModule T T;
  }.

Class TraversableRightModule (T U: Type -> Type)
  `{Return_T: Return T}
  `{Bindt_T: Bindt T T}
  `{Bindt_T: Bindt T U} :=
  { ktmod_monad :> TraversableMonad T;
    ktmod_premod :> TraversableRightPreModule T U;
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆3" := (kc3) (at level 60): tealeaves_scope.
End Notations.
