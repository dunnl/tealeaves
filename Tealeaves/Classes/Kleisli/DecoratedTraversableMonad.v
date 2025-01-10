From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.DecoratedTraversableFunctor
  Functors.Early.Writer.

Import Monoid.Notations.
Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedMonad.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import DecoratedTraversableFunctor.Notations.

#[local] Generalizable Variables ϕ U T W G A B C D F M.

(* TODO Find a better way to avoid cycles *)
#[local] Set Typeclasses Depth 5.

(** * Decorated traversable monads *)
(******************************************************************************)

(** ** Operation <<binddt>> *)
(******************************************************************************)
Class Binddt
  (W : Type)
  (T : Type -> Type)
  (U : Type -> Type)
  := binddt :
    forall (G : Type -> Type)
      `{Map G} `{Pure G} `{Mult G}
      (A B : Type),
      (W * A -> G (T B)) -> U A -> G (U B).

#[global] Arguments binddt {W}%type_scope {T} {U}%function_scope {Binddt}
  {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc7
  {W : Type}
  {T : Type -> Type}
  `{Return T}
  `{Binddt W T T}
  `{op: Monoid_op W} `{unit: Monoid_unit W}
  {A B C : Type}
  (G1 G2 : Type -> Type)
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2} :
  (W * B -> G2 (T C)) ->
  (W * A -> G1 (T B)) ->
  (W * A -> G1 (G2 (T C))) :=
  fun g f '(w, a) =>
    map (F := G1) (A := T B) (B := G2 (T C))
      (binddt (g ⦿ w)) (f (w, a)).

#[local] Infix "⋆7" := (kc7 _ _) (at level 60) : tealeaves_scope.

(** ** DTM typeclass *)
(******************************************************************************)
Class DecoratedTraversableRightPreModule
  (W : Type)
  (T U : Type -> Type)
  `{op : Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_inst : Return T}
  `{Bindd_T_inst : Binddt W T T}
  `{Bindd_U_inst : Binddt W T U} :=
  { kdtm_binddt1 : forall (A : Type),
      binddt (G := fun A => A)
        (ret (T := T) ∘ extract (W := (W ×))) = @id (U A);
    kdtm_binddt2 :
    forall `{Applicative G1} `{Applicative G2}
      `(g : W * B -> G2 (T C))
      `(f : W * A -> G1 (T B)),
      map (F := G1) (binddt g) ∘ binddt f = binddt (U := U) (G := G1 ∘ G2) (g ⋆7 f);
    kdtm_morph :
    forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ}
      `(f : W * A -> G1 (T B)),
      ϕ (U B) ∘ binddt f = binddt (ϕ (T B) ∘ f);
  }.

Class DecoratedTraversableMonad
  (W : Type)
  (T : Type -> Type)
  `{op : Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_inst : Return T}
  `{Bindd_T_inst : Binddt W T T} :=
  { kdtm_monoid :> Monoid W;
    kdtm_binddt0 : forall`{Applicative G} `(f : W * A -> G (T B)),
      binddt f ∘ ret = f ∘ ret (T := (W ×));
    kdtm_premod :> DecoratedTraversableRightPreModule W T T;
  }.

(** ** Homomorphisms *)
(******************************************************************************)
Class DecoratedTraversableMonadHom
  (T U : Type -> Type)
  `{Return T} `{Binddt W T T}
  `{Return U} `{Binddt W U U}
  (ϕ : forall (A : Type), T A -> U A) :=
  { kmon_hom_ret : forall (A : Type),
      ϕ A ∘ @ret T _ A = @ret U _ A;
    kmon_hom_bind : forall `{Applicative G}
      `(f : W * A -> G (T B)),
      map (F := G) (ϕ B) ∘ @binddt W T T _ G _ _ _ A B f =
        @binddt W U U _ G _ _ _ A B (map (F := G) (ϕ B) ∘ f) ∘ ϕ A;
  }.

(** ** Right modules *)
(******************************************************************************)
Class DecoratedTraversableRightModule
  (W : Type)
  (T U : Type -> Type)
  `{op : Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_inst : Return T}
  `{Bindd_T_inst : Binddt W T T}
  `{Bindd_U_inst : Binddt W T U}
  :=
  { kdtmod_monad :> DecoratedTraversableMonad W T;
    kdtmod_premod :> DecoratedTraversableRightPreModule W T U;
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆7" := (kc7 _ _) (at level 60) : tealeaves_scope.
End Notations.
