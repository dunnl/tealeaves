From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Functors.Early.Writer.

Import Monoid.Notations.

#[local] Generalizable Variables W T.

(** * Decorated Monads *)
(******************************************************************************)

(** ** The [bindd] operation *)
(******************************************************************************)
Class Bindd (W: Type) (T U: Type -> Type):=
  bindd: forall (A B: Type), (W * A -> T B) -> U A -> U B.

#[global] Arguments bindd {W}%type_scope {T U}%function_scope {Bindd} {A B}%type_scope.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc5 {W: Type} {T: Type -> Type}
  `{Bindd W T T} `{Monoid_op W}
  {A B C: Type}:
  (W * B -> T C) ->
  (W * A -> T B) ->
  (W * A -> T C) :=
  fun g f '(w, a) =>
    @bindd W T T _ B C (g ⦿ w) (f (w, a)).

#[local] Infix "⋆5" := (kc5) (at level 60): tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedRightPreModule (W: Type) (T U: Type -> Type)
  `{op: Monoid_op W}
  `{ret_T: Return T}
  `{bindd_TT: Bindd W T T}
  `{bindd_TU: Bindd W T U} :=
  { kdmod_bindd1: forall (A: Type),
      bindd (U := U) (ret ∘ extract (A := A)) = id;
    kdmod_bindd2: forall (A B C: Type) (g: W * B -> T C) (f: W * A -> T B),
      bindd (U := U) g ∘ bindd f = bindd (g ⋆5 f);
  }.

Class DecoratedMonad
  (W: Type)
  (T: Type -> Type)
  `{op: Monoid_op W}
  `{unit: Monoid_unit W}
  `{retT: Return T}
  `{bindd_TT: Bindd W T T} :=
  { kdm_monoid :> Monoid W;
    kdm_premod :> DecoratedRightPreModule W T T;
    kdm_bindd0: forall (A B: Type) (f: W * A -> T B),
      bindd f ∘ ret = f ∘ ret;
  }.

Lemma kdm_bindd1 `{DecoratedMonad W T}:
  forall (A: Type), bindd (ret ∘ extract) = @id (T A).
Proof.
  apply kdmod_bindd1.
Qed.

Lemma kdm_bindd2 `{DecoratedMonad W T}:
  forall (A B C: Type) (g: W * B -> T C) (f: W * A -> T B),
    bindd g ∘ bindd f = bindd (g ⋆5 f).
Proof.
  apply kdmod_bindd2.
Qed.

(** ** Homomorphisms *)
(******************************************************************************)
Class DecoratedMonadHom (W: Type) (T U: Type -> Type)
  `{Return T} `{Bindd W T T}
  `{Return U} `{Bindd W U U}
  (ϕ: forall (A: Type), T A -> U A) :=
  { kdmhom_bind : forall (A B : Type) (f : W * A -> T B),
      ϕ B ∘ @bindd W T T _ A B f = @bindd W U U _ A B (ϕ B ∘ f) ∘ ϕ A;
    kdmhom_ret : forall (A : Type),
      ϕ A ∘ @ret T _ A = @ret U _ A;
  }.

(** ** RightModules *)
(******************************************************************************)
Class DecoratedRightModule
  (W : Type) (T : Type -> Type) (U : Type -> Type)
  `{Monoid_op W} `{Monoid_unit W}
  `{Return T} `{Bindd W T T} `{Bindd W T U} :=
  { kdmod_monad :> DecoratedMonad W T;
    kdmod_premod :> DecoratedRightPreModule W T U;
  }.

(** ** Homomorphisms *)
(******************************************************************************)
Class DecoratedRightModuleHom (T U V : Type -> Type)
  `{op: Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return T} `{Bindd W T U} `{Bindd W T V}
  (ϕ : forall (A : Type), U A -> V A) :=
  { kdmod_hom_bind : forall (A B : Type) (f : W * A -> T B),
      ϕ B ∘ @bindd W T U _ A B f = @bindd W T V _ A B f ∘ ϕ A;
  }.

Class ParallelDecoratedRightModuleHom
  (T T' U V : Type -> Type)
  `{Return T}
  `{Bindd W T U}
  `{Bindd W T' V}
  (ψ : forall (A : Type), T A -> T' A)
  (ϕ : forall (A : Type), U A -> V A) :=
  { kdmod_parhom_bind : forall (A B : Type) (f : W * A -> T B),
      ϕ B ∘ bindd f = bindd (ψ B ∘ f) ∘ ϕ A;
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆5" := (kc5) (at level 60) : tealeaves_scope.
  Include Monoid.Notations.
End Notations.
