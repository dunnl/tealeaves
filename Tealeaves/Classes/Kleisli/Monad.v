From Tealeaves Require Export
  Tactics.Prelude
  Functors.Identity.

Import Functor.Notations.

#[local] Generalizable Variable T.

(** * Monads *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Class Return (T : Type -> Type) :=
  ret : (fun A => A) ⇒ T.

Class Bind (T U : Type -> Type) :=
  bind : forall (A B : Type), (A -> T B) -> U A -> U B.

#[global] Arguments ret {T}%function_scope {Return} {A}%type_scope.
#[global] Arguments bind {T} {U}%function_scope {Bind} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc1 {T : Type -> Type} `{Return T} `{Bind T T}
  {A B C : Type} (g : B -> T C) (f : A -> T B) : (A -> T C) :=
  @bind T T _ B C g ∘ f.

#[local] Infix "⋆1" := (kc1) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class RightPreModule
  (T U : Type -> Type)
  `{Return T} `{Bind T T} `{Bind T U} :=
  { kmod_bind1: forall (A : Type),
      bind (U := U) ret = @id (U A);
    kmod_bind2: forall (A B C : Type) (g : B -> T C) (f : A -> T B),
      bind (U := U) g ∘ bind f = bind (g ⋆1 f);
  }.

Class Monad (T : Type -> Type)
  `{Return_inst : Return T}
  `{Bind_inst : Bind T T} :=
  { kmon_bind0 : forall (A B : Type) (f : A -> T B),
      bind f ∘ ret = f;
    kmon_premod :> RightPreModule T T;
  }.

(* right unit law of the monoid *)
Lemma kmon_bind1 `{Monad T} : forall (A : Type),
    @bind T T _ A A (@ret T _ A) = @id (T A).
Proof.
  apply kmod_bind1.
Qed.

(* associativity of the monoid *)
Lemma kmon_bind2 `{Monad T} : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
    @bind T T _ B C g ∘ @bind T T _ A B f = @bind T T _ A C (g ⋆1 f).
Proof.
  apply kmod_bind2.
Qed.

(** ** Homomorphisms *)
(******************************************************************************)
Class MonadHom (T U : Type -> Type)
  `{Return T} `{Bind T T}
  `{Return U} `{Bind U U}
  (ϕ : forall (A : Type), T A -> U A) :=
  { kmon_hom_bind : forall (A B : Type) (f : A -> T B),
      ϕ B ∘ bind f = bind (ϕ B ∘ f) ∘ ϕ A;
    kmon_hom_ret : forall (A : Type),
      ϕ A ∘ ret (T := T) = ret;
  }.

(** ** Right modules *)
(******************************************************************************)
Class RightModule (T : Type -> Type) (U : Type -> Type)
  `{Return T} `{Bind T T} `{Bind T U} :=
  { kmod_monad :> Monad T;
    kmod_premod :> RightPreModule T U;
  }.

(** ** Homomorphisms *)
(******************************************************************************)
Class RightModuleHom (T U V : Type -> Type)
  `{Return T} `{Bind T U} `{Bind T V}
  (ϕ : forall (A : Type), U A -> V A) :=
  { kmod_hom_bind : forall (A B : Type) (f : A -> T B),
      ϕ B ∘ @bind T U _ A B f = @bind T V _ A B f ∘ ϕ A;
  }.

Class ParallelRightModuleHom (T T' U V : Type -> Type)
  `{Return T} `{Bind T U} `{Bind T' V}
  (ψ : forall (A : Type), T A -> T' A)
  (ϕ : forall (A : Type), U A -> V A) :=
  { kmodpar_hom_bind : forall (A B : Type) (f : A -> T B),
      ϕ B ∘ @bind T U _ A B f = @bind T' V _ A B (ψ B ∘ f) ∘ ϕ A;
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆1" := (kc1) (at level 60) : tealeaves_scope.
End Notations.
