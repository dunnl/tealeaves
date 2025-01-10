From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Categorical.ContainerFunctor
  Functors.Early.Subset
  Functors.Early.Ctxset
  Functors.Early.Environment.

Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.

#[local] Generalizable Variables E T.

(** * Container-like functors with context *)
(******************************************************************************)

(** ** <<toctxset>> operation *)
(******************************************************************************)
Class ToCtxset (E: Type) (F: Type -> Type) :=
  toctxset: forall A: Type, F A -> ctxset E A.

#[global] Arguments toctxset {E}%type_scope {F}%function_scope
  {ToCtxset} {A}%type_scope _.

(** ** <<element_ctx_of>> operation (∈d) *)
(******************************************************************************)
Definition element_ctx_of `{ToCtxset E T} {A: Type}:
  E * A -> T A -> Prop := fun p t => toctxset t p.
#[local] Notation "x ∈d t" :=
  (element_ctx_of x t) (at level 50): tealeaves_scope.

Lemma element_ctx_of_toctxset `{ToCtxset E T} {A: Type}:
  forall (p:E*A), element_ctx_of p = evalAt p ∘ toctxset.
Proof.
  reflexivity.
Qed.
(** ** Typeclass *)
(******************************************************************************)
Class DecoratedContainerFunctor
  (E: Type) (F: Type -> Type)
  `{Mapd E F} `{ToCtxset E F} :=
  { dcont_functor :> DecoratedFunctor E F;
    dcont_natural :> DecoratedHom E F (ctxset E) (@toctxset E _ _);
    dcont_pointwise: forall (A B: Type) (t: F A) (f g: E * A -> B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> mapd f t = mapd g t;
  }.

(** ** [ToCtxset]-preserving Natural transformations *)
(******************************************************************************)
Class DecoratedContainerTransformation
  {E: Type} {F G: Type -> Type}
  `{Map F} `{Mapd E F} `{ToCtxset E F}
  `{Map G} `{Mapd E G} `{ToCtxset E G}
  (η: F ⇒ G) :=
  { dcont_trans_natural: Natural η;
    dcont_trans_commute :
    forall A, toctxset (F := F) = toctxset (F := G) ∘ η A;
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈d t" :=
  (element_ctx_of x t) (at level 50): tealeaves_scope.

End Notations.
