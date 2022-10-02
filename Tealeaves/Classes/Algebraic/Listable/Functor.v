From Tealeaves Require Export
  Classes.Monoid
  Classes.Algebraic.Monad
  Classes.Algebraic.Setlike.Functor
  Functors.List
  Functors.Sets.

Import Classes.Functor.Notations.

#[local] Generalizable Variable A.

(** * The [shape] operation *)
(******************************************************************************)
Definition shape (F : Type -> Type) `{Fmap F} {A} : F A -> F unit :=
  fmap F (const tt).

(** * Listable functors *)
(** A [ListableFunctor] <<F>> is an endofunctor with a natural transformation to
    [list]. This is closely related to the typeclass <<Foldable>> of the GHC
    standard library for Haskell
    (https://wiki.haskell.org/Foldable_and_Traversable), but Haskell's typeclass
    is not a subset of functors for technical reasons. Furthermore Haskell's
    typeclass is based on a "fold" operation while we take [tolist] as the
    primary class method. *)
(******************************************************************************)

Section ListableFunctor_operations.

  Context
    (F : Type -> Type).

  Class Tolist :=
    tolist : F ⇒ list.

  Definition shapeliness `{Fmap F} `{Tolist} := forall A (t1 t2 : F A),
      shape F t1 = shape F t2 /\ tolist _ t1 = tolist _ t2 -> t1 = t2.

End ListableFunctor_operations.

Arguments tolist F%function_scope {Tolist} {A}%type_scope _.

Section ListableFunctor.

  Context
    (F : Type -> Type)
    `{Fmap F} `{Tolist F}.

  Class ListableFunctor :=
    { lfun_natural :> Natural (@tolist F _);
      lfun_functor :> Functor F;
      lfun_shapeliness : shapeliness F;
    }.

End ListableFunctor.

(** ** <<tolist>>-preserving natural transformations *)
(** A [ListPreservingTransformation] is a natural transformation
    between two listable functors that commutes with [tolist]. This is
    an operation that modifies the shape and type of a container without
    changing its leaves or their order. *)
(******************************************************************************)
Class ListPreservingTransformation
      {F G : Type -> Type}
      `{! Fmap F} `{Tolist F}
      `{! Fmap G} `{Tolist G}
      (η : F ⇒ G) :=
  { ltrans_commute : `(tolist F = tolist G ∘ η A);
    ltrans_natural : Natural η;
  }.

(** ** Instance for [list] *)
(** As a reasonability check, we prove that [list] is a listable functor. *)
(******************************************************************************)
#[export] Instance Tolist_list : Tolist list := fun A l => l.

Section ListableFunctor_list.

  Instance: Natural (@tolist list _).
  Proof.
    constructor; try typeclasses eauto.
    reflexivity.
  Qed.

  Theorem shapeliness_list : shapeliness list.
  Proof.
    intros A t1 t2. intuition.
  Qed.

  #[program] Instance: ListableFunctor list :=
    {| lfun_shapeliness := shapeliness_list; |}.

End ListableFunctor_list.
