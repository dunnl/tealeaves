From Tealeaves Require Export
  Classes.Categorical.Comonad
  Functors.Early.Reader.

Import Product.Notations.
Import Functor.Notations.

#[local] Generalizable Variables W T F E A.
#[local] Arguments map F%function_scope {Map}
  {A B}%type_scope f%function_scope _.
#[local] Arguments extract (W)%function_scope {Extract}
  (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin}
  {A}%type_scope _.

(** * Decorated functors *)
(**********************************************************************)

(** ** Operations *)
(**********************************************************************)
Class Decorate
  (E: Type)
  (F: Type -> Type) :=
  dec: F ⇒ F ○ (E ×).

#[global] Arguments dec {E}%type_scope _%function_scope {Decorate}
  {A}%type_scope _.
#[local] Arguments dec {E}%type_scope _%function_scope {Decorate}
  (A)%type_scope _.

(** ** Typeclass *)
(**********************************************************************)
Class DecoratedFunctor
  (E: Type)
  (F: Type -> Type)
  `{Map F}
  `{Decorate E F} :=
  { dfun_functor :> Functor F;
    dfun_dec_natural :> Natural (@dec E F _);
    dfun_dec_dec: forall (A: Type),
      dec F (E * A) ∘ dec F A = map F (cojoin (prod E)) ∘ dec F A;
    dfun_dec_extract: forall (A: Type),
      map F (extract (E ×) A) ∘ dec F A = @id (F A);
  }.

(** ** Decoration-preserving natural transformations *)
(**********************************************************************)
Class DecoratePreservingTransformation
  (F G: Type -> Type)
  `{! Map F} `{Decorate E F}
  `{! Map G} `{Decorate E G}
  (ϕ: F ⇒ G) :=
  { dectrans_commute: `(ϕ (E * A) ∘ dec F A = dec G A ∘ ϕ A);
    dectrans_natural: Natural ϕ;
  }.

(** * Decorated functor instance for [Reader] *)
(**********************************************************************)
Section DecoratedFunctor_reader.

  Context
    (E: Type).

  #[global] Instance Decorate_prod: Decorate E (prod E)
    := @cojoin (prod E) _.

  #[global, program] Instance DecoratedFunctor_prod:
    DecoratedFunctor E (prod E).

  Solve Obligations with (intros; now ext [? ?]).

End DecoratedFunctor_reader.
