From Tealeaves Require Export
  Classes.Applicative
  Classes.Comonad
  Functors.Environment.

Import Product.Notations.

#[local] Generalizable Variables ϕ G A B C.

(** * Kleisli presentation *)
(******************************************************************************)

(** ** Operation <<fmapdt>> *)
(******************************************************************************)
Section dt_operations.

  Context
    (W : Type)
    (F : Type -> Type).

  Class Fmapdt := fmapdt :
      forall `{Fmap G} `{Pure G} `{Mult G}
        {A B : Type} (f : W * A -> G B), F A -> G (F B).

End dt_operations.

#[local] Arguments fmapdt {W}%type_scope F%function_scope {Fmapdt}
  G%function_scope {H H0 H1} (A B)%type_scope f%function_scope _.

Definition kcompose_dt {A B C W : Type}
  `{Applicative G1}
  `{Applicative G2} :
  (W * B -> G2 C) ->
  (W * A -> G1 B) ->
  (W * A -> G1 (G2 C)) :=
  fun g f => fmap G1 g ∘ strength G1 ∘ cobind (prod W) f.

#[local] Notation "g ⋆dt f" := (kcompose_dt g f) (at level 40) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Section decorated_class.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Fmapdt E T}.

  Class DecoratedTraversableFunctor :=
    { kdtfun_fmapdt1 : forall (A : Type),
        fmapdt T (fun A => A) A A (extract (E ×)) = @id (T A);
      kdtfun_fmapdt2 : forall
        `{Applicative G1} `{Applicative G2}
        `(g : E * B -> G2 C) `(f : E * A -> G1 B),
        fmap G1 (fmapdt T G2 B C g) ∘ fmapdt T G1 A B f = fmapdt T (G1 ∘ G2) A C (g ⋆dt f);
      kdtfun_morph : forall `{ApplicativeMorphism G1 G2 ϕ} `(f : E * A -> G1 B),
        fmapdt T G2 A B (ϕ B ∘ f) = ϕ (T B) ∘ fmapdt T G1 A B f;
    }.

End decorated_class.

#[global] Arguments fmapdt {W}%type_scope F%function_scope {Fmapdt}
  G%function_scope {H H0 H1} {A B}%type_scope f%function_scope _.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "g ⋆dt f" := (kcompose_dt g f) (at level 40) : tealeaves_scope.

End Notations.
