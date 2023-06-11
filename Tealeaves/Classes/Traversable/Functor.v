From Tealeaves Require Export
  Classes.Applicative
  Functors.Batch.

#[local] Generalizable Variable G A B C ϕ.

(** * "Kleisi"-style presentation of traversable functors *)
(******************************************************************************)
Section operations.

  Class Traverse
    (T : Type -> Type) := traverse :
      forall (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G} (A B : Type)
        (f : A -> G B), T A -> G (T B).

End operations.

(* We don't give a dedicated name or notation to the composition
   operation <<g ⋆ f = fmap F g ∘ f>> because it is trivial and one
   wants to avoid making up too many notations. *)

#[local] Arguments traverse (T)%function_scope {Traverse}
  G%function_scope {H H0 H1} (A B)%type_scope f%function_scope _.

Section class.

  Context
    (T : Type -> Type)
    `{Traverse T}.

  Class TraversableFunctor :=
    { trf_traverse_id : forall (A : Type),
        traverse T (fun A => A) A A id = @id (T A);
      trf_traverse_traverse :
      forall (G1 G2 : Type -> Type)
        `(Applicative G2) `(Applicative G1)
          `(g : B -> G2 C) `(f : A -> G1 B),
          fmap G1 (traverse T G2 B C g) ∘ traverse T G1 A B f =
            traverse T (G1 ∘ G2) A C (fmap G1 g ∘ f);
      trf_traverse_morphism : forall `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : A -> G1 B),
          ϕ (T B) ∘ traverse T G1 A B f = traverse T G2 A B (ϕ B ∘ f);
    }.

End class.

#[global] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} {A B}%type_scope f%function_scope _.


(** ** Naturality properties for <<toBatch>> *)
(******************************************************************************)
Section naturality.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.



End naturality.

#[local] Generalizable Variable M.
