From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Classes.Monad.

#[local] Generalizable Variables T G A B ϕ.

Section operations.

  Context
    (T : Type -> Type)
    (F : Type -> Type).

  Class Bindt :=
    bindt : forall (G : Type -> Type) (A B : Type) `{Fmap G} `{Pure G} `{Mult G},
        (A -> G (T B)) -> F A -> G (F B).

End operations.

Definition kcompose_tm
  {A B C : Type}
  `{Fmap G1} `{Pure G1} `{Mult G1}
  `{Fmap G2} `{Pure G2} `{Mult G2}
  `{Bindt T T} :
  (B -> G2 (T C)) ->
  (A -> G1 (T B)) ->
  (A -> G1 (G2 (T C))) :=
  fun g f => fmap G1 (bindt T T G2 B C g) ∘ f.

#[local] Infix "⋆tm" := kcompose_tm (at level 60) : tealeaves_scope.

Section class.

  Context
    (T : Type -> Type)
    `{Return T}
    `{Bindt T T}.

  Class Monad :=
    { ktm_bindt0 : forall (A B : Type) `{Applicative G} (f : A -> G (T B)),
        bindt T T G A B f ∘ ret T = f;
      ktm_bindt1 : forall (A : Type),
        bindt T T (fun A => A) A A (ret T) = @id (T A);
      ktm_bindt2 : forall (A B C : Type) `{Applicative G1} `{Applicative G2}
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        fmap G1 (bindt T T G2 B C g) ∘ bindt T T G1 A B f =
          bindt T T (G1 ∘ G2) A C (g ⋆tm f);
      ktm_morph : forall `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : A -> G1 (T B)),
          ϕ (T B) ∘ bindt T T G1 A B f = bindt T T G2 A B (ϕ (T B) ∘ f);
    }.

End class.

#[global] Arguments bindt {T}%function_scope (F)%function_scope
  {Bindt} G%function_scope {A B}%type_scope {H H0 H1} _%function_scope _.

Module Notations.

  Infix "⋆tm" := kcompose_tm (at level 60) : tealeaves_scope.

End Notations.
