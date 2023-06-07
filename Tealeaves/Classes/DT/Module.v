From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Classes.Comonad.
From Tealeaves Require
  Classes.Monad
  Classes.Kleisli.Decorated.Monad.

Import Monad (Return, ret).
Import Decorated.Monad (prepromote).

Import Product.Notations.

Section class.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Return T}
    `{Binddt W T T} `{Binddt W T F}
    `{Monoid_op W} `{Monoid_unit W}.

  Class RightModule :=
    { kdtmd_monad :> Monad W T;
      kdtmd_binddt1 : forall (A : Type),
        binddt W T F (fun A => A) A A (ret T ∘ extract (prod W)) = @id (F A);
      kdtmd_binddt2 :
      forall (A B C : Type) `{Applicative G1} `{Applicative G2}
        (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
        fmap G1 (binddt W T F G2 B C g) ∘ binddt W T F G1 A B f =
          binddt W T F (G1 ∘ G2) A C (g ⋆dtm f);
    }.

End class.

#[export] Arguments binddt {W}%type_scope {T}%function_scope (F)%function_scope
  {Binddt} G%function_scope {A B}%type_scope {H H0 H1} _%function_scope _.
