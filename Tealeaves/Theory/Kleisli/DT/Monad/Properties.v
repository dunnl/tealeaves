From Tealeaves Require Export
  Classes.Kleisli.DT.Monad
  Theory.Kleisli.DT.Monad.ToFunctor
  Functors.Schedule.

Import Product.Notations.
Import Applicative.Notations.
Import Schedule.Notations.
#[local] Generalizable Variables W F M A B.

(** * Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import ToFunctor.Operation.
  Import ToFunctor.Instance.

  Lemma binddt_constant_applicative1
        `{Monoid M} {B : Type}
        `(f : W * A -> const M (T B)) :
    binddt (B := B) T (const M) f =
    binddt (B := False) T (const M) (f : W * A -> const M (T False)).
  Proof.
    change_right (fmap (B := T B) (const M) (fmap T exfalso)
                    ∘ (binddt (B := False) T (const M) (f : W * A -> const M (T False)))).
    rewrite (fmap_binddt T (const M)).
    - reflexivity.
    - typeclasses eauto.
  Qed.

  Lemma binddt_constant_applicative2 (fake1 fake2 : Type) `{Monoid M}
        `(f : W * A -> const M (T B)) :
    binddt (B := fake1) T (const M)
            (f : W * A -> const M (T fake1))
    = binddt (B := fake2) T (const M)
              (f : W * A -> const M (T fake2)).
  Proof.
    intros. rewrite (binddt_constant_applicative1 (B := fake1)).
    rewrite (binddt_constant_applicative1 (B := fake2)). easy.
  Qed.

End lemmas.
