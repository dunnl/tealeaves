From Tealeaves Require Export
  Classes.Categorical.Applicative.

Import Applicative.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ F G A B C.

Class ApplicativeCommutativeIdempotent (G : Type -> Type)
    `{Map G} `{Pure G} `{Mult G} :=
  { appci_applicative :> Applicative G;
    appci_idempotent : forall (A : Type) (x : G A),
      x ⊗ x = map (fun a => (a, a)) x;
    appci_commutative : forall (A B : Type) (x : G A) (y: G B),
      x ⊗ y = map (fun '(x, y) => (y, x)) (y ⊗ x);
  }.
