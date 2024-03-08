From Tealeaves Require Export
  Tactics.Prelude
  Classes.Functor
  Misc.Product
  Misc.Strength
  Functors.Identity
  Functors.Compose
  Classes.Categorical.Applicative (Pure, pure).

#[local] Generalizable Variables G A B C.

(** * Applicative functors *)
(******************************************************************************)
Class Ap (F : Type -> Type) :=
  ap : forall {A B : Type}, F (A -> B) -> F A -> F B.

Notation "Gf <⋆> Ga" := (ap Gf Ga) (at level 50, left associativity).

Class Applicative
        (G : Type -> Type)
        `{Pure G} `{Ap G} :=
  { ap1: forall `(t: G A), pure id <⋆> t = t;
    ap2: forall `(f : A -> B) (a : A),
      pure f <⋆> pure a = pure (f a);
    ap3: forall `(f : G (A -> B)) (a : A),
      f <⋆> pure a = pure (fun f => f a) <⋆> f;
    ap4: forall {A B C : Type} (f : G (B -> C)) (g : G (A -> B)) (a : G A),
      (pure compose) <⋆> f <⋆> g <⋆> a =
        f <⋆> (g <⋆> a)
  }.

Section Derived.

  Context
    `{Pure G} `{Ap G}.

  #[local] Instance Map_PureAp: Map G :=
    fun A B (f: A -> B) (a: G A) => pure f <⋆> a.

  #[export] Instance Functor_Applicative
   `{! Applicative G}: Functor G.
  Proof.
    constructor.
    - intros. unfold_ops @Map_PureAp.
      ext a. apply ap1.
    - intros. unfold_ops @Map_PureAp.
      ext a. unfold compose.
      rewrite <- ap4.
      rewrite ap2.
      rewrite ap2.
      reflexivity.
  Qed.

  Import Categorical.Applicative (Mult, Applicative).

  #[local] Instance Mult_PureAp: Mult G :=
    fun A B (p: G A * G B) =>
      match p with
      | (a, b) => pure pair <⋆> a <⋆> b : G (A * B)
      end.

  #[local] Instance CatApp_App
    `{! Applicative.Applicative G}:
    Categorical.Applicative.Applicative G.
  Proof.
    constructor.
    - typeclasses eauto.
    - intros.
      unfold_ops @Map_PureAp.
      now rewrite ap2.
    - intros.
      unfold_ops @Mult_PureAp @Map_PureAp.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      rewrite ap3.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      reflexivity.
    - intros.
      unfold_ops @Mult_PureAp @Map_PureAp.
      repeat (rewrite <- ap4; repeat rewrite ap2).
      rewrite ap3.
      repeat (rewrite <- ap4; repeat rewrite ap2).
      reflexivity.
    - intros.
      unfold_ops @Mult_PureAp @Map_PureAp.
      repeat (rewrite <- ap4; repeat rewrite ap2).
      change (left_unitor ∘ pair tt) with (@id A).
      rewrite ap1.
      reflexivity.
    - intros.
      unfold_ops @Mult_PureAp @Map_PureAp.
      repeat (rewrite <- ap4; repeat rewrite ap2).
      rewrite ap3.
      repeat (rewrite <- ap4; repeat rewrite ap2).
      apply ap1.
    - intros.
      unfold_ops @Mult_PureAp @Map_PureAp.
      repeat (rewrite <- ap4; repeat rewrite ap2).
      rewrite ap3.
      repeat (rewrite <- ap4; repeat rewrite ap2).
      reflexivity.
  Qed.

End Derived.
