From Tealeaves Require Export
  Classes.Kleisli.Decorated.Monad.
From Tealeaves Require Import
  Classes.Kleisli.Monad
  Theory.Kleisli.Decorated.Prepromote.

Import Kleisli.Monad.Notations.
Import Decorated.Monad.Notations.
Import Product.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables W T A B C.

Section kleisli_composition.

  Context
    `{Decorated.Monad.Monad W T}.

  (** * Kleisli composition *)
  (******************************************************************************)
  Lemma kcompose_incr : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      (g ∘ incr w) ⋆dm (f ∘ incr w) = (g ⋆dm f) ∘ incr w.
  Proof.
    intros. unfold kcomposed.
    ext [w' a]. rewrite prepromote_incr.
    reflexivity.
  Qed.

  Lemma precompose_kcompose : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      prepromote w (g ⋆dm f) = prepromote w (g ⋆dm f).
  Proof.
    reflexivity.
  Qed.

  Theorem dm_kleisli_id_r {B C} : forall (g : W * B -> T C),
      g ⋆dm (ret T ∘ extract (W ×)) = g.
  Proof.
    intros. unfold kcomposed.
    ext [w a]. unfold compose. cbn.
    compose near a on left.
    rewrite (kmond_bindd0 T _).
    now cbv; simpl_monoid.
  Qed.

  Theorem dm_kleisli_id_l {A B} : forall (f : W * A -> T B),
      (ret T ∘ extract (W ×)) ⋆dm f = f.
  Proof.
    intros. unfold kcomposed.
    ext [w a]. rewrite prepromote_extract.
    now rewrite (kmond_bindd1 T _).
  Qed.

  Theorem dm_kleisli_assoc {A B C D} : forall (h : W * C -> T D) (g : W * B -> T C) (f : W * A -> T B),
      h ⋆dm (g ⋆dm f) = (h ⋆dm g) ⋆dm f.
  Proof.
    intros. unfold kcomposed at 3.
    ext [w a]. unfold prepromote.
    rewrite <- kcompose_incr.
    rewrite <- (kmond_bindd2 T).
    reflexivity.
  Qed.

End kleisli_composition.
