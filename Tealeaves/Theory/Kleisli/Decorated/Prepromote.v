From Tealeaves Require Export
  Util.Prelude
  Classes.Monoid
  Functors.Writer.
From Tealeaves Require
  Classes.Kleisli.Decorated.Monad.

Import Decorated.Monad (prepromote).
Import Monoid.Notations.
Import Product.Notations.
Import Strength.Notations.

#[local] Generalizable Variables W A B.

(** * The <<prepromote>> operation *)
(** A decorated monad is a decorated functor whose monad operations
    are compatible with the decorated structure. *)
(******************************************************************************)
Lemma prepromote_zero `{Monoid W} : forall `(f : W * A -> B),
    prepromote Ƶ f = f.
Proof.
  intros. unfold prepromote.
  now rewrite incr_zero.
Qed.

Lemma prepromote_prepromote1 `{Monoid W} : forall `(f : W * A -> B) (w1 : W) (w2 : W),
    prepromote w1 (prepromote w2 f) = f ∘ incr w2 ∘ incr w1.
Proof.
  intros. unfold prepromote.
  now ext [w0 a].
Qed.

Lemma prepromote_prepromote2 `{Monoid W} : forall `(f : W * A -> B) (w1 : W) (w2 : W),
    prepromote w1 (prepromote w2 f) = f ∘ incr (w2 ● w1).
Proof.
  intros. rewrite prepromote_prepromote1.
  now rewrite <- (incr_incr).
Qed.

Lemma prepromote_incr `{Monoid W} : forall `(f : W * A -> B) (w1 : W) (w2 : W),
    prepromote w1 (f ∘ incr w2) = prepromote (w2 ● w1) f.
Proof.
  intros. unfold prepromote.
  now rewrite <- (incr_incr).
Qed.

Lemma prepromote_ret `{Monoid W} : forall `(f : W * A -> B) (w : W),
    prepromote w f ∘ ret (W ×) = f ∘ pair w.
Proof.
  intros. ext a.
  cbv. now simpl_monoid.
Qed.

Lemma prepromote_extract `{Monoid W} : forall `(f : A -> B) (w : W),
    prepromote w (f ∘ extract (W ×)) = f ∘ extract (W ×).
Proof.
  intros. ext [w' a]. unfold compose. cbn.
  reflexivity.
Qed.

Lemma prepromote_extract2 `{Monoid W} : forall (A : Type) (w : W),
    prepromote w (extract (W ×)) = extract (W ×) (A := A).
Proof.
  intros. ext [w' a]. unfold compose. cbn.
  reflexivity.
Qed.
