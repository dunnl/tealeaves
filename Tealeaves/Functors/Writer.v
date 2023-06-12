From Tealeaves Require Export
  Classes.Monoid
  Classes.Monad
  Classes.Comonad
  Functors.Environment.

Import Product.Notations.
Import Functor.Notations.
Import Monoid.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables W T F A M.

(** * Writer monad *)
(** In the even that [A] is a monoid, the product functor forms a monad. The
    return operation maps <<b>> to <<(1, b)>> where <<1>> is the monoid unit.
    The join operation monoidally combines the two monoid values. *)
(******************************************************************************)
Section writer_monad.

  Context
    `{Monoid M}.

  #[export] Instance Return_writer : Return (prod M) :=
    fun A (a : A) => (Ƶ, a).

  #[export] Instance Bind_writer : Bind (prod M) (prod M) :=
    fun A B (f : A -> M * B) (p : M * A) =>
      map_fst (uncurry (@monoid_op M _)) (α^-1 (map_snd f p)).

  #[export] Instance Natural_ret_writer : Natural (@ret (prod M) Return_writer).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. now ext a.
  Qed.

  #[export, program] Instance Monad_writer : Monad (prod M).

  Solve Obligations with
    try (intros; unfold transparent tcs; ext p;
      unfold compose in *; destruct_all_pairs;
       cbn; now simpl_monoid).

  Admit Obligations.

End writer_monad.

Section misc.

  Context
    (W : Type)
    `{Monoid W}.

  Lemma extract_pair {A : Type} :
    forall (w : W), extract (W ×) A ∘ pair w = id.
  Proof.
    reflexivity.
  Qed.

  Lemma extract_incr {A : Type} :
    forall (w : W), extract (W ×) A ∘ incr W w = extract (W ×) A.
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma extract_preincr {A : Type} :
    forall (w : W), extract (W ×) A ⦿ w = extract (W ×) A.
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma extract_preincr2 {A B : Type} (f : A -> B) :
    forall (w : W), (f ∘ extract (W ×) A) ⦿ w = f ∘ extract (W ×) A.
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma preincr_ret {A B : Type} : forall (f : W * A -> B) (w : W),
      (f ⦿ w) ∘ ret (W ×) A = f ∘ pair w.
  Proof.
    intros. ext a. cbv.
    change (op w unit0) with (w ● Ƶ).
    now simpl_monoid.
  Qed.

End misc.
