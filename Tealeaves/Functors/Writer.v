From Tealeaves Require Export
  Classes.Monoid
  Classes.Monad
  Functors.Environment.

Import Product.Notations.
Import Functor.Notations.
Import Strength.Notations.
Import Monoid.Notations.
Import Monad.Notations.

#[local] Generalizable Variables W T F A M.

(** ** <<incr>> *)
(******************************************************************************)
Section incr.

  Context
    `{Monoid W}.

  (* It sometimes useful to have this curried operation, the
  composition of [strength] and [join]. *)
  Definition incr {A : Type} : W -> W * A -> W * A :=
    fun w2 '(w1, a) => (w2 ● w1, a).

  Lemma incr_zero {A : Type} :
    incr Ƶ = @id (W * A).
  Proof.
    ext [? ?]. cbn. now simpl_monoid.
  Qed.

  Lemma incr_incr {A : Type} : forall w1 w2,
    incr (A:=A) w2 ∘ incr w1 = incr (w2 ● w1).
  Proof.
    intros. ext [w a].
    cbn. now simpl_monoid.
  Qed.

  Lemma extract_incr {A : Type} :
    forall (w : W), extract (W ×) ∘ incr w = extract (W ×) (A := A).
  Proof.
    intros. now ext [w' a].
  Qed.

End incr.


(** ** Properties of <<strength>> w.r.t. monad operations *)
(** Formalizing the product functor allows expressing some general
    properties about how the monad operations interact with the
    tensorial strength operation. These laws play a role in reasoning
    about decorated monads in particular. *)
(******************************************************************************)
Section Monad_strength_laws.

  Context
    (T : Type -> Type)
    {W : Type}
    `{Monad T}.

  Import Monad.ToFunctor.

  Lemma strength_ret : forall (A : Type),
      σ T ∘ fmap (W ×) (ret T) = ret T (A := W * A).
  Proof.
    intros. ext [w a]. unfold compose; cbn. compose near a on left.
    now rewrite (natural (G := T) (F := fun A => A)).
  Qed.

  Lemma strength_bind : forall (A B : Type) (f : A -> T B),
      σ T ∘ fmap (W ×) (bind T f) =
        bind T (σ T ∘ fmap (W ×) f) ∘ σ T.
  Proof.
    intros. ext [w t].
    change_left (σ T (w, bind T f t)).
    unfold Strength.strength, compose.
    compose near t on left.
    rewrite (fmap_bind T).
    compose near t on right.
    rewrite (bind_fmap T).
    reflexivity.
  Qed.

End Monad_strength_laws.

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
    fun A B (f : A -> M * B) (p : M * A) => map_fst (uncurry (@monoid_op M _)) (α^-1 (map_snd f p)).


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
