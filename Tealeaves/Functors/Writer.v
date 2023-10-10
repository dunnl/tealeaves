From Tealeaves Require Export
  Classes.Monoid
  Classes.Kleisli.Monad
  Classes.Kleisli.Comonad
  Functors.Environment.

Import Product.Notations.
Import Functor.Notations.
Import Monoid.Notations.
Import Monad.Notations.
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

  #[export] Instance Return_Writer : Return (prod M) :=
    fun A (a : A) => (Ƶ, a).

  #[export] Instance Bind_Writer : Bind (prod M) (prod M) :=
    fun A B (f : A -> M * B) (p : M * A) =>
      map_fst (uncurry (@monoid_op M _)) (α^-1 (map_snd f p)).

  #[export] Instance Natural_ret_Writer : Natural (@ret (prod M) Return_Writer).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. now ext a.
  Qed.

  Lemma Writer_kmon_bind0 : forall (A B : Type) (f : A -> M * B), bind (prod M) f ∘ ret (prod M) A = f.
  Proof.
    intros. ext a. unfold compose. unfold transparent tcs.
    cbn. destruct (f a). cbn. now simpl_monoid.
  Qed.

  Lemma Writer_kmon_bind1 : forall A : Type, bind (prod M) (ret (prod M) A) = id.
  Proof.
    intros. ext [m a]. unfold transparent tcs.
    cbn. now simpl_monoid.
  Qed.

  Lemma Writer_kmon_bind2 : forall (A B C : Type) (g : B -> (prod M) C) (f : A -> (prod M) B),
      bind (prod M) g ∘ bind (prod M) f = bind (prod M) (g ⋆1 f).
  Proof.
    intros. ext [m a]. unfold_ops @Bind_Writer.
    unfold kc1, bind, compose. cbn.
    unfold id. destruct (f a). cbn. unfold id. destruct (g b).
    cbn. unfold id. now simpl_monoid.
  Qed.

  #[export] Instance Monad_writer : Monad (prod M) :=
    {| kmon_bind0 := Writer_kmon_bind0;
      kmon_bind1 := Writer_kmon_bind1;
      kmon_bind2 := Writer_kmon_bind2;
    |}.

End writer_monad.

(** ** Miscellaneous properties *)
(******************************************************************************)
Section misc.

  Context
    (W : Type)
    `{Monoid W}.

  Lemma extract_pair {A : Type} :
    forall (w : W), extract (W ×) A ∘ pair w = @id A.
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
