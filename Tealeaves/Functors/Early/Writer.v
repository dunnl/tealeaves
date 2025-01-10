From Tealeaves Require Export
  Classes.Monoid
  Classes.Kleisli.Monad
  Classes.Kleisli.Comonad
  Classes.Categorical.Monad
  Classes.Categorical.Comonad
  Functors.Early.Reader.

Import Product.Notations.
Import Functor.Notations.
Import Monoid.Notations.
Import Categorical.Monad.Notations.
Import Categorical.Comonad.Notations.
Import Kleisli.Monad.Notations.
Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables W T F A M.

(** * Writer monad *)
(******************************************************************************)

(** ** Categorical instance *)
(** In the even that [A] is a monoid, the product functor forms a monad. The
    return operation maps <<b>> to <<(1, b)>> where <<1>> is the monoid unit.
    The join operation monoidally combines the two monoid values. *)
(******************************************************************************)
Section writer_monad.

  Context
    `{Monoid M}.

  #[export] Instance Join_writer: Join (prod M) :=
    fun A (p: M * (M * A)) => map_fst (uncurry (@monoid_op M _)) (α^-1 p).

  #[export] Instance Return_writer: Return (prod M) :=
    fun A (a: A) => (Ƶ, a).

  #[export] Instance Natural_ret_writer: Natural (@ret (prod M) Return_writer).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. now ext a.
  Qed.

  #[export] Instance Natural_join_writer: Natural (@join (prod M) Join_writer).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [x [x' a]].
  Qed.

  #[export, program] Instance Monad_Categorical_writer: Monad (prod M).

  Solve Obligations with
      (intros; unfold transparent tcs; ext p;
      unfold compose in *; destruct_all_pairs;
      cbn; now simpl_monoid).

End writer_monad.

(** ** Kleisli instance *)
(******************************************************************************)
Section writer_monad.

  Context
    `{Monoid W}.

  #[export] Instance Return_Writer: Return (W ×) :=
    fun A (a: A) => (Ƶ, a).

  #[export] Instance Bind_Writer: Bind (W ×) (W ×) :=
    fun A B (f: A -> W * B) (p: W * A) =>
      map_fst (uncurry (@monoid_op W _)) (α^-1 (map_snd f p)).

  #[export] Instance Natural_ret_Writer: Natural (@ret (W ×) Return_Writer).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. now ext a.
  Qed.

  Lemma Writer_kmon_bind0: forall (A B: Type) (f: A -> W * B),
      bind f ∘ ret = f.
  Proof.
    intros. ext a.
    unfold compose.
    unfold transparent tcs.
    cbn. destruct (f a).
    cbn. now simpl_monoid.
  Qed.

  Lemma Writer_kmon_bind1: forall A: Type,
      bind (ret (A := A)) = id.
  Proof.
    intros. ext [m a]. unfold transparent tcs.
    cbn. now simpl_monoid.
  Qed.

  Lemma Writer_kmon_bind2: forall (A B C: Type) (g: B -> W * C) (f: A -> W * B),
      bind g ∘ bind f = bind (g ⋆1 f).
  Proof.
    intros. ext [m a]. unfold_ops @Bind_Writer.
    unfold kc1, bind, compose. cbn.
    unfold id. destruct (f a). cbn. unfold id. destruct (g b).
    cbn. unfold id. now simpl_monoid.
  Qed.

  #[export] Instance RightPreModule_writer :
    Kleisli.Monad.RightPreModule (W ×) (W ×) :=
    {| kmod_bind1 := Writer_kmon_bind1;
       kmod_bind2 := Writer_kmon_bind2;
    |}.

  #[export] Instance Monad_writer: Kleisli.Monad.Monad (W ×) :=
    {| kmon_bind0 := Writer_kmon_bind0;
    |}.

  (** ** Miscellaneous properties *)
  (******************************************************************************)
  Lemma extract_pair {A: Type} :
    forall (w: W), extract ∘ pair w = @id A.
  Proof.
    reflexivity.
  Qed.

  Lemma extract_incr {A: Type} :
    forall (w: W), extract ∘ incr w (A := A) = extract.
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma extract_preincr {A: Type} :
    forall (w: W), extract ⦿ w = extract (A := A).
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma extract_preincr2 {A B: Type} (f: A -> B) :
    forall (w: W), (f ∘ extract) ⦿ w = f ∘ extract.
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma preincr_ret {A B: Type}: forall (f: W * A -> B) (w: W),
      (f ⦿ w) ∘ ret = f ∘ pair w.
  Proof.
    intros. ext a. cbv.
    change (op w unit0) with (w ● Ƶ).
    now simpl_monoid.
  Qed.

  Lemma incr_spec `{Monoid W} : forall A, uncurry incr = join (T := (W ×)) (A := A).
  Proof.
    intros. ext [w1 [w2 a]]. reflexivity.
  Qed.

End writer_monad.
