From Tealeaves Require Import
     Functors.Sets.

From Multisorted Require Import
     Classes.Monad
     Functors.Tag.

Import Sets.Notations.
Import Multisorted.Theory.Category.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

(** * The monad of multisorted sets *)
(** Since "multisorted" sets are defined merely as sets of pairs, we try to utilize the existing
    structure in <<Ordinary.Sets>> as much as possible rather than rebuild the
    multi-sorted interface from scratch. *)
(******************************************************************************)
Section multisorted_sets.

  Context
    `{ix : Index}.

  Implicit Types (k : K) (A B : Type).

  Definition mset : Type -> Type :=
    fun A => Tag A -> Prop.

  #[global] Instance MReturn_mset :
    MReturn (const mset) := MReturn_T_Tag set.
  #[global] Instance MBind_mset :
    MBind mset (const mset) := MBind_T_Tag set.
  #[global] Instance Monadp_mset :
    ConstantMultisortedMonad mset := CMMonad_T_Tag set.
  #[global] Instance Modulep_mset :
    MultisortedRightModule mset (const mset) := Module_T_Tag set.

  (** [bindt_mset_spec] provides a more convenient definition of
      <<bind mset f>> than its definition. *)
  Lemma mbind_mset_spec : forall A B (f : A ~k~> (const mset) B),
      mbind mset f = fun s p => exists k, exists a, s (k, a) /\ f k a p.
  Proof.
    intros. ext s [k b]. propext.
    - intro hyp. destruct hyp as [S [S_in in_S]].
      destruct S_in as [[k' a] [p_in_s p_eq]].
      subst. (now exists k' a).
    - intros [k' [a [p_in_s in_f]]]. cbv -[K].
      exists ( f k' a). split.
      + now (exists (k', a)).
      + auto.
  Qed.

  (** Contravariant map over sets, useful for some minor purposes. *)
  Definition contramap {A B} {K : Type} : (B -> A) -> mset A -> mset B :=
    fun f s '(k, a) => s (k, f a).

  Lemma preimage_fmap : forall {A B} {s : mset A} {f : A -k-> B} {k : K} {b : B},
      mfmap mset f s (k, b) <-> exists a, s (k, a) /\ f k a = b.
  Proof.
    introv. unfold_ops @MFmap_rmod. rewrite mbind_mset_spec. split.
    - destruct 1 as [k' [a [in1 in2]]].
      inverts in2. now (exists a).
    - intros [a [? heq]]. inverts heq. now (exists k a).
  Qed.

  Section mset_monoid.

    Context
      {A : Type}.

    Implicit Types (s t : mset A) (p : Tag A) (a : A).

    Definition mset_empty : mset A := const False.

    Definition mset_add : mset A -> mset A -> mset A :=
      fun x y p => x p \/ y p.

    Local Notation "∅" := mset_empty.
    Local Infix "∪" := mset_add (at level 61, left associativity).

    Lemma mset_add_nil_l : `(x ∪ ∅ = x).
    Proof.
      intro. ext p. propext; firstorder.
    Qed.

    Lemma mset_add_nil_r : `(∅ ∪ x = x).
    Proof.
      intro. ext p. propext; firstorder.
    Qed.

    Lemma mset_add_assoc : `(x ∪ y ∪ z = x ∪ (y ∪ z)).
    Proof.
      intros. ext p. propext; firstorder.
    Qed.

    Lemma mset_add_comm : `(x ∪ y = y ∪ x).
    Proof.
      intros. ext p. propext; firstorder.
    Qed.

  End mset_monoid.

  Local Notation "∅" := mset_empty.
  Local Infix "∪" := mset_add (at level 61, left associativity).

  Lemma mfmap_mset_nil `{f : A -k-> B} : mfmap mset f ∅ = ∅.
  Proof.
    ext [? ?]; propext; firstorder.
  Qed.

  Lemma mfmap_mset_add `{f : A -k-> B} {x y} :
    mfmap mset f (x ∪ y) = mfmap mset f x ∪ mfmap mset f y.
  Proof.
    ext [? ?]; propext; firstorder.
  Qed.

  Lemma mbind_mset_nil `{f : A ~k~> (const mset) B} :
    mbind mset f ∅ = ∅.
  Proof.
    ext [? ?]; propext; firstorder.
  Qed.

  Lemma mbind_mset_add `{f : A ~k~> (const mset) B} {x y} :
    mbind mset f (x ∪ y) = mbind mset f x ∪ mbind mset f y.
  Proof.
    ext [? ?]; propext; firstorder.
  Qed.

End multisorted_sets.

Hint Rewrite @mset_add_nil_l @mset_add_nil_r
     @mfmap_mset_nil @mfmap_mset_add @mbind_mset_nil
     @mbind_mset_add : tea_set.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "∅" := mset_empty : tealeaves_multi_scope.
  Notation "{{ ( k , x ) }}" := (mret (const mset) k x) : tealeaves_multi_scope.
  Infix "∪" := mset_add (at level 61, left associativity) : tealeaves_multi_scope.
End Notations.
