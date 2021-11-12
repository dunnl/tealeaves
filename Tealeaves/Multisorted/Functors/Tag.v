From Tealeaves Require Import
     Singlesorted.Classes.Functor
     Multisorted.Classes.Monad.

Import Multisorted.Category.Notations.
#[local] Open Scope tealeaves_multi_scope.

(** * The "tag" functor *)
(******************************************************************************)
Notation "'Tag'" := (prod K).

Section tag.

  Context
    `{Index}.

  #[global] Instance Mfmap_Tag : Mfmap Tag
    := fun `(f : K -> A -> B) '(k, a) => (k, f k a).

  Lemma mfmap_id_Tag {A} : mfmap Tag kid = @id (Tag A).
  Proof.
    now ext [? ?].
  Qed.

  Lemma mfmap_mfmap_Tag :
    forall `(f : A -k-> B) `(g : B -k-> C),
      mfmap Tag g ∘ mfmap Tag f = mfmap Tag (g ⊙ f).
  Proof.
    introv. now ext [? ?].
  Qed.

  #[global] Instance MFunctor_Tag : MultisortedFunctor Tag :=
    {| mfmap_id := @mfmap_id_Tag;
       mfmap_mfmap := @mfmap_mfmap_Tag; |}.

  #[global] Instance: Mreturn (const Tag) :=
    fun A k a => pair k a.

  #[global] Instance: Mbind Tag (const Tag) :=
    fun  A B f '(k, a) => f k a.

  Theorem mon_mbind_mret_Tag : forall {A},
      mbind Tag (mret (const Tag)) = @id (Tag A).
  Proof.
    introv. now ext [? ?].
  Qed.

  Theorem mon_mbind_comp_mret_Tag : forall {A B} (f : A -k-> Tag B) k,
      mbind Tag f ∘ mret (const Tag) k = f k.
  Proof.
    reflexivity.
  Qed.

  Theorem mon_mbind_mbind_Tag : forall {A B C} (f : A -k-> Tag B) (g : B -k-> Tag C),
      mbind Tag g ∘ mbind Tag f = mbind Tag (fun k => mbind Tag g ∘ f k).
  Proof.
    introv. now ext [? ?].
  Qed.

  #[global] Instance ConstantMultisortedMonad_Tag : ConstantMultisortedMonad Tag :=
    {| cmmon_mbind_mret := @mon_mbind_mret_Tag;
       cmmon_mbind_comp_mret := @mon_mbind_comp_mret_Tag;
       cmmon_mbind_mbind := @mon_mbind_mbind_Tag;
    |}.

End tag.

(** * Ordinary monads to multi-sorted monads *)
(** Suppose we have an ordinary monad <<T>>. We can construct a
    multi-sorted version of <<T>> by pre-composing with <<Tag>>. (Technically
    the multi-sorted monad is given by the constant K-indexed family of the
    resulting object map, since multi-sorted monads are K-indexed families of
    functors). For instance, from the ordinary monad [set] we can construct a
    multi-sorted monad mapping type <<A>> to <<set (Tag A)>>, sets of partitioned
    elements. *)
Section MultisortedMonad_monad.

  Context
    `{ix : Index}
    `{Monad T}.

  Implicit Types (k : K) (A B : Type).

  Local Notation "'T'' A" := (T (Tag A)) (at level 10).

  Instance Mreturn_T_Tag : Mreturn (const (fun A => T' A)) :=
    fun A => curry (Monad.ret T).

  Instance Mbind_T_Tag : Mbind (fun A => T' A) (const (fun A => T' A)) :=
    fun A B f => Monad.bind (B:=Tag B) T (uncurry f).

  Theorem mon_mbind_mret_T_Tag : forall {A},
      mbind (fun A => T' A) (mret (const (fun A => T' A))) = @id (T' A).
  Proof.
    intros. unfold mbind, Mbind_T_Tag, mret, Mreturn_T_Tag.
    now rewrite <- curry_iso_inv, (Monad.bind_id T).
  Qed.

  Theorem mon_mbind_comp_mret_T_Tag : forall {A B} (f : A -k-> T' B) k,
      mbind (fun A => T' A) f ∘ mret (const (fun A => T' A)) k = f k.
  Proof.
    intros. unfold mbind, Mbind_T_Tag, mret, Mreturn_T_Tag.
    ext a. unfold curry, compose.
    compose near (k, a). now rewrite (Monad.bind_comp_ret T).
  Qed.

  Theorem mon_mbind_mbind_T_Tag : forall {A B C} (f : A -k-> T' B) (g : B -k-> T' C),
      mbind (fun A => T' A) g ∘ mbind (fun A => T' A) f =
      mbind (fun A => T' A) (fun k => mbind (fun A => T' A) g ∘ f k).
  Proof.
    introv. unfold mbind, Mbind_T_Tag.
    rewrite (Monad.bind_bind T).
    fequal. now ext [k a].
  Qed.

  Instance CMMonad_T_Tag : ConstantMultisortedMonad (fun A => T' A) :=
    {| cmmon_mbind_mret := @mon_mbind_mret_T_Tag;
       cmmon_mbind_comp_mret := @mon_mbind_comp_mret_T_Tag;
       cmmon_mbind_mbind := @mon_mbind_mbind_T_Tag;
    |}.

  Instance Module_T_Tag : MultisortedRightModule (fun A => T' A) (const (fun A => T' A)).
  Proof.
    constructor. all: try typeclasses eauto.
    - intros. apply mon_mbind_mret_T_Tag.
    - intros. apply mon_mbind_mbind_T_Tag.
  Qed.

  (** The [fmap] for the resulting [Monad] has a complicated definition because
  it is defined in terms of [Multi.Functors.mbind] instance. Here we give a
  characterization highlighting the role of the underlying
  [Functors.fmap] instance. *)
  Theorem Monad_T_Tag_mfmap_spec : forall {A B} (f : A -k-> B),
      mfmap (fun A => T' A) f = fmap T (fun '(k, a) => (k, f k a)).
  Proof.
    intros. unfold mfmap, Mfmap_rmod, mbind, Mbind_T_Tag.
    rewrite (Monad.fmap_to_bind T). fequal. ext [k a].
    reflexivity.
  Qed.

End MultisortedMonad_monad.
