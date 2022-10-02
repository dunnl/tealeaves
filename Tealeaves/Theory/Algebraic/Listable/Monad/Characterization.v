From Tealeaves Require Import
  Classes.Algebraic.Listable.Monad
  Theory.Algebraic.Listable.Functor.Category.

From Tealeaves Require
  Theory.Algebraic.Monad.ToKleisli.

Import Functor.Notations.
Import Setlike.Functor.Notations.
Import Monad.Notations.
Import List.ListNotations.
#[local] Open Scope list_scope.

#[local] Generalizable Variables T.

(** * Characterizations of listable monad compatibility conditions *)
(******************************************************************************)
Section listable_monad_compatibility_conditions.

  Context
    `{Monad T}
    `{Tolist T}
    `{! ListableFunctor T}.

  (** The left-hand condition states that the natural transformation
      <<ret T>> commutes with taking <<tolist>>, i.e. that <<ret T>> is a
      list-preserving natural transformation. The right-hand condition
      is one half of the statement that <<tolist>> forms a monad
      homomorphism. *)
  Lemma tolist_ret_iff {A} :
    (tolist T ∘ ret T = tolist (fun x => x) (A:=A)) <->
    (tolist T ∘ ret T = ret list (A:=A)).
  Proof with auto.
    split...
  Qed.

  (** The left-hand condition states that the natural transformation
      <<join T>> is <<tolist>>-preserving. The right-hand condition is
      one half of the statement that <<tolist>> forms a monad
      homomorphism. *)
  Lemma tolist_join_iff {A} :
    `(tolist T ∘ join T (A:=A) = tolist (T ∘ T)) <->
    `(tolist T ∘ join T (A:=A) = join list ∘ tolist T ∘ fmap T (tolist T)).
  Proof with auto.
    split...
  Qed.

  Theorem listable_monad_compatibility_spec :
    Monad_Hom T list (@tolist T _) <->
    ListPreservingTransformation (@ret T _) /\
    ListPreservingTransformation (@join T _).
  Proof with auto.
    split.
    - introv mhom. inverts mhom. inverts mhom_domain. split.
      + constructor...
        introv. symmetry. rewrite tolist_ret_iff...
      + constructor...
        introv. symmetry. apply tolist_join_iff...
    - intros [h1 h2]. inverts h1. inverts h2.
      constructor; try typeclasses eauto.
      + introv. rewrite <- tolist_ret_iff...
      + introv. rewrite <- tolist_join_iff...
  Qed.

  Theorem listable_monad_compatibility_spec2 :
    Monad_Hom T list (@tolist T _) <->
    ListableMonad T.
  Proof.
    rewrite listable_monad_compatibility_spec.
    split.
    - intros [[] []]. constructor; try typeclasses eauto; eauto.
    - intros []. split.
      + constructor; try typeclasses eauto; eauto.
      + constructor; try typeclasses eauto; eauto.
  Qed.

End listable_monad_compatibility_conditions.

(** * A counter-example of a respectfulness property. *)
(******************************************************************************)

(** [list] is a counterexample to the strong respectfulness condition for <<bind>>. *)
Example f1 : nat -> list nat :=
  fun n => match n with
        | 0 => [4 ; 5]
        | 1 => [ 6 ]
        | _ => [ 42 ]
        end.

Example f2 : nat -> list nat :=
  fun n => match n with
        | 0 => [ 4 ]
        | 1 => [ 5 ; 6 ]
        | _ => [ 42 ]
        end.

Definition l := [ 0 ; 1 ].

Import Monad.ToKleisli.
Import Monad.ToKleisli.Operation.

Lemma bind_f1_f2_equal : bind list f1 l = bind list f2 l.
  reflexivity.
Qed.

Lemma f1_f2_not_equal : ~(forall x, x ∈ l -> f1 x = f2 x).
Proof.
  intro hyp.
  assert (0 ∈ l) by (cbn; now left).
  specialize (hyp 0 ltac:(auto)).
  cbv in hyp.
  now inverts hyp.
Qed.

Lemma list_not_free :
  ~ (forall (l : list nat), bind list f1 l = bind list f2 l -> (forall x, x ∈ l -> f1 x = f2 x)).
Proof.
  intro H. specialize (H l bind_f1_f2_equal).
  apply f1_f2_not_equal. apply H.
Qed.
