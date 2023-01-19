From Tealeaves Require Export
  Algebraic.Listable.Monad
  Algebraic.Setlike.Monad
  Theory.Algebraic.Listable.Functor.Properties.

Import List.ListNotations.
Import Sets.Notations.
Import Monoid.Notations.
#[local] Open Scope list_scope.

#[local] Generalizable Variable T A.

(** * Listable monads *)
(******************************************************************************)

(** * Properties of listable monads *)
(******************************************************************************)
Section ListableMonad_theory.

  Context
    `{ListableMonad T}.

  Corollary tolist_ret A (a : A) :
    tolist T (ret T a) = ret list a.
  Proof.
    intros. compose near a on left.
    now rewrite (lmon_ret T).
  Qed.

  Corollary tolist_join A (t : T (T A)) :
    tolist T (join T t) = join list (tolist T (fmap T (tolist T) t)).
  Proof.
    intros. compose near t on left.
    now rewrite (lmon_join T).
  Qed.

  Theorem return_injective : forall A (a b : A),
      ret T a = ret T b -> a = b.
  Proof.
    introv. intro heq.
    assert (lemma : tolist T (ret T a) = tolist T (ret T b)).
    { now rewrite heq. }
    rewrite 2(tolist_ret) in lemma. now inverts lemma.
  Qed.

End ListableMonad_theory.


(** ** Listable monads are set-like *)
(******************************************************************************)
Section ListableMonad_setlike.

  Context
    `{ListableMonad T}.

  Theorem toset_ret_Listable :
    `(toset T ∘ ret T (A:=A) = ret set).
  Proof.
    intros. unfold toset, Toset_Tolist, compose. ext a.
    rewrite tolist_ret.
    compose near a on left.

    rewrite toset_ret_list.
    reflexivity.
  Qed.

  Theorem toset_join_Listable :
    `(toset T ∘ join T = join set ∘ toset T ∘ fmap T (toset T (A:=A))).
  Proof.
    intros. unfold toset, Toset_Tolist.
    rewrite <- (fun_fmap_fmap T).
    reassociate -> on right.
    change_right (join (A:=A) set ∘ toset list ∘ (tolist T
                       ∘ fmap T (toset list)) ∘ fmap T (tolist T)).
    rewrite <- natural.
    reassociate <- on right.
    rewrite <- toset_join_list.
    reassociate -> on left.
    now rewrite (lmon_join T).
  Qed.

  #[export] Instance SetlikeMonad_Listable : SetlikeMonad T :=
    {| xmon_ret := toset_ret_Listable;
       xmon_join := toset_join_Listable;
       xmon_ret_injective := return_injective;
    |}.

End ListableMonad_setlike.
