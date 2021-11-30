From Tealeaves Require Export
     Singlesorted.Classes.ListableFunctor
     Singlesorted.Classes.SetlikeMonad.

Import List.ListNotations.
Import Sets.Notations.
Import Monoid.Notations.
#[local] Open Scope list_scope.
#[local] Open Scope tealeaves_scope.

(** * Listable monads *)
(******************************************************************************)
Section ListableMonad.

  Context
    (T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Tolist T}.

  Class ListableMonad :=
    { lmon_monad :> Monad T;
      lmon_functor :> ListableFunctor T;
      lmon_ret :
        `(tolist T ∘ ret T = ret list (A:=A));
      lmon_join :
        `(tolist T ∘ join T = join list ∘ tolist T ∘ fmap T (tolist T (A:=A)));
    }.

End ListableMonad.

(** ** Instance for [list] *)
(******************************************************************************)
Section Listable_list.

  #[program] Instance: ListableMonad list :=
    {| lmon_functor := ListableFunctor_instance_0; |}.

  Next Obligation.
    ext t. unfold compose. unfold_ops @Tolist_list.
    now rewrite (fun_fmap_id list).
  Qed.

End Listable_list.

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
    compose near a on left. rewrite toset_ret_list.
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

  #[global] Instance SetlikeMonad_Listable : SetlikeMonad T :=
    {| xmon_ret := toset_ret_Listable;
       xmon_join := toset_join_Listable;
       xmon_ret_injective := ListableMonad.return_injective;
    |}.

End ListableMonad_setlike.

(** * Decorated listable monads *)
(******************************************************************************)

(** ** Interaction between [tolistd] and [ret], [bindr] *)
(******************************************************************************)
Section ListableMonad_tolistd.

  Context
    (T : Type -> Type)
    `{Monoid W}
    `{Fmap T} `{Decorate W T} `{Tolist T}
    `{Return T} `{Join T}
    `{! DecoratedMonad W T}
    `{! ListableMonad T}
    {A B : Type}.

  Implicit Types (w : W) (a : A) (b : B) (t : T A).

  Theorem tolistd_ret : forall a,
      tolistd T (ret T a) = [ (Ƶ, a) ].
  Proof.
    introv. unfold tolistd, compose.
    compose near a on left. rewrite (dmon_ret W T).
    unfold compose. compose near (Ƶ, a) on left.
    now rewrite (lmon_ret T).
  Qed.

  Lemma tolistd_join1 :
    tolist T ∘ fmap T (tolist T ∘ shift T (A := A)) =
    fmap list (shift list) ∘ tolist T ∘ fmap T (fmap (prod W) (tolist T)).
  Proof.
    unfold shift. reassociate <-.
    rewrite <- (fun_fmap_fmap list).
    reassociate -> near (tolist T).
    rewrite (natural (ϕ := @tolist T _)).
    reassociate <-. reassociate -> near (fmap T (fmap (prod W) (tolist T))).
    rewrite (fun_fmap_fmap T).
    replace (strength list ∘ fmap (prod W) (tolist T))
      with (tolist T ∘ strength T (A := W) (B := W * A)).
    rewrite <- (fun_fmap_fmap T).
    rewrite <- (fun_fmap_fmap T (f := strength T)).
    do 2 reassociate <-. fequal.
    rewrite (natural (ϕ := @tolist T _)).
    reassociate -> on right; rewrite (fun_fmap_fmap T). fequal.
    fequal. now rewrite (natural (ϕ := @tolist T _)).
    ext [w t]; unfold compose; cbn. compose near t.
    now rewrite (natural (ϕ := @tolist T _)).
  Qed.

  Theorem tolistd_join : forall (t : T (T A)),
      tolistd T (join T t) = join list (fmap list (shift list) (tolistd T (fmap T (tolistd T) t))).
  Proof.
    introv. unfold tolistd, compose.
    compose near t on left. rewrite (dmon_join W T).
    unfold compose. compose near (fmap T (shift T) (dec T (fmap T (dec T) t))) on left.
    rewrite (lmon_join T). unfold compose.
    compose near (dec T (fmap T (tolist T ○ dec T) t)) on right.
    change (tolist T ○ dec T) with (tolist T ∘ dec T (A:=A)).
    rewrite <- (fun_fmap_fmap T). unfold compose.
    compose near (fmap T (dec T) t) on right.
    rewrite <- (natural (ϕ := @dec W T _)). unfold compose.
    unfold_ops @Fmap_compose. fequal. compose near (dec T (fmap T (dec T) t)).
    rewrite (fun_fmap_fmap T).
    compose near (dec T (fmap T (dec T) t)).
    now rewrite tolistd_join1.
  Qed.

End ListableMonad_tolistd.
