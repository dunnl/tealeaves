From Tealeaves Require Export
     Singlesorted.Classes.ListableFunctor
     Singlesorted.Classes.SetlikeMonad.

Import Sets.Notations.
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

(** * Instance for [list] *)
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

(** * Listable monads are set-like *)
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

(*
  (** ** Interaction between [tolistr] and [ret], [bindr] *)
  (******************************************************************************)
  Section with_types.

    Context
      {A B : Type}.

    Implicit Types (w : W) (a : A) (b : B) (t : F A).

    Theorem tolistr_ret : forall a,
        tolistr T (ret T a) = [ (Ƶ, a) ].
    Proof.
      introv. unfold tolistr, compose.
      compose near a on left. rewrite (rmon_ret W T).
      unfold compose. compose near (Ƶ, a) on left.
      now rewrite (lmon_ret T).
    Qed.

    Theorem tolistr_right_action : forall (t : F (T A)),
        tolistr F (right_action F t) = join list (fmap list (shift list) (tolistr F (fmap F (tolistr T) t))).
    Proof.
      introv. unfold tolistr, compose.
      compose near t on left. rewrite (rrmod_action W F T).
      unfold compose. compose near (fmap F (shift T) (read F (fmap F (read T) t))) on left.
      rewrite (lrmod_action F T). unfold compose.
      compose near ((read F (fmap F (fun a : T A => tolist T (read T a)) t))) on right.
      rewrite (natural (η := @tolist F _)). unfold compose.
      change ((fun a : T A => tolist T (read T a))) with (tolist T ∘ read (A:=A) T).
      rewrite <- (fun_fmap_fmap F). unfold compose.
      compose near ((fmap F (read T) t)) on right.
      rewrite <- (natural (η := @read W F _)). unfold compose.
      unfold_ops @Fmap_compose.
      compose near (read F (fmap F (read T) t)) on right.
      rewrite (fun_fmap_fmap F). unfold shift at 2.
    Abort.

 (** TODO <<tolistr_bind>>, <<tolistr_join>> *)
 *)
