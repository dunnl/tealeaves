From Tealeaves Require Export
  Classes.Monad
  Classes.Listable.Functor
  Classes.Setlike.Monad.

Import Sets.Notations.
#[local] Generalizable Variable T A.

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

(** * Characterizations of listable monad compatibility conditions *)
(******************************************************************************)
Section listable_monad_compatibility_conditions.

  Generalizable All Variables.
  
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

(*
This needs the Kleisli-style presentation available

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
*)
