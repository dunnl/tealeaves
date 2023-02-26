From Tealeaves Require Export
  Classes.Functor
  Classes.Monad
  Classes.Kleisli.Monad.

Import Product.Notations.
Import Functor.Notations.
Import Kleisli.Monad.Notations.

#[local] Generalizable Variable T.

Import Classes.Kleisli.Monad.ToFunctor.
Import Classes.Monad.ToKleisli.

(** * Algebraic operations from Kleisli operation *)
(******************************************************************************)

Section operation.

  Context
    (T : Type -> Type)
      `{Return T} `{Bind T T}.

  #[export] Instance Join_Bind : Join T :=
    fun A => bind T (@id (T A)).

End operation.

Section proofs.

  Context
    (T : Type -> Type)
      `{Classes.Kleisli.Monad.Monad T}.

  Instance: Classes.Monad.Monad T.
  Proof.
    constructor.
    - typeclasses eauto.
    - constructor.
      typeclasses eauto.
      typeclasses eauto.
      intros. unfold transparent tcs.
      now rewrite (kmon_bind0 T).
    - constructor.
      typeclasses eauto.
      typeclasses eauto.
      intros. unfold transparent tcs.
      unfold_compose_in_compose.
      do 2 rewrite (kmon_bind2 T).
      fequal. unfold kcompose.
      reassociate <- on right.
      now rewrite (kmon_bind0 T).
    - intros. unfold transparent tcs.
      unfold_compose_in_compose.
      now rewrite (kmon_bind0 T).
    - intros. unfold transparent tcs.
      unfold_compose_in_compose.
      rewrite (kmon_bind2 T).
      unfold kcompose.
      reassociate <- near (bind T (@id (T A))).
      rewrite (kmon_bind0 T). unfold compose.
      now rewrite <- (kmon_bind1 T A) at 1.
    - intros. unfold transparent tcs.
      unfold_compose_in_compose.
      rewrite (kmon_bind2 T).
      rewrite (kmon_bind2 T).
      unfold kcompose.
      reassociate <- near (bind T (@id (T A))).
      now rewrite (kmon_bind0 T).
  Qed.

End proofs.

Module Roundtrip1.

  Context
    `{Return T}
      `{fmap1 : Fmap T}
      `{join1 : Join T}
      `{! Classes.Monad.Monad T}.

  #[local] Instance bind_derived: Bind T T := Bind_join T.

  Definition fmap2 := Fmap_Bind T.
  Definition join2 := Join_Bind T.

  Goal fmap1 = fmap2.
  Proof.
    ext A B f.
    unfold fmap2, Fmap_Bind,
      bind, bind_derived, Bind_join.
    rewrite <- (fun_fmap_fmap T).
    reassociate <-.
    rewrite (mon_join_fmap_ret T).
    reflexivity.
  Qed.

  Goal join1 = join2.
  Proof.
    ext A t.
    unfold join2, Join_Bind,
      bind, bind_derived, Bind_join.
    rewrite (fun_fmap_id T).
    reflexivity.
  Qed.

End Roundtrip1.

Section RoundTrip2.

  Context
    `{Return T}
    `{bind1 : Bind T T}
    `{! Kleisli.Monad.Monad T}.

  Definition fmap_derived := Fmap_Bind.
  Definition join_derived := Join_Bind.
  Definition bind2 : Bind T T := Bind_join T.

  Goal bind1 = bind2.
  Proof.
    ext A B f.
    unfold bind2, Bind_join.
    unfold join, Join_Bind.
    unfold fmap, Fmap_Bind.
    unfold_compose_in_compose.
    rewrite (kmon_bind2 T).
    fequal. unfold kcompose.
    reassociate <-.
    rewrite (kmon_bind0 T).
    reflexivity.
  Qed.

End RoundTrip2.
