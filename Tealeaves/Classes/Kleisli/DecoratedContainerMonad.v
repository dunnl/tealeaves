From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedContainerFunctor.

Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variables A T W.

(** * Decorated container monads *)
(******************************************************************************)

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedContainerMonad
  (W : Type) (T : Type -> Type)
  `{Map T} `{Mapd W T} `{Bind T T} `{Bindd W T T} `{Return T}
  `{Monoid_op W} `{Monoid_unit W}
  `{ElementsCtx W T} :=
  { dconm_functor :> DecoratedMonadFull W T;
    dconm_morphism_ret : forall (A : Type),
      element_ctx_of ∘ ret (T := T) (A := A) =
        ret (T := ctxset W);
    dconm_morphism_bind : forall (A B : Type) (f : W * A -> T B),
        element_ctx_of ∘ bindd f =
          bindd (element_ctx_of ∘ f) ∘ element_ctx_of;
    dconm_pointwise : forall (A B : Type) (t : T A) (f g : W * A -> T B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> bindd f t = bindd g t;
  }.

(** ** Instance for <<env>> *)
(******************************************************************************)
(*
#[export] Instance DecoratedContainerMonad_env `{Monoid W} :
  DecoratedContainerMonad W (env W).
Proof.
  constructor.
  - admit.
  - intros. ext l. unfold compose.
    induction l as [| [w a] rest IHrest].
    + cbn. unfold_ops @ElementsCtx_env.
      autorewrite with tea_list.
      rewrite bindd_ctxset_nil.
      reflexivity.
    + change (bindd f ((w, a) :: rest)) with
        (shift list (w, f (w, a)) ++ bindd f rest).
      cbn.
      unfold_ops @ElementsCtx_env.
      autorewrite with tea_list.
      change (element_of (A := W * ?A)) with
        (element_ctx_of (F := env W) (A := A)).
      rewrite bindd_ctxset_add.
      rewrite bindd_ctxset_one.
      rewrite <- IHrest.
      fequal.
      rewrite (DecoratedFunctor.shift_spec). 2:admit.
      compose near (f (w, a)).
      rewrite (fun_map_map).
Abort.
*)
(** ** Basic properties of containers *)
(******************************************************************************)
Section decorated_container_monad_theory.

  Context
    `{DecoratedContainerMonad W T}.

  Variables (A B : Type).

  Implicit Types (t : T A) (b : B) (w : W) (a : A).

  Lemma ind_ret_iff : forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret (T := T) a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros.
    compose near a2 on left.
    rewrite dconm_morphism_ret.
    unfold_ops @Return_ctxset.
    intuition.
  Qed.

  Theorem ind_bindd_iff : forall w t f b,
      (w, b) ∈d bindd f t <->
        exists (wa : W) (a : A), (wa, a) ∈d t /\
                   exists wb : W, (wb, b) ∈d f (wa, a) /\
                               w = wa ● wb.
  Proof.
    introv. compose near t on left.
    rewrite dconm_morphism_bind.
    reflexivity.
  Qed.

  Lemma ind_bind_iff : forall w t f b,
      (w, b) ∈d bind f t <->
        exists (wa : W) (a : A), (wa, a) ∈d t /\
                   exists wb : W, (wb, b) ∈d f a /\
                               w = wa ● wb.
  Proof.
    introv.
    rewrite kmondf_bind_compat.
    rewrite ind_bindd_iff.
    reflexivity.
  Qed.

  Lemma ind_mapd_iff :
    forall `(f : W * A -> B) (t : T A) (w : W) (b : B),
      (w, b) ∈d mapd f t <-> exists (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros.
    eapply ind_mapd_iff.
    constructor.
    - inversion H7.
      admit.
    -
      typeclasses eauto.

End decorated_container_monad_theory.
