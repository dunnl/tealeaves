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
  `{CtxElements W T} :=
  { dconm_functor :> DecoratedMonadFull W T;
    dconm_morphism : forall (A B : Type) (f : W * A -> T B),
        ctx_element_of ∘ bindd f =
          bindd (ctx_element_of ∘ f) ∘ ctx_element_of;
    dconm_pointwise : forall (A B : Type) (t : T A) (f g : W * A -> T B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> bindd f t = bindd g t;
  }.

(** ** Instance for <<env>> *)
(******************************************************************************)
#[export] Instance DecoratedContainerMonad_env `{Monoid W} :
  DecoratedContainerMonad W (env W).
Proof.
  constructor.
  - admit.
  - intros. ext l. unfold compose.
    induction l as [| [w a] rest IHrest].
    + cbn. unfold_ops @CtxElements_env.
      autorewrite with tea_list.
      rewrite bindd_ctxset_nil.
      reflexivity.
    + change (bindd f ((w, a) :: rest)) with
        (shift list (w, f (w, a)) ++ bindd f rest).
      cbn.
      unfold_ops @CtxElements_env.
      autorewrite with tea_list.
      change (element_of (A := W * ?A)) with
        (ctx_element_of (F := env W) (A := A)).
      rewrite bindd_ctxset_add.
      rewrite bindd_ctxset_one.
      rewrite <- IHrest.
      fequal.
      rewrite (DecoratedFunctor.shift_spec). 2:admit.
      compose near (f (w, a)).
      rewrite (fun_map_map).
Abort.

(** ** Basic properties of containers *)
(******************************************************************************)
Section decorated_container_monad_theory.

  Context
    `{DecoratedContainerMonad W T}.

  Variables (A B : Type).

  Implicit Types (t : T A) (b : B) (w : W) (a : A).

  Theorem ind_bindd_iff : forall w t f b,
      (w, b) ∈d bindd f t <->
        exists (wa : W) (a : A), (wa, a) ∈d t /\
                   exists wb : W, (wb, b) ∈d f (wa, a) /\
                               w = wa ● wb.
  Proof.
    introv. compose near t on left.
    rewrite dconm_morphism.
    reflexivity.
  Qed.

End decorated_container_monad_theory.
