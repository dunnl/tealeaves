From Tealeaves Require Export
  Classes.Algebraic.Monad
  Classes.Algebraic.Listable.Functor.

#[local] Generalizable Variable A.

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
