
#[export] Instance Bind_RightAction (F T : Type -> Type) `{Fmap F} `{RightAction F T} : Bind F T :=
  fun `(f : A -> T B) => right_action F ∘ fmap F f.

(** * Kleisli laws for <<bind>> *)
(******************************************************************************)
Section Monad_kleisli_laws.

  Context
    (T : Type -> Type)
    `{Algebraic.RightModule.RightModule F T}.

   (** *** Identity law *)
  Lemma bind_id :
    `(bind F (ret T) = @id (F A)).
  Proof.
    intros. unfold transparent tcs.
    now rewrite (mod_action_fmap_ret F T).
  Qed.

  (** *** Composition law *)
  Lemma bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
      bind F g ∘ bind F f = bind F (g ⋆ f).
  Proof.
    introv. unfold transparent tcs. unfold kcompose.
    unfold_ops @Bind_Join.
    rewrite <- 2(fun_fmap_fmap F).
    reassociate <- on right.
    change (fmap ?F (fmap ?T g)) with (fmap (F ∘ T) g).
    reassociate <- on right.
    rewrite <- (mod_action_action F T).
    reassociate -> near (fmap (F ∘ T) g).
    now rewrite <- (natural (ϕ := @right_action F T _)).
  Qed.

End Monad_kleisli_laws.

#[local] Instance inst2 `{Algebraic.RightModule.RightModule F T} : Kleisli.Monad.RightModule F T :=
  {| kmod_bind1 := @bind_id T F _ _ _ _ _ _;
     kmod_bind2 := @bind_bind T F _ _ _ _ _ _;
  |}.

(** ** Specification for <<fmap>>  *)
(******************************************************************************)
Section Monad_suboperations.

  Context
    (T : Type -> Type)
    `{Algebraic.Monad.Monad T}.

  (** *** [fmap] as a special case of [bind]. *)
  Lemma fmap_to_bind : forall `(f : A -> B),
      fmap T f = bind T (ret T ∘ f).
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on right.
    now rewrite (mon_join_fmap_ret T).
  Qed.

End Monad_suboperations.
