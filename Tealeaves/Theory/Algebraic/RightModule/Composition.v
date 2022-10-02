

(** ** Right modules compose with functors *)
(******************************************************************************)
Section functor_module_composition.

  Context
    `{Functor F}
    `{RightModule G T}.

  #[global] Instance RightAction_compose : RightAction (F ∘ G) T :=
    fun A => fmap F (right_action G).

  #[local] Set Keyed Unification.

  (** It does not seem to be a good idea to add this globally. It is
      better to use it explicitly. *)
  Instance RightModule_compose : RightModule (F ∘ G) T.
  Proof.
    constructor; try typeclasses eauto.
    - constructor; try typeclasses eauto.
      introv. unfold transparent tcs.
      unfold_compose_in_compose.
      rewrite 2(fun_fmap_fmap F).
      now rewrite (natural (G := G) (F := G ∘ T)).
    - intros. unfold_ops @RightAction_compose @Fmap_compose.
      rewrite (fun_fmap_fmap F).
      rewrite (rmod_action_fmap_ret G T).
      now rewrite (fun_fmap_id F).
    - intros. unfold_ops @RightAction_compose @Fmap_compose.
      rewrite 2(fun_fmap_fmap F).
      now rewrite (rmod_action_action G T).
  Qed.

End functor_module_composition.
