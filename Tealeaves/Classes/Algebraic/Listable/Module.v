From Tealeaves Require Export
     Classes.ListableMonad
     Classes.SetlikeModule.

Import Sets.Notations.
#[local] Open Scope tealeaves_scope.

(** * Listable modules *)
(******************************************************************************)
Section ListableModule.

  Context
    (F T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Tolist T}
    `{Fmap F} `{Tolist F} `{RightAction F T}.

    Class ListableModule :=
    { lrmod_module :> RightModule F T;
      lrmod_functor :> ListableFunctor F;
      lrmod_monad :> ListableMonad T;
      lrmod_action :
        `(tolist F ∘ right_action F =
          join list ∘ tolist F ∘ fmap F (tolist T (A:=A)));
    }.

End ListableModule.

(** ** Listable monads form listable modules *)
(******************************************************************************)
Section ListableModule_monad.

  Context
    (T : Type -> Type)
    `{ListableMonad T}.

  Existing Instance RightAction_Join.
  Existing Instance RightModule_Monad.

  Instance ListableModule_Monad : ListableModule T T :=
    {| lrmod_action := lmon_join T; |}.

End ListableModule_monad.

(** ** Listable modules compose with functors *)
(******************************************************************************)
Section ListableModule_composition.

  Context
    `{ListableFunctor F}
    `{ListableModule G T}.

  Existing Instance RightModule_compose.

  Instance ListableModule_compose : ListableModule (F ∘ G) T.
  Proof.
    constructor; try typeclasses eauto.
    intros A. unfold_ops @RightAction_compose @Tolist_compose.
    #[local] Set Keyed Unification.
    rewrite <- (compose_assoc (f := join list ∘ tolist F)
                             (g := fmap F (tolist G))
                             (h := fmap F (right_action (T:=T) G))).
    #[local] Unset Keyed Unification.
    rewrite (fun_fmap_fmap F).
    rewrite (lrmod_action G T).
    rewrite <- (fun_fmap_fmap F).
    rewrite <- (fun_fmap_fmap F).
    repeat reassociate <-.
    reassociate -> near (fmap F (join list)).
    rewrite <- natural.
    reassociate <-.
    now rewrite <- (mon_join_join list).
  Qed.

End ListableModule_composition.

(** ** Basic properties *)
(******************************************************************************)
Section ListableModule_theory.

  Context
    (F : Type -> Type)
    `{ListableModule F T}.

  Corollary tolist_right_action_1 A (t : F (T A)) :
    tolist F (right_action F t) =
    join list (tolist F (fmap F (tolist T) t)).
  Proof.
    intros. compose near t on left.
    now rewrite (lrmod_action F T).
  Qed.

  Theorem tolist_right_action_2 A : forall (t : F (T A)),
    tolist F (right_action F (A:=A) t) =
    bind list (tolist T) (tolist F t).
  Proof.
    intros. compose near t.
    rewrite (lrmod_action F T).
    reassociate -> on left.
    unfold_compose_in_compose.
    now rewrite <- natural.
  Qed.

  Theorem tolist_sub `{f : A -> T B} :
    tolist F ∘ sub F f = bind list (tolist T ∘ f) ∘ tolist F.
  Proof.
    intros. unfold sub, Sub_RightAction.
    reassociate <- on left. rewrite (lrmod_action F T).
    reassociate -> on left. unfold_compose_in_compose.
    rewrite (fun_fmap_fmap F).
    reassociate -> on left.
    now rewrite <- natural.
  Qed.

End ListableModule_theory.

(** * Listable right modules are set-like *)
(******************************************************************************)
Section ListableModule_setlike.

  Context
    `{ListableModule F T}.

  Theorem toset_right_action_Listable :
    `(toset F ∘ right_action F = join set ∘ toset F ∘ fmap F (toset T (A:=A))).
  Proof.
    intros. unfold toset, Toset_Tolist.
    rewrite <- (fun_fmap_fmap F).
    reassociate -> on right.
    change_right (join (A:=A) set ∘ toset list ∘ (tolist F
                       ∘ fmap F (toset list)) ∘ fmap F (tolist T)).
    rewrite <- natural.
    reassociate <- on right.
    rewrite <- toset_join_list.
    reassociate -> on left.
    now rewrite (lrmod_action F T).
  Qed.

  #[export] Instance SetlikeModule_Listable : SetlikeModule F T :=
    {| xrmod_action := toset_right_action_Listable;
    |}.

End ListableModule_setlike.

(** * Respectfulness conditions for listable modules *)
(******************************************************************************)
Section tolist_respectfulness_module_definitions.

  Context
    (F T : Type -> Type)
    `{Tolist F} `{Tolist F}
    `{Fmap F} `{Fmap T}
    `{RightAction F T}.

  Definition tolist_sub_injective := forall A B (t1 t2 : F A) (f g : A -> T B),
      shape F t1 = shape F t2 ->
      sub F f t1 = sub F g t2 ->
      fmap list f (tolist F t1) = fmap list g (tolist F t2).

  Definition tolist_sub_respectful := forall A B (t1 t2 : F A) (f g : A -> T B),
      shape F t1 = shape F t2 ->
      fmap list f (tolist F t1) = fmap list g (tolist F t2) ->
      sub F f t1 = sub F g t2.

  Definition tolist_sub_respectful_iff := forall A B (t1 t2 : F A) (f g : A -> T B),
      shape F t1 = shape F t2 ->
      fmap list f (tolist F t1) = fmap list g (tolist F t2) <->
      sub F f t1 = sub F g t2.

End tolist_respectfulness_module_definitions.

Ltac unfold_list_properness :=
  unfold shapeliness,
  tolist_fmap_respectful,
  tolist_fmap_respectful_iff,
  tolist_sub_injective,
  tolist_sub_respectful,
  tolist_sub_respectful_iff in *.

(** ** Containments *)
(******************************************************************************)
Section tolist_respectful_module_characterizations.

  Context
    `{ListableModule F T}.

  Lemma shapeliness_equiv_4: tolist_fmap_respectful F -> tolist_sub_respectful F T.
  Proof.
    unfold_list_properness.
    intros. unfold transparent tcs.
    unfold compose. replace (fmap F g t2) with (fmap F f t1); auto.
  Qed.

  Lemma shapeliness_equiv_5 : tolist_sub_respectful F T -> tolist_fmap_respectful F.
  Proof.
    unfold_list_properness. introv hyp ? ?.
    rewrite 2(RightModule.fmap_to_sub F T). apply hyp.
    - auto.
    - rewrite <- 2(fun_fmap_fmap list). unfold compose. fequal. auto.
  Qed.

End tolist_respectful_module_characterizations.

(** * Non-collapse of right actions *)
(******************************************************************************)
Section action_shape_theory.

  Context
    (F : Type -> Type)
    `{ListableModule F T}
    `{! ShapelyFunctor F}
    `{! ShapelyFunctor T}.

  Definition noncollapse := forall A (t1 t2 : F (T A)),
      shape F t1 = shape F t2 ->
      shape F (right_action F t1) = shape F (right_action F t2) ->
      shape (F ∘ T) t1 = shape (F ∘ T) t2.

  Hypothesis
    (noncollapse_proof : noncollapse).

  Lemma action_inj1 : forall A (t1 t2 : F (T A)),
      right_action F t1 = right_action F t2 ->
      bind list (tolist T) (tolist F t1) = bind list (tolist T) (tolist F t2).
  Proof.
    introv heq. assert (lemma : tolist F (right_action F t1) = tolist F (right_action F t2)).
    now rewrite heq.
    rewrite 2(tolist_right_action_1 F) in lemma.
    compose near t1. compose near t2.
    unfold_ops @Bind_Join.
    reassociate ->.
    unfold_compose_in_compose.
    rewrite (natural (ϕ := @tolist F _) (G := list)).
    assumption.
  Qed.

  Lemma action_inj2 : forall A (t1 t2 : F (T A)),
      shape F t1 = shape F t2 ->
      right_action F t1 = right_action F t2 ->
      tolist F t1 = tolist F t2.
  Proof.
    introv t_shape_eq action_eq.
    apply noncollapse_proof in t_shape_eq.
    rewrite action_eq in t_shape_eq. specialize (t_shape_eq eq_refl).
    apply (shape_compose_2 (F := F)) in t_shape_eq.
    apply shapeliness_compose_1; auto using action_inj1.
  Qed.

  Theorem action_inj : forall A (t1 t2 : F (T A)),
      shape F t1 = shape F t2 ->
      right_action F t1 = right_action F t2 ->
      t1 = t2.
  Proof.
    intros. eapply (lfun_shapeliness F); eauto.
    split; auto using action_inj2.
  Qed.

  Corollary sub_inj1 : forall A B (t1 t2 : F A) (f g : A -> T B),
      shape F t1 = shape F t2 ->
      sub F f t1 = sub F g t2 ->
      fmap list f (tolist F t1) = fmap list g (tolist F t2).
  Proof.
    introv hshape. unfold_ops @Sub_RightAction; unfold compose.
    introv heq. apply action_inj in heq.
    2:(now rewrite 2(shape_fmap)).
    compose near t1; compose near t2.
    rewrite 2(natural). unfold compose. now rewrite heq.
  Qed.

End action_shape_theory.
