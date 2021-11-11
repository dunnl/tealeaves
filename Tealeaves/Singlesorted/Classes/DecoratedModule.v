From Tealeaves Require Export
     Singlesorted.Classes.RightModule
     Singlesorted.Classes.DecoratedMonad.

Import Functor.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import Monoid.Notations.
Import DecoratedMonad.Notations.
#[local] Open Scope tealeaves_scope.

(** * Basic properties of [shift] on modules *)
(******************************************************************************)
Section shift_module_lemmas.

  Context
    `{RightModule F T}
    `{Monoid W}.

  Lemma shift_right_action {A} (t : F (T (W * A))) (w : W) :
    shift F (w, right_action F t) =
    right_action F (fmap F (fun t => shift T (w, t)) t).
  Proof.
    rewrite shift_spec. compose near t on left.
    rewrite natural. unfold compose; cbn.
    fequal. unfold_ops @Fmap_compose.
    fequal. ext x. now rewrite shift_spec.
  Qed.

  Lemma shift_sub `(t : F (W * A)) (w : W) `(f : W * A -> T (W * B)) :
    shift F (w, sub F f t) =
    sub F (fun p => shift T (w, f p)) t.
  Proof.
    unfold_ops @Sub_RightAction. unfold compose.
    rewrite shift_right_action. fequal.
    compose near t on left.
    now rewrite (fun_fmap_fmap F).
  Qed.

End shift_module_lemmas.

(** * Decorated Right Modules *)
(******************************************************************************)
Section DecoratedModule_class.

  Context
    (W : Type)
    (F T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T}
    `{Fmap F} `{RightAction F T} `{Decorate W F}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedModule :=
    { drmod_monad :> DecoratedMonad W T;
      drmod_functor :> DecoratedFunctor W F;
      drmod_module :> RightModule F T;
      drmod_action :
        `(dec F ∘ right_action F (A:=A) =
          right_action F ∘ fmap F (shift T) ∘ dec F ∘ fmap F (dec T));
    }.

End DecoratedModule_class.

(** ** Decorated monads are decorated modules *)
(******************************************************************************)
Section DecoratedModule_Monad.

  Context
    (T : Type -> Type)
    `{DecoratedMonad W T}.

  Existing Instance RightAction_Join.

  Instance DecoratedModule_Monad : DecoratedModule W T T :=
    {| drmod_action := dmon_join W T;
       drmod_functor := dmon_functor W T;
       drmod_module := RightModule_Monad T;
    |}.

End DecoratedModule_Monad.

(** ** Decorated modules are closed under composition with functors *)
(******************************************************************************)
Section DecoratedModule_compose.

  Context
    `{Monoid W}
    `{Fmap F} `{Fmap G} `{Fmap T}
    `{Return T} `{Join T} `{RightAction F T}
    `{Decorate W F} `{Decorate W G} `{Decorate W T}
    `{! DecoratedFunctor W G}
    `{! DecoratedModule W F T}.

  Instance: RightModule (G ∘ F) T := RightModule_compose.

  Theorem drmod_action_compose :
    `(dec (G ∘ F) ∘ right_action (G ∘ F) (A:=A) =
      right_action (G ∘ F) ∘ fmap (G ∘ F) (shift T) ∘ dec (G ∘ F) ∘ fmap (G ∘ F) (dec T)).
  Proof.
    intros. unfold_ops @Decorate_compose @RightAction_compose.
    (* Use <<drmod_action>> to write the LHS with a butterfly *)
    change (?x ∘ fmap G (dec F) ∘ fmap G (right_action F))
      with (x ∘ (fmap G (dec F) ∘ fmap G (right_action F))).
    rewrite (fun_fmap_fmap G). rewrite (drmod_action W F T).
    (* Use naturality to cancel out equal terms (decorations on F and T) *)
    rewrite <- (fun_fmap_fmap G).
    change (fmap G (fmap F (dec T))) with (fmap (G ∘ F) (dec T (A := A))).
    repeat reassociate <-. fequal.
    rewrite <- (fun_fmap_fmap G).
    repeat reassociate <-. fequal.
    (* Bring left <<join (prod W)>> across the distribution, then re-associate *)
    reassociate -> on right.
    unfold shift at 3.
    reassociate <- on right.
    rewrite <- (fun_fmap_fmap G).
    reassociate <- on left.
    unfold shift at 3.
    rewrite <- (fun_fmap_fmap G).
    reassociate <- on right.
    change (fmap G (fmap F (join (A := ?A) (prod W))))
      with (fmap (G ∘ F) (join (A := A) (prod W))).
    reassociate -> near (fmap (G ∘ F) (join (prod W))).
    rewrite (fun_fmap_fmap (G ∘ F)).
    reassociate -> near (join (prod W)).
    rewrite (writer_strength_join_l).
    repeat reassociate <-.
    rewrite (fun_fmap_fmap T).
    rewrite (mon_join_join (prod W)).
    (* Bring the right action of <<T>> on <<F>> under the distribution *)
    unfold_ops @Fmap_compose.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G (g := (@right_action F T _ (W * A)))).
    repeat reassociate -> on right.
    rewrite <- (fun_fmap_fmap F).
    rewrite <- (fun_fmap_fmap F).
    repeat reassociate <- on right.
    change (fmap F (fmap T ?f)) with (fmap (F ∘ T) f).
    rewrite <- (fun_fmap_fmap (F ∘ T)).
    reassociate <- on right.
    #[local] Set Keyed Unification.
    rewrite <- (natural (ϕ := @right_action F T _)).
    #[local] Unset Keyed Unification.
    change (fmap (F ∘ T) (fmap (prod W) ?f)) with (fmap F (fmap (T ○ prod W) f)).
    reassociate -> near (fmap F (strength T)).
    rewrite (fun_fmap_fmap F).
    rewrite (natural (ϕ := @strength T _ _)).
    (* Bring up the <<fmap G (strength F) ∘ dec G>> *)
    rewrite (fun_fmap_fmap G).
    #[local] Set Keyed Unification.
    reassociate -> near (strength F).
    change (fmap F (fmap (prod W) ?f)) with (fmap (F ○ prod W) f).
    rewrite (natural (ϕ := @strength F _ _)).
    reassociate <-.
    rewrite <- (fun_fmap_fmap G).
    reassociate -> near (dec G).
    change (fmap G (fmap (prod W ○ F) (strength (B:=?B) (A:=?A) T)) ∘ dec G)
      with (fmap (G ∘ prod W) (fmap F (strength (B:=B) (A:=A) T)) ∘ dec G).
    rewrite (natural (ϕ := @dec W G _)).
    reassociate <-.
    rewrite <- (fun_fmap_fmap F).
    change (fmap F (fmap (prod W ○ T) ?f)) with (fmap (F ○ prod W) (fmap T f)).
    reassociate <-. reassociate -> near (strength F).
    rewrite (natural (ϕ := @strength F _ _)).
    reassociate <-.
    change (?x ∘ right_action F ∘ fmap F (strength T) ∘ strength F ∘ ?y)
      with (x ∘ (right_action F ∘ fmap F (strength T) ∘ strength F) ∘ y).
    rewrite <- (strength_right_action_r T F).
    reassociate -> on right.
    rewrite <- (fun_fmap_fmap G).
    rewrite <- (fun_fmap_fmap G).
    rewrite <- (fun_fmap_fmap G).
    change (fmap G (fmap (prod W ○ F) (fmap T (join (A:=?A) (prod W)))))
      with (fmap (G ∘ prod W) (fmap F (fmap T (join (A:= A) (prod W))))).
    reassociate <-. reassociate -> near (dec G).
    rewrite (natural (ϕ := @dec W G _)).
    do 2 reassociate <-.
    change (fmap G (fmap (prod W) (right_action (A:=?A) F)))
      with (fmap (G ∘ prod W) (right_action (A:=A) F)).
    reassociate -> near (dec G). rewrite (natural (ϕ := @dec W G _)).
    reassociate <-.
    rewrite (fun_fmap_fmap G).
    reassociate -> on right.
    change (fmap G (fmap F ?f)) with (fmap (G ∘ F) f).
    rewrite (fun_fmap_fmap (G ∘ F)).
    reflexivity.
  Qed.

  Instance DecoratedModule_compose : DecoratedModule W (G ∘ F) T :=
    {| drmod_action := drmod_action_compose; |}.

End DecoratedModule_compose.

(** * Kleisli presentation of decorated modules *)
(******************************************************************************)
Definition subd (F : Type -> Type) `{Fmap F} `{RightAction F T} `{Decorate W F} {A B}
  : (W * A -> T B) -> F A -> F B := fun f => sub F f ∘ dec F.

(** ** Sub-operations *)
(******************************************************************************)
Section decoratedmodule_suboperations.

  Context
    (F T : Type -> Type)
    `{DecoratedModule W F T}.

  Lemma fmapd_to_subd : forall `(f : W * A -> B),
      fmapd F f = subd F (ret T ∘ f).
  Proof.
    introv. unfold fmapd, subd.
    unfold_compose_in_compose.
    rewrite <- (RightModule.sub_fmap F T).
    now rewrite (RightModule.sub_id F T).
  Qed.

  Lemma sub_to_subd : forall `(f : A -> T B),
      sub F f = subd F (f ∘ extract (prod W)).
  Proof.
    introv. unfold subd.
    rewrite <- (RightModule.sub_fmap F T).
    reassociate -> on right.
    now rewrite (dfun_dec_extract W F).
  Qed.

  Lemma fmap_to_subd : forall `(f : A -> B),
      fmap F f = subd F (ret T ∘ f ∘ extract (prod W)).
  Proof.
    introv. now rewrite (fmap_to_fmapd F), fmapd_to_subd.
  Qed.

End decoratedmodule_suboperations.

(** ** Interaction between [dec] and [subd], [sub] *)
(******************************************************************************)
Section dec_subd.

  #[local] Set Keyed Unification.

  Context
    (F : Type -> Type)
    `{DecoratedModule W F T}.

  Theorem dec_subd : forall A B (f : W * A -> T B),
      dec F ∘ subd F f =
      subd F (shift T ∘ cobind (prod W) (dec T ∘ f)).
  Proof.
    introv. unfold subd. unfold_ops @Sub_RightAction.
    do 2 reassociate <- on left.
    rewrite (drmod_action W F T).
    reassociate -> near (fmap F f).
    rewrite (fun_fmap_fmap F).
    reassociate -> near (fmap F (dec T ∘ f)).
    rewrite <- (natural (G := F ∘ prod W) (F := F) (ϕ := @dec W F _)).
    reassociate <- on left.
    unfold_ops @Fmap_compose.
    change_left (right_action F ∘ (fmap F (shift T) ∘ fmap F (fmap (prod W) (dec T ∘ f))) ∘ dec F ∘ dec F).
    rewrite (fun_fmap_fmap F).
    reassociate -> on left.
    rewrite (dfun_dec_dec W F).
    reassociate <- on left.
    reassociate -> near (fmap F (cojoin (A:=A) (prod W))).
    now rewrite (fun_fmap_fmap F).
  Qed.

  Corollary dec_sub : forall A B (f : W * A -> T B),
      dec F ∘ sub F f =
      subd F (shift T ∘ fmap (prod W) (dec T ∘ f)).
  Proof.
    introv. rewrite (sub_to_subd F T).
    rewrite dec_subd.
    fequal. now ext [w a].
  Qed.

End dec_subd.

(** ** Kleisli laws for [subd] *)
(******************************************************************************)
Section decoratedmodule_kleisli_laws.

  Context
    (F T : Type -> Type)
    `{DecoratedModule W F T}.

  (** *** Identity law *)
  Lemma subd_id :
    `(subd F (ret T ∘ extract (prod W)) = @id (F A)).
  Proof.
    intros. unfold subd.
    rewrite <- (RightModule.sub_fmap F T).
    reassociate -> on left.
    rewrite (dfun_dec_extract W F).
    now rewrite (RightModule.sub_id F T).
  Qed.

  (** *** Composition law *)
  Lemma subd_subd {A B C} : forall (g : W * B -> T C) (f : W * A -> T B),
      subd F (g ⋆d f) = subd F g ∘ subd F f.
  Proof.
    intros. unfold subd at 2.
    reassociate -> on right.
    rewrite (dec_subd F).
    unfold subd at 2.
    reassociate <- on right.
    rewrite (RightModule.sub_sub F T).
    unfold kcomposed; reassociate -> on left.
    now rewrite (Comonad.fmap_cobind (prod W)).
  Qed.

End decoratedmodule_kleisli_laws.

(** ** Composition with suboperations *)
(******************************************************************************)
Section decoratedmonad_suboperation_composition.

  Context
    (F : Type -> Type)
    `{DecoratedModule W F T}.

  Lemma subd_fmapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      subd F g ∘ fmapd F f = subd F (g co⋆ f).
  Proof.
    introv. rewrite (fmapd_to_subd F T).
    rewrite <- (subd_subd F T).
    now rewrite (kleisli_star_1).
  Qed.

  Corollary sub_subd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      sub F g ∘ subd F f = subd F (g ⋆ f).
  Proof.
    intros. rewrite (sub_to_subd F T).
    rewrite <- (subd_subd F T).
    now rewrite (kleisli_star_2).
  Qed.

  Corollary fmapd_subd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      fmapd F g ∘ subd F f = subd F (fmap T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f)).
  Proof.
    intros. rewrite (fmapd_to_subd F T).
    rewrite <- (subd_subd F T).
    unfold kcomposed. rewrite <- (fmap_to_bind T).
    now rewrite <- (Comonad.fmap_cobind (prod W)).
  Qed.

  Corollary subd_sub {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      subd F g ∘ sub F f = subd F (bind T g ∘ shift T ∘ fmap (prod W) (dec T ∘ f)).
  Proof.
    introv. rewrite (sub_to_subd F T).
    rewrite <- (subd_subd F T).
    unfold kcomposed. rewrite <- (fmap_to_cobind (prod W)).
    reassociate -> on left. now rewrite (fun_fmap_fmap (prod W)).
  Qed.

  Lemma subd_fmap {A B C} : forall (g : W * B -> T C) (f : A -> B),
      subd F g ∘ fmap F f = subd F (g ∘ fmap (prod W) f).
  Proof.
    intros. rewrite (fmap_to_subd F T).
    rewrite <- (subd_subd F T).
    reassociate -> on left. rewrite (kleisli_star_1).
    unfold cokcompose. now rewrite (Comonad.fmap_to_cobind (prod W)).
  Qed.

  Corollary fmap_subd {A B C} : forall (g : B -> C) (f : W * A -> T B),
      fmap F g ∘ subd F f = subd F (fmap T g ∘ f).
  Proof.
    intros. rewrite (fmap_to_subd F T).
    rewrite <- (subd_subd F T).
    rewrite (kleisli_star_2). unfold kcompose.
    now rewrite <- (fmap_to_bind T).
  Qed.

End decoratedmonad_suboperation_composition.
