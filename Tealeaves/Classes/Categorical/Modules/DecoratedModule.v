From Tealeaves Require Export
  Classes.Categorical.RightModule
  Classes.Categorical.DecoratedMonad.

Import Functor.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W F T A B.

(** * Basic properties of [shift] on modules *)
(******************************************************************************)
Section shift_module_lemmas.

  Context
    `{RightModule F T}
    `{Monoid W}.

  Lemma shift_right_action {A} (t : F (T (W * A))) (w : W) :
    shift F (w, right_action F t) =
    right_action F (map F (fun t => shift T (w, t)) t).
  Proof.
    rewrite (shift_spec F). compose near t on left.
    rewrite natural. unfold compose; cbn.
    fequal. unfold_ops @Map_compose.
    fequal. ext x. now rewrite (shift_spec T).
  Qed.

  Lemma shift_sub `(t : F (W * A)) (w : W) `(f : W * A -> T (W * B)) :
    shift F (w, sub F f t) =
    sub F (fun p => shift T (w, f p)) t.
  Proof.
    unfold_ops @Sub_RightAction. unfold compose.
    rewrite shift_right_action. fequal.
    compose near t on left.
    now rewrite (fun_map_map F).
  Qed.

End shift_module_lemmas.

(** * Decorated right modules *)
(******************************************************************************)
Section DecoratedModule_class.

  Context
    (W : Type)
    (F T : Type -> Type)
    `{Map T} `{Return T} `{Join T} `{Decorate W T}
    `{Map F} `{RightAction F T} `{Decorate W F}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedModule :=
    { drmod_monad :> DecoratedMonad W T;
      drmod_functor :> DecoratedFunctor W F;
      drmod_module :> RightModule F T;
      drmod_action :
        `(dec F ∘ right_action F (A:=A) =
          right_action F ∘ map F (shift T) ∘ dec F ∘ map F (dec T));
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
    `{Map F} `{Map G} `{Map T}
    `{Return T} `{Join T} `{RightAction F T}
    `{Decorate W F} `{Decorate W G} `{Decorate W T}
    `{! DecoratedFunctor W G}
    `{! DecoratedModule W F T}.

  Instance: RightModule (G ∘ F) T := RightModule_compose.

  Theorem drmod_action_compose :
    `(dec (G ∘ F) ∘ right_action (G ∘ F) (A:=A) =
      right_action (G ∘ F) ∘ map (G ∘ F) (shift T) ∘ dec (G ∘ F) ∘ map (G ∘ F) (dec T)).
  Proof.
    intros. unfold_ops @Decorate_compose @RightAction_compose.
    (* Use <<drmod_action>> to write the LHS with a butterfly *)
    change (?x ∘ map G (dec F) ∘ map G (right_action F))
      with (x ∘ (map G (dec F) ∘ map G (right_action F))).
    rewrite (fun_map_map G). rewrite (drmod_action W F T).
    (* Use naturality to cancel out equal terms (decorations on F and T) *)
    rewrite <- (fun_map_map G).
    change (map G (map F (dec T))) with (map (G ∘ F) (dec T (A := A))).
    repeat reassociate <-. fequal.
    rewrite <- (fun_map_map G).
    repeat reassociate <-. fequal.
    (* Bring left <<join (prod W)>> across the distribution, then re-associate *)
    reassociate -> on right.
    unfold shift at 3.
    reassociate <- on right.
    rewrite <- (fun_map_map G).
    reassociate <- on left.
    unfold shift at 3.
    rewrite <- (fun_map_map G).
    reassociate <- on right.
    change (map G (map F (join (A := ?A) (prod W))))
      with (map (G ∘ F) (join (A := A) (prod W))).
    reassociate -> near (map (G ∘ F) (join (prod W))).
    rewrite (fun_map_map (G ∘ F)).
    reassociate -> near (join (prod W)).
    rewrite (strength_join_l).
    repeat reassociate <-.
    rewrite (fun_map_map T).
    rewrite (mon_join_join (prod W)).
    (* Bring the right action of <<T>> on <<F>> under the distribution *)
    unfold_ops @Map_compose.
    unfold_compose_in_compose.
    rewrite (fun_map_map G (g := (@right_action F T _ (W * A)))).
    repeat reassociate -> on right.
    rewrite <- (fun_map_map F).
    rewrite <- (fun_map_map F).
    repeat reassociate <- on right.
    change (map F (map T ?f)) with (map (F ∘ T) f).
    rewrite <- (fun_map_map (F ∘ T)).
    reassociate <- on right.
    #[local] Set Keyed Unification.
    rewrite <- (natural (ϕ := @right_action F T _)).
    #[local] Unset Keyed Unification.
    change (map (F ∘ T) (map (prod W) ?f)) with (map F (map (T ○ prod W) f)).
    reassociate -> near (map F (strength T)).
    rewrite (fun_map_map F).
    rewrite (natural (ϕ := @strength T _ _)).
    (* Bring up the <<map G (strength F) ∘ dec G>> *)
    rewrite (fun_map_map G).
    #[local] Set Keyed Unification.
    reassociate -> near (strength F).
    change (map F (map (prod W) ?f)) with (map (F ○ prod W) f).
    rewrite (natural (ϕ := @strength F _ _)).
    reassociate <-.
    rewrite <- (fun_map_map G).
    reassociate -> near (dec G).
    change (map G (map (prod W ○ F) (strength (B:=?B) (A:=?A) T)) ∘ dec G)
      with (map (G ∘ prod W) (map F (strength (B:=B) (A:=A) T)) ∘ dec G).
    rewrite (natural (ϕ := @dec W G _)).
    reassociate <-.
    rewrite <- (fun_map_map F).
    change (map F (map (prod W ○ T) ?f)) with (map (F ○ prod W) (map T f)).
    reassociate <-. reassociate -> near (strength F).
    rewrite (natural (ϕ := @strength F _ _)).
    reassociate <-.
    change (?x ∘ right_action F ∘ map F (strength T) ∘ strength F ∘ ?y)
      with (x ∘ (right_action F ∘ map F (strength T) ∘ strength F) ∘ y).
    rewrite <- (strength_right_action T F).
    reassociate -> on right.
    rewrite <- (fun_map_map G).
    rewrite <- (fun_map_map G).
    rewrite <- (fun_map_map G).
    change (map G (map (prod W ○ F) (map T (join (A:=?A) (prod W)))))
      with (map (G ∘ prod W) (map F (map T (join (A:= A) (prod W))))).
    reassociate <-. reassociate -> near (dec G).
    rewrite (natural (ϕ := @dec W G _)).
    do 2 reassociate <-.
    change (map G (map (prod W) (right_action (A:=?A) F)))
      with (map (G ∘ prod W) (right_action (A:=A) F)).
    reassociate -> near (dec G). rewrite (natural (ϕ := @dec W G _)).
    reassociate <-.
    rewrite (fun_map_map G).
    reassociate -> on right.
    change (map G (map F ?f)) with (map (G ∘ F) f).
    rewrite (fun_map_map (G ∘ F)).
    reflexivity.
  Qed.

  Instance DecoratedModule_compose : DecoratedModule W (G ∘ F) T :=
    {| drmod_action := drmod_action_compose; |}.

End DecoratedModule_compose.

(** * Kleisli presentation of decorated modules *)
(******************************************************************************)
Definition subd (F : Type -> Type) `{Map F} `{RightAction F T} `{Decorate W F} {A B}
  : (W * A -> T B) -> F A -> F B := fun f => sub F f ∘ dec F.

(** ** Sub-operations *)
(******************************************************************************)
Section decoratedmodule_suboperations.

  Context
    (F T : Type -> Type)
    `{DecoratedModule W F T}.

  Lemma mapd_to_subd : forall `(f : W * A -> B),
      mapd F f = subd F (ret T ∘ f).
  Proof.
    introv. unfold mapd, subd.
    unfold_compose_in_compose.
    rewrite <- (RightModule.sub_map F T).
    now rewrite (RightModule.sub_id F T).
  Qed.

  Lemma sub_to_subd : forall `(f : A -> T B),
      sub F f = subd F (f ∘ extract (prod W)).
  Proof.
    introv. unfold subd.
    rewrite <- (RightModule.sub_map F T).
    reassociate -> on right.
    now rewrite (dfun_dec_extract W F).
  Qed.

  Lemma map_to_subd : forall `(f : A -> B),
      map F f = subd F (ret T ∘ f ∘ extract (prod W)).
  Proof.
    introv. now rewrite (map_to_mapd F), mapd_to_subd.
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
    reassociate -> near (map F f).
    rewrite (fun_map_map F).
    reassociate -> near (map F (dec T ∘ f)).
    rewrite <- (natural (G := F ∘ prod W) (F := F) (ϕ := @dec W F _)).
    reassociate <- on left.
    unfold_ops @Map_compose.
    change_left (right_action F ∘ (map F (shift T) ∘ map F (map (prod W) (dec T ∘ f))) ∘ dec F ∘ dec F).
    rewrite (fun_map_map F).
    reassociate -> on left.
    rewrite (dfun_dec_dec W F).
    reassociate <- on left.
    reassociate -> near (map F (cojoin (A:=A) (prod W))).
    now rewrite (fun_map_map F).
  Qed.

  Corollary dec_sub : forall A B (f : W * A -> T B),
      dec F ∘ sub F f =
      subd F (shift T ∘ map (prod W) (dec T ∘ f)).
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
    rewrite <- (RightModule.sub_map F T).
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
    rewrite (sub_sub F T).
    unfold kcomposed; reassociate -> on left.
    reflexivity.
  Qed.

End decoratedmodule_kleisli_laws.

(** ** Composition with suboperations *)
(******************************************************************************)
Section decoratedmonad_suboperation_composition.

  Context
    (F : Type -> Type)
    `{DecoratedModule W F T}.

  Lemma subd_mapd {A B C} : forall (g : W * B -> T C) (f : W * A -> B),
      subd F g ∘ mapd F f = subd F (g co⋆ f).
  Proof.
    introv. rewrite (mapd_to_subd F T).
    rewrite <- (subd_subd F T).
    now rewrite (dm_kleisli_star1).
  Qed.

  Corollary sub_subd {A B C} : forall (g : B -> T C) (f : W * A -> T B),
      sub F g ∘ subd F f = subd F (g ⋆ f).
  Proof.
    intros. rewrite (sub_to_subd F T).
    rewrite <- (subd_subd F T).
    now rewrite (dm_kleisli_star4).
  Qed.

  Corollary mapd_subd {A B C} : forall (g : W * B -> C) (f : W * A -> T B),
      mapd F g ∘ subd F f = subd F (map T g ∘ shift T ∘ cobind (prod W) (dec T ∘ f)).
  Proof.
    intros. rewrite (mapd_to_subd F T).
    rewrite <- (subd_subd F T).
    unfold kcomposed.
    now rewrite <- (map_to_bind T).
  Qed.

  Corollary subd_sub {A B C} : forall (g : W * B -> T C) (f : A -> T B),
      subd F g ∘ sub F f = subd F (bind T g ∘ shift T ∘ map (prod W) (dec T ∘ f)).
  Proof.
    introv. rewrite (sub_to_subd F T).
    rewrite <- (subd_subd F T).
    unfold kcomposed. reassociate <-.
    now rewrite <- (map_to_cobind (prod W)).
  Qed.

  Lemma subd_map {A B C} : forall (g : W * B -> T C) (f : A -> B),
      subd F g ∘ map F f = subd F (g ∘ map (prod W) f).
  Proof.
    intros. rewrite (map_to_subd F T).
    rewrite <- (subd_subd F T).
    reassociate -> on left. rewrite (dm_kleisli_star1).
    unfold cokcompose. now rewrite (map_to_cobind (prod W)).
  Qed.

  Corollary map_subd {A B C} : forall (g : B -> C) (f : W * A -> T B),
      map F g ∘ subd F f = subd F (map T g ∘ f).
  Proof.
    intros. rewrite (map_to_subd F T).
    rewrite <- (subd_subd F T).
    rewrite (dm_kleisli_star4). unfold kcompose.
    now rewrite <- (map_to_bind T).
  Qed.

End decoratedmonad_suboperation_composition.
