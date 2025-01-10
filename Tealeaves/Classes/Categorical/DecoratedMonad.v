(** This file implements "monads decorated by monoid <<W>>." *)
From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.RightModule
  Functors.Early.Writer.

Import Monoid.Notations.

#[local] Generalizable Variable W T.

#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.
#[local] Arguments join T%function_scope {Join} (A)%type_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments extract (W)%function_scope {Extract} (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin} {A}%type_scope _.

(** * Decorated monads *)
(******************************************************************************)
Class DecoratedMonad
  (W : Type)
  (T : Type -> Type)
  `{Map T} `{Return T} `{Join T} `{Decorate W T}
  `{Monoid_op W} `{Monoid_unit W} :=
  { dmon_functor :> DecoratedFunctor W T;
    dmon_monad :> Monad T;
    dmon_monoid :> Monoid W;
    dmon_ret : forall (A : Type),
      dec T ∘ ret T A = ret T (W * A) ∘ pair Ƶ;
    dmon_join : forall (A : Type),
      dec T ∘ join T A =
        join T (W * A) ∘ map T (shift T) ∘ dec T ∘ map T (dec T);
  }.

(** * Decorated right modules *)
(******************************************************************************)
Section DecoratedModule.

  Context
    (W : Type)
    (F T : Type -> Type)
    `{Map T} `{Return T} `{Join T} `{Decorate W T}
    `{Map F} `{RightAction F T} `{Decorate W F}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedRightModule :=
    { dmod_monad :> DecoratedMonad W T;
      dmod_functor :> DecoratedFunctor W T;
      dmon_module :> Categorical.RightModule.RightModule F T;
      dmod_action : forall (A : Type),
        dec F ∘ right_action F (A := A) =
          right_action F ∘ map F (shift T) ∘ dec F ∘ map F (dec T);
    }.

End DecoratedModule.

(** * Basic properties of [shift] on monads *)
(******************************************************************************)
Section shift_monad_lemmas.

  #[local] Generalizable Variables A.

  Context
    `{Monad.Monad T}
    `{Monoid W}.

  (** [shift] applied to a singleton simplifies to a singleton. *)
  Lemma shift_return `(a : A) (w1 w2 : W) :
    shift T (w2, ret T _ (w1, a)) = ret T _ (w2 ● w1, a).
  Proof.
    unfold shift, compose. rewrite strength_return.
    compose near (w2, (w1, a)) on left.
    now rewrite (natural (F := fun A => A)).
  Qed.

  Lemma shift_join `(t : T (T (W * A))) (w : W) :
    shift T (w, join T (W * A) t) = join T (W * A) (map T (fun t => shift T (w, t)) t).
  Proof.
    rewrite (shift_spec T). compose near t on left.
    rewrite natural. unfold compose; cbn.
    fequal. unfold_ops @Map_compose.
    fequal. ext x. now rewrite (shift_spec T).
  Qed.

End shift_monad_lemmas.

(** * Helper lemmas for proving instances *)
(******************************************************************************)
Section helper_lemmas.

  Context
    `{Monad.Monad T}
    `{Decorate W T}
    `{Monoid W}.

  (** This lemmas is useful for proving the decoration-join law. *)
  Lemma dec_helper_4 {A} : forall (t : T (T A)) (w : W),
      dec T (join T A t) =
        join T (W * A) (map T (shift T) (dec T (map T (dec T) t))) ->
      shift T (w, dec T (join T A t)) =
        join T (W * A) (map T (shift T) (shift T (w, dec T (map T (dec T) t)))).
  Proof.
    introv IH. rewrite !(shift_spec T) in *. rewrite IH.
    compose near (dec T (map T (dec T) t)) on right.
    rewrite (fun_map_map (F := T)). rewrite (shift_increment T).
    rewrite <- (fun_map_map (F := T)).
    change (map T (map T ?f)) with (map (T ∘ T) f).
    compose near (dec T (map T (dec T) t)).
    reassociate <-.
    #[local] Set Keyed Unification.
    now rewrite <- (natural (ϕ := @join T _)).
    #[local] Unset Keyed Unification.
  Qed.

End helper_lemmas.

#[local] Generalizable Variables E F ϕ A B.

(** * Pushing decorations through a monoid homomorphism *)
(** If a functor is readable by a monoid, it is readable by any target
    of a homomorphism from that monoid too. *)
(******************************************************************************)
Section DecoratedFunctor_monoid_homomorphism.

  Import Product.Notations.

  Context
    (Wsrc Wtgt : Type)
    `{Monoid_Morphism Wsrc Wtgt ϕ}
    `{Decorate Wsrc F} `{Map F} `{Return F} `{Join F}
    `{! DecoratedMonad Wsrc F}.

  Instance Decorate_homomorphism :
    Decorate Wtgt F := fun A => map F (map_fst ϕ) ∘ dec F.

  Instance Natural_read_morphism : Natural (@dec Wtgt F Decorate_homomorphism).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Decorate_homomorphism.
      unfold_ops @Map_compose.
      reassociate <- on left.
      rewrite (fun_map_map (F := F)).
      rewrite (product_map_commute).
      rewrite <- (fun_map_map (F := F)).
      reassociate -> on left.
      change (map F (map (prod Wsrc) f)) with
        (map (F ∘ prod Wsrc) f).
      reassociate ->.
      rewrite <- (natural (ϕ := @dec Wsrc F _ )).
      reflexivity.
  Qed.

  Instance DecoratedFunctor_morphism : Categorical.DecoratedFunctor.DecoratedFunctor Wtgt F.
  Proof.
    constructor; try typeclasses eauto.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate <-. reassociate -> near (map F (map_fst ϕ)).
      rewrite <- (natural (ϕ := @dec Wsrc F _) (map_fst ϕ)).
      reassociate <-. unfold_ops @Map_compose. rewrite (fun_map_map (F := F)).
      reassociate -> near (@dec Wsrc F _ A).
      rewrite (dfun_dec_dec (E := Wsrc) (F := F)).
      reassociate <-. rewrite (fun_map_map (F := F)).
      reassociate <-. rewrite (fun_map_map (F := F)).
      fequal. fequal. ext [w a]. reflexivity.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate <-. rewrite (fun_map_map (F := F)).
      replace (extract (Wtgt ×) A ∘ map_fst ϕ)
        with (extract (Wsrc ×) A) by now ext [w a].
      now rewrite (dfun_dec_extract (E := Wsrc) (F := F)).
  Qed.

  Instance DecoratedMonad_morphism : DecoratedMonad.DecoratedMonad Wtgt F.
  Proof.
    inversion H.
    constructor; try typeclasses eauto.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate ->. rewrite (dmon_ret (W := Wsrc) (T := F)).
      reassociate <-. rewrite (natural (ϕ := @ret F _)).
      ext a. unfold compose; cbn.
      now rewrite (monmor_unit).
    - intros. unfold dec, Decorate_homomorphism.
      reassociate ->. rewrite (dmon_join (W := Wsrc) (T := F)).
      repeat reassociate <-.
      rewrite (natural (ϕ := @join F _)).
      reassociate -> near (map F (shift F)).
      unfold_ops @Map_compose.
      unfold_compose_in_compose.
      rewrite (fun_map_map (F := F) _ _ _ (shift F) (map F (map_fst ϕ))).
      reassociate -> near (map F (map_fst ϕ)). rewrite (fun_map_map (F := F)).
      rewrite <- (fun_map_map (F := F) _ _ _ (dec F) (map F (map_fst ϕ))).
      reassociate <-. reassociate -> near (map F (map F (map_fst ϕ))).
      rewrite <- (natural (ϕ := @dec Wsrc F _)).
      reassociate <-. unfold_ops @Map_compose.
      reassociate -> near (map F (map (prod Wsrc) (map F (map_fst ϕ)))).
      rewrite (fun_map_map (F := F)).
      repeat fequal. ext [w t].
      unfold compose; cbn.
      change (id ?f) with f. unfold shift.
      unfold compose; cbn.
      do 2 (compose near t;
            repeat rewrite (fun_map_map (F := F))).
      fequal. ext [w' a].
      unfold compose; cbn. rewrite monmor_op.
      reflexivity.
  Qed.

End DecoratedFunctor_monoid_homomorphism.
