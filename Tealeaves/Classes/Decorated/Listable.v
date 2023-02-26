From Tealeaves Require Export
  Classes.Decorated.Functor
  Classes.Decorated.Monad
  Classes.Listable.Functor
  Classes.Listable.Monad.

Import Monoid.Notations.
Import List.ListNotations.

#[local] Generalizable Variables W F A.

(** * Decorated listable functors *)
(******************************************************************************)

(** ** Derived operation [tolistd] *)
(******************************************************************************)
Definition tolistd F `{Decorate W F} `{Tolist F} {A} : F A -> list (W * A)
  := tolist F ∘ dec F.

(** ** General properties *)
(******************************************************************************)
Section ListableFunctor_decorated_theory.

  Context
    `{Monoid W}
    `{Fmap F} `{Decorate W F} `{Tolist F}
    `{! DecoratedFunctor W F}
    `{! ListableFunctor F}.

  (** ** Interaction between [tolistd] and [dec] *)
  (******************************************************************************)
  Theorem tolistd_dec {A} :
      tolistd F ∘ dec F (A:=A) = fmap list (cojoin (prod W)) ∘ tolistd F.
  Proof.
    intros. unfold tolistd.
    reassociate ->.
    rewrite (dfun_dec_dec W F).
    reassociate <-.
    rewrite <- natural.
    reflexivity.
  Qed.

  (** ** Corollaries: [tolist] and [dec] *)
  (******************************************************************************)
  Theorem tolist_dec {A} :
      tolist F ∘ dec F (A:=A) = tolistd F.
  Proof.
    reflexivity.
  Qed.

  (** ** Corollaries: [tolistd] and [fmap] *)
  (******************************************************************************)
  Theorem tolistd_fmap {A B} : forall (f : A -> B),
      tolistd F ∘ fmap F f = fmap list (fmap (prod W) f) ∘ tolistd F.
  Proof.
    intros. unfold tolistd.
    reassociate <-.
    rewrite natural.
    reassociate -> on right.
    change (fmap F (fmap (prod W) ?f)) with (fmap (F ∘ prod W) f).
    rewrite (natural (ϕ := @dec W F _)).
    reflexivity.
  Qed.

End ListableFunctor_decorated_theory.

(*

Below needs Kleisli-style presentation of decorated functors

(** ** General properties *)
(******************************************************************************)
Section ListableFunctor_decorated_theory.

  Context
    `{Monoid W}
    `{Fmap F} `{Decorate W F} `{Tolist F}
    `{! DecoratedFunctor W F}
    `{! ListableFunctor F}.

  #[local] Set Keyed Unification.

  (** ** Interaction between [tolistd] and [fmapd] *)
  (******************************************************************************)
  Theorem tolistd_fmapd {A B} : forall (f : W * A -> B),
      tolistd F ∘ fmapd F f = fmap list (cobind (prod W) f) ∘ tolistd F.
  Proof.
    intros. unfold fmapd, tolistd.
    reassociate <- on left; reassociate <- on right.
    change_left (tolist F ∘ (dec F ∘ fmap F f ∘ dec F)).
    rewrite <- (natural (G := F ∘ prod W)).
    reassociate <- on left. unfold_ops @Fmap_compose.
    reassociate <- on left. rewrite <- (natural (F := F)).
    reassociate -> on left. rewrite (dfun_dec_dec W F).
    change_left (fmap list (fmap (prod W) f) ∘ (tolist F ∘ fmap F (cojoin (prod W))) ∘ dec F).
    rewrite <- natural.
    reassociate <- on left. rewrite (fun_fmap_fmap list).
    reflexivity.
  Qed.

  (** ** Corollaries: [tolist] and [fmapd] *)
  (******************************************************************************)
  Theorem tolist_fmapd {A B} : forall (f : W * A -> B),
      tolist F ∘ fmapd F f = fmap list f ∘ tolistd F.
  Proof.
    intros. unfold fmapd, tolistd.
    reassociate <- on left; reassociate <- on right.
    now rewrite <- natural.
  Qed.

  (** ** Corollaries: [tolistd] and [fmap] *)
  (******************************************************************************)
  Theorem tolistd_fmap {A B} : forall (f : W * A -> B),
      tolistd F ∘ fmap F f = fmap list (fmap (prod W) f) ∘ tolistd F.
  Proof.
    intros. unfold fmapd, tolistd.
    reassociate -> on left. rewrite <- (natural (G := F ∘ prod W)).
    reassociate <- on left. unfold_ops @Fmap_compose.
    now rewrite <- (natural (F := F) (G := list)).
  Qed.

  #[local] Unset Keyed Unification.

End ListableFunctor_decorated_theory.
*)

(** * Decorated listable monads *)
(******************************************************************************)

(** ** Interaction between [tolistd], [join], and [ret] *)
(******************************************************************************)
Section ListableMonad_tolistd.

  Context
    (T : Type -> Type)
    `{Monoid W}
    `{Fmap T} `{Decorate W T} `{Tolist T}
    `{Return T} `{Join T}
    `{! DecoratedMonad W T}
    `{! ListableMonad T}
    {A B : Type}.

  Implicit Types (w : W) (a : A) (b : B) (t : T A).

  Theorem tolistd_ret : forall a,
      tolistd T (ret T a) = [ (Ƶ, a) ].
  Proof.
    introv. unfold tolistd, compose.
    compose near a on left. rewrite (dmon_ret W T).
    unfold compose. compose near (Ƶ, a) on left.
    now rewrite (lmon_ret T).
  Qed.

  Lemma tolistd_join1 :
    tolist T ∘ fmap T (tolist T ∘ shift T (A := A)) =
    fmap list (shift list) ∘ tolist T ∘ fmap T (fmap (prod W) (tolist T)).
  Proof.
    unfold shift. reassociate <-.
    rewrite <- (fun_fmap_fmap list).
    reassociate -> near (tolist T).
    rewrite (natural (ϕ := @tolist T _)).
    reassociate <-. reassociate -> near (fmap T (fmap (prod W) (tolist T))).
    rewrite (fun_fmap_fmap T).
    replace (strength list ∘ fmap (prod W) (tolist T))
      with (tolist T ∘ strength T (A := W) (B := W * A)).
    rewrite <- (fun_fmap_fmap T).
    rewrite <- (fun_fmap_fmap T _ _ _ (strength T)).
    do 2 reassociate <-. fequal.
    rewrite (natural (ϕ := @tolist T _)).
    reassociate -> on right; rewrite (fun_fmap_fmap T). fequal.
    fequal. now rewrite (natural (ϕ := @tolist T _)).
    ext [w t]; unfold compose; cbn. compose near t.
    now rewrite (natural (ϕ := @tolist T _)).
  Qed.

  Theorem tolistd_join : forall (t : T (T A)),
      tolistd T (join T t) = join list (fmap list (shift list) (tolistd T (fmap T (tolistd T) t))).
  Proof.
    introv. unfold tolistd, compose.
    compose near t on left. rewrite (dmon_join W T).
    unfold compose. compose near (fmap T (shift T) (dec T (fmap T (dec T) t))) on left.
    rewrite (lmon_join T). unfold compose.
    compose near (dec T (fmap T (tolist T ○ dec T) t)) on right.
    change (tolist T ○ dec T) with (tolist T ∘ dec T (A:=A)).
    rewrite <- (fun_fmap_fmap T). unfold compose.
    compose near (fmap T (dec T) t) on right.
    rewrite <- (natural (ϕ := @dec W T _)). unfold compose.
    unfold_ops @Fmap_compose. fequal. compose near (dec T (fmap T (dec T) t)).
    rewrite (fun_fmap_fmap T).
    compose near (dec T (fmap T (dec T) t)).
    now rewrite tolistd_join1.
  Qed.

End ListableMonad_tolistd.
