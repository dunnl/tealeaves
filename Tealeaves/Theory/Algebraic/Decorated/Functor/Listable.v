From Tealeaves Require Export
  Classes.Algebraic.Decorated.Functor
  Classes.Algebraic.Listable.Functor.

#[local] Generalizable Variables W F A.

(** * Decorated listable functors *)
(******************************************************************************)

(** ** Derived operation [tolistd] *)
(******************************************************************************)
Definition tolistd F `{Decorate W F} `{Tolist F} {A} : F A -> list (W * A)
  := tolist F ∘ dec F.

(*
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
