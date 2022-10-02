From Tealeaves Require Import
  Theory.Algebraic.Decorated.Functor.Listable
  Classes.Algebraic.Listable.Monad
  Classes.Algebraic.Decorated.Monad.

#[local] Generalizable Variables W.

Import Monoid.Notations.
Import List.ListNotations.
#[local] Open Scope list_scope.

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
