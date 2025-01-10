From Tealeaves Require Export
  Functors.Early.Reader
  Classes.Categorical.Monad
  Classes.Categorical.RightModule.

Import Product.Notations.
Import Monad.Notations.
Import Strength.Notations.

(** * Decorated traversable functor instance *)
(******************************************************************************)
Section with_E.

  Context
    (E : Type).

End with_E.

(** * Properties of <<strength>> w.r.t. monad operations *)
(******************************************************************************)
Section Monad_strength_laws.

  Context
    (T : Type -> Type)
    `{Categorical.Monad.Monad T}
    (A B : Type).

  Lemma strength_ret :
    σ ∘ map (F := (A ×)) ret = ret (T := T) (A := A * B).
  Proof.
    intros. ext [a b]. cbn.
    unfold compose; cbn.
    compose near b on left.
    now rewrite (natural (G := T) (F := fun A => A)).
  Qed.

  Lemma strength_join :
      σ ∘ map (F := (A ×)) (μ (A := B)) =
      μ (A := A * B) ∘ map (F := T) (strength (F := T)) ∘ strength (F := T).
  Proof.
    intros. ext [a t].
    unfold compose at 1.
    change_left (σ (a, μ t)).
    unfold strength, compose at 1 4.
    compose near t.
    unfold_compose_in_compose.
    rewrite (natural (A := B) (B := A * B) (ϕ := @join T _)).
    unfold compose; cbn.
    compose near t.
    rewrite (fun_map_map (F := T)).
    reflexivity.
  Qed.

  Context
    (F : Type -> Type)
    `{Categorical.RightModule.RightModule F T}.

  Lemma strength_right_action :
      σ ∘ map (F := (A ×)) (right_action F) =
      right_action F (A := A * B) ∘ map σ ∘ σ.
  Proof.
    intros. ext [a t]. change_left (σ (a, right_action F t)).
    unfold strength, compose in *.
    unfold_ops @Map_I.
    inversion H8.
    compose near t on right.
    unfold_ops @Map_compose.
    rewrite (fun_map_map (F := F)).
    unfold compose. cbn.
    compose near t on left.
    compose near t on right.
    replace (fun '(a1, t0) => (a1, t0)) with (@id (A * B)).
    rewrite (fun_map_id).
    rewrite (natural (F := F ∘ T)).
    reflexivity.
    now ext [a' b'].
  Qed.

End Monad_strength_laws.
