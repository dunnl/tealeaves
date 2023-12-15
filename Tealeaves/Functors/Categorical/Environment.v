From Tealeaves Require Export
  Misc.Product
  Misc.Strength
  Classes.Comonoid
  Classes.Categorical.Comonad.

Import Product.Notations.
Import Strength.Notations.

(** * Environment comonad (a/k/a "Reader") *)
(******************************************************************************)

(** ** Categorical instance *)
(******************************************************************************)
Section with_E.

  Context
    (E : Type).

  #[export] Instance Map_prod : Map (E ×) := (fun A B => map_snd).

  #[program, export] Instance Functor_prod : Functor (E ×).

  Solve All Obligations with (introv; now ext [? ?]).

  Lemma dup_left_spec {A B} :
    @dup_left A B  = α ∘ map_fst comonoid_comult.
  Proof.
    now ext [? ?].
  Qed.

  #[export] Instance Cojoin_env : Cojoin (E ×) :=
    @dup_left E.

  #[export] Instance Extract_env : Extract (E ×) :=
    @snd E.

  #[export] Instance Natural_extract_env : Natural (@extract (E ×) _).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [? ?].
  Qed.

  #[export] Instance Natural_cojoin_env : Natural (@cojoin (E ×) _).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [? ?].
  Qed.

  #[export, program] Instance Comonad_env : Comonad (E ×).

  Solve All Obligations with (introv; now ext [? ?]).

End with_E.

(** * Miscellaneous properties *)
(******************************************************************************)
Section with_E.

  Context
    (E : Type)
    (F : Type -> Type).

  Theorem strength_extract `{Functor F} {A : Type} :
    map extract ∘ σ = extract (W := (E ×)) (A := F A).
  Proof.
    intros. unfold strength, compose. ext [w a].
    reflexivity.
  Qed.

  Theorem strength_cojoin `{Functor F} {A : Type} :
    `(map (F := F) (cojoin (W := (E ×)) (A := A)) ∘ σ =
        σ ∘ map (F := (E ×)) σ ∘ cojoin (W := (E ×))).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite 2(fun_map_map).
  Qed.

  Theorem product_map_commute {E1 E2 A B : Type} (g : E1 -> E2) (f : A -> B) :
    map (F := (E2 ×)) f ∘ map_fst g = map_fst g ∘ map (F := (E1 ×)) f.
  Proof.
    now ext [w a].
  Qed.

End with_E.

From Tealeaves Require Export
  Classes.Categorical.Monad
  Classes.Categorical.RightModule.

Import Monad.Notations.

(** * Properties of <<strength>> w.r.t. monad operations *)
(******************************************************************************)
Section Monad_strength_laws.

  Context
    (T : Type -> Type)
    `{Classes.Categorical.Monad.Monad T}
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
      σ ∘ map (F := (A ×)) (μ T (A := B)) =
      μ T (A := A * B) ∘ map (F := T) (strength (F := T)) ∘ strength (F := T).
  Proof.
    intros. ext [a t].
    unfold compose at 1.
    change_left (σ (a, μ T t)).
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
    `{RightModule F T}.

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
