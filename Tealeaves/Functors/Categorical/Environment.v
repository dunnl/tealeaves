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
    map F (extract (E ×) A) ∘ σ F = extract (E ×) (F A).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite (fun_map_map), (fun_map_id).
  Qed.

  Theorem strength_cojoin `{Functor F} {A : Type} :
    `(map F (cojoin (E ×) (A := A)) ∘ σ F = σ F ∘ map (E ×) (σ F) ∘ cojoin (E ×)).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite 2(fun_map_map).
  Qed.

  Theorem product_map_commute {E1 E2 A B : Type} (g : E1 -> E2) (f : A -> B) :
    map (E2 ×) f ∘ map_fst g = map_fst g ∘ map (E1 ×) f.
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
    σ T ∘ map (A ×) (ret T B) = ret T (A * B).
  Proof.
    intros. ext [a b]. cbn.
    unfold compose; cbn.
    compose near b on left.
    now rewrite (natural (G := T) (F := fun A => A)).
  Qed.

  Lemma strength_join :
      σ T ∘ map (A ×) (μ T (A := B)) =
      μ T (A := A * B) ∘ map T (σ T) ∘ σ T.
  Proof.
    intros. ext [a t]. unfold compose; cbn.
    change_left (σ T (a, μ T t)).
    unfold strength, compose.
    compose near t on right.
    rewrite (fun_map_map).
    unfold compose. change_right (μ T (map (T ∘ T) (pair a) t)).
    compose near t on right. now rewrite <- (natural (F := T ∘ T)).
  Qed.

  Context
    (F : Type -> Type)
    `{RightModule F T}.

  Lemma strength_right_action :
      σ F ∘ map (A ×) (right_action F) =
      right_action F (A := A * B) ∘ map F (σ T) ∘ σ F.
  Proof.
    intros. ext [a t]. change_left (σ F (a, right_action F t)).
    unfold strength, compose in *.
    compose near t on right.
    inversion H8.
    rewrite (fun_map_map (F := F)).
    unfold compose. change_right (right_action F (map (F ∘ T) (pair a) t)).
    compose near t on right. now rewrite <- (natural (F := F ∘ T)).
  Qed.

End Monad_strength_laws.
