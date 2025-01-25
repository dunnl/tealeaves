From Tealeaves Require Import
  Misc.Product
  Misc.Strength
  Classes.Comonoid
  Classes.Kleisli.Comonad
  Classes.Categorical.Comonad.

Export Misc.Product.
Export Misc.Strength.
Export Classes.Comonoid.

Import Product.Notations.

(** * Environment/Reader Comonad *)
(**********************************************************************)

(** ** Functor Instances *)
(**********************************************************************)
#[export] Instance Map_reader (E: Type):
  Map (E ×) := (fun A B => map_snd).

#[program, export] Instance Functor_reader (E: Type):
  Functor (E ×).

Solve All Obligations with (introv; now ext [? ?]).

(** ** Categorical Comonad Instance *)
(**********************************************************************)
Section with_E.

  Context
    (E: Type).

  #[export] Instance Cojoin_reader: Cojoin (E ×) :=
    @dup_left E.

  #[export] Instance Extract_reader: Extract (E ×) :=
    @snd E.

  #[export] Instance Natural_extract_reader: Natural (@extract (E ×) _).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [? ?].
  Qed.

  #[export] Instance Natural_cojoin_reader: Natural (@cojoin (E ×) _).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [? ?].
  Qed.

  #[export, program] Instance Comonad_reader: Comonad (E ×).

  Solve All Obligations with (introv; now ext [? ?]).

End with_E.

(** ** Kleisli Comonad Instance *)
(**********************************************************************)
Section with_E.

  Context
    (E: Type).

  (*
    #[export] Instance Extract_reader: Extract (E ×) :=
    fun A '(e, a) => a.
   *)

  #[export] Instance Cobind_reader: Cobind (E ×) :=
    fun A B (f: E * A -> B) '(e, a) => (e, f (e, a)).

  #[export, program] Instance KleisliComonad_reader:
    Kleisli.Comonad.Comonad (E ×).

  Solve All Obligations with (introv; now ext [? ?]).

  (*
    #[export] Instance Map_reader: Map (E ×) :=
    Comonad.Map_Cobind (E ×).

    #[export] Instance Functor_reader: Functor (E ×) :=
    Comonad.Functor_Comonad (E ×).
   *)

  #[export] Instance Map_Cobind_Compat_Reader: Compat_Map_Cobind (E ×).
  Proof.
    reflexivity.
  Qed.

End with_E.

(** * Properties of <<strength>>  *)
(**********************************************************************)
From Tealeaves Require Import
  Classes.Categorical.Monad
  Classes.Categorical.RightModule.

(** ** Interaction with Categorical Monad Operations *)
(**********************************************************************)
Section Monad_strength_laws.

  Context
    (T : Type -> Type)
    `{Categorical.Monad.Monad T}
    (A B : Type).

  Import Strength.Notations.
  Import Monad.Notations.

  Lemma strength_ret:
    σ ∘ map (F := (A ×)) ret = ret (T := T) (A := A * B).
  Proof.
    intros. ext [a b]. cbn.
    unfold compose; cbn.
    compose near b on left.
    now rewrite (natural (G := T) (F := fun A => A)).
  Qed.

  Lemma strength_join:
    σ ∘ map (F := (A ×)) (μ (A := B)) =
      μ (A := A * B) ∘
        map (F := T) (strength (F := T)) ∘
        strength (F := T).
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

  Lemma strength_right_action:
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


(** ** Interaction with Reader Comonad Operations *)
(**********************************************************************)
Section Comonad_strength_laws.

  Context
    (E: Type)
    (F: Type -> Type).

  Theorem strength_extract `{Functor F} {A: Type}:
    map extract ∘ strength = extract (W := (E ×)) (A := F A).
  Proof.
    intros. unfold strength, compose. ext [w a].
    reflexivity.
  Qed.

  Theorem strength_cojoin `{Functor F} {A: Type}:
    `(map (F := F) (cojoin (W := (E ×)) (A := A)) ∘ strength =
        strength ∘ map (F := (E ×)) strength ∘ cojoin (W := (E ×))).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite 2(fun_map_map).
  Qed.

  Lemma map_strength_cobind_spec {G} `{Functor G}:
    forall (A B C: Type) (f: E * A -> G B) (g: E * B -> C),
      map g ∘ strength ∘ cobind (W := (E ×)) f =
        (fun '(e, a) => map (g ∘ pair e) (f (e, a))).
  Proof.
    intros. ext [w a].
    unfold strength, compose; cbn.
    compose near (f (w, a)) on left.
    rewrite fun_map_map.
    reflexivity.
  Qed.

End Comonad_strength_laws.

(** ** Miscellaneous Properties *)
(**********************************************************************)
Section with_E.

  Context
    (E: Type)
    (F: Type -> Type).

  #[export] Instance Natural_strength
    `{Functor F}: Natural (F := prod E ∘ F) (@strength F _ E).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Map_compose. ext [a t].
    unfold compose; cbn.
    compose near t on left.
    compose near t on right.
    now rewrite 2(fun_map_map).
  Qed.

  Theorem product_map_commute {E1 E2 A B: Type} (g: E1 -> E2) (f: A -> B):
    map (F := (E2 ×)) f ∘ map_fst g = map_fst g ∘ map (F := (E1 ×)) f.
  Proof.
    now ext [w a].
  Qed.

  Lemma dup_left_spec {A B}:
    @dup_left A B  = α ∘ map_fst comonoid_comult.
  Proof.
    now ext [? ?].
  Qed.


End with_E.
