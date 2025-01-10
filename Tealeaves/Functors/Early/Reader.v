From Tealeaves Require Export
  Misc.Product
  Misc.Strength
  Classes.Comonoid
  Classes.Kleisli.Comonad
  Classes.Categorical.Comonad.

Import Product.Notations.

(** * Environment/Reader comonad *)
(******************************************************************************)

(** ** Categorical instance *)
(******************************************************************************)
Section with_E.

  Context
    (E: Type).

  #[export] Instance Map_reader: Map (E ×) := (fun A B => map_snd).

  #[program, export] Instance Functor_reader: Functor (E ×).

  Solve All Obligations with (introv; now ext [? ?]).

  Lemma dup_left_spec {A B} :
    @dup_left A B  = α ∘ map_fst comonoid_comult.
  Proof.
    now ext [? ?].
  Qed.

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

(** *** Miscellaneous properties *)
(******************************************************************************)
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

  Theorem strength_extract `{Functor F} {A: Type} :
    map extract ∘ strength = extract (W := (E ×)) (A := F A).
  Proof.
    intros. unfold strength, compose. ext [w a].
    reflexivity.
  Qed.

  Theorem strength_cojoin `{Functor F} {A: Type} :
    `(map (F := F) (cojoin (W := (E ×)) (A := A)) ∘ strength =
        strength ∘ map (F := (E ×)) strength ∘ cojoin (W := (E ×))).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite 2(fun_map_map).
  Qed.

  Theorem product_map_commute {E1 E2 A B: Type} (g: E1 -> E2) (f: A -> B) :
    map (F := (E2 ×)) f ∘ map_fst g = map_fst g ∘ map (F := (E1 ×)) f.
  Proof.
    now ext [w a].
  Qed.

End with_E.

(** ** Kleisli instance *)
(******************************************************************************)
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

  Lemma map_to_cobind_reader: forall A B (f: A -> B),
      map f = cobind (f ∘ extract).
  Proof.
    reflexivity.
  Qed.

  (** *** Miscellaneous properties *)
  (******************************************************************************)
  Lemma map_strength_cobind_spec {G} `{Functor G}:
    forall (A B C: Type) (f: E * A -> G B) (g: E * B -> C),
      map g ∘ strength ∘ cobind (W := (E ×)) f =
        (fun '(w, a) => map (g ∘ pair w) (f (w, a))).
  Proof.
    intros. ext [w a].
    unfold strength, compose; cbn.
    compose near (f (w, a)) on left.
    rewrite fun_map_map.
    reflexivity.
  Qed.

End with_E.
