From Tealeaves Require Export
  Classes.Categorical.Comonad
  Functors.Early.Writer.

Import Monoid.Notations.
Import Product.Notations.
Import Functor.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W T F E A.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments extract (W)%function_scope {Extract} (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin} {A}%type_scope _.

(** * The [shift] operation *)
(* uncurry (incr W) = join (W ×) *)
(******************************************************************************)
Definition shift (F: Type -> Type) `{Map F} `{Monoid_op W} {A} :
  W * F (W * A) -> F (W * A) := map F (uncurry incr) ∘ strength.

(** ** Basic properties of <<shift>> *)
(******************************************************************************)
Section shift_functor_lemmas.

  Context
    (F: Type -> Type)
    `{Monoid W}
    `{Functor F}.

  (** The definition of [shift] is convenient for theorizing, but [shift_spec]
      offers an intuitive characterization that is more convenient for
      practical reasoning. *)
  Corollary shift_spec {A}: forall (w: W) (x: F (W * A)),
      shift F (w, x) = map F (map_fst (fun m => w ● m)) x.
  Proof.
    intros ? x. unfold shift. unfold_ops @Join_writer.
    unfold compose; cbn. compose near x on left.
    rewrite fun_map_map.
    reflexivity.
  Qed.

  Corollary shift_spec2 {A: Type} :
    shift F (A := A) = map F (join (T := (W ×))) ∘ strength.
  Proof.
    intros.
    unfold shift.
    rewrite incr_spec.
    reflexivity.
  Qed.

  (** If we think of <<shift>> as a function of two arguments,
      then it is natural in its second argument. *)
  Lemma shift_map1 {A B} (t: F (W * A)) (w: W) (f: A -> B):
    shift F (w, map (F ∘ prod W) f t)
    = map (F ∘ prod W) f (shift F (w, t)).
  Proof.
    unfold_ops @Map_compose.
    rewrite shift_spec.
    unfold compose.
    rewrite shift_spec.
    compose near t.
    rewrite 2(fun_map_map).
    unfold_ops @Map_reader.
    rewrite product_map_slide_pf.
    reflexivity.
  Qed.

  (** We can also say <<shift>> is a natural transformation
   of type <<(W ×) ∘ F ∘ (W ×) \to F ∘ (W ×)>>. *)
  Lemma shift_map2 {A B}: forall (f: A -> B),
      map (F ∘ prod W) f ∘ shift F =
      shift F ∘ map (prod W ∘ F ∘ prod W) f.
  Proof.
    intros. ext [w t]. unfold compose at 2.
    now rewrite <- shift_map1.
  Qed.

  Corollary shift_natural: Natural (@shift F _ W _).
  Proof.
    constructor; try typeclasses eauto.
    intros. apply shift_map2.
  Qed.

  (** We can increment the first argument before applying <<shift>>,
      or we can <<shift>> and then increment. This lemma is used
      e.g. in the binding case of the decorate-join law. *)
  Lemma shift_increment {A}: forall (w: W),
      shift F (A := A) ∘ map_fst (fun m: W => w ● m) =
      map F (map_fst (fun m: W => w ● m)) ∘ shift F.
  Proof.
    intros. ext [w' a]. unfold compose. cbn. rewrite 2(shift_spec).
    compose near a on right. rewrite fun_map_map.
    fequal. ext [w'' a']; cbn. now rewrite monoid_assoc.
  Qed.

  (** Applying <<shift>>, followed by discarding annotations at the
      leaves, is equivalent to simply discarding the original
      annotations and the argument to <<shift>>. *)
  Lemma shift_extract {A} :
    map F (extract (prod W) A) ∘ shift F =
    map F (extract (prod W) A) ∘ extract (prod W) (F (W * A)).
  Proof.
    unfold shift. reassociate <- on left.
    ext [w t]. unfold compose; cbn.
    do 2 compose near t on left.
    do 2 rewrite fun_map_map.
    fequal. now ext [w' a].
  Qed.

  Lemma shift_zero {A}: forall (t: F (W * A)),
    shift F (Ƶ, t) = t.
  Proof.
    intros. rewrite shift_spec.
    cut (map_fst (Y := A) (fun w => Ƶ ● w) = id).
    intros rw; rewrite rw. now rewrite fun_map_id.
    ext [w a]. cbn. now simpl_monoid.
  Qed.

End shift_functor_lemmas.

(** * Decorated functors *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Class Decorate
  (E: Type)
  (F: Type -> Type) :=
  dec: F ⇒ F ○ (E ×).

#[global] Arguments dec {E}%type_scope _%function_scope {Decorate} {A}%type_scope _.
#[local] Arguments dec {E}%type_scope _%function_scope {Decorate} (A)%type_scope _.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedFunctor
  (E: Type)
  (F: Type -> Type)
  `{Map F}
  `{Decorate E F} :=
  { dfun_functor :> Functor F;
    dfun_dec_natural :> Natural (@dec E F _);
    dfun_dec_dec: forall (A: Type),
      dec F (E * A) ∘ dec F A = map F (cojoin (prod E)) ∘ dec F A;
    dfun_dec_extract: forall (A: Type),
      map F (extract (E ×) A) ∘ dec F A = @id (F A);
  }.

(** ** Decoration-preserving natural transformations *)
(******************************************************************************)
Class DecoratePreservingTransformation
  (F G: Type -> Type)
  `{! Map F} `{Decorate E F}
  `{! Map G} `{Decorate E G}
  (ϕ: F ⇒ G) :=
  { dectrans_commute: `(ϕ (E * A) ∘ dec F A = dec G A ∘ ϕ A);
    dectrans_natural: Natural ϕ;
  }.

From Tealeaves Require Import
  Classes.Categorical.RightComodule.

(** * Helper lemmas for proving typeclass instances *)
(** Each of the following lemmas is useful for proving one of the laws
    of decorated functors in the binder case(s) of proofs that proceed
    by induction on terms. *)
(******************************************************************************)
Section helper_lemmas.

  Context
    `{Functor F}
    `{Decorate W F}
    `{Monoid W}.

  (** This lemmasis useful for proving naturality of <<dec>>. *)
  Lemma dec_helper_1 {A B}: forall (f: A -> B) (t: F A) (w: W),
      map F (map (prod W) f) (dec F A t) =
        dec F B (map F f t) ->
      map F (map (prod W) f) (shift F (w, dec F A t)) =
        shift F (w, dec F B (map F f t)).
  Proof.
    introv IH. (* there is a hidden compose to unfold *)
    unfold compose; rewrite 2(shift_spec F).
    compose near (dec F A t) on left. rewrite (fun_map_map).
    rewrite <- IH.
    compose near (dec F A t) on right. rewrite (fun_map_map).
    fequal. now ext [w' a].
  Qed.

  (** Now we can assume that <<dec>> is a natural transformation,
      which is needed for the following. *)
  Context
    `{! Natural (@dec W F _)}.

  (** This lemmas is useful for proving the dec-extract law. *)
  Lemma dec_helper_2 {A}: forall (t: F A) (w: W),
      map F (extract (prod W) A) (dec F A t) = t ->
      map F (extract (prod W) A) (shift F (w, dec F A t)) = t.
  Proof.
    intros.
    compose near (w, dec F A t).
    rewrite (shift_extract F). unfold compose; cbn.
    auto.
  Qed.

  (** This lemmas is useful for proving the double decoration law. *)
  Lemma dec_helper_3 {A}: forall (t: F A) (w: W),
      dec F (W * A) (dec F A t) = map F (cojoin (prod W)) (dec F A t) ->
      shift F (w, dec F (W * A) (shift F (w, dec F A t))) =
        map F (cojoin (prod W)) (shift F (w, dec F A t)).
  Proof.
    introv IH. unfold compose. rewrite 2(shift_spec F).
    compose near (dec F A t).
    rewrite <- (natural (F := F) (G := F ○ prod W)).
    unfold compose. compose near (dec F (W * A) (dec F A t)).
    rewrite IH. unfold_ops @Map_compose.
    rewrite (fun_map_map).
    compose near (dec F A t).
    rewrite (fun_map_map).
    rewrite (fun_map_map).
    unfold compose. fequal.
    now ext [w' a].
  Qed.

End helper_lemmas.

(** * Decorated functor instance for [Reader] *)
(******************************************************************************)
Section DecoratedFunctor_reader.

  Context
    (E: Type).

  #[global] Instance Decorate_prod: Decorate E (prod E) := @cojoin (prod E) _.

  #[global, program] Instance DecoratedFunctor_prod: DecoratedFunctor E (prod E).

  Solve Obligations with (intros; now ext [? ?]).

End DecoratedFunctor_reader.
