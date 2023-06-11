From Tealeaves Require Import
  Classes.Functor
  Classes.Monoid
  Definitions.Strength.

#[local] Generalizable Variable W.

(** * The [shift] operation *)
(** The theory of decorated functors makes frequent use of an
    operation <<shift>> that uniformly increments each of the
    annotations of a <<W>>-annotated term (i.e., something of type
    <<F (W * A)>>) by some increment <<w : W>>. This operation is used to
    define concrete instances of [dec], specially to handle binders in
    sub-cases of the recursion.  A subcase of the form <<dec (λ b . t)>>
    is defined <<λ b . (shift ([b], dec t)>>. That is, <<shift>> is applied to
    a recursive subcall to <<dec>> on the _body_ of an abstraction to
    <<cons>> the current binder on the front of each binder context. *)

(* uncurry (incr W) = join (W ×) *)

(** * The <<shift>> operation *)
(******************************************************************************)
Definition shift F `{Map F} `{Monoid_op W} {A} : W * F (W * A) -> F (W * A) :=
  map F (uncurry (incr W)) ∘ strength F.

(** ** Basic properties of <<shift>> *)
(******************************************************************************)
Section shift_functor_lemmas.

  Context
    (F : Type -> Type)
    `{Monoid W}
    `{Functor F}.

  (** The definition of [shift] is convenient for theorizing, but [shift_spec]
      offers an intuitive characterization that is more convenient for
      practical reasoning. *)
  Corollary shift_spec {A} : forall (w : W) (x : F (W * A)),
      shift F (w, x) = map F (map_fst (fun m => w ● m)) x.
  Proof.
    intros ? x. unfold shift. unfold_ops @Join_writer.
    unfold compose; cbn. compose near x on left.
    rewrite (fun_map_map F). f_equal. now ext [? ?].
  Qed.

  (** If we think of <<shift>> as a function of two arguments,
      then it is natural in its second argument. *)
  Lemma shift_map1 {A B} (t : F (W * A)) (w : W) (f : A -> B) :
    shift F (w, map (F ∘ prod W) f t) = map (F ∘ prod W) f (shift F (w, t)).
  Proof.
    unfold_ops @Map_compose. rewrite (shift_spec).
    unfold compose; rewrite shift_spec.
    compose near t. rewrite 2(fun_map_map F).
    fequal. now ext [w' a].
  Qed.

  (** We can also say <<shift>> is a natural transformation
   of type <<(W ×) ∘ F ∘ (W ×) \to F ∘ (W ×)>>. *)
  Lemma shift_map2 {A B} : forall (f : A -> B),
      map (F ∘ prod W) f ∘ shift F =
      shift F ∘ map (prod W ∘ F ∘ prod W) f.
  Proof.
    intros. ext [w t]. unfold compose at 2.
    now rewrite <- shift_map1.
  Qed.

  Corollary shift_natural : Natural (@shift F _ W _).
  Proof.
    constructor; try typeclasses eauto.
    intros. apply shift_map2.
  Qed.

  (** We can increment the first argument before applying <<shift>>,
      or we can <<shift>> and then increment. This lemma is used
      e.g. in the binding case of the decorate-join law. *)
  Lemma shift_increment {A} : forall (w : W),
      shift F (A := A) ∘ map_fst (fun m : W => w ● m) =
      map F (map_fst (fun m : W => w ● m)) ∘ shift F.
  Proof.
    intros. ext [w' a]. unfold compose. cbn. rewrite 2(shift_spec).
    compose near a on right. rewrite (fun_map_map F).
    fequal. ext [w'' a']; cbn. now rewrite monoid_assoc.
  Qed.

  (** Applying <<shift>>, followed by discarding annotations at the
      leaves, is equivalent to simply discarding the original
      annotations and the argument to <<shift>>. *)
  Lemma shift_extract {A} :
    map F (extract (prod W)) ∘ shift F =
    map F (extract (prod W)) ∘ extract (prod W) (A := F (W * A)).
  Proof.
    unfold shift. reassociate <- on left.
    ext [w t]. unfold compose; cbn.
    do 2 compose near t on left.
    do 2 rewrite (fun_map_map F).
    fequal. now ext [w' a].
  Qed.

  Lemma shift_zero {A} : forall (t : F (W * A)),
    shift F (Ƶ, t) = t.
  Proof.
    intros. rewrite shift_spec.
    cut (map_fst (Y := A) (fun w => Ƶ ● w) = id).
    intros rw; rewrite rw. now rewrite (fun_map_id F).
    ext [w a]. cbn. now simpl_monoid.
  Qed.

End shift_functor_lemmas.
