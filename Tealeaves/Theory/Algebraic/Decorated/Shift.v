From Tealeaves Require Export
  Functors.Writer
  Classes.Algebraic.Decorated.Monad
  Theory.Algebraic.Monad.Properties.

Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables T F W A.

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
(******************************************************************************)

(*
(** We define a convenience function for operations of a certain form.  *)
Definition map_then_shift `{Monoid_op W} T `{Fmap T} `{Decorate W T} {A B}
           (f : A -> T B) : W * A -> T (W * B) :=
  shift T ∘ fmap (prod W) (dec T ∘ f).
*)

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
      shift F (w, x) = fmap F (map_fst (fun m => w ● m)) x.
  Proof.
    intros ? x. unfold shift. unfold_ops @Join_writer.
    unfold compose; cbn. compose near x on left.
    rewrite (fun_fmap_fmap F). f_equal. now ext [? ?].
  Qed.

  (** If we think of <<shift>> as a function of two arguments,
      then it is natural in its second argument. *)
  Lemma shift_fmap1 {A B} (t : F (W * A)) (w : W) (f : A -> B) :
    shift F (w, fmap (F ∘ prod W) f t) = fmap (F ∘ prod W) f (shift F (w, t)).
  Proof.
    unfold_ops @Fmap_compose. rewrite (shift_spec).
    unfold compose; rewrite shift_spec.
    compose near t. rewrite 2(fun_fmap_fmap F).
    fequal. now ext [w' a].
  Qed.

  (** We can also say <<shift>> is a natural transformation
   of type <<(W ×) ∘ F ∘ (W ×) \to F ∘ (W ×)>>. *)
  Lemma shift_fmap2 {A B} : forall (f : A -> B),
      fmap (F ∘ prod W) f ∘ shift F =
      shift F ∘ fmap (prod W ∘ F ∘ prod W) f.
  Proof.
    intros. ext [w t]. unfold compose at 2.
    now rewrite <- shift_fmap1.
  Qed.

  Corollary shift_natural : Natural (@shift F _ W _).
  Proof.
    constructor; try typeclasses eauto.
    intros. apply shift_fmap2.
  Qed.

  (** We can increment the first argument before applying <<shift>>,
      or we can <<shift>> and then increment. This lemma is used
      e.g. in the binding case of the decorate-join law. *)
  Lemma shift_increment {A} : forall (w : W),
      shift F (A := A) ∘ map_fst (fun m : W => w ● m) =
      fmap F (map_fst (fun m : W => w ● m)) ∘ shift F.
  Proof.
    intros. ext [w' a]. unfold compose. cbn. rewrite 2(shift_spec).
    compose near a on right. rewrite (fun_fmap_fmap F).
    fequal. ext [w'' a']; cbn. now rewrite monoid_assoc.
  Qed.

  (** Applying <<shift>>, followed by discarding annotations at the
      leaves, is equivalent to simply discarding the original
      annotations and the argument to <<shift>>. *)
  Lemma shift_extract {A} :
    fmap F (extract (prod W)) ∘ shift F =
    fmap F (extract (prod W)) ∘ extract (prod W) (A := F (W * A)).
  Proof.
    unfold shift. reassociate <- on left.
    ext [w t]. unfold compose; cbn.
    do 2 compose near t on left.
    do 2 rewrite (fun_fmap_fmap F).
    fequal. now ext [w' a].
  Qed.

  Lemma shift_zero {A} : forall (t : F (W * A)),
    shift F (Ƶ, t) = t.
  Proof.
    intros. rewrite shift_spec.
    cut (map_fst (Y := A) (fun w => Ƶ ● w) = id).
    intros rw; rewrite rw. now rewrite (fun_fmap_id F).
    ext [w a]. cbn. now simpl_monoid.
  Qed.

End shift_functor_lemmas.

(** * Basic properties of [shift] on monads *)
(******************************************************************************)
Section shift_monad_lemmas.

  Context
    `{Monad T}
    `{Monoid W}.

  (** [shift] applied to a singleton simplifies to a singleton. *)
  Lemma shift_return `(a : A) (w1 w2 : W) :
    shift T (w2, ret T (w1, a)) = ret T (w2 ● w1, a).
  Proof.
    unfold shift, compose. rewrite strength_return.
    compose near (w2, (w1, a)) on left.
    now rewrite (natural (F := fun A => A)).
  Qed.

  Lemma shift_join `(t : T (T (W * A))) (w : W) :
    shift T (w, join T t) = join T (fmap T (fun t => shift T (w, t)) t).
  Proof.
    rewrite (shift_spec T). compose near t on left.
    rewrite natural. unfold compose; cbn.
    fequal. unfold_ops @Fmap_compose.
    fequal. ext x. now rewrite (shift_spec T).
  Qed.

  (*
  Lemma shift_bind `(t : T (W * A)) (w : W) `(f : W * A -> T (W * B)) :
    shift T (w, bind T f t) = bind T (fun p => shift T (w, f p)) t.
  Proof.
    unfold_ops @Bind_Join. unfold compose.
    rewrite shift_join. fequal.
    compose near t on left.
    now rewrite (fun_fmap_fmap T).
  Qed.
  *)

End shift_monad_lemmas.
