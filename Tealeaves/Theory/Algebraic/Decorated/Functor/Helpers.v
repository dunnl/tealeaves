From Tealeaves Require Export
  Classes.Algebraic.Decorated.Monad
  Theory.Algebraic.Decorated.Shift
  Classes.Monoid.

#[local] Generalizable Variables F W.

(** * Helper lemmas for implementing typeclass instances *)
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
  Lemma dec_helper_1 {A B} : forall (f : A -> B) (t : F A) (w : W),
      fmap F (fmap (prod W) f) (dec F t) =
        dec F (fmap F f t) ->
      fmap F (fmap (prod W) f) (shift F (w, dec F t)) =
        shift F (w, dec F (fmap F f t)).
  Proof.
    introv IH. (* there is a hidden compose to unfold *)
    unfold compose; rewrite 2(shift_spec F).
    compose near (dec F t) on left. rewrite (fun_fmap_fmap F).
    rewrite <- IH.
    compose near (dec F t) on right. rewrite (fun_fmap_fmap F).
    fequal. now ext [w' a].
  Qed.

  (** Now we can assume that <<dec>> is a natural transformation,
      which is needed for the following. *)
  Context
    `{! Natural (@dec W F _)}.

  (** This lemmas is useful for proving the dec-extract law. *)
  Lemma dec_helper_2 {A} : forall (t : F A) (w : W),
      fmap F (extract (prod W)) (dec F t) = t ->
      fmap F (extract (prod W)) (shift F (w, dec F t)) = t.
  Proof.
    intros.
    compose near (w, dec F t).
    rewrite (shift_extract F). unfold compose; cbn.
    auto.
  Qed.

  (** This lemmas is useful for proving the double decoration law. *)
  Lemma dec_helper_3 {A} : forall (t : F A) (w : W),
      dec F (dec F t) = fmap F (cojoin (prod W)) (dec F t) ->
      shift F (w, dec F (shift F (w, dec F t))) =
        fmap F (cojoin (prod W)) (shift F (w, dec F t)).
  Proof.
    introv IH. unfold compose. rewrite 2(shift_spec F).
    compose near (dec F t).
    rewrite <- (natural (F := F) (G := F ○ prod W)).
    unfold compose. compose near (dec F (dec F t)).
    rewrite IH. unfold_ops @Fmap_compose.
    rewrite (fun_fmap_fmap F).
    compose near (dec F t).
    rewrite (fun_fmap_fmap F).
    rewrite (fun_fmap_fmap F).
    unfold compose. fequal.
    now ext [w' a].
  Qed.

End helper_lemmas.
