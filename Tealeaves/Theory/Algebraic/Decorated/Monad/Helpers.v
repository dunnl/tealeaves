From Tealeaves Require Export
  Theory.Algebraic.Decorated.Shift
  Classes.Algebraic.Decorated.Functor
  Classes.Algebraic.Decorated.Monad
  Classes.Monoid.

#[local] Generalizable Variables W T.

Section helper_lemmas.

  Context
    `{Monad T}
    `{Decorate W T}
    `{Monoid W}.

  (** This lemmas is useful for proving the decoration-join law. *)
  Lemma dec_helper_4 {A} : forall (t : T (T A)) (w : W),
      dec T (join T t) =
        join T (fmap T (shift T) (dec T (fmap T (dec T) t))) ->
      shift T (w, dec T (join T t)) =
        join T (fmap T (shift T) (shift T (w, dec T (fmap T (dec T) t)))).
  Proof.
    introv IH. rewrite !(shift_spec T) in *. rewrite IH.
    compose near (dec T (fmap T (dec T) t)) on right.
    rewrite (fun_fmap_fmap T). rewrite (shift_increment T).
    rewrite <- (fun_fmap_fmap T).
    change (fmap T (fmap T ?f)) with (fmap (T ∘ T) f).
    compose near (dec T (fmap T (dec T) t)).
    reassociate <-.
    #[local] Set Keyed Unification.
    now rewrite <- (natural (ϕ := @join T _)).
    #[local] Unset Keyed Unification.
  Qed.

End helper_lemmas.
