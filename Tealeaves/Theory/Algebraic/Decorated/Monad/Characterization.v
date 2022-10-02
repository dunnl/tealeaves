From Tealeaves Require Import
  Classes.Algebraic.Decorated.Monad
  Theory.Algebraic.Decorated.Functor.Category.

Import Functor.Notations.
Import Monoid.Notations.

#[local] Generalizable Variable W T A.

(** * Decorated monads in terms of monad homomorphisms *)
(******************************************************************************)
Section DecoratedMonad_characterization.

  Context
    `{Monad T} `{Decorate W T} `{Monoid W}
    `{! DecoratedFunctor W T}.

  (** <<ret T>> commutes with decoration if and only if <<dec T>> maps
     <<ret T>> to <<ret (T ∘ W)>> *)
  Lemma dec_ret_iff {A} :
    (dec T ∘ ret T = ret T ∘ dec (fun x => x) (A:=A)) <->
    (dec T ∘ ret T = ret (T ∘ prod W) (A:=A)).
  Proof with auto.
    split...
  Qed.

  (** <<join T>> commutes with decoration if and only if <<dec T>>
     maps <<join T>> to <<join (T ∘ prod W)>> of <<dec T ∘ fmap T (dec T)>>
     (in other words iff <<dec T>> commutes with <<join>>). *)
  Lemma dec_join_iff {A} :
    `(dec T ∘ join T = join T ∘ dec (T ∘ T) (A := A)) <->
    `(dec T ∘ join T = join (T ∘ prod W) ∘ dec T ∘ fmap T (dec T (A:=A))).
  Proof.
    enough (Heq : join T ∘ dec (A := A) (T ∘ T)
                  = join (T ∘ prod W) ∘ dec T ∘ fmap T (dec T))
      by (split; intro hyp; now rewrite hyp).
    unfold_ops @Join_Beck @Decorate_compose @BeckDistribution_strength.
    repeat reassociate <-. fequal. fequal.
    rewrite (natural (ϕ := @join T _)).
    unfold_ops @Fmap_compose. reassociate -> on right.
    now unfold_compose_in_compose; rewrite (fun_fmap_fmap T).
  Qed.

  Theorem decorated_monad_compatibility_spec :
    Monad_Hom T (T ∘ prod W) (@dec W T _) <->
    DecoratePreservingTransformation (@ret T _) /\
    DecoratePreservingTransformation (@join T _).
  Proof with auto.
    split.
    - introv mhom. inverts mhom. inverts mhom_domain. split.
      + constructor...
        introv. symmetry. rewrite dec_ret_iff. apply mhom_ret.
      + constructor...
        introv. symmetry. rewrite dec_join_iff. apply mhom_join.
    - intros [h1 h2]. inverts h1. inverts h2.
      constructor; try typeclasses eauto.
      + introv. rewrite <- dec_ret_iff...
      + introv. rewrite <- dec_join_iff...
  Qed.

  Theorem decorated_monad_spec :
    DecoratedMonad W T <-> Monad_Hom T (T ∘ prod W) (@dec W T _).
  Proof with try typeclasses eauto.
    rewrite decorated_monad_compatibility_spec.
    split; intro hyp.
    - inversion hyp. constructor...
      + constructor... intros. now rewrite dmon_ret.
      + constructor... intros. now rewrite dmon_join.
    - destruct hyp as [hyp1 hyp2]. constructor...
      + intros. inversion hyp1. now rewrite dectrans_commute.
      + intros. inversion hyp2. now rewrite <- dectrans_commute.
  Qed.

End DecoratedMonad_characterization.
