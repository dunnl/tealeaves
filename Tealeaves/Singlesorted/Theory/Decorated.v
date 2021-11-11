From Tealeaves Require Import
     Singlesorted.Classes.DecoratedModule
     Singlesorted.Classes.RightComodule
     Singlesorted.Classes.BeckDistributiveLaw.

Import Functor.Notations.
Import Monoid.Notations.
#[local] Open Scope tealeaves_scope.

(** * A decorated functor is precisely a right comodule of <<prod W>> *)
(******************************************************************************)
Section RightComodule_DecoratedFunctor.

  Context `{DecoratedFunctor W F}.

  Definition RightComodule_DecoratedFunctor : RightComodule F (prod W) :=
  {| rcom_coaction_coaction := dfun_dec_dec W F;
     rcom_fmap_extr_coaction := dfun_dec_extract W F;
  |}.

End RightComodule_DecoratedFunctor.

Section DecoratedFunctor_RightComodule.

  (** This context is declared so that <<RightComodule>> uses the
  reader/writer comonad rather than an opaque one. *)
  Context
    `{Fmap F} `{RightCoaction F (prod W)}
    `{! RightComodule F (prod W)} `{Monoid W}.

  Definition DecoratedFunctor_RightComodule : DecoratedFunctor W F :=
  {| dfun_dec_dec := rcom_coaction_coaction F (prod W);
     dfun_dec_extract := rcom_fmap_extr_coaction F (prod W);
  |}.

End DecoratedFunctor_RightComodule.

(** * Decorated monads in terms of homomorphisms *)
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

(** * Pushing decorations through a monoid homomorphism *)
(** If a functor is readable by a monoid, it is readable by any target
    of a homomorphism from that monoid too. *)
(******************************************************************************)
Section DecoratedFunctor_monoid_homomorphism.

  Context
    `{Monoid_Morphism Wsrc Wtgt ϕ}
    `{DecoratedFunctor Wsrc F}.

  Instance Decorate_homomorphism :
    Decorate Wtgt F := fun A => fmap F (map_fst ϕ) ∘ dec F.

  Lemma Natural_read_morphism : Natural (@dec Wtgt F _).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Decorate_homomorphism.
      unfold_ops @Fmap_compose.
      reassociate <- on left.
      rewrite (fun_fmap_fmap F).
      rewrite (reader1).
      rewrite <- (fun_fmap_fmap F).
      reassociate -> on left.
      change (fmap F (fmap (prod Wsrc) f)) with
          (fmap (F ∘ prod Wsrc) f).
      now rewrite (natural (ϕ := @dec Wsrc F _ )).
  Qed.

End DecoratedFunctor_monoid_homomorphism.
