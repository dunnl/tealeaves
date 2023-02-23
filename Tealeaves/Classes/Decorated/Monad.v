(** This file implements "monads decorated by monoid <<W>>." *)
From Tealeaves Require Export
  Classes.Monoid
  Classes.Decorated.Functor
  Classes.Monad
  Functors.Writer.

Import Monoid.Notations.

#[local] Generalizable Variable W.

(** * Decorated monads *)
(******************************************************************************)
Section DecoratedMonad.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedMonad:=
    { dmon_functor :> DecoratedFunctor W T;
      dmon_monad :> Monad T;
      dmon_monoid :> Monoid W;
      dmon_ret : forall (A : Type),
        dec T ∘ ret T = ret T ∘ pair Ƶ (B:=A);
      dmon_join : forall (A : Type),
        dec T ∘ join T (A:=A) =
          join T ∘ fmap T (shift T) ∘ dec T ∘ fmap T (dec T);
    }.

End DecoratedMonad.

(** * Decorated right modules *)
(******************************************************************************)
Section DecoratedModule.

  Context
    (W : Type)
    (F T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T} `{Decorate W T}
    `{Fmap F} `{RightAction F T} `{Decorate W F}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedRightModule :=
    { dmod_monad :> DecoratedMonad W T;
      dmod_functor :> DecoratedFunctor W T;
      dmon_module :> RightModule F T;
      dmod_action : forall (A : Type),
        dec F ∘ right_action F (A := A) =
          right_action F ∘ fmap F (shift T) ∘ dec F ∘ fmap F (dec T);
    }.

End DecoratedModule.

(** * Algebraic decorated monad to Kleisli decorated monad *)
(******************************************************************************)

From Tealeaves Require Classes.Kleisli.Decorated.Monad.

(** ** Kleisli laws *)
(******************************************************************************)
Module ToKleisli.
  
  #[local] Generalizable Variables A B C.
  
  Import Classes.Kleisli.Decorated.Monad.
  Import Classes.Kleisli.Decorated.Monad.Notations.
  
  Section operation.
    
    Context
      (W : Type)
      (T : Type -> Type)
      `{Fmap T} `{Join T} `{Decorate W T}.

    #[export] Instance Bindd_dec : Bindd W T T :=
      fun A B f => join T ∘ fmap T f ∘ dec T.

  End operation.
  
  Section with_monad.

    Context
      (T : Type -> Type)
      `{DecoratedMonad W T}.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma bindd_id :
      `(bindd T (ret T ∘ extract (prod W)) = @id (T A)).
    Proof.
      intros. unfold_ops @Bindd_dec.
      rewrite <- (fun_fmap_fmap T).
      reassociate <-.
      rewrite (mon_join_fmap_ret T).
      reassociate ->.
      rewrite (dfun_dec_extract W T).
      reflexivity.
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma bindd_bindd : forall `(g : W * B -> T C) `(f : W * A -> T B),
        bindd T g ∘ bindd T f = bindd T (g ⋆dm f).
    Proof.
      intros. unfold bindd at 1 2, Bindd_dec.
      (* change (join T ∘ fmap T ?f) with (bind T f).*)
      do 2 reassociate <-.
      reassociate -> near (join T). rewrite (dmon_join W T).
      repeat reassociate <-.
      reassociate -> near (fmap T f).
      rewrite (fun_fmap_fmap T).
      change (?g ∘ dec T ∘ fmap T (dec T ∘ f) ∘ dec T)
        with (g ∘ (dec T ∘ fmap T (dec T ∘ f) ∘ dec T)).
      rewrite <- (cobind_dec T).
      reassociate <-.
      change (?g ∘ fmap T (shift T) ∘ fmap T (cobind (prod W) (dec T ∘ f)) ∘ ?h)
        with (g ∘ (fmap T (shift T) ∘ fmap T (cobind (prod W) (dec T ∘ f))) ∘ h).
      rewrite (fun_fmap_fmap T).
      unfold bindd.
      change (?h ∘ fmap T g ∘ join T ∘ fmap T (shift T ∘ cobind (prod W) (dec T ∘ f)) ∘ ?i)
        with (h ∘ (fmap T g ∘ join T ∘ fmap T (shift T ∘ cobind (prod W) (dec T ∘ f))) ∘ i).
      fequal.
      unfold kcompose_dm, bindd, preincr.
      rewrite natural.
      reassociate ->. unfold_ops @Fmap_compose. unfold_compose_in_compose.
      rewrite (fun_fmap_fmap T).
      replace (fun '(w, a) => (join T ∘ fmap T (g ∘ incr w) ∘ dec T) (f (w, a)))
        with (join T ∘ (fun '(w, a) => (fmap T (g ∘ incr w) ∘ dec T) (f (w, a))))
        by (ext [? ?]; reflexivity).
      reassociate <-.
      #[local] Set Keyed Unification.
      rewrite (mon_join_join T).
      #[local] Unset Keyed Unification.
      reassociate ->.
      fequal. unfold_compose_in_compose.
      rewrite (fun_fmap_fmap T).
      fequal. fequal. ext [w a].
      unfold shift, compose; cbn.
      compose near (dec T (f (w, a))) on left.
      rewrite (fun_fmap_fmap T).
      compose near (dec T (f (w, a))) on left.
      rewrite (fun_fmap_fmap T).
      fequal. ext [w' b].
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma bindd_comp_ret `(f : W * A -> T B) :
      bindd T f ∘ ret T = f ∘ pair Ƶ.
    Proof.
      intros. unfold_ops Bindd_dec.
      reassociate -> on left.
      rewrite (dmon_ret W T).
      reassociate <- on left.
      reassociate -> near (ret T).
      rewrite (natural (G := T) (ϕ := @ret T _)).
      reassociate <-. rewrite (mon_join_ret T).
      reflexivity.
    Qed.

    #[export] Instance: Kleisli.Decorated.Monad.Monad T :=
      {| kmond_bindd0 := @bindd_comp_ret;
        kmond_bindd1 := @bindd_id;
        kmond_bindd2 := @bindd_bindd;
      |}.

  End with_monad.

End ToKleisli.

(** * Basic properties of [shift] on monads *)
(******************************************************************************)
Section shift_monad_lemmas.

  #[local] Generalizable Variables T A.
  
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

(** * Helper lemmas for proving instances *)
(******************************************************************************)
Section helper_lemmas.

  #[local] Generalizable Variables T.
  
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

#[local] Generalizable Variables E F ϕ A B.

(** * Pushing decorations through a monoid homomorphism *)
(** If a functor is readable by a monoid, it is readable by any target
    of a homomorphism from that monoid too. *)
(******************************************************************************)
Section DecoratedFunctor_monoid_homomorphism.

  Import Product.Notations.

  Context
    (Wsrc Wtgt : Type)
    `{Monoid_Morphism Wsrc Wtgt ϕ}
    `{Decorate Wsrc F} `{Fmap F} `{Return F} `{Join F}
    `{! DecoratedMonad Wsrc F}.

  Instance Decorate_homomorphism :
    Decorate Wtgt F := fun A => fmap F (map_fst ϕ) ∘ dec F.

  Instance Natural_read_morphism : Natural (@dec Wtgt F Decorate_homomorphism).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Decorate_homomorphism.
      unfold_ops @Fmap_compose.
      reassociate <- on left.
      rewrite (fun_fmap_fmap F).
      rewrite (product_fmap_commute).
      rewrite <- (fun_fmap_fmap F).
      reassociate -> on left.
      change (fmap F (fmap (prod Wsrc) f)) with
          (fmap (F ∘ prod Wsrc) f).
      now rewrite (natural (ϕ := @dec Wsrc F _ )).
  Qed.

  Instance DecoratedFunctor_morphism : DecoratedFunctor Wtgt F.
  Proof.
    constructor; try typeclasses eauto.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate <-. reassociate -> near (fmap F (map_fst ϕ)).
      rewrite <- (natural (ϕ := @dec Wsrc F _) (map_fst ϕ)).
      reassociate <-. unfold_ops @Fmap_compose. rewrite (fun_fmap_fmap F).
      reassociate -> near (@dec Wsrc F _ A).
      rewrite (dfun_dec_dec Wsrc F).
      reassociate <-. rewrite (fun_fmap_fmap F).
      reassociate <-. rewrite (fun_fmap_fmap F).
      fequal. fequal. ext [w a]. reflexivity.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate <-. rewrite (fun_fmap_fmap F).
      replace (extract (Wtgt ×) ∘ map_fst ϕ)
        with (@extract (Wsrc ×) _ A) by now ext [w a].
      now rewrite (dfun_dec_extract Wsrc F).
  Qed.

  Instance DecoratedMonad_morphism : DecoratedMonad Wtgt F.
  Proof.
    inversion H3.
    constructor; try typeclasses eauto.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate ->. rewrite (dmon_ret Wsrc F).
      reassociate <-. rewrite (natural (ϕ := @ret F _)).
      ext a. unfold compose; cbn.
      now rewrite (monmor_unit).
    - intros. unfold dec, Decorate_homomorphism.
      reassociate ->. rewrite (dmon_join Wsrc F).
      repeat reassociate <-.
      rewrite (natural (ϕ := @join F _)).
      reassociate -> near (fmap F (shift F)).
      unfold_ops @Fmap_compose.
      unfold_compose_in_compose.
      rewrite (fun_fmap_fmap F _ _ _ (shift F) (fmap F (map_fst ϕ))).
      reassociate -> near (fmap F (map_fst ϕ)). rewrite (fun_fmap_fmap F).
      rewrite <- (fun_fmap_fmap F _ _ _ (dec F) (fmap F (map_fst ϕ))).
      reassociate <-. reassociate -> near (fmap F (fmap F (map_fst ϕ))).
      rewrite <- (natural (ϕ := @dec Wsrc F _)).
      reassociate <-. unfold_ops @Fmap_compose.
      reassociate -> near (fmap F (fmap (prod Wsrc) (fmap F (map_fst ϕ)))).
      rewrite (fun_fmap_fmap F).
      repeat fequal. ext [w t].
      unfold compose; cbn.
      change (id ?f) with f. unfold shift.
      unfold compose; cbn.
      do 2 (compose near t;
            repeat rewrite (fun_fmap_fmap F)).
      fequal. ext [w' a].
      unfold compose; cbn. rewrite monmor_op.
      reflexivity.
  Qed.

End DecoratedFunctor_monoid_homomorphism.

(** * Decorated monads in terms of monad homomorphisms *)
(******************************************************************************)
Section DecoratedMonad_characterization.

  Generalizable Variables T.
  
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
      + constructor... intros. now rewrite (dmon_ret W T).
      + constructor... intros. now rewrite (dmon_join W T).
    - destruct hyp as [hyp1 hyp2]. constructor...
      + intros. inversion hyp1. now rewrite dectrans_commute.
      + intros. inversion hyp2. now rewrite <- dectrans_commute.
  Qed.

End DecoratedMonad_characterization.
