From Tealeaves Require Export
  Classes.Categorical.DecoratedMonad
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.Comonad.

Import DecoratedMonad.Notations.
Import Product.Notations.
Import Monoid.Notations.
Import Functor.Notations.
Import Comonad.Notations.

#[local] Notation "( X  × )" := (prod X) : function_scope.
#[local] Generalizable Variables T A B C.

(** * Decorated monads from Kleisli decorated monads *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section operations.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Bindd W T T}
    `{Return T}.

  #[export] Instance Map_Bindd: Map T :=
    fun A B f => bindd T (ret T B ∘ f ∘ extract (W ×) A).
  #[export] Instance Join_Bindd: Join T :=
    fun A => bindd T (B := A) (A := T A) (extract (W ×) (T A)).
  #[export] Instance Decorate_Bindd: Decorate W T :=
    fun A => bindd T (ret T (W * A)).

End operations.

(** ** Derived laws *)
(******************************************************************************)
Module ToCategorical.

  Import Kleisli.DecoratedMonad.DerivedInstances.

  Section with_monad.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Kleisli.DecoratedMonad.DecoratedMonad W T}.

    (** *** Functor laws *)
    (******************************************************************************)
    Lemma map_id : forall (A : Type),
        map T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Map_Bindd.
      change (ret T A ∘ id) with (ret T A).
      now rewrite (kmond_bindd1 (T := T)).
    Qed.

    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map T g ∘ map T f = map T (g ∘ f).
    Proof.
      intros. unfold_ops @Map_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      rewrite (kc5_00 T).
      reflexivity.
    Qed.

    #[local] Instance: Classes.Functor.Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

    (** *** Monad laws *)
    (******************************************************************************)
    Lemma ret_natural : Natural (@ret T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Map_Bindd.
        rewrite (kmond_bindd0 (T := T)).
        reflexivity.
    Qed.

    Lemma join_natural : Natural (@join T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros.
        unfold_ops @Map_compose.
        unfold_ops @Map_Bindd.
        unfold_ops @Join_Bindd.
        unfold_compose_in_compose.
        rewrite (kmond_bindd2 (T := T)). (* left *)
        rewrite (kmond_bindd2 (T := T)). (* right *)
        rewrite kc5_05.
        rewrite (kc5_50 T).
        rewrite map_to_cobind.
        rewrite kcom_cobind0.
        reflexivity.
    Qed.

    Lemma join_ret : `(join T ∘ ret T (T A) = @id (T A)).
    Proof.
      intros.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      rewrite (kmond_bindd0 (T := T)).
      reflexivity.
    Qed.

    Lemma join_map_ret : `(join T ∘ map T (ret T A) = @id (T A)).
    Proof.
      intros.
      unfold_ops @Map_Bindd.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      rewrite (kmond_bindd2 (T := T)).
      rewrite (kc5_50 T).
      rewrite map_to_cobind.
      rewrite kcom_cobind0.
      rewrite (kmond_bindd1 (T := T)).
      reflexivity.
    Qed.

    Lemma join_join :
      `(join T ∘ join T (A := T A) = join T ∘ map T (join T)).
    Proof.
      intros.
      (* Merge LHS *)
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      rewrite (kmond_bindd2 (T := T)).
      (* Merge RHS *)
      unfold_ops @Map_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      fequal.
      rewrite (kc5_50 T).
      rewrite map_to_cobind.
      rewrite kcom_cobind0.
      unfold kc5.
      cbn.
      ext [w t].
      setoid_rewrite extract_preincr.
      reflexivity.
    Qed.

    #[local] Instance: Categorical.Monad.Monad T :=
      {| Monad.mon_ret_natural := ret_natural;
        mon_join_natural := join_natural;
        mon_join_ret := join_ret;
        mon_join_map_ret := join_map_ret;
        mon_join_join := join_join;
      |}.

    (** *** Decorated functor laws *)
    (******************************************************************************)
    Lemma dec_dec : forall (A : Type),
        dec T ∘ dec T = map T (cojoin (W ×)) ∘ dec T (A := A).
    Proof.
      intros.
      (* Merge LHS *)
      unfold_ops @Decorate_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      (* Merge RHS *)
      unfold_ops @Map_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      fequal.
      rewrite (kc5_05 T).
      change (ret T (W * A)) with (ret T (W * A) ∘ id) at 1.
      rewrite (kc5_54 T).
      unfold kc4.
      rewrite (natural (ϕ := ret T)).
      reflexivity.
    Qed.

    Lemma dec_extract : forall (A : Type),
        map T (extract (W ×) A) ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_ops @Decorate_Bindd.
      unfold_ops @Map_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      change (ret T (W * A)) with (ret T (W * A) ∘ @id (W * A)).
      rewrite kc5_05.
      change (?f ∘ id) with f.
      rewrite (natural (ϕ := ret T)).
      apply (kmond_bindd1 (T := T)).
    Qed.

    Lemma dec_natural : Natural (@dec W T _).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. unfold_ops @Map_compose.
        unfold_ops @Map_Bindd.
        unfold_ops @Decorate_Bindd.
        rewrite (kmond_bindd2 (T := T)).
        rewrite (kmond_bindd2 (T := T)).
        fequal.
        rewrite kc5_05.
        rewrite (kc5_50 T).
        rewrite (natural (ϕ := ret T)).
        reflexivity.
    Qed.

    #[local] Instance: Categorical.DecoratedFunctor.DecoratedFunctor W T :=
      {| dfun_dec_natural := dec_natural;
        dfun_dec_dec := dec_dec;
        dfun_dec_extract := dec_extract;
      |}.

    (** *** Decorated monad laws *)
    (******************************************************************************)
    Lemma dmon_ret_ : forall (A : Type),
        dec T ∘ ret T A = ret T (W * A) ∘ pair Ƶ (B:=A).
    Proof.
      intros.
      unfold_ops @Decorate_Bindd.
      now rewrite (kmond_bindd0 (T := T)).
    Qed.

    Lemma dmon_join_ : forall (A : Type),
        dec T ∘ join T (A:=A) = join T ∘ map T (shift T) ∘ dec T ∘ map T (dec T).
    Proof.
      intros.
      unfold shift. unfold strength.
      unfold_ops @Decorate_Bindd.
      unfold_ops @Map_Bindd.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      (* Fuse LHS *)
      rewrite (kmond_bindd2 (T := T)) at 1.
      change (extract (W ×) (T A))
        with (id ∘ extract (W ×) (T A)) at 1.
      rewrite (kc5_51).
      rewrite (fun_map_id (F := (W ×))).
      change (?f ∘ id) with f.
      (* Fuse RHS *)
      rewrite (kmond_bindd2 (T := T)).
      reassociate -> near (extract (W ×) _).
      rewrite (kc5_54 T).
      rewrite (DerivedInstances.kc4_id_l).
      rewrite (kmond_bindd2 (T := T)).
      change (ret T ((W × ) (T ((W × ) A))))
        with ((ret T ((W × ) (T ((W × ) A)))) ∘ id).
      rewrite (kc5_54 T).
      rewrite (DerivedInstances.kc4_04).
      change (?f ∘ id) with f.
      rewrite (kmond_bindd2 (T := T)).
      rewrite (kc5_54 T).
      rewrite (DerivedInstances.kc4_40).
      (* Now compare inner functions *)
      fequal.
      ext [w t].
      do 2 (unfold compose; cbn).
      compose near t on right.
      rewrite (kmond_bindd2).
      change (ret T ((W × ) A)) with (ret T ((W × ) A) ∘ id).
      rewrite (kc5_54 T).
      compose near t on right.
      rewrite (kmond_bindd2).
      (* Now compare inner functions again *)
      fequal.
      ext [w' a].
      unfold preincr; unfold compose; cbn.
      unfold kc4; unfold_ops @Cobind_env.
      unfold compose; cbn.
      change (id ?x) with x.
      compose near (w, (w', a)).
      rewrite (kmond_bindd0).
      reflexivity.
    Qed.

    #[local] Instance: Categorical.DecoratedMonad.DecoratedMonad W T :=
      {| dmon_ret := dmon_ret_;
        dmon_join := dmon_join_;
      |}.

  End with_monad.

End ToCategorical.
