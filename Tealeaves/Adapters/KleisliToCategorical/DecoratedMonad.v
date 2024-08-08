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

  #[local] Instance Map_Bindd: Map T :=
    fun A B f => bindd (ret ∘ f ∘ extract).
  #[export] Instance Join_Bindd: Join T :=
    fun A => bindd (B := A) (A := T A) (extract (W := (W ×))).
  #[export] Instance Decorate_Bindd: Decorate W T :=
    fun A => bindd (ret (A := W * A)).

End operations.

(** ** Derived laws *)
(******************************************************************************)
Module ToCategorical.

  Section with_monad.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Kleisli.DecoratedMonad.DecoratedMonad W T}.

    Existing Instances Map_Bindd Join_Bindd Decorate_Bindd.

    (** *** Functor laws *)
    (******************************************************************************)
    Lemma map_id : forall (A : Type),
        map (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Map_Bindd.
      change (ret ∘ id) with (ret (A := A)).
      now rewrite (kmond_bindd1 (T := T)).
    Qed.

    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map g ∘ map f = map (F := T) (g ∘ f).
    Proof.
      intros. unfold_ops @Map_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      rewrite kc5_00.
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
        rewrite kc5_50.
        rewrite map_to_cobind.
        rewrite kcom_cobind0.
        reflexivity.
    Qed.

    Lemma join_ret : `(join (T := T) ∘ ret (T := T) = @id (T A)).
    Proof.
      intros.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      rewrite (kmond_bindd0 (T := T)).
      reflexivity.
    Qed.

    Lemma join_map_ret : `(join (T := T) ∘ map (F := T) ret = @id (T A)).
    Proof.
      intros.
      unfold_ops @Map_Bindd.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      rewrite (kmond_bindd2 (T := T)).
      rewrite kc5_50.
      rewrite map_to_cobind.
      rewrite kcom_cobind0.
      rewrite (kmond_bindd1 (T := T)).
      reflexivity.
    Qed.

    Lemma join_join :
      `(join ∘ join (T := T) (A := T A) =
          join ∘ map (F := T) join).
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
      rewrite kc5_50.
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
        dec T ∘ dec T = map (F := T) (cojoin (W := (W ×))) ∘ dec T (A := A).
    Proof.
      intros.
      (* Merge LHS *)
      unfold_ops @Decorate_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      (* Merge RHS *)
      unfold_ops @Map_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      fequal.
      rewrite kc5_05.
      change (ret (T := T) (A := W * A)) with
        (ret (T := T) (A := W * A) ∘ id) at 1.
      rewrite kc5_54.
      unfold kc4.
      rewrite (natural (ϕ := @ret T _)).
      reflexivity.
    Qed.

    Lemma dec_extract : forall (A : Type),
        map (F := T) (extract (W := (W ×))) ∘ dec T = @id (T A).
    Proof.
      intros.
      unfold_ops @Decorate_Bindd.
      unfold_ops @Map_Bindd.
      rewrite (kmond_bindd2 (T := T)).
      change (ret (A := W * A)) with (ret (A := W * A) ∘ @id (W * A)).
      rewrite kc5_05.
      change (?f ∘ id) with f.
      rewrite (natural (ϕ := @ret T _)).
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
        rewrite kc5_50.
        rewrite (natural (ϕ := @ret T _)).
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
        dec T ∘ ret (T := T) = ret ∘ pair Ƶ (B := A).
    Proof.
      intros.
      unfold_ops @Decorate_Bindd.
      now rewrite (kmond_bindd0 (T := T)).
    Qed.

    Lemma dmon_join_ : forall (A : Type),
        dec T ∘ join (T := T) (A:=A) =
          join (T := T) ∘ map (F := T) (shift T) ∘ dec T ∘ map (F := T) (dec T).
    Proof.
      intros.
      unfold shift, strength.
      unfold_ops @Decorate_Bindd.
      unfold_ops @Map_Bindd.
      unfold_ops @Join_Bindd.
      unfold_compose_in_compose.
      (* Fuse LHS *)
      rewrite kmond_bindd2 at 1.
      change (extract (W := (W ×)) (A := T A))
        with (id ∘ extract (W := (W ×)) (A := T A)) at 1.
      rewrite kc5_51.
      rewrite fun_map_id.
      change (?f ∘ id) with f.
      (* Fuse RHS *)
      rewrite kmond_bindd2.
      reassociate -> near (extract (W := (W ×))).
      rewrite kc5_54.
      rewrite kc4_id_l.
      rewrite kmond_bindd2.
      change (ret (T := T) ( A:= (W ×) (T ((W ×) A))))
        with ((ret (T := T) (A := (W ×) (T ((W ×) A)))) ∘ id).
      rewrite kc5_54.
      rewrite kc4_04.
      change (?f ∘ id) with f.
      rewrite kmond_bindd2.
      rewrite kc5_54.
      rewrite kc4_40.
      (* Now compare inner functions *)
      fequal.
      ext [w t].
      do 2 (unfold compose; cbn).
      compose near t on right.
      rewrite kmond_bindd2.
      change (ret (A := (W ×) A)) with (ret (A := (W ×) A) ∘ id).
      rewrite kc5_54.
      compose near t on right.
      rewrite kmond_bindd2.
      (* Now compare inner functions again *)
      fequal.
      ext [w' a].
      unfold preincr; unfold compose; cbn.
      unfold kc4; unfold_ops @Cobind_reader.
      unfold compose; cbn.
      change (id ?x) with x.
      compose near (w, (w', a)).
      rewrite kmond_bindd0.
      reflexivity.
    Qed.

    #[local] Instance: Categorical.DecoratedMonad.DecoratedMonad W T :=
      {| dmon_ret := dmon_ret_;
        dmon_join := dmon_join_;
      |}.

  End with_monad.

End ToCategorical.
