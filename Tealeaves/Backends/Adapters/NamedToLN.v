From Tealeaves Require Import
  Backends.LN
  Backends.Named.Common
  Backends.Common.Names
  Backends.Named.Named
  Backends.Named.Alpha
  Functors.Option
  Theory.DecoratedTraversableFunctorPoly
  CategoricalToKleisli.DecoratedFunctorPoly
  CategoricalToKleisli.DecoratedTraversableFunctorPoly.


Import Subset.Notations.
Import Classes.Categorical.DecoratedFunctorPoly.
Import DecoratedTraversableMonad.UsefulInstances.
Import List.ListNotations.

#[local] Open Scope list_scope.

Require Import Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly.

(*
Import Kleisli.DecoratedTraversableMonadPoly.DerivedOperations.
*)

Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.
Import CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedOperations.
Import CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedInstances.
Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.
Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.

Print Instances DecoratedTraversableFunctorPoly.

#[local] Generalizable Variables W T U.

#[local] Open Scope nat_scope.

From Tealeaves Require
  Adapters.MonoidHom.DecoratedTraversableMonad
  Adapters.PolyToMono.DecoratedFunctor
  Adapters.PolyToMono.DecoratedTraversableFunctor
  Adapters.PolyToMono.DecoratedTraversableMonad.

Section DTM.

  Context
    (T: Type -> Type -> Type)
    `{Categorical.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly T}.

  #[export] Instance Binddt_MONO_NAME:
    Binddt (list name) (T name) (T name).
  apply PolyToMono.DecoratedTraversableMonad.Binddt_of_Binddtp.
  Defined.

  #[export] Instance Binddt_MONO:
    Binddt nat (T unit) (T unit).
  assert (Binddt (list unit) (T unit) (T unit)).
  apply PolyToMono.DecoratedTraversableMonad.Binddt_of_Binddtp.
  apply (MonoidHom.DecoratedTraversableMonad.Binddt_Morphism (@length unit)).
  Defined.

  Import PolyToMono.DecoratedTraversableMonad.

  #[export] Instance DTM_MONO:
    DecoratedTraversableMonad nat (T unit).
  Proof.
    assert (DecoratedTraversableMonad (list unit) (T unit)).
    { apply PolyToMono.DecoratedTraversableMonad.DTM_of_DTMP. }
    apply MonoidHom.DecoratedTraversableMonad.DTM_of_DTM.
    { constructor; try typeclasses eauto.
      reflexivity. intros.
      unfold monoid_op, Monoid_op_list.
      induction a1.
      reflexivity.
      cbn. now  rewrite IHa1.
    }
  Qed.

End DTM.





(** * Local Translations *)
(**********************************************************************)
Section with_DTM.

  Context
    (T: Type -> Type -> Type)
      `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.


  Import Categorical.DecoratedFunctorPoly.
  Import CategoricalToKleisli.DecoratedFunctorPoly.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.
  Import Adapters.PolyToMono.DecoratedFunctor.

  Import Adapters.PolyToMono.DecoratedTraversableFunctor.
  Import Kleisli.DecoratedTraversableFunctor.DerivedOperations.


  (** ** Named to Locally Nameless *)
  (**********************************************************************)
  Definition binding_to_ln: Binding -> LN.
  Proof.
    intros [prefix var postfix| ub_context ].
    exact (Bd (length prefix)).
    exact (Fr n).
  Defined.

  Definition name_to_ln:
    list name * name -> LN.
  Proof.
    intros [ctx x].
    exact (binding_to_ln (get_binding ctx x)).
  Defined.

  (** ** Locally Nameless to Named *)
  (**********************************************************************)
  Definition INDEX_EXCEEDS_CONTEXT: nat := 1337.

  Fixpoint ix_new_name_core (avoid: list name) (n: nat): name :=
    match n with
    | 0 => fresh avoid
    | S n' => fresh (avoid ++ [ix_new_name_core avoid n'])
    end.

  Definition ix_new_name (top_conflicts: list name) (ctx: list unit) (n: nat) :=
    if Nat.ltb n (length ctx)
    then ix_new_name_core top_conflicts (n - length ctx)
    else INDEX_EXCEEDS_CONTEXT.

  Definition ln_to_name (top_conflicts: list name):
    list unit * LN -> name :=
    fun '(depth, v) =>
      match v with
      | Fr x => x
      | Bd n => ix_new_name (top_conflicts) depth n
      end.


  Definition ln_to_binder (top_conflicts: list name):
    list unit * unit -> name :=
    (fun '(ctx, _) => ix_new_name top_conflicts ctx (length ctx)).

  (** ** Lifted Operations *)
  (**********************************************************************)
  Definition term_ln_to_nominal (conflicts: list name):
    T unit LN -> T name name :=
    mapdp (T := T)
      (ln_to_binder conflicts)
      (ln_to_name conflicts).


  Definition term_nominal_to_ln:
    T name name -> T unit LN :=
    mapdp (T := T) (const tt) name_to_ln.

  Definition roundtrip_Named:
    T name name -> T name name :=
    fun t => let t_ln := term_nominal_to_ln t
          in term_ln_to_nominal (LN.free t_ln) t_ln.

  Lemma roundtrip_Named_spec: forall (t: T name name),
      roundtrip_Named t =
        mapdp
          (kc_dz (ln_to_binder (free (mapdp (const tt) name_to_ln t))) (const tt))
          (kc_dfunp (ln_to_name (free (mapdp (const tt) name_to_ln t))) (const tt) name_to_ln) t.
  Proof.
    intros.
    unfold roundtrip_Named.
    unfold term_ln_to_nominal.
    unfold term_nominal_to_ln.
    compose near t on left.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  Lemma alpha_principle:
    forall (f: list name * name -> name)
      (t: T name name),
      (forall (ctx: list name) (v: name),
          element_ctx_of (T := T name) (ctx, v) t ->
          alpha_equiv_local (ctx, v) (ctx, f (ctx, v)))
      -> False.
  Proof.
    intros.
    Print Instances MapdPoly.
    Check alpha (T name) (mapdp (T := T) extract f t) t.
  Proof.
    intros.
    unfold alpha.
    replace ((traversep (T := T) (G := fun A => A -> Prop)
                (fun _ _: Z name => True) alpha_equiv_local) (decp t))
      with (mapdtp (G := fun A => A -> Prop)
              (B2 := Z name) (A2 := Z name) (fun _ _: Z name => True) alpha_equiv_local t).
    2:{  admit. }

    change (
    rewrite kdtfp_mapdtp2.
              with
  Qed.

  Axiom (allthings: forall P, P).

  Lemma correctness: forall (t: T name name),
        (alpha T t (roundtrip_Named t)).
  Proof.
    intros.
    rewrite roundtrip_Named_spec.
    unfold roundtrip_Named.
    unfold alpha.
    compose near t on right.
    replace ((traversep (T := T) (G := fun A => A -> Prop)
                (fun _ _: Z name => True) alpha_equiv_local) (decp t))
      with (mapdtp (G := fun A => A -> Prop)
              (B2 := Z name) (A2 := Z name) (fun _ _: Z name => True) alpha_equiv_local t).
    2:{ unfold mapdtp.
        unfold traversep.
        admit.
    }
    rewrite mapdtp_through_toBatchp.
    2:{ admit. }
    unfold compose at 1.
    unfold mapdtp, Mapdt_Categorical.
    do 2 reassociate <- on right.
    change (decp ∘ ?f) with (map (F := fun A => A) (decp) ∘ f).
    assert (ApplicativeCommutativeIdempotent (fun A: Type => A)).
    { admit. }
    rewrite <- (DecoratedTraversableFunctorPoly.dtfp_dist2_decpoly _ _ (G := fun A => A)).
    repeat reassociate -> on right.
    reassociate <- near decp.
    rewrite polydecnat.
    reassociate -> on right.
    Search decp.
    rewrite dfunp_dec_dec.
    reassociate <- near (map2 (TraversableFunctor.dist Z (fun A: Type => A)) TraversableFunctor2.dist2).
    rewrite fun2_map_map.
    do 2 reassociate <- on right.
    reassociate -> near (map2 cojoin cojoin_Z2).
    rewrite fun2_map_map.
    change ((TraversableFunctor2.dist2 (G := fun A => A)
               ∘ map2 ?g ?f
               ∘ decp)) with
      (mapdtp (G := fun A => A) (T := T) g f).
    rewrite mapdtp_through_toBatchp.
    2:{ typeclasses eauto. }
    unfold compose at 5.
    repeat change ((fun x => x) ∘ ?f) with f.
    repeat change ((fun x => x) ?x) with x.
    assert
      (HAHA: (@toBatchp T
       (fun (B1 B2 V1 V2: Type) (G: Type -> Type) (Map_G: Map G) (Pure_G: Pure G) (Mult_G: Mult G)
          (ρ: list B1 * B1 -> G B2) (σ: list B1 * V1 -> G V2) =>
        @TraversableFunctor2.dist2 T H1 G Map_G Pure_G Mult_G B2 V2
        ∘ @map2 T H (list B1 * B1) (list B1 * V1) (G B2) (G V2) ρ σ ∘ @decp T H0 B1 V1) name (Z name) atom
       (Z name) t)
       =
         (@toBatchp T (@Mapdt_Categorical T H H0 H1) name (Z name) name (Z2 name name) t)).
    reflexivity.
    rewrite HAHA.
    unfold compose.
    cbn.
    induction ((@toBatchp T (@Mapdt_Categorical T H H0 H1) name (Z name) name (Z2 name name) t)).
    - cbn. reflexivity.
    - cbn.
      Import Applicative.Notations.
      destruct p as [ctx nm].
      cbn.
      admit.
    - admit.
  Abort.

End with_DTM.
