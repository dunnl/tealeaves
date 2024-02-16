From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedContainerFunctor.

Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variables A T U W.

(** * Decorated container monads *)
(******************************************************************************)

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedContainerMonad
  (W : Type) (T : Type -> Type)
  `{Monoid_op W} `{Monoid_unit W}
  `{Bindd W T T} `{Return T}
  `{ElementsCtx W T} :=
  { dconm_functor :> DecoratedMonad W T;
    decom_hom :> DecoratedMonadHom W T (ctxset W) (@element_ctx_of W T _);
    dconm_pointwise : forall (A B : Type) (t : T A) (f g : W * A -> T B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> bindd f t = bindd g t;
  }.

Class DecoratedContainerRightModule
  (W : Type) (T U : Type -> Type)
  `{Monoid_op W} `{Monoid_unit W}
  `{Bindd W T T} `{Return T}
  `{Bindd W T U}
  `{ElementsCtx W T}
  `{ElementsCtx W U} :=
  { dconmod_module :> DecoratedRightModule W T U;
    dconmod_hom :> ParallelDecoratedRightModuleHom T (ctxset W) U (ctxset W)
      (@element_ctx_of W T _)
      (@element_ctx_of W U _);
    dconmod_pointwise : forall (A B : Type) (t : U A) (f g : W * A -> T B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> bindd f t = bindd (U := U) g t;
  }.

Class DecoratedContainerMonadFull
  (W : Type) (T : Type -> Type)
  `{Map T}
  `{Mapd W T}
  `{Bind T T}
  `{Bindd W T T}
  `{Return T}
  `{Monoid_op W}
  `{Monoid_unit W}
  `{Monoid W}
  `{ElementsCtx W T} `{Elements T} :=
  { dconmf_dconm :> DecoratedContainerMonad W T;
    dconmf_functor :> DecoratedMonadFull W T;
    dconmf_element_compat :> Compat_Elements_ElementsCtx;
  }.

(*
#[local] Instance tmp `{DecoratedContainerMonadFull W T} :
  DecoratedContainerFunctorFull W T.
Proof.
  constructor.
  - admit.
  - constructor.
    + admit.
    + constructor.
      intros.
      assert (lemma : mapd f = bindd (ret ∘ f)). admit.
      rewrite lemma.
      rewrite dconm_morphism_bind.
      fequal.
      ext p.
      rewrite (@ctxset_mapd_to_bindd W _ _).
      2: admit.
      fequal.
      reassociate <- on right.
      rewrite dconm_morphism_ret.
      reflexivity.
    + intros.
      assert (lemma : mapd f = bindd (ret ∘ f)). admit.
      assert (lemma2 : mapd g = bindd (ret ∘ g)). admit.
      rewrite lemma.
      rewrite lemma2.
      apply dconm_pointwise.
      admit.
Admitted.
     *)

(** * Basic properties of containers *)
(******************************************************************************)
Section decorated_container_monad_theory.

  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{ret_inst : Return T}
      `{Bindd_T_inst : Bindd W T T}
      `{Mapd_T_inst : Mapd W T}
      `{Bind_T_inst : Bind T T}
      `{Map_T_inst : Map T}
      `{Map_Bindd_T_inst : ! Compat_Map_Bindd W T T}
      `{Bind_Bindd_T_inst : ! Compat_Bind_Bindd W T T}
      `{Mapd_Bindd_T_inst : ! Compat_Mapd_Bindd W T T}
      `{ElementsCtx_T_inst : ElementsCtx W T}
      `{Elements_T_inst : Elements T}
      `{! Compat_Elements_ElementsCtx (E := W) (T := T)}
      `{! DecoratedContainerMonad W T}
      `{Mapd_U_inst : Mapd W U}
      `{Bind_U_inst : Bind T U}
      `{Map_U_inst : Map U}
      `{Bindd_U_inst : Bindd W T U}
      `{Map_Bindd_inst : ! Compat_Map_Bindd W T U}
      `{Bind_Bindd_inst : ! Compat_Bind_Bindd W T U}
      `{Mapd_Bindd_inst : ! Compat_Mapd_Bindd W T U}
      `{ElementsCtx_U_inst : ElementsCtx W U}
      `{Elements_U_inst : Elements U}
      `{! Compat_Elements_ElementsCtx (E := W) (T := U)}
      `{Module_inst : ! DecoratedContainerRightModule W T U}.

  Variables (A B : Type).

  Implicit Types (t : U A) (b : B) (w : W) (a : A).

  Lemma dconm_morphism_ret : forall (A : Type),
      element_ctx_of ∘ ret (T := T) (A := A) =
        ret (T := ctxset W).
  Proof.
    apply kmond_hom_ret.
  Qed.

  Theorem ind_ret_iff : forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret (T := T) a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros.
    compose near a2 on left.
    rewrite kmond_hom_ret.
    unfold_ops @Return_ctxset.
    intuition.
  Qed.

  Lemma dconm_morphism_bind : forall (A B : Type) (f : W * A -> T B),
      element_ctx_of ∘ bindd (U := U) f =
        bindd (U := ctxset W) (element_ctx_of ∘ f) ∘ element_ctx_of (F := U).
  Proof.
    apply kmoddpar_hom_bind.
  Qed.

  Theorem ind_bindd_iff : forall w t f b,
      (w, b) ∈d bindd (U := U) f t <->
        exists (wa : W) (a : A), (wa, a) ∈d t /\
                              exists wb : W, (wb, b) ∈d f (wa, a) /\
                                          w = wa ● wb.
  Proof.
    introv.
    compose near t on left.
    rewrite kmoddpar_hom_bind.
    reflexivity.
  Qed.

  Theorem ind_bindd_iff' :
    forall `(f : W * A -> T B) (t : U A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd f t <->
        exists (w1 w2 : W) (a : A),
          (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
          /\ wtotal = w1 ● w2.
  Proof.
    intros.
    rewrite ind_bindd_iff.
    splits; intros ?; preprocess;
      (repeat eexists); eauto.
  Qed.

  Corollary ind_bind_iff : forall w t f b,
      (w, b) ∈d bind f t <->
        exists (wa : W) (a : A), (wa, a) ∈d t /\
                   exists wb : W, (wb, b) ∈d f a /\
                               w = wa ● wb.
  Proof.
    introv.
    rewrite bind_to_bindd.
    rewrite ind_bindd_iff.
    reflexivity.
  Qed.

  Corollary ind_bind_iff': forall w t f b,
      (w, b) ∈d bind f t <->
        exists (wa wb : W) (a : A),
          (wa, a) ∈d t /\
            (wb, b) ∈d f a /\
            w = wa ● wb.
  Proof.
    introv.
    rewrite ind_bind_iff.
    splits; intros ?; preprocess;
      (repeat eexists); eauto.
  Qed.

  Corollary in_bindd_iff : forall t f b,
      b ∈ bindd (U := U) f t <->
        exists (wa : W) (a : A),
          (wa, a) ∈d t /\ b ∈ f (wa, a).
  Proof.
    introv.
    rewrite ind_iff_in.
    setoid_rewrite ind_bindd_iff.
    setoid_rewrite ind_iff_in.
    split.
    - intros [w [wa [a [Hin [wb [Hin' Heq]]]]]].
      eauto.
    - intros [wa [a [Hin [w rest]]]].
      exists (wa ● w) wa a. eauto.
  Qed.

  (******************************************************************************)
  Corollary bindd_respectful :
    forall A B (t : U A) (f : W * A -> T B) (g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd f t = bindd g t.
  Proof.
    introv hyp.
    apply dconmod_pointwise.
    assumption.
  Qed.

  Corollary bindd_respectful_bind :
    forall A B (t : U A) (f : W * A -> T B) (g : A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> bindd f t = bind g t.
  Proof.
    introv hyp.
    rewrite bind_to_bindd.
    apply bindd_respectful.
    introv Hin.
    eauto.
  Qed.

  Corollary bindd_respectful_mapd :
    forall A B (t : U A) (f : W * A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret (g (w, a)))
      -> bindd f t = mapd g t.
  Proof.
    introv hyp.
    rewrite mapd_to_bindd.
    apply bindd_respectful.
    assumption.
  Qed.

  Corollary bindd_respectful_map :
    forall A B (t : U A) (f : W * A -> T B) (g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret (g a))
      -> bindd f t = map g t.
  Proof.
    introv hyp.
    rewrite map_to_bindd.
    apply bindd_respectful.
    assumption.
  Qed.

  Corollary bindd_respectful_id :
    forall A (t : U A) (f : W * A -> T A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret a)
      -> bindd f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- kmodd_bindd1.
    eapply bindd_respectful.
    eauto.
  Qed.

End decorated_container_monad_theory.


(** ** Instance for <<env>> *)
(******************************************************************************)
(*
#[export] Instance DecoratedContainerMonad_env `{Monoid W} :
  DecoratedContainerMonad W (env W).
Proof.
  constructor.
  - admit.
  - intros. ext l. unfold compose.
    induction l as [| [w a] rest IHrest].
    + cbn. unfold_ops @ElementsCtx_env.
      autorewrite with tea_list.
      rewrite bindd_ctxset_nil.
      reflexivity.
    + change (bindd f ((w, a) :: rest)) with
        (shift list (w, f (w, a)) ++ bindd f rest).
      cbn.
      unfold_ops @ElementsCtx_env.
      autorewrite with tea_list.
      change (element_of (A := W * ?A)) with
        (element_ctx_of (F := env W) (A := A)).
      rewrite bindd_ctxset_add.
      rewrite bindd_ctxset_one.
      rewrite <- IHrest.
      fequal.
      rewrite (DecoratedFunctor.shift_spec). 2:admit.
      compose near (f (w, a)).
      rewrite (fun_map_map).
Abort.
*)
