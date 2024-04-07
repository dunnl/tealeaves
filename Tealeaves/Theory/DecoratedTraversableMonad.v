From Tealeaves Require Export
  Adapters.KleisliToCoalgebraic.TraversableMonad
  Adapters.KleisliToCoalgebraic.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Kleisli.Theory.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedContainerMonad
  Theory.DecoratedTraversableFunctor
  Theory.TraversableMonad.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.
Import DecoratedTraversableMonad.Notations.

#[local] Generalizable Variables M U W T G A B C.

#[local] Arguments runBatch {A B}%type_scope {F}%function_scope
  {H H0 H1} ϕ%function_scope {C}%type_scope b.

Section lemmas.

  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Monoid_inst: Monoid W}.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Mapd_T_inst : Mapd W T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Mapdt_T_inst : Mapdt W T}
      `{Bindd_T_inst : Bindd W T T}
      `{Bindt_T_inst : Bindt T T}
      `{Binddt_T_inst : Binddt W T T}
      `{ToSubset_T_inst: ToSubset T}
      `{! Compat_Map_Binddt W T T}
      `{! Compat_Mapd_Binddt W T T}
      `{! Compat_Traverse_Binddt W T T}
      `{! Compat_Bind_Binddt W T T}
      `{! Compat_Mapdt_Binddt W T T}
      `{! Compat_Bindd_Binddt W T T}
      `{! Compat_Bindt_Binddt W T T}.

  Context
    `{Map_U_inst : Map U}
      `{Mapd_U_inst : Mapd W U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Mapdt_U_inst : Mapdt W U}
      `{Bindd_U_inst : Bindd W T U}
      `{Bindt_U_inst : Bindt T U}
      `{Binddt_U_inst : Binddt W T U}
      `{ToSubset_U_inst: ToSubset U}
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Mapd_Binddt W T U}
      `{! Compat_Traverse_Binddt W T U}
      `{! Compat_Bind_Binddt W T U}
      `{! Compat_Mapdt_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U}
      `{! Compat_Bindt_Binddt W T U}
      `{! Compat_ToSubset_Traverse T}
      `{! Compat_ToSubset_Traverse U}.

  Context
    `{Monad_inst : ! DecoratedTraversableMonad W T}
      `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  (** ** Respectfulness for <<binddt>> *)
  (******************************************************************************)
  Lemma binddt_respectful_core :
    forall A B (t : U A) G `{Mult G} `{Map G} `{Pure G} (f g : W * A -> G (T B)),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a)) =
        Forall_ctx (fun '(w, a) => f (w, a) = g (w, a)) t.
  Proof.
    intros.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.

  Theorem binddt_respectful :
    forall A B (t : U A) G `{Mult G} `{Map G} `{Pure G} `{! Applicative G}
      (f g : W * A -> G (T B)),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> binddt f t = binddt (U := U) g t.
  Proof.
    introv App_inst.
    intros f g.
    rewrite (binddt_respectful_core A B t G f g).
    unfold Forall_ctx.
    rewrite (foldMapd_through_runBatch2 A B).
    do 2 rewrite binddt_through_runBatch.
    unfold compose.
    rewrite toBatch6_to_toBatch7.
    rewrite <- runBatch_mapsnd.
    induction (toBatch7 t).
    - cbn. reflexivity.
    - destruct a as [w a].
      cbn.
      intros [hyp1 hyp2].
      rewrite hyp2.
      rewrite IHb; auto.
  Qed.

  Theorem binddt_respectful_pure :
    forall A (t : U A) {G} `{Mult G} `{Map G} `{Pure G} `{! Applicative G}
      (f : W * A -> G (T A)),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = pure (F := G) (ret (T := T) a))
      -> binddt f t = pure t.
  Proof.
    intros.
    rewrite <- (binddt_pure A).
    apply binddt_respectful;
    assumption.
  Qed.

  (** ** Respectfulness for <<bindd>> *)
  (******************************************************************************)
  Lemma bindd_respectful_core :
    forall A B (t : U A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a)) =
        Forall_ctx (fun '(w, a) => f (w, a) = g (w, a)) t.
    intros.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.

  Theorem bindd_respectful :
    forall A B (t : U A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd f t = bindd (U := U) g t.
  Proof.
    introv.
    rewrite (bindd_respectful_core A B t f g).
    unfold Forall_ctx.
    rewrite (foldMapd_through_runBatch2 A B).
    do 2 rewrite bindd_through_runBatch.
    unfold compose.
    rewrite toBatch6_to_toBatch7.
    rewrite <- runBatch_mapsnd.
    induction (toBatch7 t).
    - cbn. reflexivity.
    - destruct a as [w a].
      cbn.
      intros [hyp1 hyp2].
      rewrite hyp2.
      rewrite IHb; auto.
  Qed.

End lemmas.

Section instances.

  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Monoid_inst: Monoid W}.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Mapd_T_inst : Mapd W T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Mapdt_T_inst : Mapdt W T}
      `{Bindd_T_inst : Bindd W T T}
      `{Bindt_T_inst : Bindt T T}
      `{Binddt_T_inst : Binddt W T T}
      `{ToSubset_T_inst: ToSubset T}
      `{! Compat_Map_Binddt W T T}
      `{! Compat_Mapd_Binddt W T T}
      `{! Compat_Traverse_Binddt W T T}
      `{! Compat_Bind_Binddt W T T}
      `{! Compat_Mapdt_Binddt W T T}
      `{! Compat_Bindd_Binddt W T T}
      `{! Compat_Bindt_Binddt W T T}.

  Context
    `{Map_U_inst : Map U}
      `{Mapd_U_inst : Mapd W U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Mapdt_U_inst : Mapdt W U}
      `{Bindd_U_inst : Bindd W T U}
      `{Bindt_U_inst : Bindt T U}
      `{Binddt_U_inst : Binddt W T U}
      `{ToSubset_U_inst: ToSubset U}
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Mapd_Binddt W T U}
      `{! Compat_Traverse_Binddt W T U}
      `{! Compat_Bind_Binddt W T U}
      `{! Compat_Mapdt_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U}
      `{! Compat_Bindt_Binddt W T U}
      `{! Compat_ToSubset_Traverse T}
      `{! Compat_ToSubset_Traverse U}.

  Context
    `{Monad_inst : ! DecoratedTraversableMonad W T}
      `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  #[export] Instance DTM_ContainerMonad:
    DecoratedContainerMonad W T.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros; apply bindd_respectful; auto.
  Qed.

      #[export] Instance DTM_ContainerModule:
        DecoratedContainerRightModule W T U.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros; apply bindd_respectful; auto.
  Qed.

End instances.
