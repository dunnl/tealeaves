From Tealeaves Require Export
     Classes.DecoratedTraversableMonad
     Classes.DecoratedModule
     Classes.TraversableModule.

Import DecoratedTraversableMonad.Notations.
#[local] Open Scope tealeaves_scope.

(** * Decorated-Traversable Module *)
(******************************************************************************)
Section DecoratedTraverableModule.

  Context
  (W : Type)
  (F T : Type -> Type)
  `{op : Monoid_op W}
  `{unit : Monoid_unit W}
  `{Fmap T} `{Return T} `{Join T}
  `{Decorate W T} `{Dist T}
  `{Fmap F} `{RightAction F T}
  `{Decorate W F} `{Dist F}.

  Class DecoratedTraversableModule :=
    { dtmod_functor :> DecoratedTraversableFunctor W F;
      dtmod_monad   :> DecoratedTraversableMonad W T;
      dtmod_dec     :> DecoratedModule W F T;
      dtmod_trav    :> TraversableModule F T;
    }.

End DecoratedTraverableModule.

(** ** D-T monads are D-T modules *)
(******************************************************************************)
Section DecoratedTraversableModule_Monad.

  Existing Instance RightAction_Join.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad W T}.

  Instance DecoratedTraversableModule_Monad :
    DecoratedTraversableModule W T T :=
    {| dtmod_dec := DecoratedModule_Monad T;
       dtmod_trav := TraversableModule_Monad T;
    |}.

End DecoratedTraversableModule_Monad.

(** ** D-T modules are closed under composition with D-T functors *)
(******************************************************************************)
Section DecoratedTraversableModule_compose.

  Context
    `{Monoid W}
    `{Fmap F} `{Fmap G} `{Fmap T}
    `{Return T} `{Join T} `{RightAction F T}
    `{Dist F} `{Dist G} `{Dist T}
    `{Decorate W F} `{Decorate W G} `{Decorate W T}
    `{! DecoratedTraversableFunctor W G}
    `{! DecoratedTraversableModule W F T}.

  Instance: RightModule (G ∘ F) T := RightModule_compose.
  Instance: DecoratedModule W (G ∘ F) T := DecoratedModule_compose.
  Instance: TraversableModule (G ∘ F) T := TraversableModule_compose.

  Instance DecoratedTraversableModule_compose : DecoratedTraversableModule W (G ∘ F) T.
  Proof.
    constructor; typeclasses eauto.
  Qed.

End DecoratedTraversableModule_compose.

Section test_typeclasses.

  Context
    `{DecoratedTraversableModule W F T}.

  Goal Functor T. typeclasses eauto. Qed.
  Goal DecoratedFunctor W T. typeclasses eauto. Qed.
  Goal ListableFunctor T. typeclasses eauto. Qed.
  Goal TraversableFunctor T. typeclasses eauto. Qed.
  Goal SetlikeFunctor T. typeclasses eauto. Qed.
  Goal ListableFunctor T. typeclasses eauto. Qed.

  Goal Monad T. typeclasses eauto. Qed.
  Goal DecoratedMonad W T. typeclasses eauto. Qed.
  Goal ListableMonad T. typeclasses eauto. Qed.
  Goal TraversableMonad T. typeclasses eauto. Qed.
  Goal SetlikeMonad T. typeclasses eauto. Qed.
  Goal ListableMonad T. typeclasses eauto. Qed.
  Goal DecoratedTraversableMonad W T. typeclasses eauto. Qed.

  Goal Functor F. typeclasses eauto. Qed.
  Goal DecoratedFunctor W F. typeclasses eauto. Qed.
  Goal ListableFunctor F. typeclasses eauto. Qed.
  Goal TraversableFunctor F. typeclasses eauto. Qed.
  Goal SetlikeFunctor F. typeclasses eauto. Qed.
  Goal ListableFunctor F. typeclasses eauto. Qed.

  Goal RightModule F T. typeclasses eauto. Qed.
  Goal DecoratedModule W F T. typeclasses eauto. Qed.
  Goal ListableModule F T. typeclasses eauto. Qed.
  Goal TraversableModule F T. typeclasses eauto. Qed.
  Goal SetlikeModule F T. typeclasses eauto. Qed.
  Goal ListableModule F T. typeclasses eauto. Qed.
  Goal DecoratedTraversableFunctor W F. typeclasses eauto. Qed.

End test_typeclasses.

(** * Kleisli presentation *)
(******************************************************************************)

(** ** Lifting operation <<subdt>> *)
(******************************************************************************)
Definition subdt F
           `{Fmap F} `{Decorate W F} `{Dist F} `{RightAction F T}
           `{Fmap T} `{Decorate W T} `{Dist T} `{Join T}
           `{Fmap G} `{Pure G} `{Mult G}
           {A B : Type} (f : W * A -> G (T B)) : F A -> G (F B)
  := fmap G (right_action F) ∘ dist F G ∘ fmap F f ∘ dec F.

(** ** Specifications for sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableModule_suboperations.

  Context
    (F : Type -> Type)
    `{DecoratedTraversableModule W F T}.

  (** *** [subdd] as a special case of [subdt] *)
  Theorem subd_to_subdt {A B} : forall (f : W * A -> T B),
      subd F f = subdt F (G := fun A => A) f.
  Proof.
    intros. unfold subdt.
    change (fmap (fun A => A) ?f) with f.
    now rewrite (dist_unit F).
  Qed.

  (** *** [subt] as a special case of [subdt] *)
  Theorem subt_to_subdt {A B} `{Applicative G} : forall (f : A -> G (T B)),
      subt F f = subdt F (f ∘ extract (prod W)).
  Proof.
    intros. unfold subdt, subt.
    now rewrite (fmap_to_fmapd F).
  Qed.

  (** *** [fmapdt] as a special case of [subdt] *)
  Theorem fmapdt_to_subdt {A B} `{Applicative G} :
    forall (f : W * A -> G B),
      fmapdt F f = subdt F (fmap G (ret T) ∘ f).
  Proof.
    introv. unfold subdt.
    (* Kill the join *)
    rewrite <- (fun_fmap_fmap F). reassociate <- on right.
    change (fmap F (fmap G ?f)) with (fmap (F ∘ G) f).
    bring (dist F G (A := T B)) and
          (fmap (F ∘ G) (ret T (A := B))) together.
    rewrite <- (dist_natural F). reassociate <-.
    unfold_ops @Fmap_compose.
    unfold_compose_in_compose; rewrite (fun_fmap_fmap G).
    rewrite (rmod_action_fmap_ret F T).
    now rewrite (fun_fmap_id G).
  Qed.

  (** *** [fmapd] as a special case of [subdt] *)
  Theorem fmapd_to_subdt {A B} : forall (f : W * A -> B),
      fmapd F f = subdt F (G := (fun A => A)) (ret T ∘ f).
  Proof.
    intros. rewrite (DecoratedTraversableFunctor.fmapd_to_fmapdt F).
    now rewrite (fmapdt_to_subdt).
  Qed.

  (** *** [traverse] as a special case of [subdt] *)
  Theorem fmapt_to_subdt {A B} `{Applicative G} : forall (f : A -> G B),
      traverse F G f = subdt F (fmap G (ret T) ∘ f ∘ extract (prod W)).
  Proof.
    introv. rewrite (DecoratedTraversableFunctor.traverse_to_fmapdt F).
    now rewrite (fmapdt_to_subdt).
  Qed.

  (** *** [sub] as a special case of [subdt] *)
  Theorem sub_to_subdt {A B} : forall (f : A -> T B),
      sub F f = subdt F (G := (fun A => A)) (f ∘ extract (prod W)).
  Proof.
    intros. rewrite (sub_to_subd F T).
    now rewrite (subd_to_subdt).
  Qed.

  (** *** [fmap] as a special case of [subdt] *)
  Theorem fmap_to_subdt {A B} : forall (f : A -> B),
      fmap F f = subdt F (G := (fun A => A)) (ret T ∘ f ∘ extract (prod W)).
  Proof.
    introv. rewrite (DecoratedTraversableFunctor.fmap_to_fmapdt F).
    now rewrite (fmapdt_to_subdt).
  Qed.

End DecoratedTraversableModule_suboperations.

(** ** Functoriality of <<subdt>> *)
(******************************************************************************)
Section DecoratedTraversableMonad_subdt.

  Context
    (T : Type -> Type)
    `{DecoratedTraversableModule W F T}.

  Theorem subdt_id {A} : subdt (G := fun A => A) F (ret T ∘ extract (prod W)) = @id (F A).
  Proof.
    introv. rewrite <- (subd_to_subdt F).
    apply (subd_id F T).
  Qed.

  Theorem subdt_subdt {A B C} `{Applicative G1} `{Applicative G2}
          (f : W * A -> G1 (T B)) (g : W * B -> G2 (T C)) :
    fmap G1 (subdt F g) ∘ subdt F f = subdt (G := G1 ∘ G2) F (g ⋆dtm f).
  Proof.
  Admitted.

End DecoratedTraversableMonad_subdt.

(** ** Composition with sub-operations  *)
(******************************************************************************)
Section DecoratedTraversableMonad_composition.

End DecoratedTraversableMonad_composition.
