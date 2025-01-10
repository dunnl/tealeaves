From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Kleisli.Theory.DecoratedTraversableFunctor.

Import Monoid.Notations.
Import Subset.Notations.
Import List.ListNotations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variable W M T U G A B C.

(** * Derived instances *)
(******************************************************************************)
Section derived.

  Section operations.

    Context
      W T U
        `{Return_inst : Return T}
        `{Bindd_inst : Binddt W T U}.

    #[local] Instance Map_Binddt : Map U :=
      fun (A B : Type) (f : A -> B) => binddt (G := fun A => A) (ret (T := T) ∘ f ∘ extract (W := (W ×))).
    #[local] Instance Mapdt_Binddt: Mapdt W U
      := fun G _ _ _ A B f => binddt (map (F := G) (ret (T := T)) ∘ f).
    #[local] Instance Bindd_Binddt: Bindd W T U
      := fun A B f => binddt (G := fun A => A) f.
    #[local] Instance Bindt_Binddt: Bindt T U
      := fun G _ _ _ A B f => binddt (f ∘ extract (W := (W ×))).
    #[local] Instance Bind_Binddt: Bind T U
      := fun A B f => binddt (T := T) (G := fun A => A) (f ∘ extract (W := (W ×))).
    #[local] Instance Mapd_Binddt: Mapd W U
      := fun A B f => binddt (G := fun A => A) (ret (T := T) ∘ f).
    #[local] Instance Traverse_Binddt: Traverse U
      := fun G _ _ _ A B f => binddt (T := T) (map (F := G) (ret (T := T)) ∘ f ∘ extract (W := (W ×))).

  End operations.

  Section compat.

    Context
      W T U
    `{Return_inst : Return T}
    `{Map_inst : Map U}
    `{Mapd_inst : Mapd W U}
    `{Traverse_inst : Traverse U}
    `{Bind_inst : Bind T U}
    `{Mapdt_inst : Mapdt W U}
    `{Bindd_inst : Bindd W T U}
    `{Bindt_inst : Bindt T U}
    `{Binddt_inst : Binddt W T U}.

    Class Compat_Map_Binddt : Prop :=
      compat_map_binddt :
        @map U Map_inst = @map U (@Map_Binddt W T U Return_inst Binddt_inst).

    Class Compat_Mapd_Binddt : Prop :=
      compat_mapd_binddt :
        @mapd W U Mapd_inst = @mapd W U (@Mapd_Binddt W T U Return_inst Binddt_inst).

    Class Compat_Traverse_Binddt : Prop :=
      compat_traverse_binddt :
        @traverse U Traverse_inst = @traverse U (@Traverse_Binddt W T U Return_inst Binddt_inst).

    Class Compat_Bind_Binddt : Prop :=
      compat_bind_binddt :
        @bind T U Bind_inst = @bind T U (@Bind_Binddt W T U Binddt_inst).

    Class Compat_Bindd_Binddt : Prop :=
      compat_bindd_binddt :
        @bindd W T U Bindd_inst = @bindd W T U (@Bindd_Binddt W T U Binddt_inst).

    Class Compat_Bindt_Binddt : Prop :=
      compat_bindt_binddt :
        @bindt T U Bindt_inst = @bindt T U (@Bindt_Binddt W T U Binddt_inst).

    Class Compat_Mapdt_Binddt : Prop :=
      compat_mapdt_binddt :
        @mapdt W U Mapdt_inst = @mapdt W U (@Mapdt_Binddt W T U Return_inst Binddt_inst).

  End compat.

  Section self.

    Context
    `{Return_inst : Return T}
    `{Binddt_inst : Binddt W T U}.

    #[export] Instance Compat_Map_Binddt_Self:
      Compat_Map_Binddt W T U (Map_inst := Map_Binddt W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Mapd_Binddt_Self:
      Compat_Mapd_Binddt W T U (Mapd_inst := Mapd_Binddt W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Traverse_Binddt_Self:
      Compat_Traverse_Binddt W T U (Traverse_inst := Traverse_Binddt W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Bind_Binddt_Self:
      Compat_Bind_Binddt W T U (Bind_inst := Bind_Binddt W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Bindd_Binddt_Self:
      Compat_Bindd_Binddt W T U (Bindd_inst := Bindd_Binddt W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Bindt_Binddt_Self:
      Compat_Bindt_Binddt W T U (Bindt_inst := Bindt_Binddt W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Mapdt_Binddt_Self:
      Compat_Mapdt_Binddt W T U (Mapdt_inst := Mapdt_Binddt W T U).
    Proof.
      reflexivity.
    Qed.

    Ltac normalize_binddt :=
      repeat (rewrite (compat_map_binddt W T U) ||
                rewrite (compat_mapd_binddt W T U) ||
                  rewrite (compat_traverse_binddt W T U) ||
                    rewrite (compat_mapdt_binddt W T U) ||
                      rewrite (compat_bind_binddt W T U) ||
                        rewrite (compat_bindd_binddt W T U) ||
                          rewrite (compat_bindt_binddt W T U)).

    Ltac solve_compat :=
      hnf;
      normalize_binddt;
      unfold_ops @Map_Bind @Map_Traverse @Map_Mapd;
      unfold_ops @Map_Mapdt @Mapd_Mapdt @Traverse_Mapdt;
      unfold_ops @Map_Bindd @Mapd_Bindd @Bind_Bindd;
      unfold_ops @Map_Bindt @Traverse_Bindt @Bind_Bindt;
      normalize_binddt;
      reflexivity.

    Section pairwise_compatibility.

      Context
        `{Map_inst: Map U}
        `{Mapd_inst: Mapd W U}
        `{Traverse_inst: Traverse U}
        `{Mapdt_inst: Mapdt W U}
        `{Bind_inst: Bind T U}
        `{Bindd_inst: Bindd W T U}
        `{Bindt_inst: Bindt T U}
        `{! Compat_Map_Binddt W T U}
        `{! Compat_Mapd_Binddt W T U}
        `{! Compat_Traverse_Binddt W T U}
        `{! Compat_Mapdt_Binddt W T U}
        `{! Compat_Bind_Binddt W T U}
        `{! Compat_Bindd_Binddt W T U}
        `{! Compat_Bindt_Binddt W T U}.

    #[export] Instance Compat_Map_Bind_Bindd:
      Compat_Map_Bind U T := ltac:(solve_compat).

    (** ** Compatibility with <<traverse>>, <<mapd>>, and <<bind>>.*)
    #[export] Instance Compat_Map_Traverse_Binddt:
      Compat_Map_Traverse U := ltac:(solve_compat).

    #[export] Instance Compat_Map_Mapd_Binddt:
      Compat_Map_Mapd := ltac:(solve_compat).

    #[export] Instance Compat_Map_Bind_Binddt:
      Compat_Map_Bind U T := ltac:(solve_compat).

    (** ** Compatibility with <<bindd>> *)
    #[export] Instance Compat_Map_Bindd_Binddt:
      Compat_Map_Bindd W T U := ltac:(solve_compat).

    #[export] Instance Compat_Mapd_Bindd_Binddt:
      Compat_Mapd_Bindd W T U := ltac:(solve_compat).

    #[export] Instance Compat_Bind_Bindd_Binddt:
      Compat_Bind_Bindd W T U := ltac:(solve_compat).

    (** ** Compatibility with <<bindt>> *)
    #[export] Instance Compat_Map_Bindt_Bindtt:
      Compat_Map_Bindt T U := ltac:(solve_compat).

    #[export] Instance Compat_Traverse_Bindt_Bindtt:
      Compat_Traverse_Bindt T U := ltac:(solve_compat).

    #[export] Instance Compat_Bind_Bindt_Bindtt:
        Compat_Bind_Bindt T U := ltac:(solve_compat).

    (** ** Compatibility with <<mapdt>> *)
    #[export] Instance Compat_Map_Mapdt_Binddt:
      Compat_Map_Mapdt := ltac:(solve_compat).

    #[export] Instance Compat_Mapd_Mapdt_Binddt:
      Compat_Mapd_Mapdt := ltac:(solve_compat).

    #[export] Instance Compat_Traverse_Mapdt_Binddt:
      Compat_Traverse_Mapdt := ltac:(solve_compat).

  End pairwise_compatibility.

  Section compat_laws.

    Context
    `{Map_inst : Map U}
    `{Mapd_inst : Mapd W U}
    `{Traverse_inst : Traverse U}
    `{Bind_inst : Bind T U}
    `{Mapdt_inst : Mapdt W U}
    `{Bindd_inst : Bindd W T U}
    `{Bindt_inst : Bindt T U}.

    Lemma map_to_binddt `{! Compat_Map_Binddt W T U} :
      forall `(f : A -> B), map (F := U) f = binddt (G := fun A => A) (ret (T := T) ∘ f ∘ extract).
    Proof.
      rewrite (compat_map_binddt W T U).
      reflexivity.
    Qed.

    Lemma mapd_to_binddt `{! Compat_Mapd_Binddt W T U} `(f : W * A -> B):
      mapd (T := U) f = binddt (G := fun A => A) (ret (T := T) ∘ f).
    Proof.
      rewrite (compat_mapd_binddt W T U).
      reflexivity.
    Qed.

    Lemma traverse_to_binddt `{! Compat_Traverse_Binddt W T U}
      `{Applicative G} `(f : A -> G B):
      traverse (G := G) (T := U) f = binddt (U := U) (map (F := G) (ret (T := T)) ∘ f ∘ extract).
    Proof.
      rewrite (compat_traverse_binddt W T U).
      reflexivity.
    Qed.

    Lemma bind_to_binddt `{! Compat_Bind_Binddt W T U} `(f : A -> T B):
      bind (U := U) f = binddt (U := U) (f ∘ extract).
    Proof.
      rewrite (compat_bind_binddt W T U).
      reflexivity.
    Qed.

    Lemma mapdt_to_binddt `{! Compat_Mapdt_Binddt W T U} :
      forall `{Applicative G} `(f : W * A -> G B),
        mapdt (G := G) f = binddt (map (ret (T := T)) ∘ f).
    Proof.
      rewrite (compat_mapdt_binddt W T U).
      reflexivity.
    Qed.

    Lemma mapdt_to_binddt' `{! Compat_Mapdt_Binddt W T U} :
      forall `{Applicative G}
        (A B : Type),
        mapdt (T := U) (G := G) (A := A) (B := B) =
         binddt ○ compose (map ret).
    Proof.
      intros.
      ext f.
      rewrite mapdt_to_binddt.
      reflexivity.
    Qed.

    Lemma bindd_to_binddt `{! Compat_Bindd_Binddt W T U} :
      forall A B,
      bindd (T := T) (U := U) (A := A) (B := B) = binddt (G := fun A => A).
    Proof.
      rewrite (compat_bindd_binddt W T U).
      reflexivity.
    Qed.

    Lemma bindt_to_binddt `{! Compat_Bindt_Binddt W T U}
      `{Applicative G} `(f : A -> G (T B)):
      (* TODO Swap arguments to bindt *)
      bindt (G := G) f =
        binddt (U := U) (f ∘ extract).
    Proof.
      rewrite (compat_bindt_binddt W T U).
      reflexivity.
    Qed.

    Lemma map_to_bind
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Bind_Binddt W T U}
      : forall (A B : Type) (f : A -> B),
        map f = bind (ret ∘ f).
    Proof.
      rewrite compat_map_bind.
      reflexivity.
    Qed.

    Lemma map_to_bindd
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U}
      : forall (A B : Type) (f : A -> B),
        map (F := U) f = bindd (ret ∘ f ∘ extract).
    Proof.
      intros.
      rewrite (compat_map_bindd W T U).
      reflexivity.
    Qed.

  End compat_laws.

  End self.

End derived.

Class DecoratedTraversableMonadFull
  (W : Type)
  (T : Type -> Type)
  `{op : Monoid_op W}
  `{unit : Monoid_unit W}
  `{ret_inst : Return T}
  `{Map_inst : Map T}
  `{Mapd_inst : Mapd W T}
  `{Traverse_inst : Traverse T}
  `{Bind_inst : Bind T T}
  `{Mapdt_inst : Mapdt W T}
  `{Bindd_inst : Bindd W T T}
  `{Bindt_inst : Bindt T T}
  `{Binddt_inst : Binddt W T T}
  :=
  { kdtmf_kmond :> DecoratedTraversableMonad W T;
    kdtmf_map_compat :> Compat_Map_Binddt W T T;
    kdtmf_mapd_compat :> Compat_Mapd_Binddt W T T;
    kdtmf_traverse_compat :> Compat_Traverse_Binddt W T T;
    kdtmf_bind_compat :> Compat_Bind_Binddt W T T;
    kdtmf_mapdt_compat :> Compat_Mapdt_Binddt W T T;
    kdtmf_bindd_compat :> Compat_Bindd_Binddt W T T;
    kdtmf_bindt_compat :> Compat_Bindt_Binddt W T T;
  }.

Class DecoratedTraversableRightModuleFull
  (W : Type)
  (T : Type -> Type)
  (U : Type -> Type)
  `{op : Monoid_op W}
  `{unit : Monoid_unit W}
  `{ret_inst : Return T}
  `{Map_T_inst : Map T}
  `{Mapd_T_inst : Mapd W T}
  `{Traverse_T_inst : Traverse T}
  `{Bind_T_inst : Bind T T}
  `{Mapdt_T_inst : Mapdt W T}
  `{Bindd_T_inst : Bindd W T T}
  `{Bindt_T_inst : Bindt T T}
  `{Binddt_T_inst : Binddt W T T}
  `{Map_U_inst : Map U}
  `{Mapd_U_inst : Mapd W U}
  `{Traverse_U_inst : Traverse U}
  `{Bind_U_inst : Bind T U}
  `{Mapdt_U_inst : Mapdt W U}
  `{Bindd_U_inst : Bindd W T U}
  `{Bindt_U_inst : Bindt T U}
  `{Binddt_U_inst : Binddt W T U}
  :=
  { kdtmodf_kmond :> DecoratedTraversableMonadFull W T;
    kdtmodf_mod :> DecoratedTraversableRightModule W T U;
    kdtmodf_map_compat :> Compat_Map_Binddt W T U;
    kdtmodf_mapd_compat :> Compat_Mapd_Binddt W T U;
    kdtmodf_traverse_compat :> Compat_Traverse_Binddt W T U;
    kdtmodf_bind_compat :> Compat_Bind_Binddt W T U;
    kdtmodf_mapdt_compat :> Compat_Mapdt_Binddt W T U;
    kdtmodf_bindd_compat :> Compat_Bindd_Binddt W T U;
    kdtmodf_bindt_compat :> Compat_Bindt_Binddt W T U;
  }.

Section MonadFull.

  #[local] Instance
    DecoratedTraversableMonadFull_DecoratedTraversableMonad
    (W : Type) (T : Type -> Type)
    `{Monad_inst : DecoratedTraversableMonad W T} :
  DecoratedTraversableMonadFull W T
    (Map_inst := Map_Binddt W T T)
    (Mapd_inst := Mapd_Binddt W T T)
    (Traverse_inst := Traverse_Binddt W T T)
    (Bind_inst := Bind_Binddt W T T)
    (Mapdt_inst := Mapdt_Binddt W T T)
    (Bindd_inst := Bindd_Binddt W T T)
    (Bindt_inst := Bindt_Binddt W T T)
  :=
  {| kdtmf_kmond := _
  |}.

  #[local] Instance DecoratedTraversableRightModuleFull_DecoratedTraversableRightModule
    (W : Type) (T : Type -> Type) (U : Type -> Type)
    `{Module_inst : DecoratedTraversableRightModule W T U} :
    DecoratedTraversableRightModuleFull W T U
    (Map_T_inst := Map_Binddt W T T)
    (Mapd_T_inst := Mapd_Binddt W T T)
    (Traverse_T_inst := Traverse_Binddt W T T)
    (Bind_T_inst := Bind_Binddt W T T)
    (Mapdt_T_inst := Mapdt_Binddt W T T)
    (Bindd_T_inst := Bindd_Binddt W T T)
    (Bindt_T_inst := Bindt_Binddt W T T)
    (Map_U_inst := Map_Binddt W T U)
    (Mapd_U_inst := Mapd_Binddt W T U)
    (Traverse_U_inst := Traverse_Binddt W T U)
    (Bind_U_inst := Bind_Binddt W T U)
    (Mapdt_U_inst := Mapdt_Binddt W T U)
    (Bindd_U_inst := Bindd_Binddt W T U)
    (Bindt_U_inst := Bindt_Binddt W T U) :=
    {| kdtmodf_kmond := _
    |}.

  #[local] Instance DecoratedTraversableRightModule_DecoratedTraversableMonad
    (W : Type) (T : Type -> Type)
    `{Monad_inst : DecoratedTraversableMonad W T} :
    DecoratedTraversableRightModule W T T :=
    {| kdtmod_premod := kdtm_premod ; |}.

  #[local] Instance DecoratedTraversableRightModuleFull_DecoratedTraversableMonadFull
    (W : Type) (T : Type -> Type)
    `{Monad_inst : DecoratedTraversableMonadFull W T} :
    DecoratedTraversableRightModuleFull W T T.
  Proof.
    constructor.
    - typeclasses eauto.
    - apply DecoratedTraversableRightModule_DecoratedTraversableMonad.
      apply kdtmf_kmond.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

End MonadFull.

(** * Tactical support (TODO move me) *)
(******************************************************************************)
Ltac unfold_map_id :=
  repeat (change (map (F := fun A => A) ?f) with f).

#[local] Hint Unfold kc7 kc6 kc5 kc4 kc3 kc2 kc1 : tealeaves_kc_unfold.

#[local] Ltac setup :=
  intros; autounfold with tealeaves_kc_unfold; ext [w a];
  unfold_map_id.

(** * Laws for Kleisli composition *)
(******************************************************************************)
Section kc7.

  Context
    `{Return T}
    `{Binddt W T T}
    `{op: Monoid_op W} `{unit: Monoid_unit W} `{! Monoid W}.

  (** ** Interaction with [incr], [preincr] *)
  (******************************************************************************)
  Section incr.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Lemma kc7_incr :
      forall `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)) (w : W),
        (g ∘ incr w) ⋆7 (f ∘ incr w) = (g ⋆7 f) ∘ incr w.
    Proof.
      intros. unfold kc7. ext [w' a].
      unfold preincr. reassociate ->.
      rewrite incr_incr.
      reflexivity.
    Qed.

    Lemma kc7_preincr :
      forall `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)) (w : W),
        (g ⦿ w) ⋆7 (f ⦿ w) = (g ⋆7 f) ⦿ w.
    Proof.
      intros. unfold preincr. rewrite kc7_incr.
      reflexivity.
    Qed.

  End incr.

  Context
    `{! DecoratedTraversableMonad W T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}
    {A B C D : Type}.

  (** ** Kleisi category laws *)
  (******************************************************************************)
  #[local] Set Typeclasses Iterative Deepening.

  (** *** Left identity *)
  (******************************************************************************)
  Lemma kc7_id1 : forall (f : W * A -> G (T B)),
      kc7 G (fun A => A) (ret (T := T) ∘ extract (W := (W ×))) f = f.
  Proof.
    setup.
    rewrite preincr_assoc.
    rewrite extract_preincr.
    rewrite kdtm_binddt1.
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

  (** *** Right identity *)
  (******************************************************************************)
  Lemma kc7_id2 : forall (g : W * A -> G (T B)),
      kc7 (fun A => A) G g (ret (T := T) ∘ extract (W := (W ×))) = g.
  Proof.
    setup.
    change_left ((binddt (T := T) (g ⦿ w) ∘ ret (T := T)) a).
    rewrite kdtm_binddt0.
    change (g (w ● Ƶ, a) = g (w, a)).
    simpl_monoid.
    reflexivity.
  Qed.

  (** *** Associativity *)
  (******************************************************************************)
  Lemma kc7_assoc :
    forall (h : W * C -> G3 (T D)) (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
      kc7 (G1 ∘ G2) G3 h (g ⋆7 f) = kc7 G1 (G2 ∘ G3) (h ⋆7 g) f.
  Proof.
    setup.
    unfold_ops @Map_compose.
    compose near (f (w, a)) on left.
    inversion H8.
    rewrite (fun_map_map (F := G1)).
    rewrite kdtm_binddt2.
    rewrite kc7_preincr.
    reflexivity.
  Qed.

End kc7.

(** * Interaction of <<binddt>> with composition in the applicative functor *)
(* TODO Move me to Theory/ *)
(******************************************************************************)
Section properties.

  Context
    `{DecoratedTraversableRightModule W T U}.

  Lemma binddt_app_l :
    forall {G : Type -> Type} {A B : Type}
      `{Applicative G} (f : W * A -> G (T B)),
      @binddt W T U _ ((fun A => A) ∘ G)
        (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G)
        (Mult_compose (fun A => A) G) A B f =
        binddt (T := T) f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma binddt_app_r :
    forall {G : Type -> Type} {A B : Type}
      `{Applicative G} (f : W * A -> G (T B)),
      @binddt W T U _ (G ∘ (fun A => A))
        (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A))
        (Mult_compose G (fun A => A)) A B f =
        binddt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity1 G).
  Qed.

End properties.

(** * Derived typeclass instances *)
(******************************************************************************)
Section derived_instances.

  Context
    `{op : Monoid_op W}
    `{unit : Monoid_unit W}
    `{ret_inst : Return T}
    `{Map_T_inst : Map T}
    `{Mapd_T_inst : Mapd W T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Mapdt_T_inst : Mapdt W T}
    `{Bindd_T_inst : Bindd W T T}
    `{Bindt_T_inst : Bindt T T}
    `{Binddt_T_inst : Binddt W T T}
    `{! Compat_Map_Binddt W T T}
    `{! Compat_Mapd_Binddt W T T}
    `{! Compat_Traverse_Binddt W T T}
    `{! Compat_Bind_Binddt W T T}
    `{! Compat_Mapdt_Binddt W T T}
    `{! Compat_Bindd_Binddt W T T}
    `{! Compat_Bindt_Binddt W T T}
    `{Monad_inst : ! DecoratedTraversableMonad W T}
    `{Map_U_inst : Map U}
    `{Mapd_U_inst : Mapd W U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Mapdt_U_inst : Mapdt W U}
    `{Bindd_U_inst : Bindd W T U}
    `{Bindt_U_inst : Bindt T U}
    `{Binddt_U_inst : Binddt W T U}
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Mapd_Binddt W T U}
    `{! Compat_Traverse_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    `{! Compat_Mapdt_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    `{! Compat_Bindt_Binddt W T U}
    `{Module_inst : ! DecoratedTraversableRightPreModule W T U}.

  (** ** Identity laws *)
  (******************************************************************************)
  Lemma bindd_id : forall A : Type,
      bindd (U := U) (ret ∘ extract (W := (W ×))) = @id (U A).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma bindt_id : forall A : Type,
      bindt (G := fun A => A) (ret (T := T)) = @id (U A).
  Proof.
    intros.
    rewrite bindt_to_binddt.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma mapdt_id : forall A : Type,
      mapdt (T := U) (G := fun A => A) (extract (W := (W ×))) = @id (U A).
  Proof.
    intros.
    rewrite (mapdt_to_binddt (G := fun A => A)).
    unfold_ops @Map_I.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma mapd_id : forall A : Type,
      mapd (extract (W := (W ×))) = @id (U A).
  Proof.
    intros.
    rewrite mapd_to_binddt.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma traverse_id : forall A : Type,
      traverse (T := T) (G := fun A => A) (@id A) = id.
  Proof.
    intros.
    rewrite traverse_to_binddt.
    change (?f ∘ id) with f.
    unfold_ops @Map_I.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma bind_id : forall A : Type,
      bind (ret (T := T)) = @id (U A).
  Proof.
    intros.
    rewrite bind_to_binddt.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma map_id : forall A : Type,
      map (F := U) (@id A) = @id (U A).
  Proof.
    intros.
    rewrite map_to_binddt.
    change (?f ∘ id) with f.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  (** ** Composition with <<ret>> *)
  (******************************************************************************)
  Lemma bindd_ret :
    forall (A B : Type) (f : W * A -> T B),
      bindd (T := T) f ∘ ret (T := T) = f ∘ ret (T := (W ×)).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite (kdtm_binddt0 (G := fun A => A)).
    reflexivity.
  Qed.

  Lemma bindt_ret :
    forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt f ∘ ret (T := T) = f.
  Proof.
    intros.
    rewrite bindt_to_binddt.
    rewrite kdtm_binddt0.
    reflexivity.
  Qed.

  Lemma bind_ret :
    forall (A B : Type) (f : A -> T B),
      bind f ∘ ret (T := T) = f.
  Proof.
    intros.
    rewrite bind_to_binddt.
    rewrite (kdtm_binddt0 (G := fun A => A)).
    reflexivity.
  Qed.

  (** ** Interaction with applicative morphisms *)
  (******************************************************************************)
  Section applicative_morphisms.

    Context
      (G1 G2 : Type -> Type)
        `{Map G1} `{Mult G1} `{Pure G1}
        `{Map G2} `{Mult G2} `{Pure G2}
        (ϕ : forall A : Type, G1 A -> G2 A)
        `{Hmorph : ! ApplicativeMorphism G1 G2 ϕ }.

    Lemma bindt_morph:
      forall (A B : Type) (f : A -> G1 (T B)),
        ϕ (U B) ∘ bindt f = bindt (ϕ (T B) ∘ f).
    Proof.
      intros.
      inversion Hmorph.
      rewrite bindt_to_binddt.
      rewrite (kdtm_morph G1 G2).
      reassociate <- on left.
      rewrite <- bindt_to_binddt.
      reflexivity.
    Qed.

    Lemma mapdt_morph:
      forall (A B : Type) (f : W * A -> G1 B),
        mapdt (ϕ B ∘ f) = ϕ (U B) ∘ mapdt (T := U) f.
    Proof.
      intros.
      inversion Hmorph.
      rewrite mapdt_to_binddt.
      reassociate <- on left.
      rewrite (natural (ϕ := ϕ)).
      reassociate -> on left.
      rewrite <- (kdtm_morph G1 G2).
      rewrite <- mapdt_to_binddt.
      reflexivity.
    Qed.

    Lemma traverse_morph:
      forall (A B : Type) (f : A -> G1 B),
        ϕ (T B) ∘ traverse (T := T) (G := G1) f = traverse (T := T) (G := G2) (ϕ B ∘ f).
    Proof.
      intros.
      inversion Hmorph.
      rewrite traverse_to_binddt.
      rewrite (kdtm_morph G1 G2).
      do 2 reassociate <- on left.
      rewrite <- (natural (ϕ := ϕ)).
      reassociate -> near f.
      rewrite <- traverse_to_binddt.
      reflexivity.
    Qed.

  End applicative_morphisms.

  (** ** Homogeneous Kleisli composition laws *)
  (******************************************************************************)
  Section composition.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Variables (A B C : Type).

    (** *** Lemmas <<kc7_xx>> *)
    (******************************************************************************)
    Lemma kc7_66 :
      forall (g : W * B -> G2 C) (f : W * A -> G1 B),
        (map (F := G2) (ret (T := T)) ∘ g) ⋆7
          (map (F := G1) (ret (T := T)) ∘ f) =
          map (F := G1 ∘ G2) (ret (T := T)) ∘ (g ⋆6 f).
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      (* LHS *)
      unfold compose at 2.
      compose near (f (w, a)).
      rewrite (fun_map_map (F := G1)).
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      (* RHS *)
      unfold kc6.
      unfold_ops @Map_compose.
      do 2 reassociate <- on right.
      unfold_compose_in_compose; rewrite (fun_map_map (F := G1)).
      unfold_ops @Cobind_reader; unfold strength.
      unfold compose at 3 4.
      compose near (f (w, a)) on right.
      rewrite (fun_map_map (F := G1)).
      reflexivity.
    Qed.

    Lemma kc7_55 : forall
        `(g : W * B -> T C) `(f : W * A -> T B),
        kc7 (fun A => A) (fun A => A) g f = g ⋆5 f.
    Proof.
      intros.
      unfold kc5.
      ext [w a].
      rewrite bindd_to_binddt.
      reflexivity.
    Qed.

    Lemma kc7_44 : forall
        `(g : W * B -> C) `(f : W * A -> B),
        kc7 (fun A => A) (fun A => A)
          (ret (T := T) ∘ g) (ret (T := T) ∘ f) =
          ret (T := T) ∘ (g ⋆4 f).
    Proof.
      intros.
      rewrite kc7_55.
      unfold kc5.
      ext [w a].
      unfold compose at 2.
      compose near (f (w, a)) on left.
      rewrite bindd_ret.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_33 :
      forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        kc7 G1 G2
          (g ∘ extract (W := (W ×)))
          (f ∘ extract (W := (W ×))) =
          (g ⋆3 f) ∘ extract (W := (W ×)).
    Proof.
      setup.
      rewrite bindt_to_binddt.
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    Lemma kc7_22 :
      forall (g : B -> G2 C) (f : A -> G1 B),
        kc7 G1 G2
          (map (F := G2) (ret (T := T)) ∘ g ∘ extract (W := (W ×)))
          (map (F := G1) (ret (T := T)) ∘ f ∘ extract (W := (W ×))) =
          map (F := G1 ∘ G2) (ret (T := T)) ∘
            (map (F := G1) g ∘ f) ∘ extract (W := (W ×)).
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      rewrite preincr_assoc.
      do 2 reassociate ->.
      rewrite extract_preincr.
      unfold compose at 1 2 3 4; cbn.
      compose near (f a) on left.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      unfold_ops @Map_compose.
      unfold compose; cbn.
      compose near (f a) on right.
      rewrite fun_map_map.
      reflexivity.
    Qed.

    Lemma kc7_11 :
      forall (g : B -> T C) (f : A -> T B),
        kc7 (fun A => A) (fun A => A)
          (g ∘ extract (W := (W ×)))
          (f ∘ extract (W := (W ×))) =
          (g ⋆1 f) ∘ extract (W := (W ×)).
    Proof.
      setup.
      rewrite (bind_to_binddt (T := T)).
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    Lemma kc7_00 :
      forall (g : B -> C) (f : A -> B),
        kc7 (fun A => A) (fun A => A)
          (ret (T := T) ∘ g ∘ extract (W := (W ×)))
          (ret (T := T) ∘ f ∘ extract (W := (W ×))) =
          (ret (T := T) ∘ g ∘ f ∘ extract (W := (W ×))).
    Proof.
      setup; unfold compose; cbn.
      compose near (f a) on left.
      unfold_ops @Map_I.
      rewrite (kdtm_binddt0 (T := T) (G := fun A => A)).
      rewrite preincr_ret.
      reflexivity.
    Qed.

  End composition.

  (** ** Homogeneous composition laws *)
  (******************************************************************************)
  Section composition.

    Context
      (G1 : Type -> Type) `{Map G1} `{Pure G1} `{Mult G1}
        `{! Applicative G1}
      (G2 : Type -> Type) `{Map G2} `{Pure G2} `{Mult G2}
      `{! Applicative G2}.

    Variables (A B C : Type).

    (* composition_66 *)
    Lemma mapdt_mapdt: forall
        (g : W * B -> G2 C)
        (f : W * A -> G1 B),
        map (F := G1) (A := U B) (B := G2 (U C))
          (mapdt (T := U) g) ∘ mapdt (T := U) f =
          mapdt (T := U) (G := G1 ∘ G2) (g ⋆6 f).
    Proof.
      intros.
      do 2 rewrite mapdt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_66.
      rewrite <- mapdt_to_binddt.
      reflexivity.
    Qed.

    (* composition_55 *)
    Lemma bindd_bindd : forall
        (g : W * B -> T C)
        (f : W * A -> T B),
        bindd g ∘ bindd (U := U) f = bindd (U := U) (g ⋆5 f).
    Proof.
      intros.
      do 2 rewrite bindd_to_binddt.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      change ((fun A => A) ?f) with f.
      rewrite (kdtm_binddt2 (T := T) (U := U) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite (binddt_app_l (T := T) (U := U)).
      rewrite kc7_55.
      rewrite <- bindd_to_binddt.
      reflexivity.
    Qed.

    (* composition_44 *)
    Lemma mapd_mapd : forall (g : W * B -> C) (f : W * A -> B),
        mapd g ∘ mapd f = mapd (g ∘ cobind (W := (W ×)) f).
    Proof.
      intros.
      do 2 rewrite mapd_to_binddt.
      change (binddt (ret (T := T) ∘ g)) with
        (map (F := fun A => A) (binddt (ret (T := T) ∘ g))).
      change ((fun A => A) ?f) with f.
      rewrite (kdtm_binddt2 (T := T) (U := U) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_44.
      rewrite <- mapd_to_binddt.
      reflexivity.
    Qed.

    (* composition_33 *)
    Lemma bindt_bindt :
      forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        map (F := G1) (bindt g) ∘ bindt f =
          bindt (U := U) (G := G1 ∘ G2) (g ⋆3 f).
    Proof.
      intros.
      do 2 rewrite bindt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_33.
      rewrite <- (bindt_to_binddt (A := A) (B := C)
                   (U := U) (T := T) (G := G1 ○ G2)).
      reflexivity.
    Qed.

    (* composition_22 *)
    Lemma traverse_traverse : forall (g : B -> G2 C) (f : A -> G1 B),
        map (F := G1) (traverse (G := G2) g) ∘ traverse (G := G1) f =
          traverse (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      intros.
      do 2 rewrite traverse_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_22.
      rewrite <- traverse_to_binddt.
      reflexivity.
    Qed.

    (* composition_11 *)
    Lemma bind_bind : forall (g : B -> T C) (f : A -> T B),
        bind g ∘ bind f = bind (U := U) (g ⋆1 f).
    Proof.
      intros.
      do 2 rewrite bind_to_binddt.
      change (binddt (g ∘ extract)) with
        (map (F := fun A => A) (binddt (g ∘ extract))).
      change ((fun A => A) ?f) with f.
      rewrite (kdtm_binddt2 (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_11.
      rewrite <- bind_to_binddt.
      reflexivity.
    Qed.

    (* composition_00 *)
    Lemma map_map : forall (f : A -> B) (g : B -> C),
        map g ∘ map f = map (F := U) (g ∘ f).
    Proof.
      intros.
      do 2 rewrite map_to_binddt.
      change (binddt (?ret ∘ g ∘ ?extract)) with
        (map (F := fun A => A) (binddt (ret ∘ g ∘ extract))).
      change ((fun A => A) ?f) with f.
      rewrite (kdtm_binddt2 (T := T) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_00.
      change (?ret ∘ g ∘ f ∘ ?extract) with
        (ret ∘ (g ∘ f) ∘ extract).
      rewrite <- map_to_binddt.
      reflexivity.
    Qed.

  End composition.

End derived_instances.

Section derived_instances.

    Context
      (W : Type)
      (T : Type -> Type)
      `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Mapd_T_inst : Mapd W T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Mapdt_T_inst : Mapdt W T}
      `{Bindd_T_inst : Bindd W T T}
      `{Bindt_T_inst : Bindt T T}
      `{Binddt_T_inst : Binddt W T T}
      `{! Compat_Map_Binddt W T T}
      `{! Compat_Mapd_Binddt W T T}
      `{! Compat_Traverse_Binddt W T T}
      `{! Compat_Bind_Binddt W T T}
      `{! Compat_Mapdt_Binddt W T T}
      `{! Compat_Bindd_Binddt W T T}
      `{! Compat_Bindt_Binddt W T T}
      `{Monad_inst : ! DecoratedTraversableMonad W T}
      `{Map_U_inst : Map U}
      `{Mapd_U_inst : Mapd W U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Mapdt_U_inst : Mapdt W U}
      `{Bindd_U_inst : Bindd W T U}
      `{Bindt_U_inst : Bindt T U}
      `{Binddt_U_inst : Binddt W T U}
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Mapd_Binddt W T U}
      `{! Compat_Traverse_Binddt W T U}
      `{! Compat_Bind_Binddt W T U}
      `{! Compat_Mapdt_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U}
      `{! Compat_Bindt_Binddt W T U}
      `{Module_inst : ! DecoratedTraversableRightPreModule W T U}.

  (** ** Derived typeclass instances *)
  (******************************************************************************)
  #[export] Instance: DecoratedRightPreModule W T U :=
    {| kmodd_bindd1 := bindd_id;
       kmodd_bindd2 := bindd_bindd;
    |}.

  #[export] Instance: DecoratedRightPreModule W T T :=
    {| kmodd_bindd1 := bindd_id;
       kmodd_bindd2 := bindd_bindd;
    |}.

  #[export] Instance: DecoratedMonad W T :=
    {| kmond_bindd0 := bindd_ret;
    |}.

  #[export] Instance: DecoratedRightModule W T T :=
    {| kmodd_monad := _
    |}.

  #[export] Instance: DecoratedRightModule W T U :=
    {| kmodd_monad := _
    |}.

  #[export] Instance: TraversableRightPreModule T U :=
    {| ktm_bindt1 := bindt_id;
      ktm_bindt2 := bindt_bindt;
      ktm_morph := bindt_morph;
    |}.

  #[export] Instance: TraversableRightPreModule T T :=
    {| ktm_bindt1 := bindt_id;
      ktm_bindt2 := bindt_bindt;
      ktm_morph := bindt_morph;
    |}.

  #[export] Instance: TraversableMonad T :=
    {| ktm_bindt0 := bindt_ret;
    |}.

  #[export] Instance: TraversableRightModule T U :=
    {| ktmod_monad := _
    |}.

  #[export] Instance: DecoratedTraversableFunctor W T :=
    {| kdtfun_mapdt1 := mapdt_id;
      kdtfun_mapdt2 := mapdt_mapdt;
      kdtfun_morph := mapdt_morph;
    |}.

  #[export] Instance: DecoratedTraversableFunctor W U :=
    {| kdtfun_mapdt1 := mapdt_id;
      kdtfun_mapdt2 := mapdt_mapdt;
      kdtfun_morph := mapdt_morph;
    |}.

End derived_instances.

(** * Other composition laws *)
(******************************************************************************)
Section other_composition_laws.

  Context
    `{op : Monoid_op W}
    `{unit : Monoid_unit W}
    `{ret_inst : Return T}
    `{Map_T_inst : Map T}
    `{Mapd_T_inst : Mapd W T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Mapdt_T_inst : Mapdt W T}
    `{Bindd_T_inst : Bindd W T T}
    `{Bindt_T_inst : Bindt T T}
    `{Binddt_T_inst : Binddt W T T}
    `{! Compat_Map_Binddt W T T}
    `{! Compat_Mapd_Binddt W T T}
    `{! Compat_Traverse_Binddt W T T}
    `{! Compat_Bind_Binddt W T T}
    `{! Compat_Mapdt_Binddt W T T}
    `{! Compat_Bindd_Binddt W T T}
    `{! Compat_Bindt_Binddt W T T}
    `{Monad_inst : ! DecoratedTraversableMonad W T}
    `{Map_U_inst : Map U}
    `{Mapd_U_inst : Mapd W U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Mapdt_U_inst : Mapdt W U}
    `{Bindd_U_inst : Bindd W T U}
    `{Bindt_U_inst : Bindt T U}
    `{Binddt_U_inst : Binddt W T U}
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Mapd_Binddt W T U}
    `{! Compat_Traverse_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    `{! Compat_Mapdt_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    `{! Compat_Bindt_Binddt W T U}
    `{Module_inst : ! DecoratedTraversableRightPreModule W T U}.

  (** ** Rewriting rules for special cases of <<kc7>> *)
  (******************************************************************************)
  Section kc7_special_cases.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C D : Type}.

    Ltac kdtmf_normalize_T :=
      repeat
        ( rewrite (map_to_binddt (U := T) (T := T)) ||
            rewrite (bind_to_binddt (U := T) (T := T)) ||
              rewrite (traverse_to_binddt (U := T) (T := T)) ||
                rewrite (mapd_to_binddt (U := T) (T := T)) ||
                  rewrite (mapdt_to_binddt (U := T) (T := T)) ||
                    rewrite (bindd_to_binddt (U := T) (T := T)) ||
                      rewrite (bindt_to_binddt (U := T) (T := T))).

    Ltac solve_kc7 :=
      setup;
      kdtmf_normalize_T;
      try (reflexivity ||
             rewrite preincr_assoc;
           rewrite extract_preincr;
           reflexivity).

    (** *** Lemmas <<kc7_x7>> *)
    (******************************************************************************)
    Lemma kc7_07 :
      forall (g : B -> C) (f : W * A -> G1 (T B)),
        ret (T := T) ∘ g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1) (map (F := T) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_17 :
      forall (g : B -> T C) (f : W * A -> G1 (T B)),
        g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1) (bind (U := T) (T := T) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_27 :
      forall (g : B -> G2 C) (f : W * A -> G1 (T B)),
        map (F := G2) (ret (T := T)) ∘ g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1) (traverse (T := T) (G := G2) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_37 :
      forall (g : B -> G2 (T C)) (f : W * A -> G1 (T B)),
        (g ∘ extract (W := (W ×))) ⋆7 f = g ⋆3 f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_47 :
      forall (g : W * B -> C) (f : W * A -> G1 (T B)),
        kc7 G1 (fun A => A) (ret (T := T) ∘ g) f =
          (fun '(w, a) => map (F := G1) (mapd (g ⦿ w)) (f (w, a))).
    Proof.
      solve_kc7.
    Qed.


    Lemma kc7_57 :
      forall (g : W * B -> T C) (f : W * A -> G1 (T B)),
        kc7 G1 (fun A => A) g f = g ⋆7 f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc7_67 :
      forall (g : W * B -> G2 C) (f : W * A -> G1 (T B)),
        (map (F := G2) (ret (T := T)) ∘ g) ⋆7 f =
          (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f (w, a))).
    Proof.
      solve_kc7.
    Qed.

    (** *** Lemmas <<kc7_7x>> *)
    (******************************************************************************)
    Lemma kc7_76 :
      forall (g : W * B -> G2 (T C)) (f : W * A -> G1 B),
        g ⋆7 (map (F := G1) ret ∘ f) = g ⋆6 f.
    Proof.
      intros. unfold kc7, kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)).
      rewrite fun_map_map.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_75 :
      forall (g : W * B -> G2 (T C)) (f : W * A -> T B),
        kc7 (fun A => A) G2 g f = fun '(w, a) => binddt (g ⦿ w) (f (w, a)).
    Proof.
      reflexivity.
    Qed.

    Lemma kc7_74 :
      forall (g : W * B -> G2 (T C)) (f : W * A -> B),
        kc7 (fun A => A) G2 g (ret (T := T) ∘ f) = g ⋆4 f.
    Proof.
      intros. unfold kc7.
      ext [w a].
      unfold compose at 1.
      compose near (f (w, a)).
      change (map (F := fun A => A) ?f) with f.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_73 :
      forall (g : W * B -> G2 (T C)) (f : A -> G1 (T B)),
        g ⋆7 (f ∘ extract (W := (W ×))) =
          fun '(w, a) => map (F := G1) (binddt (g ⦿ w)) (f a).
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_72 :
      forall (g : W * B -> G2 (T C)) (f : A -> G1 B),
        g ⋆7 (map (F := G1) ret ∘ f ∘ extract (W := (W ×))) =
          fun '(w, a) => map (F := G1) (g ∘ pair w) (f a).
    Proof.
      setup.
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_71 :
      forall (g : W * B -> G2 (T C)) (f : A -> T B),
        kc7 (fun A => A) G2 g (f ∘ extract (W := (W ×))) =
          fun '(w, a) => binddt (g ⦿ w) (f a).
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_70 :
      forall (g : W * B -> G2 (T C)) (f : A -> B),
        kc7 (fun A => A) G2 g (ret (T := T) ∘ f ∘ extract (W := (W ×))) =
          g ∘ map (F := (W ×)) f.
    Proof.
      setup.
      unfold compose; cbn.
      compose near (f a) on left.
      change (map (F := fun A => A) ?f) with f.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    (** *** Other lemmas *)
    (******************************************************************************)
    Lemma kc7_56 :
      forall (g : W * B -> T C) (f : W * A -> G1 B),
        g ⋆7 map (F := G1)(ret (T := T)) ∘ f =
          (fun '(w, a) => map (F := G1) (g ∘ pair w) (f (w, a))).
    Proof.
      setup.
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite fun_map_map.
      rewrite (kdtm_binddt0 (G := fun A => A)).
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_36 :
      forall (g : B -> G2 (T C)) (f : W * A -> G1 B),
        g ∘ extract ⋆7 map ret ∘ f = map g ∘ f.
    Proof.
      setup.
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

  End kc7_special_cases.

  Section composition_special_cases_top.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<binddt>> purity *)
    (******************************************************************************)
    Lemma binddt_pure:
      forall (A : Type) `{Applicative G},
        binddt (pure (F := G) ∘ ret (T := T) (A := A) ∘ extract) =
          pure (F := G).
    Proof.
      intros.
      reassociate -> on left.
      rewrite <- (kdtm_morph (fun A => A) G (ϕ := @pure G _)).
      rewrite kdtm_binddt1.
      reflexivity.
    Qed.

    (** *** <<binddt>> on the right *)
    (******************************************************************************)
    (* composition_67 *)
    Lemma mapdt_binddt:
      forall (g : W * B -> G2 C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (mapdt g) ∘ binddt f =
          binddt (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_67.
      reflexivity.
    Qed.

    (* composition_57 *)
    Lemma bindd_binddt:
      forall (g : W * B -> T C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (bindd g) ∘ binddt f =
          binddt (fun '(w, a) => map (F := G1) (bindd (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      rewrite bindd_to_binddt.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite binddt_app_r.
      unfold kc7.
      reflexivity.
    Qed.

    (* composition_47 *)
    Lemma mapd_binddt: forall
        (g : W * B -> C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (mapd g) ∘ binddt f =
          binddt (fun '(w, a) => map (F := G1) (mapd (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite mapd_to_binddt.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite binddt_app_r.
      rewrite kc7_47.
      reflexivity.
    Qed.

    (* composition_37 *)
    Lemma bindt_binddt:
      forall (g : B -> G2 (T C))
        (f : W * A -> G1 (T B)),
        map (F := G1) (bindt g) ∘ binddt f =
          binddt (G := G1 ∘ G2) (map (F := G1) (bindt g) ∘ f).
    Proof.
      intros.
      rewrite bindt_to_binddt at 1.
      rewrite kdtm_binddt2.
      rewrite kc7_37.
      reflexivity.
    Qed.

    (* composition_27 *)
    Lemma traverse_binddt: forall
        (g : B -> G2 C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (traverse (T := T) (G := G2) g) ∘ binddt f =
          binddt (T := T) (G := G1 ∘ G2) (map (F := G1) (traverse (T := T) (G := G2)  g) ∘ f).
    Proof.
      intros.
      rewrite traverse_to_binddt at 1.
      rewrite kdtm_binddt2.
      rewrite kc7_27.
      reflexivity.
    Qed.

    (* composition_17 *)
    Lemma bind_binddt: forall
        (g : B -> T C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (bind g) ∘ binddt f =
          binddt (map (F := G1) (bind g) ∘ f).
    Proof.
      intros.
      rewrite bind_to_binddt at 1.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite kc7_17.
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (* composition_07 *)
    Lemma map_binddt:
      forall (g : B -> C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (map (F := U) g) ∘ binddt f =
          binddt (map (F := G1) (map (F := T) g) ∘ f).
    Proof.
      intros.
      rewrite (map_to_binddt (U := U)).
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite kc7_07.
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (** *** <<binddt>> on the left *)
    (******************************************************************************)
    (* composition_76 *)
    Lemma binddt_mapdt: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> G1 B),
        map (F := G1) (binddt g) ∘ mapdt f =
          binddt (U := U) (G := G1 ∘ G2)
            (fun '(w, a) => map (F := G1) (fun b => g (w, b)) (f (w, a))).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_76.
      rewrite kc6_spec.
      reflexivity.
    Qed.

    (* composition_75 *)
    Lemma binddt_bindd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> T B),
        binddt g ∘ bindd f =
          binddt (U := U) (fun '(w, a) => binddt (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_l.
      reflexivity.
    Qed.

    (* composition_74 *)
    Lemma binddt_mapd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> B),
        binddt g ∘ mapd f = binddt (g ⋆4 f).
    Proof.
      intros.
      rewrite mapd_to_binddt.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite kc7_74.
      rewrite binddt_app_l.
      reflexivity.
    Qed.

    (* composition_73 *)
    Lemma binddt_bindt: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 (T B)),
        map (F := G1) (binddt g) ∘ bindt f =
          binddt (T := T) (G := G1 ∘ G2)
            (fun '(w, a) => map (F := G1) (binddt (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite bindt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_73.
      reflexivity.
    Qed.

    (* composition_72 *)
    Lemma binddt_traverse: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 B),
        map (F := G1) (binddt g) ∘ traverse (T := U) (G := G1) f =
          binddt (G := G1 ∘ G2)
            (fun '(w, a) => map (F := G1) (fun b => g (w, b)) (f a)).
    Proof.
      intros.
      rewrite traverse_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_72.
      reflexivity.
    Qed.

    (* composition_71 *)
    Lemma binddt_bind: forall
        (g : W * B -> G2 (T C))
        (f : A -> T B),
        binddt g ∘ bind f =
          binddt (U := U) (fun '(w, a) => binddt (g ⦿ w) (f a)).
    Proof.
      intros.
      rewrite bind_to_binddt.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_71.
      reflexivity.
    Qed.

    (* composition_70 *)
    Lemma binddt_map: forall
        (g : W * B -> G2 (T C))
        (f : A -> B),
        binddt g ∘ map (F := U) f =
          binddt (U := U) (g ∘ map (F := (W ×)) f).
    Proof.
      intros.
      rewrite (map_to_binddt (U := U)).
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_70.
      reflexivity.
    Qed.

  End composition_special_cases_top.

  Section composition_special_cases_middle.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<bindd>>, <<mapdt>>, <<bindt>> *)
    (******************************************************************************)
    (* composition_56 *)
    Lemma bindd_mapdt: forall
        (g : W * B -> T C)
        (f : W * A -> G1 B),
        map (F := G1) (bindd g) ∘ mapdt f =
          binddt (U := U) (fun '(w, a) => map (F := G1) (g ∘ pair w) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      rewrite (binddt_mapdt (G2 := fun A => A)).
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (* composition_65 *)
    Lemma mapdt_bindd: forall
        (g : W * B -> G2 C)
        (f : W * A -> T B),
        mapdt g ∘ bindd f =
          binddt (U := U) (fun '(w, a) => mapdt (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite binddt_bindd.
      fequal. ext [w a]. (* TODO can this be improved? *)
      rewrite mapdt_to_binddt.
      reflexivity.
    Qed.

    (* composition_35 *)
    Lemma bindt_bindd: forall
        (g : B -> G2 (T C))
        (f : W * A -> T B),
        bindt g ∘ bindd f = binddt (U := U) (bindt g ∘ f).
    Proof.
      intros.
      rewrite bindt_to_binddt.
      rewrite bindt_to_binddt.
      rewrite binddt_bindd.
      fequal. ext [w a].
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    (* composition_53 *)
    Lemma bindd_bindt: forall
        (g : W * B -> T C)
        (f : A -> G1 (T B)),
        map (F := G1) (bindd g) ∘ bindt f =
          binddt (U := U) (fun '(w, a) => map (F := G1) (bindd (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      rewrite bindt_to_binddt.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite binddt_app_r.
      rewrite bindd_to_binddt.
      reflexivity.
    Qed.

    (* composition_63 *)
    Lemma mapdt_bindt: forall
        (g : W * B -> G2 C)
        (f : A -> G1 (T B)),
        map (F := G1) (mapdt g) ∘ bindt f =
          binddt (U := U) (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite bindt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_73.
      rewrite (compat_mapdt_binddt W T T).
      reflexivity.
      rewrite compat
      rewrite (mapdt_to_binddt
                 (W := W) (T := T) (U := T) (A := B) (B := C)
                 (Mapdt_inst := Mapdt_T_inst)
                 (G := G2)
                 (H := H3)
                 (H0 := H4)
                 (H1 := H5)
                 (@preincr W op B (G2 C) g w)
              ).
      About mapdt_to_binddt.
      rewrite (@mapdt_to_binddt _ _ W T Mapdt_T_inst).
      reflexivity.
    Qed.

    (* composition_36 *)
    Lemma bindt_mapdt: forall
        (g : B -> G2 (T C))
        (f : W * A -> G1 B),
        map (F := G1) (bindt g) ∘ mapdt f =
          binddt (U := U) (G := G1 ∘ G2) (map (F := G1) g ∘ f).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite bindt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_36.
      reflexivity.
    Qed.

  End composition_special_cases_middle.

  (* The lemmas below can cite the ones above *)
  Section composition_special_cases_bottom.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<bindd>> on the right *)
    (******************************************************************************)

    (* composition_25 *)
    Lemma traverse_bindd: forall
        (g : B -> G2 C)
        (f : W * A -> T B),
        traverse (T := U) (G := G2) g ∘ bindd f =
          binddt (fun '(w, a) => traverse (T := T) (G := G2) g (f (w, a))).
    Proof.
      (* TODO Use traverse_to_bindt to solve simpler  *)
      intros.
      rewrite traverse_to_binddt.
      rewrite bindd_to_binddt.
      change (binddt (?mapret ∘ g ∘ ?extract)) with
        (map (F := fun A => A) (binddt (mapret ∘ g ∘ extract))).
      rewrite (kdtm_binddt2 (T := T) (G1 := fun A => A)).
      rewrite (binddt_app_l).
      fequal. ext [w a].
      unfold kc7.
      rewrite preincr_assoc.
      rewrite extract_preincr.
      rewrite traverse_to_binddt.
      reflexivity.
    Qed.

    (* composition_52 *)
    (* TODO bindd_traverse *)

    (* composition_43 *)
    Lemma mapd_bindt : forall (g : W * B -> C) (f : A -> G1 (T B)),
        map (F := G1) (mapd g) ∘ bindt (G := G1) f =
        binddt (U := U) (fun '(w, a) => map (F := G1) (mapd (g ⦿ w)) (f a)).
    Proof.
      introv.
      rewrite mapd_to_mapdt.
      rewrite (mapdt_bindt (G2 := fun A => A)).
      rewrite binddt_app_r.
      fequal. ext [w a].
      rewrite mapd_to_mapdt.
      reflexivity.
    Qed.
    (* composition_34 *)
    (* TODO bindt_mapd *)

    (* composition_16 *)
    (* TODO bind_mapdt *)

    (* composition_61 *)
    (* TODO mapdt_bind *)

  End composition_special_cases_bottom.

End other_composition_laws.


(** * Theory of DTMs *)
(******************************************************************************)
Section lemmas.

  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Monoid_inst: ! Monoid W}.

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

  (** ** Composition in the applicative functor *)
  (******************************************************************************)
  Lemma binddt_app_const_r:
    forall {G : Type -> Type}
      `{Monoid M} {A B : Type} `{Applicative G} (f : W * A -> G M),
      @binddt W T U _ (G ∘ const M)
        (Map_compose G (const M))
        (Pure_compose G (const M))
        (Mult_compose G (const M)) A B f =
        binddt (U := U) (G := const (G M)) (B := B) f.
  Proof.
    intros. fequal.
    - ext X Y h x.
      unfold_ops @Map_compose @Map_const.
      now rewrite (fun_map_id (Functor := app_functor)).
    - ext X Y [x y].
      unfold_ops @Mult_compose @Mult_const.
      unfold_ops @Monoid_op_applicative.
      reflexivity.
  Qed.

  (** ** Lemmas for particular applicative functors *)
  (******************************************************************************)

  (** *** <<binddt>> with constant applicative functors *)
  (******************************************************************************)
  Section constant_applicative.

    Context `{Monoid M}.

    Lemma binddt_constant_applicative1 {A B : Type}
      `(f : W * A -> const M (T B)) :
      binddt (T := T) (U := U) f =
        binddt (T := T) (U := U) (B := False) f.
    Proof.
      change_right (map (F := const M) (A := U False) (B := U B)
                      (map (F := U) (A := False) (B := B) exfalso)
                      ∘ binddt (T := T) (U := U) (B := False) f).
      rewrite (map_binddt (G1 := const M)).
      reflexivity.
    Qed.

    Lemma binddt_constant_applicative2 (fake1 fake2 : Type)
      `(f : W * A -> const M (T B)) :
      binddt (T := T) (U := U) (B := fake1) f =
        binddt (T := T) (U := U) (B := fake2) f.
    Proof.
      intros.
      rewrite (binddt_constant_applicative1 (B := fake1)).
      rewrite (binddt_constant_applicative1 (B := fake2)).
      reflexivity.
    Qed.

  End constant_applicative.


  (** ** Properties of <<foldMapd>> *)
  (******************************************************************************)

  (** *** Composition with monad operattions *)
  (******************************************************************************)
  Theorem foldMapd_ret `{Monoid M} : forall `(f : W * A -> M),
      foldMapd (T := T) f ∘ ret = f ∘ ret.
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1. (* todo get rid of this arg *)
    rewrite mapdt_to_binddt.
    rewrite (kdtm_binddt0 (G := const M) (A := A) (B := False)).
    reflexivity.
  Qed.

  Theorem foldMapd_binddt `{Applicative G} `{Monoid M} :
    forall `(g : W * B -> M) `(f : W * A -> G (T B)),
      map (foldMapd g) ∘ binddt f =
        foldMapd (fun '(w, a) => map (foldMapd (g ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    rewrite (kdtm_binddt2 (G2 := const M) (G1 := G)). (* TODO args *)
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    rewrite binddt_app_const_r.
    unfold foldMapd.
    (* TODO Make mapdt_to_binddt work immediately here *)
    fequal. ext [w a].
    unfold compose. cbn.
    rewrite mapdt_to_binddt.
    reflexivity.
  Qed.

  Corollary foldMap_binddt `{Applicative G} `{Monoid M} :
    forall `(g : B -> M) `(f : W * A -> G (T B)),
      map (foldMap g) ∘ binddt f =
        foldMapd (fun '(w, a) => map (foldMap g) (f (w, a))).
  Proof.
    intros.
    rewrite foldMap_to_foldMapd.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_binddt.
    fequal; ext [w a].
    rewrite extract_preincr2.
    reflexivity.
  Qed.

  Corollary foldMapd_binddt_I `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd g ∘ binddt (U := U) (G := fun A => A) f =
        foldMapd (T := U) (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
  Proof.
    intros.
    change (foldMapd g) with (map (F := fun A => A) (foldMapd (T := U) g)).
    rewrite (foldMapd_binddt (G := fun A => A)).
    reflexivity.
  Qed.

  Corollary foldMapd_bindd `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd g ∘ bindd f =
        foldMapd (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite foldMapd_binddt_I.
    reflexivity.
  Qed.

  Corollary foldMap_bindd `{Monoid M} : forall `(g : B -> M) `(f : W * A -> T B),
      foldMap g ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap g (f (w, a))).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_binddt_I.
    fequal; ext [w a].
    rewrite extract_preincr2.
    rewrite foldMap_to_foldMapd.
    reflexivity.
  Qed.

  (** ** <<tolistd>> *)
  (******************************************************************************)

  (** *** Relating <<tolistd>> and <<binddt>> / <<ret>> *)
  (******************************************************************************)
  Lemma toctxlist_ret : forall (A : Type) (a : A),
      toctxlist (ret (T := T) a) = [ (Ƶ, a) ].
  Proof.
    intros.
    rewrite toctxlist_to_foldMapd.
    compose near a on left.
    rewrite foldMapd_ret.
    reflexivity.
  Qed.

  Lemma toctxlist_binddt : forall `{Applicative G} `(f : W * A -> G (T B)),
      map (F := G) toctxlist ∘ binddt (G := G) f =
        foldMapd (T := U)
          (fun '(w, a) => map (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite toctxlist_to_foldMapd.
    rewrite foldMapd_binddt.
    reflexivity.
  Qed.

  Lemma toctxlist_bindd : forall `(f : W * A -> T B),
      toctxlist ∘ bindd f =
        foldMapd (T := U) (fun '(w, a) => (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite toctxlist_to_foldMapd.
    rewrite foldMapd_bindd.
    reflexivity.
  Qed.

  (** *** Corollaries for the rest *)
  (******************************************************************************)
  Corollary tolist_binddt : forall `{Applicative G} `(f : W * A -> G (T B)),
      map tolist ∘ binddt f = foldMapd (T := U) (map tolist ∘ f).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_binddt.
    (* todo why isn't reflexivity enough... b.c. destructing the pair? *)
    fequal. ext [w a].
    reflexivity.
  Qed.

  Corollary tolist_bindd : forall `(f : W * A -> T B),
      tolist ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap (ret (T := list)) (f (w, a))).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_bindd.
    reflexivity.
  Qed.

  Corollary tolist_to_binddt : forall (A : Type),
      tolist = binddt (G := const (list A))
                 (B := False) (ret (T := list) ∘ extract).
  Proof.
    intros.
    rewrite tolist_to_traverse1.
    rewrite traverse_to_binddt.
    reflexivity.
  Qed.

  (** ** Relating <<toctxset>>  *)
  (******************************************************************************)
  Corollary toctxset_ret : forall (A : Type) (a : A),
      toctxset (ret (T := T) a) = {{ (Ƶ, a) }}.
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    compose near a on left.
    rewrite foldMapd_ret.
    reflexivity.
  Qed.

  Lemma toctxset_bindd:
    forall `(f : W * A -> T B),
      toctxset ∘ bindd (T := T) (U := U) f =
        bindd (U := ctxset W) (toctxset (F := T) ∘ f) ∘ toctxset (F := U).
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_bindd.
    rewrite toctxset_to_foldMapd.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_morphism.
    fequal.
    ext [w a].
    change_right
      (bindd (T := ctxset W) (foldMapd (ret (T := subset)) ∘ f) {{(w, a)}}).
    rewrite bindd_ctxset_one.
    unfold compose.
    rewrite (DecoratedFunctor.shift_spec subset
               (W := W) (op := op) (A := B)).
    compose near (f (w, a)) on right.
    rewrite foldMapd_morphism.
    rewrite (natural (ϕ := @ret subset _)).
    reflexivity.
  Qed.

  Lemma tosubset_bindd : forall `(f : W * A -> T B),
      tosubset ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap (ret (T := subset)) (f (w, a))).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_bindd.
    reflexivity.
  Qed.

  (** ** Set operations to binddt *)
  (******************************************************************************)
  Corollary toctxset_to_binddt : forall (A: Type),
      toctxset (F := U) = binddt (G := const (subset (W * A)))
                     (B := False) (ret (T := subset)).
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    reflexivity.
  Qed.

  Corollary tosubset_to_binddt : forall (A: Type),
      tosubset = binddt (G := const (subset A))
                     (B := False) (ret (T := subset) ∘ extract).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_to_traverse1.
    rewrite traverse_to_binddt.
    reflexivity.
  Qed.

  (** ** Characterizing <<∈d>> *)
  (******************************************************************************)
  Lemma element_ctx_of_ret: forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret (T := T) a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros.
    unfold element_ctx_of.
    rewrite toctxset_ret.
    unfold subset_one.
    rewrite pair_equal_spec.
    easy.
  Qed.

  Corollary element_of_to_binddt: forall (A: Type) (t: U A) (a: A),
      a ∈ t = binddt (G := const Prop)
                (H0 := @Pure_const Prop Monoid_unit_false)
                (H1 := @Mult_const Prop Monoid_op_or)
                (B := False) (eq a ∘ extract) t.
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite foldMap_to_traverse1.
    rewrite traverse_to_binddt.
    reflexivity.
  Qed.

  Corollary element_ctx_of_to_binddt: forall (A: Type) (t: U A) (w: W) (a: A),
      (w, a) ∈d t = binddt (G := const Prop)
                      (H0 := @Pure_const Prop Monoid_unit_false)
                      (H1 := @Mult_const Prop Monoid_op_or)
                      (B := False) (eq (w, a)) t.
  Proof.
    intros.
    rewrite element_ctx_of_to_foldMapd.
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    reflexivity.
  Qed.

End lemmas.

Section instances.

  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Monoid_inst: ! Monoid W}.

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

  #[export] Instance:
    DecoratedMonadHom W T (ctxset W) (@toctxset W T _).
  Proof.
    constructor.
    - intros.
      rewrite toctxset_bindd.
      reflexivity.
    - intros.
      ext a [w a']. unfold compose.
      rewrite toctxset_ret.
      cbv.
      apply propositional_extensionality.
      rewrite pair_equal_spec.
      easy.
  Qed.

  #[export] Instance DTM_ctxset_DecoratedMonadHom:
    DecoratedMonadHom W T (ctxset W) (@toctxset W T _).
  Proof.
    constructor.
    - intros.
      rewrite toctxset_bindd.
      reflexivity.
    - intros.
      ext a [w a']. unfold compose.
      rewrite toctxset_ret.
      cbv.
      apply propositional_extensionality.
      rewrite pair_equal_spec.
      easy.
  Qed.

  #[export] Instance DTM_ctxset_DecoratedModuleHom:
    ParallelDecoratedRightModuleHom
      T (ctxset W) U (ctxset W)
      (@toctxset W T _) (@toctxset W U _).
  Proof.
    constructor.
    intros.
    rewrite toctxset_bindd.
    reflexivity.
  Qed.

End instances.
