From Tealeaves Require Export
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.Theory.Monad.

Import DecoratedMonad.Notations.
Import Kleisli.Comonad.Notations.
Import Kleisli.Monad.Notations.
Import Product.Notations.

#[local] Generalizable Variables W T U A B C.

(** * Kleisli category *)
(******************************************************************************)
Section DecoratedMonad_kleisli_category.

  Context
    (T: Type -> Type)
    `{DecoratedMonad W T}.

  (** ** Interaction with [incr], [preincr] *)
  (******************************************************************************)
  Lemma kc5_incr : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      (g ∘ incr w) ⋆5 (f ∘ incr w) = (g ⋆5 f) ∘ incr w.
  Proof.
    intros.
    unfold kc5.
    ext [w' a].
    unfold preincr.
    reassociate ->.
    rewrite incr_incr.
    reflexivity.
  Qed.

  Lemma kc5_preincr : forall `(g : W * B -> T C) `(f : W * A -> T B) (w : W),
      (g ⋆5 f) ⦿ w = g ⦿ w ⋆5 f ⦿ w.
  Proof.
    intros.
    unfold preincr.
    rewrite kc5_incr.
    reflexivity.
  Qed.

  (** ** Right identity law *)
  (******************************************************************************)
  Theorem kc5_id_r {B C} : forall (g : W * B -> T C),
      g ⋆5 (ret ∘ extract) = g.
  Proof.
    intros.
    unfold kc5.
    ext [w a].
    unfold compose; cbn.
    compose near a on left.
    rewrite kdm_bindd0.
    rewrite preincr_ret.
    reflexivity.
  Qed.

  (** ** Left identity law *)
  (******************************************************************************)
  Theorem kc5_id_l {A B} : forall (f : W * A -> T B),
      (ret ∘ extract) ⋆5 f = f.
  Proof.
    intros.
    unfold kc5.
    ext [w a].
    rewrite preincr_assoc.
    rewrite extract_preincr.
    rewrite kdm_bindd1.
    reflexivity.
  Qed.

  (** ** Associativity law *)
  (******************************************************************************)
  Theorem kc5_assoc {A B C D} : forall (h : W * C -> T D) (g : W * B -> T C) (f : W * A -> T B),
      h ⋆5 (g ⋆5 f) = (h ⋆5 g) ⋆5 f.
  Proof.
    intros. unfold kc5.
    ext [w a].
    compose near (f (w, a)) on left.
    rewrite kdm_bindd2.
    rewrite <- kc5_preincr.
    reflexivity.
  Qed.

End DecoratedMonad_kleisli_category.

(** * Derived instances *)
(******************************************************************************)
Section operations.

  Section operations.

    Context
      W T U
      `{Return_inst : Return T}
      `{Bindd_inst : Bindd W T U}.

    #[local] Instance Map_Bindd: Map U :=
      fun A B f => bindd (ret ∘ f ∘ extract).
    #[local] Instance Bind_Bindd: Bind T U :=
      fun A B f => bindd (f ∘ extract).
    #[local] Instance Mapd_Bindd: Mapd W U :=
      fun A B f => bindd (ret ∘ f).

  End operations.

  Section compat.

    Context
      (W: Type)
        (T: Type -> Type)
        (U: Type -> Type)
        `{Map_U: Map U}
        `{Bind_TU: Bind T U}
        `{Mapd_WU: Mapd W U}
        `{Return_T: Return T}
        `{Bindd_WTU: Bindd W T U}.

    Class Compat_Map_Bindd: Prop :=
      compat_map_bindd: Map_U = @Map_Bindd W T U Return_T Bindd_WTU.

    Class Compat_Mapd_Bindd: Prop :=
      compat_mapd_bindd: Mapd_WU = @Mapd_Bindd W T U Return_T Bindd_WTU.

    Class Compat_Bind_Bindd: Prop :=
      compat_bind_bindd: Bind_TU = @Bind_Bindd W T U Bindd_WTU.

  End compat.

  Section self.

    Context
    `{Return_T: Return T}
    `{Bindd_TU: Bindd W T U}.

    #[export] Instance Compat_Map_Bindd_Self:
      Compat_Map_Bindd W T U (Map_U := Map_Bindd W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Mapd_Bindd_Self:
      Compat_Mapd_Bindd W T U (Mapd_WU := Mapd_Bindd W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Bind_Bindd_Self:
      Compat_Bind_Bindd W T U (Bind_TU := Bind_Bindd W T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Map_Bind_Bindd
     `{Map_U: Map U} `{Bind_TU: Bind T U}
      `{! Compat_Bind_Bindd W T U}
      `{! Compat_Map_Bindd W T U} :
      Compat_Map_Bind U T.
    Proof.
      hnf.
      rewrite (compat_map_bindd W T U).
      rewrite (compat_bind_bindd W T U).
      reflexivity.
    Qed.

    (*
    #[export] Instance Compat_Map_Mapd_Bindd
     `{Map U} `{Mapd W U}
      `{! Compat_Mapd_Bindd W T U}
      `{! Compat_Map_Bindd W T U} :
      Compat_Map_Mapd W U.
    Proof.
      hnf.
      ...
      reflexivity.
    Qed.
    *)

  End self.

  Section compat_laws.

    Context
    `{Map_U: Map U}
    `{Bind_TU: Bind T U}
    `{Mapd_WU: Mapd W U}
    `{Return_T: Return T}
    `{Bindd_WTU: Bindd W T U}.

    Lemma map_to_bindd `{! Compat_Map_Bindd W T U} `(f: A -> B):
      map (F := U) f = bindd (ret ∘ f ∘ extract).
    Proof.
      rewrite (compat_map_bindd W T U).
      reflexivity.
    Qed.

    Lemma mapd_to_bindd `{! Compat_Mapd_Bindd W T U} `(f: W * A -> B):
      mapd f = bindd (ret ∘ f).
    Proof.
      rewrite (compat_mapd_bindd W T U).
      reflexivity.
    Qed.

    Lemma bind_to_bindd  `{! Compat_Bind_Bindd W T U} `(f: A -> T B):
      bind f = bindd (f ∘ extract).
    Proof.
      rewrite (compat_bind_bindd W T U).
      reflexivity.
    Qed.

    Lemma map_to_bind
      `{! Compat_Map_Bindd W T U}
      `{! Compat_Bind_Bindd W T U}
     : forall (A B: Type) (f: A -> B),
        map f = bind (ret ∘ f).
    Proof.
      intros.
      rewrite map_to_bindd.
      rewrite bind_to_bindd.
      reflexivity.
    Qed.

    Lemma map_to_mapd
      `{! Compat_Map_Bindd W T U}
      `{! Compat_Mapd_Bindd W T U}
     : forall (A B: Type) (f: A -> B),
        map f = mapd (f ∘ extract).
    Proof.
      intros.
      rewrite map_to_bindd.
      rewrite mapd_to_bindd.
      reflexivity.
    Qed.

  End compat_laws.

End operations.

Class DecoratedMonadFull
  (W: Type)
  (T: Type -> Type)
  `{ret_inst: Return T}
  `{Bindd_inst: Bindd W T T}
  `{Mapd_inst: Mapd W T}
  `{Bind_inst: Bind T T}
  `{Map_inst: Map T}
  `{op: Monoid_op W} `{unit: Monoid_unit W}
  :=
  { kmondf_kmond :> DecoratedMonad W T;
    kmondf_map_compat :> Compat_Map_Bindd W T T;
    kmondf_mapd_compat :> Compat_Mapd_Bindd W T T;
    kmondf_bind_compat :> Compat_Bind_Bindd W T T;
  }.

Class DecoratedRightModuleFull
  (W: Type)
  (T: Type -> Type)
  (U: Type -> Type)
  `{ret_inst: Return T}
  `{Bindd_T_inst: Bindd W T T}
  `{Bindd_U_inst: Bindd W T U}
  `{Mapd_T_inst: Mapd W T}
  `{Mapd_U_inst: Mapd W U}
  `{Bind_T_inst: Bind T T}
  `{Bind_U_inst: Bind T U}
  `{Map_T_inst: Map T}
  `{Map_U_inst: Map U}
  `{op: Monoid_op W}
  `{unit: Monoid_unit W}
  :=
  { kmoddf_kmond :> DecoratedMonadFull W T;
    kmoddf_mod :> DecoratedRightModule W T U;
    kmoddf_map_compat :> Compat_Map_Bindd W T U;
    kmoddf_mapd_compat :> Compat_Mapd_Bindd W T U;
    kmoddf_bind_compat :> Compat_Bind_Bindd W T U;
  }.

Section MonadFull.

  #[local] Instance DecoratedMonadFull_DecoratedMonad
    (W: Type) (T: Type -> Type)
    `{Monad_inst: DecoratedMonad W T} :
  DecoratedMonadFull W T
    (Map_inst := Map_Bindd W T T)
    (Mapd_inst := Mapd_Bindd W T T)
    (Bind_inst := Bind_Bindd W T T)
  :=
  {| kmondf_kmond := _
  |}.

  #[local] Instance DecoratedRightModuleFull_DecoratedRightModule
    (W: Type) (T: Type -> Type) (U: Type -> Type)
    `{Module_inst: DecoratedRightModule W T U} :
    DecoratedRightModuleFull W T U
      (Map_T_inst := Map_Bindd W T T)
      (Map_U_inst := Map_Bindd W T U)
      (Mapd_T_inst := Mapd_Bindd W T T)
      (Mapd_U_inst := Mapd_Bindd W T U)
      (Bind_T_inst := Bind_Bindd W T T)
      (Bind_U_inst := Bind_Bindd W T U) :=
    {| kmoddf_kmond := _
    |}.

  #[local] Instance DecoratedRightModule_DecoratedMonad
    (W: Type) (T: Type -> Type)
    `{Monad_inst: DecoratedMonad W T} :
    DecoratedRightModule W T T :=
    {| kdmod_premod := kdm_premod ; |}.

  #[local] Instance DecoratedRightModuleFull_DecoratedMonadFull
    (W: Type) (T: Type -> Type)
    `{Monad_inst: DecoratedMonadFull W T} :
    DecoratedRightModuleFull W T T.
  Proof.
    constructor.
    - typeclasses eauto.
    - apply DecoratedRightModule_DecoratedMonad.
      apply kmondf_kmond.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

End MonadFull.

(** * More Kleisli laws *)
(******************************************************************************)
Section kleisli.

  Context
    `{ret_inst: Return T}
      `{Bindd_T_inst: Bindd W T T}
      `{Mapd_T_inst: Mapd W T}
      `{Bind_T_inst: Bind T T}
      `{Map_T_inst: Map T}
      `{op: Monoid_op W}
      `{unit: Monoid_unit W}
      `{Map_Bindd_T_inst: ! Compat_Map_Bindd W T T}
      `{Bind_Bindd_T_inst: ! Compat_Bind_Bindd W T T}
      `{Mapd_Bindd_T_inst: ! Compat_Mapd_Bindd W T T}
      `{Module_inst: ! DecoratedMonad W T}.

  (*
  Context
    `{DecoratedMonadFull W T}.
   *)

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)

  (** *** Homogeneous cases *)
  (******************************************************************************)
  Lemma kc5_44: forall `(g: W * B -> C) `(f: W * A -> B),
      (ret ∘ g) ⋆5 (ret ∘ f) = ret ∘ (g ⋆4 f).
  Proof.
    intros. unfold kc5. ext [w' a].
    unfold compose at 2.
    compose near (f (w', a)).
    rewrite kdm_bindd0.
    rewrite preincr_ret.
    reflexivity.
  Qed.

  Lemma kc5_11: forall `(g: B -> T C) `(f: A -> T B),
      g ∘ extract ⋆5 f ∘ extract = (g ⋆1 f) ∘ extract.
  Proof.
    intros. unfold kc5, kc1. ext [w a].
    rewrite extract_preincr2.
    rewrite bind_to_bindd.
    cbv.
    reflexivity.
  Qed.

  Lemma kc5_00: forall `(g: B -> C) `(f: A -> B),
      (ret ∘ g ∘ extract) ⋆5 (ret ∘ f ∘ extract) =
        ret ∘ g ∘ f ∘ extract.
  Proof.
    intros. unfold kc5. ext [w a].
    unfold compose at 3 4. cbn.
    compose near (f a) on left.
    rewrite kdm_bindd0.
    rewrite extract_preincr2.
    reflexivity.
  Qed.

  (** *** Heterogeneous cases *)
  (******************************************************************************)
  Lemma kc5_54 {A B C}: forall (g: W * B -> T C) (f: W * A -> B),
      g ⋆5 (ret ∘ f) = g ⋆4 f.
  Proof.
    intros. unfold kc5, kc4.
    ext [w a]. unfold compose; cbn.
    compose near (f (w, a)) on left.
    rewrite kdm_bindd0.
    rewrite preincr_ret.
    reflexivity.
  Qed.

  Lemma kc5_51 {A B C}: forall (g: W * B -> T C) (f: A -> T B),
      g ⋆5 (f ∘ extract) = (fun '(w, t) => bindd (g ⦿ w) t) ∘ map f.
  Proof.
    intros. ext [w a]. reflexivity.
  Qed.

  Lemma kc5_50 {A B C}: forall (g: W * B -> T C) (f: A -> B),
      g ⋆5 (ret ∘ f ∘ extract) = g ∘ map f.
  Proof.
    intros. ext [w a]. unfold kc5.
    unfold compose; cbn.
    compose near (f a).
    rewrite kdm_bindd0.
    rewrite preincr_ret.
    reflexivity.
  Qed.

  Lemma kc5_45 {A B C}: forall (g: W * B -> C) (f: W * A -> T B),
      (ret ∘ g) ⋆5 f = fun '(w, t) => mapd (g ⦿ w) (f (w, t)).
  Proof.
    intros. unfold kc5.
    ext [w a].
    rewrite mapd_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_15 {A B C}: forall (g: B -> T C) (f: W * A -> T B),
      (g ∘ extract) ⋆5 f = g ⋆1 f.
  Proof.
    intros. unfold kc5, kc1.
    ext [w a].
    rewrite extract_preincr2.
    rewrite bind_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_05 {A B C}: forall (g: B -> C) (f: W * A -> T B),
      (ret ∘ g ∘ extract) ⋆5 f = map g ∘ f.
  Proof.
    intros. ext [w a]. unfold kc5.
    rewrite extract_preincr2.
    rewrite map_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_14 {A B C}: forall (g: B -> T C) (f: W * A -> B),
      (g ∘ extract) ⋆5 (ret ∘ f) = g ∘ f.
  Proof.
    intros. unfold kc5. ext [w a].
    unfold compose at 2; cbn.
    compose near (f (w, a)) on left.
    rewrite kdm_bindd0.
    rewrite extract_preincr2.
    reflexivity.
  Qed.

  Lemma kc5_41 {A B C}: forall (g: W * B -> C) (f: A -> T B),
      (ret ∘ g) ⋆5 (f ∘ extract) = fun '(w, a) => mapd (g ⦿ w) (f a).
  Proof.
    intros. unfold kc5. ext [w a].
    rewrite mapd_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_04 {A B C}: forall (g: B -> C) (f: W * A -> B),
      (ret ∘ g ∘ extract) ⋆5 (ret ∘ f) = ret ∘ g ∘ f.
  Proof.
    intros. unfold kc5. ext [w a].
    unfold compose at 3; cbn.
    compose near (f (w, a)) on left.
    rewrite kdm_bindd0.
    reflexivity.
  Qed.

  Lemma kc5_40 {A B C}: forall (g: W * B -> C) (f: A -> B),
      (ret ∘ g) ⋆5 (ret ∘ f ∘ extract) = ret ∘ g ∘ map f.
  Proof.
    intros. unfold kc5. ext [w a].
    unfold compose; cbn.
    compose near (f a).
    rewrite kdm_bindd0.
    unfold compose; cbn.
    compose near (f a) on left.
    rewrite preincr_ret.
    reflexivity.
  Qed.

End kleisli.

(** * Composition laws *)
(******************************************************************************)
Section derived_instances.

  Context
    `{ret_inst: Return T}
      `{Bindd_T_inst: Bindd W T T}
      `{Bindd_U_inst: Bindd W T U}
      `{Mapd_T_inst: Mapd W T}
      `{Mapd_U_inst: Mapd W U}
      `{Bind_T_inst: Bind T T}
      `{Bind_U_inst: Bind T U}
      `{Map_T_inst: Map T}
      `{Map_U_inst: Map U}
      `{op: Monoid_op W}
      `{unit: Monoid_unit W}
      `{Map_Bindd_T_inst: ! Compat_Map_Bindd W T T}
      `{Bind_Bindd_T_inst: ! Compat_Bind_Bindd W T T}
      `{Mapd_Bindd_T_inst: ! Compat_Mapd_Bindd W T T}
      `{Map_Bindd_inst: ! Compat_Map_Bindd W T U}
      `{Bind_Bindd_inst: ! Compat_Bind_Bindd W T U}
      `{Mapd_Bindd_inst: ! Compat_Mapd_Bindd W T U}
      `{Module_inst: ! DecoratedRightModule W T U}
      `{Monad_inst: ! DecoratedMonad W T}.
  (*
    `{Module_inst: DecoratedRightModuleFull W T U}.
   *)

  (** ** Special cases for composition laws *)
  (******************************************************************************)

  (** *** Homogeneous cases *)
  (******************************************************************************)
  Lemma mapd_mapd: forall (A B C: Type) (g: W * B -> C) (f: W * A -> B),
      mapd (T := U) g ∘ mapd f = mapd (g ⋆4 f).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite mapd_to_bindd.
    rewrite mapd_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_44.
    reflexivity.
  Qed.

  Lemma bind_bind: forall (A B C: Type) (g: B -> T C) (f: A -> T B),
      bind g ∘ bind f = bind (U := U) (g ⋆1 f).
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite bind_to_bindd.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_11.
    reflexivity.
  Qed.

  (** *** Composition with <<bindd>> and <<bind>> *)
  (******************************************************************************)
  Corollary bind_bindd {A B C}: forall (g: B -> T C) (f: W * A -> T B),
      bind g ∘ bindd f = bindd (U := U) (g ⋆1 f).
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_15.
    reflexivity.
  Qed.

  Corollary bindd_bind {A B C}: forall (g: W * B -> T C) (f: A -> T B),
      bindd g ∘ bind f = bindd (U := U) ((fun '(w, t) => bindd (g ⦿ w) t) ∘ map f).
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_51.
    reflexivity.
  Qed.

  (** *** Composition with <<bindd>> and <<mapd>> *)
  (******************************************************************************)
  Lemma bindd_mapd {A B C}: forall (g: W * B -> T C) (f: W * A -> B),
      bindd g ∘ mapd f = bindd (U := U) (g ⋆4 f).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_54.
    reflexivity.
  Qed.

  Corollary mapd_bindd {A B C}: forall (g: W * B -> C) (f: W * A -> T B),
      mapd g ∘ bindd f = bindd (U := U) (fun '(w, t) => mapd (g ⦿ w) (f (w, t))).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_45.
    reflexivity.
  Qed.

  (** *** Composition with <<map>> *)
  (******************************************************************************)
  Lemma bindd_map {A B C}: forall (g: W * B -> T C) (f: A -> B),
      bindd g ∘ map f = bindd (U := U) (g ∘ map f).
  Proof.
    intros.
    rewrite map_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_50.
    reflexivity.
  Qed.

  Corollary map_bindd {A B C}: forall (g: B -> C) (f: W * A -> T B),
      map g ∘ bindd f = bindd (U := U) (map g ∘ f).
  Proof.
    intros.
    rewrite map_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_05.
    reflexivity.
  Qed.

  (** *** Composition between <<mapd>> and <<bind>> *)
  (******************************************************************************)
  Lemma mapd_bind: forall (A B C: Type) (g: W * B -> C) (f: A -> T B),
      mapd g ∘ bind f = bindd (U := U) (fun '(w, a) => mapd (g ⦿ w) (f a)).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_41.
    reflexivity.
  Qed.

  Lemma bind_mapd: forall (A B C: Type) (g: B -> T C) (f: W * A -> B),
      bind g ∘ mapd f = bindd (U := U) (g ∘ f).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_14.
    reflexivity.
  Qed.

  (** ** Composition with <<ret>> *)
  (******************************************************************************)
  Lemma bind_ret: forall (A B: Type) (f: A -> T B),
      bind (U := T) f ∘ ret = f.
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite kdm_bindd0.
    reflexivity.
  Qed.

  Lemma mapd_ret: forall (A B: Type) (f: W * A -> B),
      mapd (T := T) f ∘ ret = ret ∘ f ∘ ret (T := (W ×)).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite kdm_bindd0.
    reflexivity.
  Qed.

  (** ** Identity laws *)
  (******************************************************************************)
  Lemma bind_id: forall (A: Type),
      bind (U := U) ret = @id (U A).
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd1.
    reflexivity.
  Qed.

  Lemma mapd_id: forall (A: Type),
      mapd (T := U) extract = @id (U A).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite kdmod_bindd1.
    reflexivity.
  Qed.

End derived_instances.

(** * Derived instances *)
(******************************************************************************)
Section derived_instances.

  Context
    W T U
    `{ret_inst: Return T}
      `{Bindd_T_inst: Bindd W T T}
      `{Bindd_U_inst: Bindd W T U}
      `{Mapd_T_inst: Mapd W T}
      `{Mapd_U_inst: Mapd W U}
      `{Bind_T_inst: Bind T T}
      `{Bind_U_inst: Bind T U}
      `{Map_T_inst: Map T}
      `{Map_U_inst: Map U}
      `{op: Monoid_op W}
      `{unit: Monoid_unit W}
      `{Map_Bindd_T_inst: ! Compat_Map_Bindd W T T}
      `{Bind_Bindd_T_inst: ! Compat_Bind_Bindd W T T}
      `{Mapd_Bindd_T_inst: ! Compat_Mapd_Bindd W T T}
      `{Map_Bindd_inst: ! Compat_Map_Bindd W T U}
      `{Bind_Bindd_inst: ! Compat_Bind_Bindd W T U}
      `{Mapd_Bindd_inst: ! Compat_Mapd_Bindd W T U}
      `{Module_inst: ! DecoratedRightModule W T U}
      `{Monad_inst: ! DecoratedMonad W T}.

  #[local] Existing Instance DecoratedRightModule_DecoratedMonad.

  #[export] Instance RightPreModule_DecoratedRightPreModule :
    RightPreModule T U :=
    {| kmod_bind1 := bind_id;
       kmod_bind2 := bind_bind;
    |}.

  #[export] Instance RightPreModule_DecoratedRightPreModule_Monad :
    RightPreModule T T :=
    {| kmod_bind1 := bind_id;
       kmod_bind2 := bind_bind;
    |}.

  #[export] Instance Monad_DecoratedMonad :
    Monad T :=
    {| kmon_bind0 := bind_ret;
    |}.

  #[export] Instance MonadFull_DecoratedMonadFull :
    MonadFull T :=
    {| kmonf_kmon := _ |}.

  #[export] Instance DecoratedFunctor_DecoratedRightModule:
    DecoratedFunctor W U :=
    {| kdf_mapd1 := mapd_id;
      kdf_mapd2 := mapd_mapd;
    |}.

End derived_instances.
