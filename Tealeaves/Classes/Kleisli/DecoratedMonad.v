From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.Monad
  Classes.Kleisli.Comonad
  Functors.Early.Writer.

From Tealeaves Require Import
  Classes.Categorical.Monad (join).

Import Monoid.Notations.

#[local] Generalizable Variables W T U.

(** * Decorated Monads *)
(**********************************************************************)

(** ** Operation <<bindd>> *)
(**********************************************************************)
Class Bindd (W: Type) (T U: Type -> Type):=
  bindd: forall (A B: Type), (W * A -> T B) -> U A -> U B.

#[global] Arguments bindd {W}%type_scope {T U}%function_scope
  {Bindd} {A B}%type_scope.

(** ** Kleisli Composition *)
(**********************************************************************)
Definition kc5
  {W: Type}
  {T: Type -> Type}
  `{Monoid_op_W: Monoid_op W}
  `{Bindd_WTT: Bindd W T T}
  {A B C: Type}:
  (W * B -> T C) ->
  (W * A -> T B) ->
  (W * A -> T C) :=
  fun g f '(w, a) =>
    @bindd W T T Bindd_WTT B C (g ⦿ w) (f (w, a)).

#[local] Infix "⋆5" := (kc5) (at level 60): tealeaves_scope.

(** ** Typeclass *)
(**********************************************************************)
Class DecoratedRightPreModule (W: Type) (T U: Type -> Type)
  `{Monoid_op_W: Monoid_op W}
  `{Return_T: Return T}
  `{Bindd_WTT: Bindd W T T}
  `{Bindd_WTU: Bindd W T U} :=
  { kdmod_bindd1:
    forall (A: Type),
      bindd (U := U) (ret ∘ extract (A := A)) = id;
    kdmod_bindd2:
    forall (A B C: Type) (g: W * B -> T C) (f: W * A -> T B),
      bindd (U := U) g ∘ bindd f = bindd (g ⋆5 f);
  }.

Class DecoratedMonad
  (W: Type)
  (T: Type -> Type)
  `{Monoid_unit_W: Monoid_unit W}
  `{Monoid_op_W: Monoid_op W}
  `{Return_T: Return T}
  `{Bindd_WTT: Bindd W T T} :=
  { kdm_monoid :> Monoid W;
    kdm_premod :> DecoratedRightPreModule W T T;
    kdm_bindd0: forall (A B: Type) (f: W * A -> T B),
      bindd f ∘ ret = f ∘ ret;
  }.

Class DecoratedRightModule
  (W: Type)
  (T: Type -> Type)
  (U: Type -> Type)
  `{Monoid_unit_W: Monoid_unit W}
  `{Monoid_op_W: Monoid_op W}
  `{Return_T: Return T}
  `{Bindd_WTT: Bindd W T T}
  `{Bindd_WTU: Bindd W T U}
  :=
  { kdmod_monad :> DecoratedMonad W T;
    kdmod_premod :> DecoratedRightPreModule W T U;
  }.

#[local] Instance DecoratedRightModule_DecoratedMonad
  (W: Type)
  (T: Type -> Type)
  `{DecoratedMonad_WT: DecoratedMonad W T}:
  DecoratedRightModule W T T :=
  {| kdmod_premod := kdm_premod;
  |}.

Lemma kdm_bindd1 `{DecoratedMonad W T}:
  forall (A: Type), bindd (ret ∘ extract) = @id (T A).
Proof.
  apply kdmod_bindd1.
Qed.

Lemma kdm_bindd2 `{DecoratedMonad W T}:
  forall (A B C: Type) (g: W * B -> T C) (f: W * A -> T B),
    bindd g ∘ bindd f = bindd (g ⋆5 f).
Proof.
  apply kdmod_bindd2.
Qed.

(** ** Kleisli Category Laws *)
(**********************************************************************)
Section decorated_monad_kleisli_category.

  Context
    (T: Type -> Type)
    `{DecoratedMonad W T}.

  #[local] Generalizable Variables A B C D.

  (** *** Interaction with [incr], [preincr] *)
  (********************************************************************)
  Lemma kc5_incr: forall `(g: W * B -> T C) `(f: W * A -> T B) (w: W),
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

  Lemma kc5_preincr: forall `(g: W * B -> T C) `(f: W * A -> T B) (w: W),
      (g ⋆5 f) ⦿ w = g ⦿ w ⋆5 f ⦿ w.
  Proof.
    intros.
    unfold preincr.
    rewrite kc5_incr.
    reflexivity.
  Qed.

  (** *** Right identity law *)
  (********************************************************************)
  Theorem kc5_id_r {B C}: forall (g: W * B -> T C),
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

  (** *** Left identity law *)
  (********************************************************************)
  Theorem kc5_id_l {A B}: forall (f: W * A -> T B),
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

  (** *** Associativity law *)
  (********************************************************************)
  Theorem kc5_assoc {A B C D}:
    forall (h: W * C -> T D)
      (g: W * B -> T C) (f: W * A -> T B),
      h ⋆5 (g ⋆5 f) = (h ⋆5 g) ⋆5 f.
  Proof.
    intros. unfold kc5.
    ext [w a].
    compose near (f (w, a)) on left.
    rewrite kdm_bindd2.
    rewrite <- kc5_preincr.
    reflexivity.
  Qed.

End decorated_monad_kleisli_category.

(** ** Decorated Monad Homomorphisms *)
(**********************************************************************)
Class DecoratedMonadHom
  (W: Type)
  (T: Type -> Type)
  (U: Type -> Type)
  `{Return T} `{Bindd W T T}
  `{Return U} `{Bindd W U U}
  (ϕ: forall (A: Type), T A -> U A) :=
  { kdm_hom_bind: forall (A B: Type) (f: W * A -> T B),
      ϕ B ∘ @bindd W T T _ A B f = @bindd W U U _ A B (ϕ B ∘ f) ∘ ϕ A;
    kdm_hom_ret: forall (A: Type),
      ϕ A ∘ @ret T _ A = @ret U _ A;
  }.

Class DecoratedRightModuleHom
  (W: Type)
  (T: Type -> Type)
  (U: Type -> Type)
  (V: Type -> Type)
  `{Monoid_unit_W: Monoid_unit W}
  `{Monoid_op_W: Monoid_op W}
  `{Return_T: Return T}
  `{Bindd_WTT: Bindd W T V}
  `{Bindd_WTU: Bindd W T U}
  (ϕ: forall (A: Type), U A -> V A) :=
  { kdmod_hom_bind: forall (A B: Type) (f: W * A -> T B),
      ϕ B ∘ @bindd W T U _ A B f = @bindd W T V _ A B f ∘ ϕ A;
  }.

Class ParallelDecoratedRightModuleHom
  (T T' U U': Type -> Type)
  `{Return T}
  `{Bindd W T U}
  `{Bindd W T' U'}
  (ψ: forall (A: Type), T A -> T' A)
  (ϕ: forall (A: Type), U A -> U' A) :=
  { kdmod_parhom_bind: forall (A B: Type) (f: W * A -> T B),
      ϕ B ∘ bindd f = bindd (ψ B ∘ f) ∘ ϕ A;
  }.

(** * Derived Structures *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.
  Section operations.

    Context
      (W: Type)
      (T: Type -> Type)
      (U: Type -> Type)
      `{Return_T: Return T}
      `{Bindd_WTU: Bindd W T U}.

    #[export] Instance Map_Bindd: Map U :=
      fun A B f => bindd (ret ∘ f ∘ extract).
    #[export] Instance Bind_Bindd: Bind T U :=
      fun A B f => bindd (f ∘ extract).
    #[export] Instance Mapd_Bindd: Mapd W U :=
      fun A B f => bindd (ret ∘ f).

  End operations.
End DerivedOperations.

Section compatibility.

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
    compat_map_bindd:
      Map_U = @DerivedOperations.Map_Bindd W T U Return_T Bindd_WTU.

  Class Compat_Mapd_Bindd: Prop :=
    compat_mapd_bindd:
      Mapd_WU = @DerivedOperations.Mapd_Bindd W T U Return_T Bindd_WTU.

  Class Compat_Bind_Bindd: Prop :=
    compat_bind_bindd:
      Bind_TU = @DerivedOperations.Bind_Bindd W T U Bindd_WTU.

End compatibility.

Section self.

  Context
    `{Return_T: Return T}
    `{Bindd_WTU: Bindd W T U}.

  #[export] Instance Compat_Map_Bindd_Self:
    Compat_Map_Bindd W T U
      (Map_U := DerivedOperations.Map_Bindd W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Mapd_Bindd_Self:
    Compat_Mapd_Bindd W T U
      (Mapd_WU := DerivedOperations.Mapd_Bindd W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Bind_Bindd_Self:
    Compat_Bind_Bindd W T U
      (Bind_TU := DerivedOperations.Bind_Bindd W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Map_Bind_Bindd
    `{Map_U: Map U}
    `{Bind_TU: Bind T U}
    `{! Compat_Bind_Bindd W T U}
    `{! Compat_Map_Bindd W T U}:
    Compat_Map_Bind T U.
  Proof.
    hnf.
    rewrite (compat_map_bindd W T U).
    rewrite (compat_bind_bindd W T U).
    reflexivity.
  Qed.

  #[export] Instance Compat_Map_Mapd_Bindd
    `{Map_U: Map U}
    `{Mapd_WU: Mapd W U}
    `{! Compat_Mapd_Bindd W T U}
    `{! Compat_Map_Bindd W T U}:
    Compat_Map_Mapd W U.
  Proof.
    hnf.
    rewrite (compat_map_bindd W T U).
    rewrite (compat_mapd_bindd W T U).
    reflexivity.
  Qed.

End self.

Section compat_laws.

  #[local] Generalizable Variables A B.

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

(** ** Derived Kleisli Composition Laws *)
(**********************************************************************)
Section decorated_monad_derived_kleisli_laws.

  Import Kleisli.Monad.Notations.
  Import Kleisli.Comonad.Notations.

  #[local] Generalizable Variables A B C.

  Context
    `{Return_T: Return T}
    `{Bindd_WTT: Bindd W T T}
    `{Mapd_WT: Mapd W T}
    `{Bind_TT: Bind T T}
    `{Map_T: Map T}
    `{op: Monoid_op W}
    `{unit: Monoid_unit W}
    `{! Compat_Map_Bindd W T T}
    `{! Compat_Bind_Bindd W T T}
    `{! Compat_Mapd_Bindd W T T}
    `{! DecoratedMonad W T}.

  Context {A B C: Type}.

  (** *** Homogeneous cases *)
  (********************************************************************)
  Lemma kc5_11: forall (g: W * B -> C) (f: W * A -> B),
      (ret ∘ g) ⋆5 (ret ∘ f) = ret ∘ (g ⋆1 f).
  Proof.
    intros. unfold kc5. ext [w' a].
    unfold compose at 2.
    compose near (f (w', a)).
    rewrite kdm_bindd0.
    rewrite preincr_ret.
    reflexivity.
  Qed.

  Lemma kc5_44: forall (g: B -> T C) (f: A -> T B),
      g ∘ extract ⋆5 f ∘ extract = (g ⋆ f) ∘ extract.
  Proof.
    intros. unfold kc5, kc. ext [w a].
    rewrite extract_preincr2.
    rewrite bind_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_00: forall (g: B -> C) (f: A -> B),
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
  (********************************************************************)
  Lemma kc5_51: forall (g: W * B -> T C) (f: W * A -> B),
      g ⋆5 (ret ∘ f) = g ⋆1 f.
  Proof.
    intros. unfold kc5, kc1.
    ext [w a]. unfold compose; cbn.
    compose near (f (w, a)) on left.
    rewrite kdm_bindd0.
    rewrite preincr_ret.
    reflexivity.
  Qed.

  Lemma kc5_54: forall (g: W * B -> T C) (f: A -> T B),
      g ⋆5 (f ∘ extract) = (fun '(w, t) => bindd (g ⦿ w) t) ∘ map f.
  Proof.
    intros. ext [w a]. reflexivity.
  Qed.

  Lemma kc5_50: forall (g: W * B -> T C) (f: A -> B),
      g ⋆5 (ret ∘ f ∘ extract) = g ∘ map f.
  Proof.
    intros. ext [w a]. unfold kc5.
    unfold compose; cbn.
    compose near (f a).
    rewrite kdm_bindd0.
    rewrite preincr_ret.
    reflexivity.
  Qed.

  Lemma kc5_15: forall (g: W * B -> C) (f: W * A -> T B),
      (ret ∘ g) ⋆5 f = fun '(w, t) => mapd (g ⦿ w) (f (w, t)).
  Proof.
    intros. unfold kc5.
    ext [w a].
    rewrite mapd_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_45: forall (g: B -> T C) (f: W * A -> T B),
      (g ∘ extract) ⋆5 f = g ⋆ f.
  Proof.
    intros. unfold kc5, kc.
    ext [w a].
    rewrite extract_preincr2.
    rewrite bind_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_05: forall (g: B -> C) (f: W * A -> T B),
      (ret ∘ g ∘ extract) ⋆5 f = map g ∘ f.
  Proof.
    intros. ext [w a]. unfold kc5.
    rewrite extract_preincr2.
    rewrite map_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_41: forall (g: B -> T C) (f: W * A -> B),
      (g ∘ extract) ⋆5 (ret ∘ f) = g ∘ f.
  Proof.
    intros. unfold kc5. ext [w a].
    unfold compose at 2; cbn.
    compose near (f (w, a)) on left.
    rewrite kdm_bindd0.
    rewrite extract_preincr2.
    reflexivity.
  Qed.

  Lemma kc5_14: forall (g: W * B -> C) (f: A -> T B),
      (ret ∘ g) ⋆5 (f ∘ extract) = fun '(w, a) => mapd (g ⦿ w) (f a).
  Proof.
    intros. unfold kc5. ext [w a].
    rewrite mapd_to_bindd.
    reflexivity.
  Qed.

  Lemma kc5_01: forall (g: B -> C) (f: W * A -> B),
      (ret ∘ g ∘ extract) ⋆5 (ret ∘ f) = ret ∘ g ∘ f.
  Proof.
    intros. unfold kc5. ext [w a].
    unfold compose at 3; cbn.
    compose near (f (w, a)) on left.
    rewrite kdm_bindd0.
    reflexivity.
  Qed.

  Lemma kc5_10: forall (g: W * B -> C) (f: A -> B),
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

End decorated_monad_derived_kleisli_laws.

(** ** Derived Composition Laws *)
(**********************************************************************)
Section decorated_monad_derived_composition_laws.

  Import Kleisli.Monad.Notations.
  Import Kleisli.Comonad.Notations.
  Import Product.Notations.

  #[local] Generalizable Variables A B C.

  Context
    `{Return_T: Return T}
    `{Bindd_WTT: Bindd W T T}
    `{Bindd_WTU: Bindd W T U}
    `{Mapd_WT: Mapd W T}
    `{Mapd_WU: Mapd W U}
    `{Bind_TT: Bind T T}
    `{Bind_TU: Bind T U}
    `{Map_T: Map T}
    `{Map_U: Map U}
    `{op: Monoid_op W}
    `{unit: Monoid_unit W}
    `{! Compat_Map_Bindd W T T}
    `{! Compat_Bind_Bindd W T T}
    `{! Compat_Mapd_Bindd W T T}
    `{! Compat_Map_Bindd W T U}
    `{! Compat_Bind_Bindd W T U}
    `{! Compat_Mapd_Bindd W T U}
    `{! DecoratedRightPreModule W T U}
    `{! DecoratedMonad W T}.

  Context (A B C: Type).

  (** *** Homogeneous cases *)
  (********************************************************************)
  Lemma mapd_mapd: forall (g: W * B -> C) (f: W * A -> B),
      mapd (T := U) g ∘ mapd f = mapd (g ⋆1 f).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite mapd_to_bindd.
    rewrite mapd_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_11.
    reflexivity.
  Qed.

  Lemma bind_bind: forall (g: B -> T C) (f: A -> T B),
      bind g ∘ bind f = bind (U := U) (g ⋆ f).
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite bind_to_bindd.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_44.
    reflexivity.
  Qed.

  (** *** Composition with <<bindd>> and <<bind>> *)
  (********************************************************************)
  Corollary bind_bindd: forall (g: B -> T C) (f: W * A -> T B),
      bind g ∘ bindd f = bindd (U := U) (g ⋆ f).
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_45.
    reflexivity.
  Qed.

  Corollary bindd_bind: forall (g: W * B -> T C) (f: A -> T B),
      bindd g ∘ bind (U := U) f =
        bindd ((fun '(w, t) => bindd (g ⦿ w) t) ∘ map f).
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_54.
    reflexivity.
  Qed.

  (** *** Composition with <<bindd>> and <<mapd>> *)
  (********************************************************************)
  Lemma bindd_mapd: forall (g: W * B -> T C) (f: W * A -> B),
      bindd g ∘ mapd f = bindd (U := U) (g ⋆1 f).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_51.
    reflexivity.
  Qed.

  Corollary mapd_bindd: forall (g: W * B -> C) (f: W * A -> T B),
      mapd g ∘ bindd f =
        bindd (U := U) (fun '(w, t) => mapd (g ⦿ w) (f (w, t))).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_15.
    reflexivity.
  Qed.

  (** *** Composition with <<map>> *)
  (********************************************************************)
  Lemma bindd_map: forall (g: W * B -> T C) (f: A -> B),
      bindd g ∘ map f = bindd (U := U) (g ∘ map f).
  Proof.
    intros.
    rewrite map_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_50.
    reflexivity.
  Qed.

  Corollary map_bindd: forall (g: B -> C) (f: W * A -> T B),
      map g ∘ bindd f = bindd (U := U) (map g ∘ f).
  Proof.
    intros.
    rewrite map_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_05.
    reflexivity.
  Qed.

  (** *** Composition between <<mapd>> and <<bind>> *)
  (********************************************************************)
  Lemma mapd_bind: forall (g: W * B -> C) (f: A -> T B),
      mapd g ∘ bind f =
        bindd (U := U) (fun '(w, a) => mapd (g ⦿ w) (f a)).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_14.
    reflexivity.
  Qed.

  Lemma bind_mapd: forall (g: B -> T C) (f: W * A -> B),
      bind g ∘ mapd f = bindd (U := U) (g ∘ f).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd2.
    rewrite kc5_41.
    reflexivity.
  Qed.

  (** *** Composition with <<ret>> *)
  (********************************************************************)
  Lemma bind_ret: forall (f: A -> T B),
      bind (U := T) f ∘ ret = f.
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite kdm_bindd0.
    reflexivity.
  Qed.

  Lemma mapd_ret: forall (f: W * A -> B),
      mapd (T := T) f ∘ ret = ret ∘ f ∘ ret (T := (W ×)).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite kdm_bindd0.
    reflexivity.
  Qed.

  (** *** Identity laws *)
  (********************************************************************)
  Lemma bind_id:
    bind (U := U) ret = @id (U A).
  Proof.
    intros.
    rewrite bind_to_bindd.
    rewrite kdmod_bindd1.
    reflexivity.
  Qed.

  Lemma mapd_id:
    mapd (T := U) extract = @id (U A).
  Proof.
    intros.
    rewrite mapd_to_bindd.
    rewrite kdmod_bindd1.
    reflexivity.
  Qed.

End decorated_monad_derived_composition_laws.

(** ** Derived Typeclass Instances *)
(**********************************************************************)
Module DerivedInstances.
  Section decorated_monad_derivedinstances.

    Context
      (W: Type)
      (T: Type -> Type)
      (U: Type -> Type)
      `{Return_T: Return T}
      `{Bindd_WTT: Bindd W T T}
      `{Bindd_WTU: Bindd W T U}
      `{Mapd_WT: Mapd W T}
      `{Mapd_WU: Mapd W U}
      `{Bind_TT: Bind T T}
      `{Bind_TU: Bind T U}
      `{Map_T: Map T}
      `{Map_U: Map U}
      `{op: Monoid_op W}
      `{unit: Monoid_unit W}
      `{! Compat_Map_Bindd W T T}
      `{! Compat_Bind_Bindd W T T}
      `{! Compat_Mapd_Bindd W T T}
      `{! Compat_Map_Bindd W T U}
      `{! Compat_Bind_Bindd W T U}
      `{! Compat_Mapd_Bindd W T U}
      `{! DecoratedRightPreModule W T U}
      `{! DecoratedMonad W T}.

    #[local] Existing Instance DecoratedRightModule_DecoratedMonad.

    #[export] Instance RightPreModule_DecoratedRightPreModule:
      RightPreModule T U :=
      {| kmod_bind1 := bind_id;
         kmod_bind2 := bind_bind;
      |}.

    #[export] Instance RightPreModule_DecoratedRightPreModule_Monad:
      RightPreModule T T :=
      {| kmod_bind1 := bind_id;
         kmod_bind2 := bind_bind;
      |}.

    #[export] Instance Monad_DecoratedMonad:
      Kleisli.Monad.Monad T :=
      {| kmon_bind0 := bind_ret;
      |}.

    #[export] Instance DecoratedFunctor_DecoratedRightModule:
      Kleisli.DecoratedFunctor.DecoratedFunctor W U :=
      {| kdf_mapd1 := mapd_id;
         kdf_mapd2 := mapd_mapd;
      |}.

  End decorated_monad_derivedinstances.
End DerivedInstances.

(** * Instance for Writer *)
(**********************************************************************)
Import Product.Notations.

Section decorated_functor_reader.

  Context {W: Type} `{Monoid W}.

  #[export] Instance Bindd_Writer: Bindd W (W ×) (W ×) :=
    fun A B f => join (T := (W ×)) ∘ cobind f.

  (* This is local because exporting it leads to frequent
     typeclass resolution divergence for Monoid instances
     due to the circularity Monoid<-DecoratedMonad_Writer<-Monoid.
   *)

  #[local] Instance DecoratedMonad_Writer:
    DecoratedMonad W (W ×).
  Proof.
    constructor.
    - assumption.
    - constructor;
        unfold_ops @Bindd_Writer; intros.
      + rewrite <- map_to_cobind.
        rewrite Monad.mon_join_map_ret.
        reflexivity.
      + ext [w a].
        unfold kc5.
        unfold transparent tcs.
        unfold bindd.
        unfold compose, preincr, incr.
        unfold map_fst, map_tensor.
        unfold uncurry, associator, associator_inv.
        unfold compose, id.
        destruct (f (w, a)).
        destruct (g (w ● w0, b)).
        rewrite monoid_assoc.
        reflexivity.
    - intros. ext a.
      unfold ret, Return_Writer.
      unfold bindd, Bindd_Writer.
      unfold join, Join_writer.
      unfold compose.
      cbn.
      destruct (f (Ƶ, a)).
      cbn.
      rewrite monoid_id_r.
      reflexivity.
  Qed.

End decorated_functor_reader.

(** * Notations *)
(**********************************************************************)
Module Notations.
  Infix "⋆5" := (kc5) (at level 60): tealeaves_scope.
  Include Monoid.Notations.
End Notations.
