From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.DecoratedTraversableFunctor.

Import Monoid.Notations.
Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedMonad.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import DecoratedTraversableFunctor.Notations.

#[local] Generalizable Variables ϕ U T W G A B C D F M.

(** * Decorated traversable monads *)
(******************************************************************************)

(** ** Operation <<binddt>> *)
(******************************************************************************)
Class Binddt
  (W : Type)
  (T : Type -> Type)
  (U : Type -> Type)
  := binddt :
    forall (G : Type -> Type)
      `{Map G} `{Pure G} `{Mult G}
      (A B : Type),
      (W * A -> G (T B)) -> U A -> G (U B).

#[global] Arguments binddt {W}%type_scope {T} {U}%function_scope {Binddt}
  {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc7
  {W : Type}
  {T : Type -> Type}
  `{Return T}
  `{Binddt W T T}
  `{op: Monoid_op W} `{unit: Monoid_unit W}
  {A B C : Type}
  (G1 G2 : Type -> Type)
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2} :
  (W * B -> G2 (T C)) ->
  (W * A -> G1 (T B)) ->
  (W * A -> G1 (G2 (T C))) :=
  fun g f '(w, a) =>
    map (F := G1) (A := T B) (B := G2 (T C))
      (binddt (g ⦿ w)) (f (w, a)).

#[local] Infix "⋆7" := (kc7 _ _) (at level 60) : tealeaves_scope.

(** ** DTM typeclass *)
(******************************************************************************)
Class DecoratedTraversableRightPreModule
  (W : Type)
  (T U : Type -> Type)
  `{op : Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_inst : Return T}
  `{Bindd_T_inst : Binddt W T T}
  `{Bindd_U_inst : Binddt W T U} :=
  { kdtm_binddt1 : forall (A : Type),
      binddt (G := fun A => A)
        (ret (T := T) ∘ extract (W := (W ×))) = @id (U A);
    kdtm_binddt2 :
    forall `{Applicative G1} `{Applicative G2}
      `(g : W * B -> G2 (T C))
      `(f : W * A -> G1 (T B)),
      map (F := G1) (binddt g) ∘ binddt f = binddt (U := U) (G := G1 ∘ G2) (g ⋆7 f);
    kdtm_morph :
    forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ}
      `(f : W * A -> G1 (T B)),
      ϕ (U B) ∘ binddt f = binddt (ϕ (T B) ∘ f);
  }.

Class DecoratedTraversableMonad
  (W : Type)
  (T : Type -> Type)
  `{op : Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_inst : Return T}
  `{Bindd_T_inst : Binddt W T T} :=
  { kdtm_monoid :> Monoid W;
    kdtm_binddt0 : forall`{Applicative G} `(f : W * A -> G (T B)),
      binddt f ∘ ret = f ∘ ret (T := (W ×));
    kdtm_premod :> DecoratedTraversableRightPreModule W T T;
  }.

(** ** Homomorphisms *)
(******************************************************************************)
Class DecoratedTraversableMonadHom
  (T U : Type -> Type)
  `{Return T} `{Binddt W T T}
  `{Return U} `{Binddt W U U}
  (ϕ : forall (A : Type), T A -> U A) :=
  { kmon_hom_ret : forall (A : Type),
      ϕ A ∘ @ret T _ A = @ret U _ A;
    kmon_hom_bind : forall `{Applicative G}
      `(f : W * A -> G (T B)),
      map (F := G) (ϕ B) ∘ @binddt W T T _ G _ _ _ A B f =
        @binddt W U U _ G _ _ _ A B (map (F := G) (ϕ B) ∘ f) ∘ ϕ A;
  }.

(** ** Right modules *)
(******************************************************************************)
Class DecoratedTraversableRightModule
  (W : Type)
  (T U : Type -> Type)
  `{op : Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_inst : Return T}
  `{Bindd_T_inst : Binddt W T T}
  `{Bindd_U_inst : Binddt W T U}
  :=
  { kdtmod_monad :> DecoratedTraversableMonad W T;
    kdtmod_premod :> DecoratedTraversableRightPreModule W T U;
  }.

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

    #[export] Instance Compat_Map_Bind_Bindd
     `{Map U} `{Bind T U}
      `{! Compat_Bind_Binddt W T U}
      `{! Compat_Map_Binddt W T U} :
      Compat_Map_Bind U T.
    Proof.
      hnf.
      rewrite (compat_map_binddt W T U).
      unfold_ops @Map_Bind.
      rewrite (compat_bind_binddt W T U).
      reflexivity.
    Qed.

    #[export] Instance Compat_Map_Traverse_Binddt
     `{Map U} `{Traverse U}
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Traverse_Binddt W T U} :
      Compat_Map_Traverse U.
    Proof.
      hnf.
      rewrite (compat_map_binddt W T U).
      unfold_ops @Map_Traverse.
      rewrite (compat_traverse_binddt W T U).
      reflexivity.
    Qed.

    #[export] Instance Compat_Map_Bindd_Binddt
     `{Map U} `{Bindd W T U}
      `{! Compat_Bindd_Binddt W T U}
      `{! Compat_Map_Binddt W T U} :
      Compat_Map_Bindd W T U.
    Proof.
      hnf.
      rewrite (compat_map_binddt W T U).
      unfold_ops @Map_Bindd.
      rewrite (compat_bindd_binddt W T U).
      reflexivity.
    Qed.

    #[export] Instance Compat_Mapd_Bindd_Binddt
     `{Mapd W U} `{Bindd W T U}
      `{! Compat_Mapd_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U} :
        Compat_Mapd_Bindd W T U.
    Proof.
      hnf.
      rewrite (compat_mapd_binddt W T U).
      unfold_ops @Mapd_Bindd.
      rewrite (compat_bindd_binddt W T U).
      reflexivity.
    Qed.

    #[export] Instance Compat_Bind_Bindd_Binddt
     `{Bind T U} `{Bindd W T U}
      `{! Compat_Bind_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U} :
        Compat_Bind_Bindd W T U.
    Proof.
      hnf.
      rewrite (compat_bind_binddt W T U).
      unfold_ops @Bind_Bindd.
      rewrite (compat_bindd_binddt W T U).
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

    ...

    *)

  End self.

  Section compat_laws.

    Context
    `{Return_inst : Return T}
    `{Map_inst : Map U}
    `{Mapd_inst : Mapd W U}
    `{Traverse_inst : Traverse U}
    `{Bind_inst : Bind T U}
    `{Mapdt_inst : Mapdt W U}
    `{Bindd_inst : Bindd W T U}
    `{Bindt_inst : Bindt T U}
    `{Binddt_inst : Binddt W T U}.

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

    Lemma bind_to_binddt  `{! Compat_Bind_Binddt W T U} `(f : A -> T B):
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

  (** *** Left identity *)
  (******************************************************************************)
  Lemma kc7_id1 : forall (f : W * A -> G (T B)),
      kc7 G (fun A => A) (ret (T := T) ∘ extract (W := (W ×))) f = f.
  Proof.
    setup.
    rewrite preincr_assoc.
    rewrite extract_preincr.
    rewrite kdtm_binddt1.
    rewrite fun_map_id.
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
    rewrite fun_map_map.
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
    `{Monad_inst : ! DecoratedTraversableRightModule W T U}.

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
        map (F := G1) (A := T B) (B := G2 (T C))
          (mapdt g) ∘ mapdt f =
          mapdt (G := G1 ∘ G2) (g ⋆6 f).
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
      `{Monad_inst : ! DecoratedTraversableRightModule W T U}.

  (** ** Derived typeclass instances *)
  (******************************************************************************)
    #[local] Existing Instance
      DecoratedTraversableRightModule_DecoratedTraversableMonad.

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
    `{Monad_inst : ! DecoratedTraversableRightModule W T U}.

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
      rewrite mapdt_to_binddt'.
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
      Fail rewrite mapd_to_mapdt. (* TODO Solve this part *)
      Fail rewrite mapdt_bindt.
    Abort.

    (* composition_34 *)
    (* TODO bindt_mapd *)

    (* composition_16 *)
    (* TODO bind_mapdt *)

    (* composition_61 *)
    (* TODO mapdt_bind *)

  End composition_special_cases_bottom.

End other_composition_laws.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆7" := (kc7 _ _) (at level 60) : tealeaves_scope.
End Notations.
