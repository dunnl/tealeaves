From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.DecoratedTraversableFunctor
  Functors.Early.Writer.

Import Monoid.Notations.
Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedMonad.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import DecoratedTraversableFunctor.Notations.

#[local] Generalizable Variables ϕ U T W G A B C D F M.
(* TODO Find a better way to avoid cycles *)
(*
#[local] Set Typeclasses Depth 5.
*)

(** * Decorated Traversable Monads *)
(******************************************************************************)

(** ** The <<binddt>> Operation *)
(******************************************************************************)
Class Binddt
  (W: Type)
  (T: Type -> Type)
  (U: Type -> Type)
  := binddt :
    forall (G: Type -> Type)
      `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G}
      (A B: Type),
      (W * A -> G (T B)) -> U A -> G (U B).

#[global] Arguments binddt {W}%type_scope {T} {U}%function_scope {Binddt}
  {G}%function_scope {Map_G Pure_G Mult_G} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc7
  {W: Type}
  {T: Type -> Type}
  `{Return_T: Return T}
  `{Binddt_WTT: Binddt W T T}
  `{op: Monoid_op W} `{unit: Monoid_unit W}
  {A B C: Type}
  (G1 G2: Type -> Type)
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2} :
  (W * B -> G2 (T C)) ->
  (W * A -> G1 (T B)) ->
  (W * A -> G1 (G2 (T C))) :=
  fun g f '(w, a) =>
    map (F := G1) (A := T B) (B := G2 (T C))
      (binddt (g ⦿ w)) (f (w, a)).

#[local] Infix "⋆7" := (kc7 _ _) (at level 60): tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedTraversableRightPreModule
  (W: Type)
  (T U: Type -> Type)
  `{op: Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_T: Return T}
  `{Bindd_T: Binddt W T T}
  `{Bindd_U: Binddt W T U} :=
  { kdtm_binddt1: forall (A: Type),
      binddt (G := fun A => A)
        (ret (T := T) ∘ extract (W := (W ×))) = @id (U A);
    kdtm_binddt2:
    forall `{Applicative G1} `{Applicative G2}
      `(g: W * B -> G2 (T C))
      `(f: W * A -> G1 (T B)),
      map (F := G1) (binddt g) ∘ binddt f = binddt (U := U) (G := G1 ∘ G2) (g ⋆7 f);
    kdtm_morph:
    forall (G1 G2: Type -> Type) `{morph: ApplicativeMorphism G1 G2 ϕ}
      `(f: W * A -> G1 (T B)),
      ϕ (U B) ∘ binddt f = binddt (ϕ (T B) ∘ f);
  }.

Class DecoratedTraversableMonad
  (W: Type)
  (T: Type -> Type)
  `{op: Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_inst: Return T}
  `{Bindd_T_inst: Binddt W T T} :=
  { kdtm_monoid :> Monoid W;
    kdtm_binddt0: forall `{Applicative G} `(f: W * A -> G (T B)),
      binddt f ∘ ret = f ∘ ret (T := (W ×));
    kdtm_premod :> DecoratedTraversableRightPreModule W T T;
  }.

Class DecoratedTraversableRightModule
  (W: Type)
  (T U: Type -> Type)
  `{op: Monoid_op W}
  `{unit: Monoid_unit W}
  `{Return_inst: Return T}
  `{Bindd_T_inst: Binddt W T T}
  `{Bindd_U_inst: Binddt W T U}
  :=
  { kdtmod_monad :> DecoratedTraversableMonad W T;
    kdtmod_premod :> DecoratedTraversableRightPreModule W T U;
  }.

(** ** Homomorphisms *)
(******************************************************************************)
Class DecoratedTraversableMonadHom
  (T U: Type -> Type)
  `{Return T} `{Binddt W T T}
  `{Return U} `{Binddt W U U}
  (ϕ: forall (A: Type), T A -> U A) :=
  { kmon_hom_ret: forall (A: Type),
      ϕ A ∘ @ret T _ A = @ret U _ A;
    kmon_hom_bind: forall `{Applicative G}
      `(f: W * A -> G (T B)),
      map (F := G) (ϕ B) ∘ @binddt W T T _ G _ _ _ A B f =
        @binddt W U U _ G _ _ _ A B (map (F := G) (ϕ B) ∘ f) ∘ ϕ A;
  }.

(** ** Kleisi Category Laws *)
(******************************************************************************)
Section decorated_monad_kleisli_composition.

  (*
  #[local] Set Typeclasses Iterative Deepening.
   *)

  Context
    `{DecoratedTraversableMonad W T}.


  (** *** Interaction with [incr], [preincr] *)
  (******************************************************************************)
  Section incr.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C: Type}.

    Lemma kc7_incr :
      forall `(g: W * B -> G2 (T C)) `(f: W * A -> G1 (T B)) (w: W),
        (g ∘ incr w) ⋆7 (f ∘ incr w) = (g ⋆7 f) ∘ incr w.
    Proof.
      intros. unfold kc7. ext [w' a].
      unfold preincr. reassociate ->.
      rewrite incr_incr.
      reflexivity.
    Qed.

    Lemma kc7_preincr :
      forall `(g: W * B -> G2 (T C)) `(f: W * A -> G1 (T B)) (w: W),
        (g ⦿ w) ⋆7 (f ⦿ w) = (g ⋆7 f) ⦿ w.
    Proof.
      intros. unfold preincr. rewrite kc7_incr.
      reflexivity.
    Qed.

  End incr.

  Context
    `{Applicative G}
    {A B C D: Type}.

  (** *** Left identity *)
  (******************************************************************************)
  Lemma kc7_id1: forall (f: W * A -> G (T B)),
      kc7 G (fun A => A) (ret (T := T) ∘ extract (W := (W ×))) f = f.
  Proof.
    intros.
    unfold kc7.
    ext [w a].
    rewrite preincr_assoc.
    rewrite extract_preincr.
    rewrite kdtm_binddt1.
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

  (** *** Right identity *)
  (******************************************************************************)
  Lemma kc7_id2: forall (g: W * A -> G (T B)),
      kc7 (fun A => A) G g (ret (T := T) ∘ extract (W := (W ×))) = g.
  Proof.
    intros.
    unfold kc7.
    ext [w a].
    unfold_ops @Map_I.
    change_left ((binddt (T := T) (g ⦿ w) ∘ ret (T := T)) a).
    rewrite kdtm_binddt0.
    change (g (w ● Ƶ, a) = g (w, a)).
    simpl_monoid.
    reflexivity.
  Qed.

  (** *** Associativity *)
  (******************************************************************************)
  Lemma kc7_assoc
    `{Applicative G3}
    `{Applicative G2}
    `{Applicative G1}:
    forall (h: W * C -> G3 (T D)) (g: W * B -> G2 (T C)) (f: W * A -> G1 (T B)),
      kc7 (G1 ∘ G2) G3 h (g ⋆7 f) = kc7 G1 (G2 ∘ G3) (h ⋆7 g) f.
  Proof.
    intros.
    unfold kc7 at 1 2.
    ext [w a].
    unfold_ops @Map_compose.
    compose near (f (w, a)) on left.
    rewrite (fun_map_map (F := G1)).
    rewrite kdtm_binddt2.
    rewrite kc7_preincr.
    unfold kc7 at 2.
    reflexivity.
  Qed.

End decorated_monad_kleisli_composition.

(** * Derived Structures *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.
  Section operations.

    Context
      (W: Type)
      (T: Type -> Type)
      (U: Type -> Type)
      `{Return_T: Return T}
      `{Bindd_WTU: Binddt W T U}.

    #[export] Instance Map_Binddt: Map U :=
      fun (A B: Type) (f: A -> B) =>
        binddt (G := fun A => A) (ret (T := T) ∘ f ∘ extract (W := (W ×))).
    #[export] Instance Mapdt_Binddt: Mapdt W U
      := fun G _ _ _ A B f =>
           binddt (map (F := G) (ret (T := T)) ∘ f).
    #[export] Instance Bindd_Binddt: Bindd W T U
      := fun A B f => binddt (G := fun A => A) f.

    #[export] Instance Bindt_Binddt: Bindt T U
      := fun G _ _ _ A B f =>
           binddt (f ∘ extract (W := (W ×))).

    #[export] Instance Bind_Binddt: Bind T U
      := fun A B f =>
           binddt (G := fun A => A) (f ∘ extract (W := (W ×))).

    #[export] Instance Mapd_Binddt: Mapd W U
      := fun A B f => binddt (G := fun A => A) (ret (T := T) ∘ f).

    #[export] Instance Traverse_Binddt: Traverse U
      := fun G _ _ _ A B f =>
           binddt (map (F := G) (ret (T := T)) ∘ f ∘ extract (W := (W ×))).

  End operations.
End DerivedOperations.

(** ** Compatibility Typeclasses *)
(******************************************************************************)
Section decorated_traversable_monad_compat.

  Context
    (W: Type)
    (T: Type -> Type)
    (U: Type -> Type)
    `{Return_T: Return T}
    `{Binddt_inst: Binddt W T U}
    `{Map_inst: Map U}
    `{Mapd_inst: Mapd W U}
    `{Traverse_inst: Traverse U}
    `{Bind_inst: Bind T U}
    `{Mapdt_inst: Mapdt W U}
    `{Bindd_inst: Bindd W T U}
    `{Bindt_inst: Bindt T U}.

  Class Compat_Map_Binddt: Prop :=
    compat_map_binddt:
      Map_inst =
        @DerivedOperations.Map_Binddt W T U Return_T Binddt_inst.

  Class Compat_Mapd_Binddt: Prop :=
    compat_mapd_binddt:
      Mapd_inst =
        @DerivedOperations.Mapd_Binddt W T U Return_T Binddt_inst.

  Class Compat_Traverse_Binddt: Prop :=
    compat_traverse_binddt:
      Traverse_inst =
        @DerivedOperations.Traverse_Binddt W T U Return_T Binddt_inst.

  Class Compat_Bind_Binddt: Prop :=
    compat_bind_binddt:
      Bind_inst =
        @DerivedOperations.Bind_Binddt W T U Binddt_inst.

  Class Compat_Bindd_Binddt: Prop :=
    compat_bindd_binddt:
      Bindd_inst =
        @DerivedOperations.Bindd_Binddt W T U Binddt_inst.

  Class Compat_Bindt_Binddt: Prop :=
    compat_bindt_binddt:
      Bindt_inst =
        @DerivedOperations.Bindt_Binddt W T U Binddt_inst.

  Class Compat_Mapdt_Binddt: Prop :=
    compat_mapdt_binddt:
      Mapdt_inst =
        @DerivedOperations.Mapdt_Binddt W T U Return_T Binddt_inst.

  Class Compat_Full_Binddt: Prop :=
    { compat_map_binddt_full :> Compat_Map_Binddt;
      compat_mapd_binddt_full :> Compat_Mapd_Binddt;
      compat_traverse_binddt_full :> Compat_Traverse_Binddt;
      compat_bind_binddt_full :> Compat_Bind_Binddt;
      compat_bindd_binddt_full :> Compat_Bindd_Binddt;
      compat_bindt_binddt_full :> Compat_Bindt_Binddt;
      compat_mapdt_binddt_full :> Compat_Mapdt_Binddt;
    }.

End decorated_traversable_monad_compat.

Section decorated_traversable_monad_compat_self.

  Context
    (W: Type)
    (T: Type -> Type)
    (U: Type -> Type)
    `{Return_T: Return T}
    `{Binddt_WTU: Binddt W T U}.

  #[export] Instance Compat_Map_Binddt_Self:
    Compat_Map_Binddt W T U
      (Map_inst := DerivedOperations.Map_Binddt W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Mapd_Binddt_Self:
    Compat_Mapd_Binddt W T U
      (Mapd_inst := DerivedOperations.Mapd_Binddt W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Traverse_Binddt_Self:
    Compat_Traverse_Binddt W T U
      (Traverse_inst := DerivedOperations.Traverse_Binddt W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Bind_Binddt_Self:
    Compat_Bind_Binddt W T U
      (Bind_inst := DerivedOperations.Bind_Binddt W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Bindd_Binddt_Self:
    Compat_Bindd_Binddt W T U
      (Bindd_inst := DerivedOperations.Bindd_Binddt W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Bindt_Binddt_Self:
    Compat_Bindt_Binddt W T U
      (Bindt_inst := DerivedOperations.Bindt_Binddt W T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Mapdt_Binddt_Self:
    Compat_Mapdt_Binddt W T U
      (Mapdt_inst := DerivedOperations.Mapdt_Binddt W T U).
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
    unfold_ops @DerivedOperations.Map_Bind;
    unfold_ops @DerivedOperations.Map_Traverse;
    unfold_ops @DerivedOperations.Map_Mapd;
    unfold_ops @DerivedOperations.Map_Mapdt;
    unfold_ops @DerivedOperations.Mapd_Mapdt;
    unfold_ops @DerivedOperations.Traverse_Mapdt;
    unfold_ops @DerivedOperations.Map_Bindd;
    unfold_ops @DerivedOperations.Mapd_Bindd;
    unfold_ops @DerivedOperations.Bind_Bindd;
    unfold_ops @DerivedOperations.Map_Bindt;
    unfold_ops @DerivedOperations.Traverse_Bindt;
    unfold_ops @DerivedOperations.Bind_Bindt;
    normalize_binddt;
    reflexivity.

  Context
    `{Map_U: Map U}
    `{Mapd_WU: Mapd W U}
    `{Traverse_U: Traverse U}
    `{Mapdt_WU: Mapdt W U}
    `{Bind_TU: Bind T U}
    `{Bindd_WTU: Bindd W T U}
    `{Bindt_TU: Bindt T U}
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Mapd_Binddt W T U}
    `{! Compat_Traverse_Binddt W T U}
    `{! Compat_Mapdt_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    `{! Compat_Bindt_Binddt W T U}.

  (** *** Compatibility with <<traverse>>, <<mapd>>, and <<bind>>.*)
  #[export] Instance Compat_Map_Traverse_Binddt:
    Compat_Map_Traverse U := ltac:(solve_compat).

  #[export] Instance Compat_Map_Mapd_Binddt:
    Compat_Map_Mapd W U := ltac:(solve_compat).

  #[export] Instance Compat_Map_Bind_Binddt:
    Compat_Map_Bind T U := ltac:(solve_compat).

  (** *** Compatibility with <<bindd>> *)
  #[export] Instance Compat_Map_Bindd_Binddt:
    Compat_Map_Bindd W T U := ltac:(solve_compat).

  #[export] Instance Compat_Mapd_Bindd_Binddt:
    Compat_Mapd_Bindd W T U := ltac:(solve_compat).

  #[export] Instance Compat_Bind_Bindd_Binddt:
    Compat_Bind_Bindd W T U := ltac:(solve_compat).

  (** *** Compatibility with <<bindt>> *)
  #[export] Instance Compat_Map_Bindt_Bindtt:
    Compat_Map_Bindt T U := ltac:(solve_compat).

  #[export] Instance Compat_Traverse_Bindt_Bindtt:
    Compat_Traverse_Bindt T U := ltac:(solve_compat).

  #[export] Instance Compat_Bind_Bindt_Bindtt:
    Compat_Bind_Bindt T U := ltac:(solve_compat).

  (** *** Compatibility with <<mapdt>> *)
  #[export] Instance Compat_Map_Mapdt_Binddt:
    Compat_Map_Mapdt W U := ltac:(solve_compat).

  #[export] Instance Compat_Mapd_Mapdt_Binddt:
    Compat_Mapd_Mapdt W U := ltac:(solve_compat).

  #[export] Instance Compat_Traverse_Mapdt_Binddt:
    Compat_Traverse_Mapdt W U := ltac:(solve_compat).

End decorated_traversable_monad_compat_self.

(** ** Rewriting <<X>> to <<binddt>> Lemmas *)
(******************************************************************************)
Section rewriting.

  Context
    `{Return_T: Return T}
    `{Map_U: Map U}
    `{Mapd_WU: Mapd W U}
    `{Traverse_U: Traverse U}
    `{Bind_TU: Bind T U}
    `{Mapdt_WU: Mapdt W U}
    `{Bindd_WTU: Bindd W T U}
    `{Bindt_TU: Bindt T U}
    `{Binddt_WTU: Binddt W T U}.

  Lemma map_to_binddt `{! Compat_Map_Binddt W T U}:
    forall `(f: A -> B),
      map (F := U) f =
        binddt (G := fun A => A) (ret (T := T) ∘ f ∘ extract).
  Proof.
    rewrite (compat_map_binddt W T U).
    reflexivity.
  Qed.

  Lemma mapd_to_binddt `{! Compat_Mapd_Binddt W T U}:
    forall `(f: W * A -> B),
      mapd (T := U) f =
        binddt (G := fun A => A) (ret (T := T) ∘ f).
  Proof.
    rewrite (compat_mapd_binddt W T U).
    reflexivity.
  Qed.

  Lemma traverse_to_binddt `{! Compat_Traverse_Binddt W T U}
    `{Applicative G}:
    forall `(f: A -> G B),
      traverse (G := G) (T := U) f =
        binddt (U := U) (map (F := G) (ret (T := T)) ∘ f ∘ extract).
  Proof.
    rewrite (compat_traverse_binddt W T U).
    reflexivity.
  Qed.

  Lemma bind_to_binddt `{! Compat_Bind_Binddt W T U}:
    forall `(f: A -> T B),
    bind (U := U) f = binddt (U := U) (f ∘ extract).
  Proof.
    rewrite (compat_bind_binddt W T U).
    reflexivity.
  Qed.

  Lemma mapdt_to_binddt `{! Compat_Mapdt_Binddt W T U}:
    forall `{Applicative G} `(f: W * A -> G B),
      mapdt (G := G) f = binddt (map (ret (T := T)) ∘ f).
  Proof.
    rewrite (compat_mapdt_binddt W T U).
    reflexivity.
  Qed.

  Lemma mapdt_to_binddt' `{! Compat_Mapdt_Binddt W T U}:
    forall `{Applicative G}
      (A B: Type),
      mapdt (T := U) (G := G) (A := A) (B := B) =
        binddt ∘ compose (map ret).
  Proof.
    intros.
    ext f.
    rewrite mapdt_to_binddt.
    reflexivity.
  Qed.

  Lemma bindd_to_binddt `{! Compat_Bindd_Binddt W T U}:
    forall A B,
      bindd (T := T) (U := U) (A := A) (B := B) = binddt (G := fun A => A).
  Proof.
    rewrite (compat_bindd_binddt W T U).
    reflexivity.
  Qed.

  Lemma bindt_to_binddt `{! Compat_Bindt_Binddt W T U}
    `{Applicative G} `(f: A -> G (T B)):
    bindt (G := G) f =
      binddt (U := U) (f ∘ extract).
  Proof.
    rewrite (compat_bindt_binddt W T U).
    reflexivity.
  Qed.

  Lemma map_to_bind
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    : forall (A B: Type) (f: A -> B),
      map f = bind (ret ∘ f).
  Proof.
    rewrite (compat_map_bind
               (Compat_Map_Bind :=
                  Compat_Map_Bind_Binddt W T U)).
    reflexivity.
  Qed.

  Lemma map_to_bindd
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    : forall (A B: Type) (f: A -> B),
      map (F := U) f = bindd (ret ∘ f ∘ extract).
  Proof.
    intros.
    rewrite (compat_map_bindd W T U
               (Compat_Map_Bindd :=
                  Compat_Map_Bindd_Binddt W T U)).
    reflexivity.
  Qed.

End rewriting.

(** ** Composition with the Identity Applicative Functor *)
(******************************************************************************)
Section properties.

  Context
    `{DecoratedTraversableRightModule W T U}.

  Lemma binddt_app_id_l :
    forall {G: Type -> Type} {A B: Type}
      `{Applicative G} (f: W * A -> G (T B)),
      @binddt W T U _ ((fun A => A) ∘ G)
        (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G)
        (Mult_compose (fun A => A) G) A B f =
        binddt (T := T) f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma binddt_app_id_r :
    forall {G: Type -> Type} {A B: Type}
      `{Applicative G} (f: W * A -> G (T B)),
      @binddt W T U _ (G ∘ (fun A => A))
        (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A))
        (Mult_compose G (fun A => A)) A B f =
        binddt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity1 G).
  Qed.

End properties.

(** ** Derived Kleisli Composition Laws *)
(******************************************************************************)
Section derived_instances.

  (** *** Section Context *)
  (******************************************************************************)
  Context
    `{op: Monoid_op W}
    `{unit: Monoid_unit W}
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Mapd_T_inst: Mapd W T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Mapdt_T_inst: Mapdt W T}
    `{Bindd_T_inst: Bindd W T T}
    `{Bindt_T_inst: Bindt T T}
    `{Binddt_T_inst: Binddt W T T}
    `{! Compat_Map_Binddt W T T}
    `{! Compat_Mapd_Binddt W T T}
    `{! Compat_Traverse_Binddt W T T}
    `{! Compat_Bind_Binddt W T T}
    `{! Compat_Mapdt_Binddt W T T}
    `{! Compat_Bindd_Binddt W T T}
    `{! Compat_Bindt_Binddt W T T}
    `{Monad_inst: ! DecoratedTraversableMonad W T}
    `{Map_U_inst: Map U}
    `{Mapd_U_inst: Mapd W U}
    `{Traverse_U_inst: Traverse U}
    `{Bind_U_inst: Bind T U}
    `{Mapdt_U_inst: Mapdt W U}
    `{Bindd_U_inst: Bindd W T U}
    `{Bindt_U_inst: Bindt T U}
    `{Binddt_U_inst: Binddt W T U}
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Mapd_Binddt W T U}
    `{! Compat_Traverse_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    `{! Compat_Mapdt_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    `{! Compat_Bindt_Binddt W T U}
    `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  (*
  Context
    {W: Type}
    {T: Type -> Type}
    `{Compat_Full_Binddt W T T}
    `{Monoid_unit_W: Monoid_unit W}
    `{Monoid_op_W: Monoid_op W}
    `{! DecoratedTraversableMonad W T}.
*)


  (** *** Tactical support (TODO move me) *)
  (******************************************************************************)
  #[local] Ltac unfold_map_id :=
    repeat (change (map (F := fun A => A) ?f) with f).

  #[local] Hint Unfold kc7 kc6 kc5 kc kc3 kc2 kc1: tealeaves_kc_unfold.

  #[local] Ltac setup :=
    intros;
    autounfold with tealeaves_kc_unfold;
    ext [w a];
    unfold_map_id.

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

  (** *** Homogeneous Kleisli composition laws *)
  (******************************************************************************)
  Section composition.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Variables (A B C: Type).

    (** **** Lemmas <<kc7_xx>> *)
    (******************************************************************************)
    Lemma kc7_33:
      forall (g: W * B -> G2 C) (f: W * A -> G1 B),
        (map (F := G2) (ret (T := T)) ∘ g) ⋆7
          (map (F := G1) (ret (T := T)) ∘ f) =
          map (F := G1 ∘ G2) (ret (T := T)) ∘ (g ⋆3 f).
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
      unfold kc3.
      unfold_ops @Map_compose.
      do 2 reassociate <- on right.
      unfold_compose_in_compose; rewrite (fun_map_map (F := G1)).
      unfold_ops @Cobind_reader; unfold strength.
      unfold compose at 3 4.
      compose near (f (w, a)) on right.
      rewrite (fun_map_map (F := G1)).
      reflexivity.
    Qed.

    Lemma kc7_55:
      forall `(g: W * B -> T C) `(f: W * A -> T B),
        kc7 (fun A => A) (fun A => A) g f = g ⋆5 f.
    Proof.
      intros.
      unfold kc5.
      ext [w a].
      rewrite bindd_to_binddt.
      reflexivity.
    Qed.

    Lemma kc7_44:
      forall `(g: W * B -> C) `(f: W * A -> B),
        kc7 (fun A => A) (fun A => A)
          (ret (T := T) ∘ g) (ret (T := T) ∘ f) =
          ret (T := T) ∘ (g ⋆1 f).
    Proof.
      intros.
      rewrite kc7_55.
      unfold kc5.
      ext [w a].
      unfold compose at 2.
      compose near (f (w, a)) on left.
      rewrite bindd_to_binddt.
      rewrite (kdtm_binddt0 (G := fun A => A)).
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_66:
      forall (g: B -> G2 (T C)) (f: A -> G1 (T B)),
        kc7 G1 G2
          (g ∘ extract (W := (W ×)))
          (f ∘ extract (W := (W ×))) =
          (g ⋆6 f) ∘ extract (W := (W ×)).
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      rewrite preincr_assoc.
      rewrite extract_preincr.
      unfold kc6.
      rewrite bindt_to_binddt.
      reflexivity.
    Qed.

    Lemma kc7_22:
      forall (g: B -> G2 C) (f: A -> G1 B),
        kc7 G1 G2
          (map (F := G2) (ret (T := T)) ∘ g ∘ extract (W := (W ×)))
          (map (F := G1) (ret (T := T)) ∘ f ∘ extract (W := (W ×))) =
          kc2 (G1 := G1 ∘ G2) (ret (T := T))
            ((map (F := G1) g ∘ f)) ∘ extract (W := (W ×)).
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
      unfold kc2.
      unfold_ops @Map_compose.
      unfold compose; cbn.
      compose near (f a) on right.
      rewrite fun_map_map.
      reflexivity.
    Qed.

    Lemma kc7_11 :
      forall (g: B -> T C) (f: A -> T B),
        kc7 (fun A => A) (fun A => A)
          (g ∘ extract (W := (W ×)))
          (f ∘ extract (W := (W ×))) =
          (g ⋆ f) ∘ extract (W := (W ×)).
    Proof.
      setup.
      rewrite (bind_to_binddt (T := T)).
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    Lemma kc7_00 :
      forall (g: B -> C) (f: A -> B),
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

  (** ** Rewriting rules for special cases of <<kc7>> *)
  (******************************************************************************)
  Section kc7_special_cases.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C D: Type}.

    (** *** Lemmas <<kc7_x7>> *)
    (******************************************************************************)
    Lemma kc7_07:
      forall (g: B -> C) (f: W * A -> G1 (T B)),
        ret (T := T) ∘ g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1) (map (F := T) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_17:
      forall (g: B -> T C) (f: W * A -> G1 (T B)),
        g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1) (bind (U := T) (T := T) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_27:
      forall (g: B -> G2 C) (f: W * A -> G1 (T B)),
        map (F := G2) (ret (T := T)) ∘ g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1) (traverse (T := T) (G := G2) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_67:
      forall (g: B -> G2 (T C)) (f: W * A -> G1 (T B)),
        (g ∘ extract (W := (W ×))) ⋆7 f = g ⋆6 f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_47:
      forall (g: W * B -> C) (f: W * A -> G1 (T B)),
        kc7 G1 (fun A => A) (ret (T := T) ∘ g) f =
          (fun '(w, a) => map (F := G1) (mapd (g ⦿ w)) (f (w, a))).
    Proof.
      solve_kc7.
    Qed.


    Lemma kc7_57:
      forall (g: W * B -> T C) (f: W * A -> G1 (T B)),
        kc7 G1 (fun A => A) g f = g ⋆7 f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc7_37:
      forall (g: W * B -> G2 C) (f: W * A -> G1 (T B)),
        (map (F := G2) (ret (T := T)) ∘ g) ⋆7 f =
          (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f (w, a))).
    Proof.
      solve_kc7.
    Qed.

    (** *** Lemmas <<kc7_7x>> *)
    (******************************************************************************)
    Lemma kc7_73:
      forall (g: W * B -> G2 (T C)) (f: W * A -> G1 B),
        g ⋆7 (map (F := G1) ret ∘ f) = g ⋆3 f.
    Proof.
      intros. unfold kc7, kc3.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)).
      rewrite fun_map_map.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_75:
      forall (g: W * B -> G2 (T C)) (f: W * A -> T B),
        kc7 (fun A => A) G2 g f = fun '(w, a) => binddt (g ⦿ w) (f (w, a)).
    Proof.
      reflexivity.
    Qed.

    Lemma kc7_74:
      forall (g: W * B -> G2 (T C)) (f: W * A -> B),
        kc7 (fun A => A) G2 g (ret (T := T) ∘ f) = g ⋆1 f.
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

    Lemma kc7_76:
      forall (g: W * B -> G2 (T C)) (f: A -> G1 (T B)),
        g ⋆7 (f ∘ extract (W := (W ×))) =
          fun '(w, a) => map (F := G1) (binddt (g ⦿ w)) (f a).
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_72:
      forall (g: W * B -> G2 (T C)) (f: A -> G1 B),
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

    Lemma kc7_71:
      forall (g: W * B -> G2 (T C)) (f: A -> T B),
        kc7 (fun A => A) G2 g (f ∘ extract (W := (W ×))) =
          fun '(w, a) => binddt (g ⦿ w) (f a).
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_70:
      forall (g: W * B -> G2 (T C)) (f: A -> B),
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
    Lemma kc7_56:
      forall (g: W * B -> T C) (f: W * A -> G1 B),
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

    Lemma kc7_63:
      forall (g: B -> G2 (T C)) (f: W * A -> G1 B),
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

End derived_instances.

(** ** Derived Composition Laws *)
(******************************************************************************)
Section other_composition_laws.

  Context
    `{op: Monoid_op W}
    `{unit: Monoid_unit W}
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Mapd_T_inst: Mapd W T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Mapdt_T_inst: Mapdt W T}
    `{Bindd_T_inst: Bindd W T T}
    `{Bindt_T_inst: Bindt T T}
    `{Binddt_T_inst: Binddt W T T}
    `{! Compat_Map_Binddt W T T}
    `{! Compat_Mapd_Binddt W T T}
    `{! Compat_Traverse_Binddt W T T}
    `{! Compat_Bind_Binddt W T T}
    `{! Compat_Mapdt_Binddt W T T}
    `{! Compat_Bindd_Binddt W T T}
    `{! Compat_Bindt_Binddt W T T}
    `{Monad_inst: ! DecoratedTraversableMonad W T}
    `{Map_U_inst: Map U}
    `{Mapd_U_inst: Mapd W U}
    `{Traverse_U_inst: Traverse U}
    `{Bind_U_inst: Bind T U}
    `{Mapdt_U_inst: Mapdt W U}
    `{Bindd_U_inst: Bindd W T U}
    `{Bindt_U_inst: Bindt T U}
    `{Binddt_U_inst: Binddt W T U}
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Mapd_Binddt W T U}
    `{! Compat_Traverse_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    `{! Compat_Mapdt_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    `{! Compat_Bindt_Binddt W T U}
    `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.


  (*
  Context
    {W: Type}
    {T: Type -> Type}
    `{Return_T: Return T}
    `{Map_T: Map T}
    `{Mapd_T: Mapd W T}
    `{Traverse_T: Traverse T}
    `{Bind_T: Bind T T}
    `{Mapdt_T: Mapdt W T}
    `{Bindd_T: Bindd W T T}
    `{Bindt_T: Bindt T T}
    `{Binddt_T: Binddt W T T}
    `{Monoid_unit_W: Monoid_unit W}
    `{Monoid_op_W: Monoid_op W}
    `{! DecoratedTraversableMonad W T}
    `{! Compat_Full_Binddt W T T}.

  Context
    {U: Type -> Type}
    `{Map_U: Map U}
    `{Mapd_U: Mapd W U}
    `{Traverse_U: Traverse U}
    `{Bind_U: Bind T U}
    `{Mapdt_U: Mapdt W U}
    `{Bindd_U: Bindd W T U}
    `{Bindt_U: Bindt T U}
    `{Binddt_U: Binddt W T U}
    `{! DecoratedTraversableRightModule W T U}
    `{! Compat_Full_Binddt W T U}.
*)

  (** *** Homogeneous composition laws *)
  (******************************************************************************)
  Section composition.

    Context
      {G1: Type -> Type}
      `{Map G1} `{Pure G1} `{Mult G1} `{! Applicative G1}
      {G2: Type -> Type}
      `{Map G2} `{Pure G2} `{Mult G2} `{! Applicative G2}.

    Variables (A B C: Type).

    (* composition_33 *)
    Lemma mapdt_mapdt: forall
        (g: W * B -> G2 C)
        (f: W * A -> G1 B),
        map (F := G1) (A := U B) (B := G2 (U C))
          (mapdt (T := U) g) ∘ mapdt (T := U) f =
          mapdt (T := U) (G := G1 ∘ G2) (g ⋆3 f).
    Proof.
      intros.
      do 2 rewrite mapdt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_33.
      rewrite <- mapdt_to_binddt.
      reflexivity.
    Qed.

    (* composition_55 *)
    Lemma bindd_bindd: forall
        (g: W * B -> T C)
        (f: W * A -> T B),
        bindd g ∘ bindd (U := U) f = bindd (U := U) (g ⋆5 f).
    Proof.
      intros.
      do 2 rewrite bindd_to_binddt.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      change ((fun A => A) ?f) with f.
      rewrite (kdtm_binddt2 (T := T) (U := U) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite (binddt_app_id_l (T := T) (U := U)).
      rewrite kc7_55.
      rewrite <- bindd_to_binddt.
      reflexivity.
    Qed.

    (* composition_44 *)
    Lemma mapd_mapd: forall (g: W * B -> C) (f: W * A -> B),
        mapd g ∘ mapd f = mapd (g ∘ cobind (W := (W ×)) f).
    Proof.
      intros.
      do 2 rewrite mapd_to_binddt.
      change (binddt (ret (T := T) ∘ g)) with
        (map (F := fun A => A) (binddt (ret (T := T) ∘ g))).
      change ((fun A => A) ?f) with f.
      rewrite (kdtm_binddt2 (T := T) (U := U) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_id_l.
      rewrite kc7_44.
      rewrite <- mapd_to_binddt.
      reflexivity.
    Qed.

    (* composition_66 *)
    Lemma bindt_bindt:
      forall (g: B -> G2 (T C)) (f: A -> G1 (T B)),
        map (F := G1) (bindt g) ∘ bindt f =
          bindt (U := U) (G := G1 ∘ G2) (g ⋆6 f).
    Proof.
      intros.
      do 2 rewrite bindt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_66.
      rewrite <- (bindt_to_binddt (A := A) (B := C)
                   (U := U) (T := T) (G := G1 ○ G2)).
      reflexivity.
    Qed.

    (* composition_22 *)
    Lemma traverse_traverse: forall (g: B -> G2 C) (f: A -> G1 B),
        map (F := G1) (traverse (G := G2) g) ∘ traverse (G := G1) f =
          traverse (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      intros.
      do 2 rewrite traverse_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_22.
      unfold kc2.
      rewrite <- (traverse_to_binddt
                   (T := T)
                   (G := G1 ∘ G2)
                   (@map G1 H B (G2 C) g ∘ f)).
      reflexivity.
    Qed.

    (* composition_11 *)
    Lemma bind_bind: forall (g: B -> T C) (f: A -> T B),
        bind g ∘ bind f = bind (U := U) (g ⋆ f).
    Proof.
      intros.
      do 2 rewrite bind_to_binddt.
      change (binddt (g ∘ extract)) with
        (map (F := fun A => A) (binddt (g ∘ extract))).
      change ((fun A => A) ?f) with f.
      rewrite (kdtm_binddt2 (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_id_l.
      rewrite kc7_11.
      rewrite <- bind_to_binddt.
      reflexivity.
    Qed.

    (* composition_00 *)
    Lemma map_map: forall (f: A -> B) (g: B -> C),
        map g ∘ map f = map (F := U) (g ∘ f).
    Proof.
      intros.
      do 2 rewrite map_to_binddt.
      change (binddt (?ret ∘ g ∘ ?extract)) with
        (map (F := fun A => A) (binddt (ret ∘ g ∘ extract))).
      change ((fun A => A) ?f) with f.
      rewrite (kdtm_binddt2 (T := T) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_id_l.
      rewrite kc7_00.
      change (?ret ∘ g ∘ f ∘ ?extract) with
        (ret ∘ (g ∘ f) ∘ extract).
      rewrite <- map_to_binddt.
      reflexivity.
    Qed.

    (*
  End composition.

  Section composition_special_cases_top.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C: Type}.

    *)

    (** *** <<binddt>> on the right *)
    (******************************************************************************)
    (* composition_67 *)
    Lemma mapdt_binddt:
      forall (g: W * B -> G2 C)
        (f: W * A -> G1 (T B)),
        map (F := G1) (mapdt g) ∘ binddt f =
          binddt (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_37.
      reflexivity.
    Qed.

    (* composition_57 *)
    Lemma bindd_binddt:
      forall (g: W * B -> T C)
        (f: W * A -> G1 (T B)),
        map (F := G1) (bindd g) ∘ binddt f =
          binddt (fun '(w, a) => map (F := G1) (bindd (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      rewrite bindd_to_binddt.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite binddt_app_id_r.
      unfold kc7.
      reflexivity.
    Qed.

    (* composition_47 *)
    Lemma mapd_binddt: forall
        (g: W * B -> C)
        (f: W * A -> G1 (T B)),
        map (F := G1) (mapd g) ∘ binddt f =
          binddt (fun '(w, a) => map (F := G1) (mapd (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite mapd_to_binddt.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite binddt_app_id_r.
      rewrite kc7_47.
      reflexivity.
    Qed.

    (* composition_67 *)
    Lemma bindt_binddt:
      forall (g: B -> G2 (T C))
        (f: W * A -> G1 (T B)),
        map (F := G1) (bindt g) ∘ binddt f =
          binddt (G := G1 ∘ G2) (map (F := G1) (bindt g) ∘ f).
    Proof.
      intros.
      rewrite bindt_to_binddt at 1.
      rewrite kdtm_binddt2.
      rewrite kc7_67.
      reflexivity.
    Qed.

    (* composition_27 *)
    Lemma traverse_binddt: forall
        (g: B -> G2 C)
        (f: W * A -> G1 (T B)),
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
        (g: B -> T C)
        (f: W * A -> G1 (T B)),
        map (F := G1) (bind g) ∘ binddt f =
          binddt (map (F := G1) (bind g) ∘ f).
    Proof.
      intros.
      rewrite bind_to_binddt at 1.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite kc7_17.
      rewrite binddt_app_id_r.
      reflexivity.
    Qed.

    (* composition_07 *)
    Lemma map_binddt:
      forall (g: B -> C)
        (f: W * A -> G1 (T B)),
        map (F := G1) (map (F := U) g) ∘ binddt f =
          binddt (map (F := G1) (map (F := T) g) ∘ f).
    Proof.
      intros.
      rewrite (map_to_binddt (U := U)).
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite kc7_07.
      rewrite binddt_app_id_r.
      reflexivity.
    Qed.

    (** *** <<binddt>> on the left *)
    (******************************************************************************)
    (* composition_73 *)
    Lemma binddt_mapdt: forall
        (g: W * B -> G2 (T C))
        (f: W * A -> G1 B),
        map (F := G1) (binddt g) ∘ mapdt f =
          binddt (U := U) (G := G1 ∘ G2)
            (fun '(w, a) => map (F := G1) (fun b => g (w, b)) (f (w, a))).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_73.
      rewrite kc3_spec.
      reflexivity.
    Qed.

    (* composition_75 *)
    Lemma binddt_bindd: forall
        (g: W * B -> G2 (T C))
        (f: W * A -> T B),
        binddt g ∘ bindd f =
          binddt (U := U) (fun '(w, a) => binddt (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_id_l.
      reflexivity.
    Qed.

    (* composition_74 *)
    Lemma binddt_mapd: forall
        (g: W * B -> G2 (T C))
        (f: W * A -> B),
        binddt g ∘ mapd f = binddt (g ⋆1 f).
    Proof.
      intros.
      rewrite mapd_to_binddt.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite kc7_74.
      rewrite binddt_app_id_l.
      reflexivity.
    Qed.

    (* composition_76 *)
    Lemma binddt_bindt: forall
        (g: W * B -> G2 (T C))
        (f: A -> G1 (T B)),
        map (F := G1) (binddt g) ∘ bindt f =
          binddt (T := T) (G := G1 ∘ G2)
            (fun '(w, a) => map (F := G1) (binddt (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite bindt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_76.
      reflexivity.
    Qed.

    (* composition_72 *)
    Lemma binddt_traverse: forall
        (g: W * B -> G2 (T C))
        (f: A -> G1 B),
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
        (g: W * B -> G2 (T C))
        (f: A -> T B),
        binddt g ∘ bind f =
          binddt (U := U) (fun '(w, a) => binddt (g ⦿ w) (f a)).
    Proof.
      intros.
      rewrite bind_to_binddt.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_id_l.
      rewrite kc7_71.
      reflexivity.
    Qed.

    (* composition_70 *)
    Lemma binddt_map: forall
        (g: W * B -> G2 (T C))
        (f: A -> B),
        binddt g ∘ map (F := U) f =
          binddt (U := U) (g ∘ map (F := (W ×)) f).
    Proof.
      intros.
      rewrite (map_to_binddt (U := U)).
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_id_l.
      rewrite kc7_70.
      reflexivity.
    Qed.

  End composition.

  Section composition_special_cases_middle.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C: Type}.

    (** *** <<bindd>>, <<mapdt>>, <<bindt>> *)
    (******************************************************************************)
    (* composition_56 *)
    Lemma bindd_mapdt: forall
        (g: W * B -> T C)
        (f: W * A -> G1 B),
        map (F := G1) (bindd g) ∘ mapdt f =
          binddt (U := U) (fun '(w, a) => map (F := G1) (g ∘ pair w) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      rewrite (binddt_mapdt (G2 := fun A => A)).
      rewrite binddt_app_id_r.
      reflexivity.
    Qed.

    (* composition_65 *)
    Lemma mapdt_bindd: forall
        (g: W * B -> G2 C)
        (f: W * A -> T B),
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

    (* composition_65 *)
    Lemma bindt_bindd: forall
        (g: B -> G2 (T C))
        (f: W * A -> T B),
        bindt g ∘ bindd f = binddt (U := U) (bindt g ∘ f).
    Proof.
      intros.
      rewrite bindt_to_binddt.
      rewrite bindt_to_binddt.
      rewrite binddt_bindd.
      try rewrite kc7_65. (* TODO *)
      fequal. ext [w a].
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    (* composition_56 *)
    Lemma bindd_bindt: forall
        (g: W * B -> T C)
        (f: A -> G1 (T B)),
        map (F := G1) (bindd g) ∘ bindt f =
          binddt (U := U) (fun '(w, a) => map (F := G1) (bindd (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      rewrite bindt_to_binddt.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      unfold kc7.
      rewrite binddt_app_id_r.
      rewrite bindd_to_binddt.
      reflexivity.
    Qed.

    Lemma mapdt_bindt: forall
        (g: W * B -> G2 C)
        (f: A -> G1 (T B)),
        map (F := G1) (mapdt g) ∘ bindt f =
          binddt (U := U) (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite bindt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_76.
      try rewrite mapdt_to_binddt.
      rewrite (compat_mapdt_binddt W T T).
      unfold DerivedOperations.Mapdt_Binddt.
      reflexivity.
      (*
      Set Printing All.
      Print Instances Compat_Mapdt_Binddt.
      About compat_mapdt_binddt.
      Set Typeclasses Debug.
      About Compat_Full_Binddt0.
      About Compat_Mapdt_Binddt.
      Print Instances Mapdt.
      (*
      assert (Compat_Mapdt_Binddt W T T).
      Set Printing All.
      typeclasses eauto.
       *)
      Set Printing All.
      Hint Unfold mapdt: typeclasses_instances.
      About compat_mapdt_binddt.
      assert (@Compat_Mapdt_Binddt W T T Return_T
                (@mapdt W T Mapdt_T) Binddt_T).
      { try typeclasses eauto.
        unfold mapdt.
        try typeclasses eauto.
      }
      clear H1.
      try rewrite (compat_mapdt_binddt W T T
                     (Binddt_inst := Binddt_T)
                     (Return_T := Return_T)).
      rewrite (compat_mapdt_binddt W T T
                 (Mapdt_inst := ltac:(auto))
                 (Return_T := Return_T)).
                 (Compat_Mapdt_Binddt := compat_mapdt_binddt_full _ _ _)).
       *)
    Qed.

    Lemma bindt_mapdt: forall
        (g: B -> G2 (T C))
        (f: W * A -> G1 B),
        map (F := G1) (bindt g) ∘ mapdt f =
          binddt (U := U) (G := G1 ∘ G2) (map (F := G1) g ∘ f).
    Proof.
      intros.
      rewrite mapdt_to_binddt.
      rewrite bindt_to_binddt.
      rewrite kdtm_binddt2.
      rewrite kc7_63.
      reflexivity.
    Qed.

  End composition_special_cases_middle.

  (* The lemmas below can cite the ones above *)
  Section composition_special_cases_bottom.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C: Type}.

    (** *** <<bindd>> on the right *)
    (******************************************************************************)

    (* composition_25 *)
    Lemma traverse_bindd: forall
        (g: B -> G2 C)
        (f: W * A -> T B),
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
      rewrite (binddt_app_id_l).
      fequal. ext [w a].
      unfold kc7.
      rewrite preincr_assoc.
      rewrite extract_preincr.
      rewrite traverse_to_binddt.
      reflexivity.
    Qed.

    (* composition_52 *)
    (* TODO bindd_traverse *)

    (* composition_46 *)
    Lemma mapd_bindt: forall (g: W * B -> C) (f: A -> G1 (T B)),
        map (F := G1) (mapd g) ∘ bindt (G := G1) f =
          binddt (U := U) (fun '(w, a) => map (F := G1) (mapd (g ⦿ w)) (f a)).
    Proof.
      introv.
      rewrite mapd_to_mapdt.
      rewrite (mapdt_bindt (G2 := fun A => A)).
      rewrite binddt_app_id_r.
      fequal. ext [w a].
      rewrite mapd_to_mapdt.
      reflexivity.
    Qed.
    (* composition_64 *)
    (* TODO bindt_mapd *)

    (* composition_16 *)
    (* TODO bind_mapdt *)

    (* composition_61 *)
    (* TODO mapdt_bind *)

  End composition_special_cases_bottom.

End other_composition_laws.

(** ** Derived Identity/<<ret>>/Appl. Homomorphism Laws *)
(******************************************************************************)
Section derived_instances.

  Context
    `{op: Monoid_op W}
    `{unit: Monoid_unit W}
    `{ret_inst: Return T}
    `{Map_T_inst: Map T}
    `{Mapd_T_inst: Mapd W T}
    `{Traverse_T_inst: Traverse T}
    `{Bind_T_inst: Bind T T}
    `{Mapdt_T_inst: Mapdt W T}
    `{Bindd_T_inst: Bindd W T T}
    `{Bindt_T_inst: Bindt T T}
    `{Binddt_T_inst: Binddt W T T}
    `{! Compat_Map_Binddt W T T}
    `{! Compat_Mapd_Binddt W T T}
    `{! Compat_Traverse_Binddt W T T}
    `{! Compat_Bind_Binddt W T T}
    `{! Compat_Mapdt_Binddt W T T}
    `{! Compat_Bindd_Binddt W T T}
    `{! Compat_Bindt_Binddt W T T}
    `{Monad_inst: ! DecoratedTraversableMonad W T}
    `{Map_U_inst: Map U}
    `{Mapd_U_inst: Mapd W U}
    `{Traverse_U_inst: Traverse U}
    `{Bind_U_inst: Bind T U}
    `{Mapdt_U_inst: Mapdt W U}
    `{Bindd_U_inst: Bindd W T U}
    `{Bindt_U_inst: Bindt T U}
    `{Binddt_U_inst: Binddt W T U}
    `{! Compat_Map_Binddt W T U}
    `{! Compat_Mapd_Binddt W T U}
    `{! Compat_Traverse_Binddt W T U}
    `{! Compat_Bind_Binddt W T U}
    `{! Compat_Mapdt_Binddt W T U}
    `{! Compat_Bindd_Binddt W T U}
    `{! Compat_Bindt_Binddt W T U}
    `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  (** *** <<binddt>> purity *)
  (******************************************************************************)
  Lemma binddt_pure:
    forall (A: Type) `{Applicative G},
      binddt (pure (F := G) ∘ ret (T := T) (A := A) ∘ extract) =
        pure (F := G).
  Proof.
    intros.
    reassociate -> on left.
    rewrite <- (kdtm_morph (fun A => A) G (ϕ := @pure G _)).
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  (** *** Identity laws *)
  (******************************************************************************)
  Lemma bindd_id: forall A: Type,
      bindd (U := U) (ret ∘ extract (W := (W ×))) = @id (U A).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma bindt_id: forall A: Type,
      bindt (G := fun A => A) (ret (T := T)) = @id (U A).
  Proof.
    intros.
    rewrite bindt_to_binddt.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma mapdt_id: forall A: Type,
      mapdt (T := U) (G := fun A => A) (extract (W := (W ×))) = @id (U A).
  Proof.
    intros.
    rewrite (mapdt_to_binddt (G := fun A => A)).
    unfold_ops @Map_I.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma mapd_id: forall A: Type,
      mapd (extract (W := (W ×))) = @id (U A).
  Proof.
    intros.
    rewrite mapd_to_binddt.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma traverse_id: forall A: Type,
      traverse (T := T) (G := fun A => A) (@id A) = id.
  Proof.
    intros.
    rewrite traverse_to_binddt.
    change (?f ∘ id) with f.
    unfold_ops @Map_I.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma bind_id: forall A: Type,
      bind (ret (T := T)) = @id (U A).
  Proof.
    intros.
    rewrite bind_to_binddt.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  Lemma map_id: forall A: Type,
      map (F := U) (@id A) = @id (U A).
  Proof.
    intros.
    rewrite map_to_binddt.
    change (?f ∘ id) with f.
    rewrite kdtm_binddt1.
    reflexivity.
  Qed.

  (** *** Composition with <<ret>> *)
  (******************************************************************************)
  Lemma bindd_ret:
    forall (A B: Type) (f: W * A -> T B),
      bindd (T := T) f ∘ ret (T := T) = f ∘ ret (T := (W ×)).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite (kdtm_binddt0 (G := fun A => A)).
    reflexivity.
  Qed.

  Lemma bindt_ret:
    forall (G: Type -> Type) `{Applicative G} (A B: Type) (f: A -> G (T B)),
      bindt f ∘ ret (T := T) = f.
  Proof.
    intros.
    rewrite bindt_to_binddt.
    rewrite kdtm_binddt0.
    reflexivity.
  Qed.

  Lemma bind_ret:
    forall (A B: Type) (f: A -> T B),
      bind f ∘ ret (T := T) = f.
  Proof.
    intros.
    rewrite bind_to_binddt.
    rewrite (kdtm_binddt0 (G := fun A => A)).
    reflexivity.
  Qed.

  (** *** Naturality in Applicative Morphisms *)
  (******************************************************************************)
  Section applicative_morphisms.

    Context
      (G1 G2: Type -> Type)
        `{Map G1} `{Mult G1} `{Pure G1}
        `{Map G2} `{Mult G2} `{Pure G2}
        (ϕ: forall A: Type, G1 A -> G2 A)
        `{Hmorph: ! ApplicativeMorphism G1 G2 ϕ }.

    Lemma bindt_morph:
      forall (A B: Type) (f: A -> G1 (T B)),
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
      forall (A B: Type) (f: W * A -> G1 B),
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
      forall (A B: Type) (f: A -> G1 B),
        ϕ (T B) ∘ traverse (T := T) (G := G1) f =
          traverse (T := T) (G := G2) (ϕ B ∘ f).
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

End derived_instances.

(** ** Derived Typeclass Instances *)
(******************************************************************************)
Section derived_instances.

    Context
      (W: Type)
      (T: Type -> Type)
      `{op: Monoid_op W}
      `{unit: Monoid_unit W}
      `{ret_inst: Return T}
      `{Map_T_inst: Map T}
      `{Mapd_T_inst: Mapd W T}
      `{Traverse_T_inst: Traverse T}
      `{Bind_T_inst: Bind T T}
      `{Mapdt_T_inst: Mapdt W T}
      `{Bindd_T_inst: Bindd W T T}
      `{Bindt_T_inst: Bindt T T}
      `{Binddt_T_inst: Binddt W T T}
      `{! Compat_Map_Binddt W T T}
      `{! Compat_Mapd_Binddt W T T}
      `{! Compat_Traverse_Binddt W T T}
      `{! Compat_Bind_Binddt W T T}
      `{! Compat_Mapdt_Binddt W T T}
      `{! Compat_Bindd_Binddt W T T}
      `{! Compat_Bindt_Binddt W T T}
      `{Monad_inst: ! DecoratedTraversableMonad W T}.

    #[export] Instance: DecoratedRightPreModule W T T :=
      {| kdmod_bindd1 := bindd_id;
        kdmod_bindd2 := bindd_bindd;
      |}.

    #[export] Instance: DecoratedMonad W T :=
      {| kdm_bindd0 := bindd_ret;
      |}.

    #[export] Instance: TraversableRightPreModule T T.
    Proof.
      constructor; intros.
      - apply bindt_id.
      - apply bindt_bindt.
      - apply (bindt_morph G1 G2 ϕ).
    Qed.

    #[export] Instance: TraversableMonad T :=
      {| ktm_bindt0 := bindt_ret;
      |}.

    #[export] Instance: DecoratedTraversableFunctor W T.
    Proof.
      constructor; intros.
      - apply mapdt_id.
      - apply mapdt_mapdt.
      - apply (mapdt_morph G1 G2 ϕ).
    Qed.

    Context
      (U: Type -> Type)
      `{Map_U_inst: Map U}
      `{Mapd_U_inst: Mapd W U}
      `{Traverse_U_inst: Traverse U}
      `{Bind_U_inst: Bind T U}
      `{Mapdt_U_inst: Mapdt W U}
      `{Bindd_U_inst: Bindd W T U}
      `{Bindt_U_inst: Bindt T U}
      `{Binddt_U_inst: Binddt W T U}
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Mapd_Binddt W T U}
      `{! Compat_Traverse_Binddt W T U}
      `{! Compat_Bind_Binddt W T U}
      `{! Compat_Mapdt_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U}
      `{! Compat_Bindt_Binddt W T U}
      `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

    #[export] Instance: TraversableRightPreModule T U.
    Proof.
      constructor; intros.
      - apply bindt_id.
      - apply bindt_bindt.
      - apply (bindt_morph G1 G2 ϕ).
    Qed.

    #[export] Instance: TraversableRightModule T U :=
      {| ktmod_monad := _
      |}.

    #[export] Instance: DecoratedRightPreModule W T U :=
      {| kdmod_bindd1 := bindd_id;
        kdmod_bindd2 := bindd_bindd;
      |}.

    #[export] Instance: DecoratedRightModule W T U :=
      {| kdmod_monad := _
      |}.

    #[export] Instance: DecoratedTraversableFunctor W U.
    Proof.
      constructor; intros.
      - apply mapdt_id.
      - apply mapdt_mapdt.
      - apply (mapdt_morph G1 G2 ϕ).
    Qed.

    #[local] Instance: DecoratedRightModule W T T :=
      {| kdmod_monad := _
      |}.

    #[local] Instance
      DecoratedTraversableRightModule_DecoratedTraversableMonad:
      DecoratedTraversableRightModule W T T :=
      {| kdtmod_premod := kdtm_premod ; |}.

End derived_instances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆7" := (kc7 _ _) (at level 60): tealeaves_scope.
End Notations.
