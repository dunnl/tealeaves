From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Categorical.Monad (Return, ret).

#[local] Generalizable Variables U T G A B C D ϕ M f.

(** * Traversable Monads *)
(******************************************************************************)

(** ** The [bindt] operation *)
(******************************************************************************)
Class Bindt (T: Type -> Type) (U: Type -> Type) :=
  bindt: forall (G: Type -> Type)
           `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G}
           (A B: Type), (A -> G (T B)) -> U A -> G (U B).

#[global] Arguments bindt {T U}%function_scope {Bindt} {G}%function_scope
  {Map_G Pure_G Mult_G} {A B}%type_scope _%function_scope _.

(** ** Kleisli Composition *)
(******************************************************************************)
Definition kc6
  `{Bindt T T}
  {A B C: Type}
  {G1 G2: Type -> Type}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2}:
  (B -> G2 (T C)) ->
  (A -> G1 (T B)) ->
  (A -> G1 (G2 (T C))) :=
  fun g f => map (F := G1) (bindt g) ∘ f.

#[local] Infix "⋆6" := (kc6) (at level 60): tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class TraversableRightPreModule (T: Type -> Type) (U: Type -> Type)
  `{Return_T: Return T}
  `{Bindt_TT: Bindt T T}
  `{Bindt_TU: Bindt T U} :=
  { ktm_bindt1: forall (A: Type),
      bindt (U := U) (G := fun A => A) (ret (T := T)) = @id (U A);
    ktm_bindt2:
    forall `{Applicative G1} `{Applicative G2} (A B C: Type)
      (g: B -> G2 (T C)) (f: A -> G1 (T B)),
      map (F := G1) (bindt g) ∘ bindt (U := U) f =
        bindt (U := U) (kc6 (G1 := G1) (G2 := G2) g f);
    ktm_morph:
    forall `{morphism: ApplicativeMorphism G1 G2 ϕ}
      (A B: Type) `(f: A -> G1 (T B)),
      ϕ (U B) ∘ bindt (U := U) f = bindt (ϕ (T B) ∘ f);
  }.

Class TraversableMonad (T: Type -> Type)
  `{Return_T: Return T}
  `{Bindt_TT: Bindt T T} :=
  { ktm_bindt0: forall `{Applicative G} (A B: Type) (f: A -> G (T B)),
      bindt f ∘ ret = f;
    ktm_premod :> TraversableRightPreModule T T;
  }.

Class TraversableRightModule (T U: Type -> Type)
  `{Return_T: Return T}
  `{Bindt_TT: Bindt T T}
  `{Bindt_TU: Bindt T U} :=
  { ktmod_monad :> TraversableMonad T;
    ktmod_premod :> TraversableRightPreModule T U;
  }.

#[local] Instance TraversableRightModule_TraversableMonad
  (T: Type -> Type)
  `{TraversableMonad_T: TraversableMonad T} :
  TraversableRightModule T T :=
  {| ktmod_premod := ktm_premod;
  |}.

(** ** Kleisli Category laws *)
(******************************************************************************)
Section Kleisli_composition.

  Context
    `{TraversableMonad T}
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}.

  Lemma kc6_id_l_I: forall `(g: A -> G2 (T B)),
      kc6 (T := T) (G1 := fun A => A) g (ret (T := T)) = g.
  Proof.
    intros.
    unfold kc6.
    unfold_ops @Map_I.
    rewrite ktm_bindt0.
    reflexivity.
  Qed.

  Lemma kc6_id_l: forall `(g: A -> G2 (T B)),
      kc6 (T := T) g (map (F := G1) ret) = map g.
  Proof.
    intros.
    unfold kc6.
    rewrite (fun_map_map (F := G1)).
    rewrite ktm_bindt0.
    reflexivity.
  Qed.

  Lemma kc6_id_r: forall `(f: A -> G1 (T B)),
      kc6 (T := T) (G2 := fun A => A) (ret (T := T)) f = f.
  Proof.
    intros.
    unfold kc6.
    rewrite ktm_bindt1.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma kc6_assoc:
    forall `(h: C -> G3 (T D))
      `(g: B -> G2 (T C))
      `(f: A -> G1 (T B)),
      kc6 (G1 := G1 ∘ G2) h (g ⋆6 f) =
        kc6 (G2 := G2 ∘ G3) (h ⋆6 g) f.
  Proof.
    intros.
    unfold kc6.
    unfold_ops @Map_compose.
    unfold_compose_in_compose.
    ext a.
    unfold compose at 1 2.
    compose near (f a) on left.
    rewrite fun_map_map.
    rewrite ktm_bindt2.
    unfold compose at 2 3.
    reflexivity.
  Qed.

End Kleisli_composition.

(** * Derived Structures *)
(******************************************************************************)
From Tealeaves.Classes.Kleisli Require Import
  TraversableFunctor Monad.


(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.
  Section operations.

    Context
      (T U: Type -> Type)
      `{Return_T: Return T}
      `{Bindt_TU: Bindt T U}.

    #[local] Instance Map_Bindt: Map U :=
      fun (A B: Type) (f: A -> B) => bindt (G := fun A => A) (ret (T := T) ∘ f).

    #[local] Instance Bind_Bindt: Bind T U
      := fun A B f => bindt (T := T) (G := fun A => A) f.

    #[local] Instance Traverse_Bindt: Traverse U
      := fun G _ _ _ A B f => bindt (map (F := G) (ret (T := T)) ∘ f).

  End operations.
End DerivedOperations.

Section compat_classes.

  Context
    (T U: Type -> Type)
    `{Return_T: Return T}
    `{Map_U: Map U}
    `{Traverse_U: Traverse U}
    `{Bind_TU: Bind T U}
    `{Bindt_TU: Bindt T U}.

  Class Compat_Map_Bindt: Prop :=
    compat_map_bindt:
      Map_U = @DerivedOperations.Map_Bindt T U Return_T Bindt_TU.

  Class Compat_Bind_Bindt: Prop :=
    compat_bind_bindt:
      @Bind_TU = @DerivedOperations.Bind_Bindt T U Bindt_TU.

  Class Compat_Traverse_Bindt: Prop :=
    compat_traverse_bindt:
      forall (G: Type -> Type)
        `{Map_G: Map G}
        `{Pure_G: Pure G}
        `{Mult_G: Mult G}
        `{! Applicative G},
        @Traverse_U G Map_G Pure_G Mult_G =
          @DerivedOperations.Traverse_Bindt T U Return_T
            Bindt_TU G Map_G Pure_G Mult_G.

End compat_classes.

Section compat_instances.

  Context
    `{Return_T: Return T}
    `{Bindt_TU: Bindt T U}.

  #[export] Instance Compat_Map_Bindt_Self:
    Compat_Map_Bindt T U (Map_U := DerivedOperations.Map_Bindt T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Bind_Bindt_Self:
    Compat_Bind_Bindt T U (Bind_TU := DerivedOperations.Bind_Bindt T U).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Traverse_Bindt_Self:
    Compat_Traverse_Bindt T U (Traverse_U := DerivedOperations.Traverse_Bindt T U).
  Proof.
    hnf. intros.
    reflexivity.
  Qed.

  #[export] Instance Compat_Map_Bind_Bindt
    `{Map U} `{Bind T U}
    `{! Compat_Bind_Bindt T U}
    `{! Compat_Map_Bindt T U}:
    Compat_Map_Bind T U.
  Proof.
    hnf.
    rewrite (compat_map_bindt T U).
    unfold_ops @DerivedOperations.Map_Bind.
    rewrite (compat_bind_bindt T U).
    reflexivity.
  Qed.

  #[export] Instance Compat_Map_Traverse_Bindt
    `{Map U} `{Traverse U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Map_Bindt T U}:
    Compat_Map_Traverse U.
  Proof.
    hnf.
    rewrite (compat_map_bindt T U).
    unfold_ops @TraversableFunctor.DerivedOperations.Map_Traverse.
    rewrite (compat_traverse_bindt T U (fun A => A)).
    reflexivity.
  Qed.

End compat_instances.

Section rewriting_laws.

  Context
    `{Return_T: Return T}
    `{Map_U: Map U}
    `{Traverse_U: Traverse U}
    `{Bind_TU: Bind T U}
    `{Bindt_TU: Bindt T U}.

  Lemma map_to_bindt `{! Compat_Map_Bindt T U} :
    forall `(f: A -> B), map (F := U) f = bindt (G := fun A => A) (ret (T := T) ∘ f).
  Proof.
    rewrite (compat_map_bindt T U).
    reflexivity.
  Qed.

  Lemma bind_to_bindt `{! Compat_Bind_Bindt T U} `(f: A -> T B):
    bind (U := U) f = bindt (G := fun A => A) f.
  Proof.
    rewrite (compat_bind_bindt T U).
    reflexivity.
  Qed.

  Lemma traverse_to_bindt `{! Compat_Traverse_Bindt T U}
    `{Applicative G} `(f: A -> G B):
    traverse (G := G) (T := U) f = bindt (U := U) (map (F := G) (ret (T := T)) ∘ f).
  Proof.
    rewrite (compat_traverse_bindt T U G).
    reflexivity.
  Qed.

End rewriting_laws.

(** ** Composition with the Identity Applicative *)
(******************************************************************************)
Section traversable_monad_identity_applicative.

  Context
    `{TraversableRightModule T U}.

  Lemma bindt_app_id_l :
    forall {A B: Type} `{Applicative G} (f: A -> G (T B)),
      @bindt T U _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f = bindt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma bindt_app_id_r :
    forall {A B: Type} `{Applicative G} (f: A -> G (T B)),
      @bindt T U _ (G ∘ (fun A => A)) (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f = bindt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity1 G).
  Qed.

End traversable_monad_identity_applicative.

(** ** Derived Kleisli Composition Laws *)
(******************************************************************************)
Section traversable_monad_derived_kleisli_composition_laws.

  Context
    `{Return_T: Return T}
    `{Map_T: Map T}
    `{Traverse_T: Traverse T}
    `{Bind_T: Bind T T}
    `{Bindt_TT: Bindt T T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! TraversableMonad T}.

  Import Kleisli.Monad.Notations.
  Import Kleisli.TraversableFunctor.Notations.

  Context
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}.

  Context (A B C: Type).

  (** *** Homogeneous cases *)
  (******************************************************************************)
  Lemma kc6_22: forall (g: B -> G2 C) (f: A -> G1 B),
      (map ret ∘ g) ⋆6 (map ret ∘ f) =
        map (F := G1 ∘ G2) ret ∘ map (F := G1) g ∘ f.
  Proof.
    intros. unfold kc6.
    reassociate <-.
    rewrite fun_map_map.
    unfold_ops @Map_compose.
    unfold_compose_in_compose.
    rewrite fun_map_map.
    rewrite ktm_bindt0.
    reflexivity.
  Qed.

  Lemma kc6_44: forall (g: B -> T C) (f: A -> T B),
      kc6 (G1 := fun A => A) (G2 := fun A => A) g f = (g ⋆ f).
  Proof.
    intros. unfold kc6, kc.
    rewrite (bind_to_bindt (T := T)).
    reflexivity.
  Qed.

  Lemma kc6_00: forall (g: B -> C) (f: A -> B),
      kc6 (T := T) (G1 := fun A => A) (G2 := fun A => A)
        (ret ∘ g) (ret ∘ f) = ret ∘ g ∘ f.
  Proof.
    intros. unfold kc6.
    reassociate <-.
    change (map (F := fun A => A) ?f) with f.
    rewrite (ktm_bindt0 (G := fun A => A)).
    reflexivity.
  Qed.

  (** *** Heterogeneous cases *)
  (******************************************************************************)
  Lemma kc6_64: forall (g: B -> G2 (T C)) (f: A -> T B),
      kc6 (G1 := fun A => A) (G2 := G2) g f = bindt (G := G2) g ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kc6_62: forall (g: B -> G2 (T C)) (f: A -> G1 B),
      g ⋆6 map ret ∘ f = map g ∘ f.
  Proof.
    intros. unfold kc6.
    reassociate <-.
    rewrite fun_map_map.
    rewrite ktm_bindt0.
    reflexivity.
  Qed.

  Lemma kc6_60: forall (g: B -> G2 (T C)) (f: A -> B),
      kc6 (T := T) (G1 := fun A => A) (G2 := G2) g (ret ∘ f) = g ∘ f.
  Proof.
    intros. unfold kc6. reassociate <-.
    change (map (F := fun A => A) ?f) with f.
    rewrite ktm_bindt0.
    reflexivity.
  Qed.

  Lemma kc6_46: forall (g: B -> T C) (f: A -> G1 (T B)),
      kc6 (G2 := fun A => A) g f = map (F := G1) (bind (T := T) g) ∘ f.
  Proof.
    intros.
    rewrite (bind_to_bindt (T := T)).
    reflexivity.
  Qed.

  Lemma kc6_26: forall (g: B -> G2 C) (f: A -> G1 (T B)),
      map ret ∘ g ⋆6 f = map (traverse g) ∘ f.
  Proof.
    intros.
    rewrite traverse_to_bindt.
    reflexivity.
  Qed.

  Lemma kc6_06: forall (g: B -> C) (f: A -> G1 (T B)),
      kc6 (T := T) (G2 := fun A => A) (ret ∘ g) f = map (map g) ∘ f.
  Proof.
    intros.
    rewrite (map_to_bindt (T := T) (U := T)).
    reflexivity.
  Qed.

  Lemma kc6_42: forall (g: B -> T C) (f: A -> G1 B),
      kc6 (T := T) (G2 := fun A => A) g (map ret ∘ f) = map g ∘ f.
  Proof.
    intros.
    unfold kc6.
    reassociate <-.
    rewrite fun_map_map.
    rewrite (ktm_bindt0 (G := fun A => A)).
    reflexivity.
  Qed.

  Lemma kc6_24: forall (g: B -> G2 C) (f: A -> T B),
      kc6 (map ret ∘ g) f = traverse (G := G2) g ∘ f.
  Proof.
    intros.
    unfold kc6.
    rewrite traverse_to_bindt.
    reflexivity.
  Qed.

  Lemma kc6_20: forall (g: B -> G2 C) (f: A -> B),
      kc6 (T := T) (G1 := fun A => A) (map ret ∘ g) (ret ∘ f) = map ret ∘ g ∘ f.
  Proof.
    intros.
    unfold kc6.
    reassociate <-.
    change (map (F := fun A => A) ?f) with f.
    rewrite ktm_bindt0.
    reflexivity.
  Qed.

  Lemma kc6_02: forall (g: B -> C) (f: A -> G1 B),
      kc6 (T := T) (G2 := fun A => A) (ret ∘ g) (map ret ∘ f) =
        map ret ∘ map g ∘ f.
  Proof.
    intros.
    unfold kc6.
    reassociate <-.
    rewrite fun_map_map.
    rewrite fun_map_map.
    rewrite (ktm_bindt0 (G := fun A => A)).
    reflexivity.
  Qed.

  Lemma kc6_04: forall (g: B -> C) (f: A -> T B),
      kc6 (T := T) (G1 := fun A => A) (G2 := fun A => A) (ret ∘ g) f =
        map g ∘ f.
  Proof.
    intros.
    unfold kc6.
    rewrite (map_to_bindt (U := T) (T := T)).
    reflexivity.
  Qed.

  Lemma kc6_40: forall (g: B -> T C) (f: A -> B),
      kc6 (T := T) (G1 := fun A => A) (G2 := fun A => A) g (ret ∘ f) = g ∘ f.
  Proof.
    intros.
    unfold kc6.
    reassociate <-.
    change (map (F := fun A => A) ?f) with f.
    rewrite (ktm_bindt0 (G := fun A => A)).
    reflexivity.
  Qed.

End traversable_monad_derived_kleisli_composition_laws.

(** ** Derived Composition Laws *)
(******************************************************************************)
Section traversable_monad_derived_composition_laws.

  Import Kleisli.Monad.Notations.
  Import Kleisli.TraversableFunctor.Notations.

  Context
    `{Return_T: Return T}
    `{Map_T: Map T}
    `{Traverse_T: Traverse T}
    `{Bind_T: Bind T T}
    `{Bindt_TT: Bindt T T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{! TraversableMonad T}.

  Context
    `{Map_U: Map U}
    `{Traverse_U: Traverse U}
    `{Bind_TU: Bind T U}
    `{Bindt_TU: Bindt T U}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{! TraversableRightPreModule T U}.

  Context
    `{Applicative G1}
    `{Applicative G2}
    (A B C: Type).

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma traverse_bindt: forall (g: B -> G2 C) (f: A -> G1 (T B)),
      map (traverse g) ∘ bindt f =
        bindt (U := U) (G := G1 ∘ G2) (map (traverse g) ∘ f).
  Proof.
    intros.
    rewrite traverse_to_bindt.
    rewrite traverse_to_bindt.
    rewrite ktm_bindt2.
    reflexivity.
  Qed.

  Lemma bindt_traverse: forall (g: B -> G2 (T C)) (f: A -> G1 B),
      map (bindt g) ∘ traverse f = bindt (U := U) (G := G1 ∘ G2) (map g ∘ f).
  Proof.
    intros.
    rewrite traverse_to_bindt.
    rewrite ktm_bindt2.
    rewrite kc6_62.
    reflexivity.
  Qed.

  (** *** Composition with <<bind>> *)
  (******************************************************************************)
  Lemma bind_bindt: forall (g: B -> T C) (f: A -> G1 (T B)),
      map (bind g) ∘ bindt f = bindt (U := U) (map (bind g) ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt (U := T)).
    rewrite (bind_to_bindt (U := U)).
    rewrite (ktm_bindt2 (G2 := fun A => A)).
    rewrite bindt_app_id_r.
    reflexivity.
  Qed.

  Lemma bindt_bind: forall (g: B -> G2 (T C)) (f: A -> T B),
      bindt g ∘ bind f = bindt (U := U) (bindt g ∘ f).
  Proof.
    intros.
    rewrite bind_to_bindt.
    change (bindt (U := U) g) with
      (map (F := fun A => A) (bindt (U := U) g)).
    rewrite (ktm_bindt2 (G1 := fun A => A)).
    rewrite bindt_app_id_l.
    reflexivity.
  Qed.

  (** *** Composition with <<map>> *)
  (******************************************************************************)
  Lemma map_bindt: forall (g: B -> C) (f: A -> G1 (T B)),
      map (map g) ∘ bindt f = bindt (map (map g) ∘ f).
  Proof.
    intros.
    rewrite (map_to_bindt (U := T)).
    rewrite (map_to_bindt (U := U)).
    rewrite (ktm_bindt2 (G2 := fun A => A)).
    rewrite bindt_app_id_r.
    reflexivity.
  Qed.

  Lemma bindt_map: forall (g: B -> G2 (T C)) (f: A -> B),
      bindt g ∘ map f = bindt (U := U) (g ∘ f).
  Proof.
    intros.
    rewrite (map_to_bindt (T := T) (U := U)).
    change (bindt g) with (map (F := fun A => A) (bindt g)).
    rewrite (ktm_bindt2 (G1 := fun A => A)).
    rewrite bindt_app_id_l.
    rewrite kc6_60.
    reflexivity.
  Qed.

  (** *** Composition between <<traverse>> and <<bind>> *)
  (******************************************************************************)
  Lemma traverse_bind: forall (g: B -> G2 C) (f: A -> T B),
      traverse g ∘ bind f = bindt (traverse g ∘ f).
  Proof.
    intros.
    rewrite traverse_to_bindt.
    rewrite (bind_to_bindt (U := U)).
    change (bindt ?g) with (map (F := fun A => A) (bindt g)) at 1.
    rewrite (ktm_bindt2 (G1 := fun A => A)).
    rewrite bindt_app_id_l.
    rewrite kc6_24.
    rewrite traverse_to_bindt.
    reflexivity.
  Qed.

  Lemma bind_traverse: forall (g: B -> T C) (f: A -> G1 B),
      map (bind g) ∘ traverse f = bindt (map g ∘ f).
  Proof.
    intros.
    rewrite traverse_to_bindt.
    rewrite (bind_to_bindt (U := U)).
    rewrite (ktm_bindt2 (G2 := fun A => A)).
    rewrite bindt_app_id_r.
    rewrite kc6_42.
    reflexivity.
  Qed.

  (** ** Monad Laws *)
  (******************************************************************************)
  Lemma bind_ret: forall (A B: Type) (f: A -> T B),
      bind f ∘ ret = f.
  Proof.
    intros.
    rewrite bind_to_bindt.
    rewrite (ktm_bindt0 (G := fun A => A)).
    reflexivity.
  Qed.

  Lemma bind_id: forall (A: Type),
      bind ret = @id (U A).
  Proof.
    intros.
    rewrite bind_to_bindt.
    rewrite ktm_bindt1.
    reflexivity.
  Qed.

  Lemma bind_bind: forall (g: B -> T C) (f: A -> T B),
      bind g ∘ bind f = bind (U := U) (g ⋆ f).
  Proof.
    intros.
    do 2 rewrite bind_to_bindt.
    change (bindt g) with (map (F := fun A => A) (bindt g)).
    change ((fun A => A) ?x) with x.
    rewrite (ktm_bindt2 (G1 := fun A => A) (G2 := fun A => A)).
    rewrite bindt_app_id_r.
    rewrite kc6_44.
    rewrite bind_to_bindt.
    reflexivity.
  Qed.

  (** ** Traversable Laws *)
  (******************************************************************************)
  Lemma traverse_id: forall (A: Type),
      traverse (G := fun A => A) (@id A) = @id (U A).
  Proof.
    intros.
    rewrite (traverse_to_bindt (G := fun A => A)).
    change (?g ∘ id) with g.
    change (map (F := fun A => A) ?f) with f.
    rewrite ktm_bindt1.
    reflexivity.
  Qed.

  Lemma traverse_traverse:
    forall (g: B -> G2 C) (f: A -> G1 B),
      map (traverse g) ∘ traverse f =
        traverse (T := U) (G := G1 ∘ G2) (map g ∘ f).
  Proof.
    intros.
    rewrite traverse_to_bindt.
    rewrite traverse_to_bindt.
    rewrite ktm_bindt2.
    rewrite kc6_22.
    rewrite traverse_to_bindt.
    reflexivity.
  Qed.

  Lemma traverse_morphism:
    forall `{! ApplicativeMorphism G1 G2 ϕ} (A B: Type) (f: A -> G1 B),
      ϕ (U B) ∘ traverse f = traverse (ϕ B ∘ f).
  Proof.
    intros.
      infer_applicative_instances.
      rewrite traverse_to_bindt.
      rewrite traverse_to_bindt.
      rewrite ktm_morph.
      reassociate <-.
      rewrite appmor_natural_pf.
      reflexivity.
    Qed.

End traversable_monad_derived_composition_laws.

(** ** Derived Typeclass Instances *)
(******************************************************************************)
Module DerivedInstances.

  Section instances.

    Context
      `{Return_T: Return T}
      `{Map_T: Map T}
      `{Traverse_T: Traverse T}
      `{Bind_TT: Bind T T}
      `{Bindt_TT: Bindt T T}
      `{! Compat_Map_Bindt T T}
      `{! Compat_Traverse_Bindt T T}
      `{! Compat_Bind_Bindt T T}
      `{! TraversableMonad T}.

    #[export] Instance TraversableFunctor_TraversableMonad:
      TraversableFunctor T.
    Proof.
      constructor; intros.
      - apply traverse_id.
      - apply traverse_traverse.
      - apply traverse_morphism.
    Qed.

    #[export] Instance RightPreModule_TraversableMonad:
      RightPreModule T T :=
      {| kmod_bind1 := bind_id;
        kmod_bind2 := bind_bind;
      |}.

    #[export] Instance Monad_TraversableMonad: Monad T :=
      {| kmon_bind0 := bind_ret;
      |}.

    #[export] Instance TraversableRightModule_TraversableMonad:
      TraversableRightModule T T :=
      {| ktmod_monad := _; |}.

    #[export] Instance Functor_TraversableMonad: Functor T
      := DerivedInstances.Functor_TraversableFunctor.
    (* or DerivedInstances.Functor_Monad. *)

    Context
      `{Map_U_inst: Map U}
      `{Traverse_U_inst: Traverse U}
      `{Bind_U_inst: Bind T U}
      `{Bindt_U_inst: Bindt T U}
      `{! Compat_Map_Bindt T U}
      `{! Compat_Traverse_Bindt T U}
      `{! Compat_Bind_Bindt T U}
      `{! TraversableRightModule T U}.

    #[export] Instance TraversableFunctor_TraversableRightModule:
      TraversableFunctor U.
    Proof.
      constructor; intros.
      - apply traverse_id.
      - apply traverse_traverse.
      - apply traverse_morphism.
    Qed.

    #[export] Instance Functor_TraversableRightModule:
      Functor U :=  DerivedInstances.Functor_TraversableFunctor.

    #[export] Instance RightPreModule_TraversableRightPreModule:
      RightPreModule T U :=
      {| kmod_bind1 := bind_id;
         kmod_bind2 := bind_bind;
      |}.

    #[export] Instance RightModule_TraversableRightModule:
      RightModule T U :=
      {| kmod_premod := _
      |}.

  End instances.

End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆6" := (kc6) (at level 60): tealeaves_scope.
End Notations.
