From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.Applicative
  Classes.Kleisli.Monad
  Classes.Kleisli.TraversableFunctor.

Import Monad.Notations.
Import TraversableFunctor.Notations.

#[local] Generalizable Variables U T G A B C D ϕ M f.

(** * Traversable monad *)
(******************************************************************************)

(** ** [bindt] operation *)
(******************************************************************************)
Class Bindt
  (T : Type -> Type)
  (U : Type -> Type)
  := bindt :
    forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B : Type), (A -> G (T B)) -> U A -> G (U B).

#[global] Arguments bindt {T U}%function_scope {Bindt} {G}%function_scope
  {H H0 H1} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc3
  `{Bindt T T}
  {A B C : Type}
  {G1 G2 : Type -> Type}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2} :
  (B -> G2 (T C)) ->
  (A -> G1 (T B)) ->
  (A -> G1 (G2 (T C))) :=
  fun g f => map (F := G1) (A := T B) (B := G2 (T C))
            (@bindt T T _ G2 _ _ _ B C g) ∘ f.

#[local] Infix "⋆3" := (kc3) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class TraversableRightPreModule
  (T U : Type -> Type)
  `{Return_inst : Return T}
  `{Bindt_T_inst : Bindt T T}
  `{Bindt_U_inst : Bindt T U} :=
  { ktm_bindt1 : forall (A : Type),
      bindt (U := U) (G := fun A => A) (ret (T := T)) = @id (U A);
    ktm_bindt2 :
    forall `{Applicative G1} `{Applicative G2} {A B C : Type}
      (g : B -> G2 (T C)) (f : A -> G1 (T B)),
      map (F := G1) (bindt g) ∘ bindt (U := U) f =
        bindt (U := U) (kc3 (G1 := G1) (G2 := G2) g f);
    ktm_morph : forall `{morphism : ApplicativeMorphism G1 G2 ϕ} {A B : Type} `(f : A -> G1 (T B)),
      ϕ (U B) ∘ bindt (U := U) f = bindt (ϕ (T B) ∘ f);
  }.

Class TraversableMonad (T : Type -> Type)
  `{Return_inst : Return T}
  `{Bindt_inst : Bindt T T} :=
  { ktm_bindt0 : forall `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt f ∘ ret = f;
    ktm_premod :> TraversableRightPreModule T T;
  }.

Class TraversableRightModule (T U : Type -> Type)
  `{Return_inst : Return T}
  `{Bindt_T_inst : Bindt T T}
  `{Bindt_T_inst : Bindt T U} :=
  { ktmod_monad :> TraversableMonad T;
    ktmod_premod :> TraversableRightPreModule T U;
  }.

(** * Derived instances *)
(******************************************************************************)
Section derived.

  Section operations.

    Context
      T U
      `{Return_inst : Return T}
      `{Bindt_inst : Bindt T U}.

    #[local] Instance Map_Bindt : Map U :=
      fun (A B : Type) (f : A -> B) => bindt (G := fun A => A) (ret (T := T) ∘ f).
    #[local] Instance Bind_Bindt: Bind T U
      := fun A B f => bindt (T := T) (G := fun A => A) f.
    #[local] Instance Traverse_Bindt: Traverse U
      := fun G _ _ _ A B f => bindt (map (F := G) (ret (T := T)) ∘ f).

  End operations.

  Section compat.

    Context
      T U
    `{Return_inst : Return T}
    `{Map_inst : Map U}
    `{Traverse_inst : Traverse U}
    `{Bind_inst : Bind T U}
    `{Bindt_inst : Bindt T U}.

    Class Compat_Map_Bindt : Prop :=
      compat_map_bindt :
        @map U Map_inst = @map U (@Map_Bindt T U Return_inst Bindt_inst).

    Class Compat_Bind_Bindt : Prop :=
      compat_bind_bindt :
        @bind T U Bind_inst = @bind T U (@Bind_Bindt T U Bindt_inst).

    Class Compat_Traverse_Bindt : Prop :=
      compat_traverse_bindt :
        forall {G : Type -> Type}
          `{Map_inst : Map G}
          `{Mult_inst : Mult G}
          `{Pure_inst : Pure G}
          `{! Applicative G},
          @traverse U Traverse_inst G Map_inst Pure_inst Mult_inst =
            @traverse U (@Traverse_Bindt T U Return_inst Bindt_inst)
              G Map_inst Pure_inst Mult_inst.

  End compat.

  Section self.

    Context
    `{Return_inst : Return T}
    `{Bindt_inst : Bindt T U}.

    #[export] Instance Compat_Map_Bindt_Self:
      Compat_Map_Bindt T U (Map_inst := Map_Bindt T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Bind_Bindt_Self:
      Compat_Bind_Bindt T U (Bind_inst := Bind_Bindt T U).
    Proof.
      reflexivity.
    Qed.

    #[export] Instance Compat_Traverse_Bindt_Self:
      Compat_Traverse_Bindt T U (Traverse_inst := Traverse_Bindt T U).
    Proof.
      hnf. intros.
      reflexivity.
    Qed.

    #[export] Instance Compat_Map_Bind_Bindt
     `{Map U} `{Bind T U}
      `{! Compat_Bind_Bindt T U}
      `{! Compat_Map_Bindt T U} :
      Compat_Map_Bind U T.
    Proof.
      hnf.
      rewrite (compat_map_bindt T U).
      unfold_ops @Map_Bind.
      rewrite (compat_bind_bindt T U).
      reflexivity.
    Qed.

    #[export] Instance Compat_Map_Traverse_Bindt
      `{Map U} `{Traverse U}
      `{! Compat_Traverse_Bindt T U}
      `{! Compat_Map_Bindt T U} :
      Compat_Map_Traverse U.
    Proof.
      hnf.
      rewrite (compat_map_bindt T U).
      unfold_ops @Map_Traverse.
      rewrite (compat_traverse_bindt T U).
      reflexivity.
    Qed.

  End self.

  Section compat_laws.

    Context
    `{Return_inst : Return T}
    `{Map_inst : Map U}
    `{Traverse_inst : Traverse U}
    `{Bind_inst : Bind T U}
    `{Bindt_inst : Bindt T U}.

    Lemma map_to_bindt `{! Compat_Map_Bindt T U} :
      forall `(f : A -> B), map (F := U) f = bindt (G := fun A => A) (ret (T := T) ∘ f).
    Proof.
      rewrite (compat_map_bindt T U).
      reflexivity.
    Qed.

    Lemma bind_to_bindt `{! Compat_Bind_Bindt T U} `(f : A -> T B):
      bind (U := U) f = bindt (G := fun A => A) f.
    Proof.
      rewrite (compat_bind_bindt T U).
      reflexivity.
    Qed.

    Lemma traverse_to_bindt `{! Compat_Traverse_Bindt T U}
      `{Applicative G} `(f : A -> G B):
      traverse (G := G) (T := U) f = bindt (U := U) (map (F := G) (ret (T := T)) ∘ f).
    Proof.
      rewrite (compat_traverse_bindt T U).
      reflexivity.
    Qed.

  End compat_laws.

End derived.

Class TraversableMonadFull
  (T : Type -> Type)
  `{ret_inst : Return T}
  `{Map_inst : Map T}
  `{Traverse_inst : Traverse T}
  `{Bind_inst : Bind T T}
  `{Bindt_inst : Bindt T T} :=
  { ktmf_ktm :> TraversableMonad T;
    ktmf_map_compat :> Compat_Map_Bindt T T;
    ktmf_bind_compat :> Compat_Bind_Bindt T T;
    ktmf_traverse_compat :> Compat_Traverse_Bindt T T;
  }.

Class TraversableRightModuleFull
  (T : Type -> Type)
  (U : Type -> Type)
  `{ret_inst : Return T}
  `{Map_T_inst : Map T}
  `{Traverse_T_inst : Traverse T}
  `{Bind_T_inst : Bind T T}
  `{Bindt_T_inst : Bindt T T}
  `{Map_U_inst : Map U}
  `{Traverse_U_inst : Traverse U}
  `{Bind_U_inst : Bind T U}
  `{Bindt_U_inst : Bindt T U} :=
  { ktmodf_kmond :> TraversableMonadFull T;
    ktmodf_mod :> TraversableRightModule T U;
    ktmodf_map_compat :> Compat_Map_Bindt T U;
    ktmodf_traverse_compat :> Compat_Traverse_Bindt T U;
    ktmodf_bind_compat :> Compat_Bind_Bindt T U;
  }.

Section instances.

  #[local] Instance
    TraversableMonadFull_TraversableMonad
    (T : Type -> Type)
    `{Monad_inst : TraversableMonad T} :
  TraversableMonadFull T
    (Map_inst := Map_Bindt T T)
    (Traverse_inst := Traverse_Bindt T T)
    (Bind_inst := Bind_Bindt T T)
  :=
  {| ktmf_ktm := _
  |}.

  #[local] Instance TraversableRightModuleFull_TraversableRightModule
    (W : Type) (T : Type -> Type) (U : Type -> Type)
    `{Module_inst : TraversableRightModule T U} :
    TraversableRightModuleFull T U
    (Map_T_inst := Map_Bindt T T)
    (Traverse_T_inst := Traverse_Bindt T T)
    (Bind_T_inst := Bind_Bindt T T)
    (Map_U_inst := Map_Bindt T U)
    (Traverse_U_inst := Traverse_Bindt T U)
    (Bind_U_inst := Bind_Bindt T U) :=
    {| ktmodf_kmond := _;
    |}.

  #[local] Instance TraversableRightModule_TraversableMonad
    (T : Type -> Type)
    `{Monad_inst : TraversableMonad T} :
    TraversableRightModule T T :=
    {| ktmod_premod := _ ; |}.

  #[local] Instance TraversableRightModuleFull_TraversableMonadFull
    (T : Type -> Type)
    `{Monad_inst : TraversableMonadFull T} :
    TraversableRightModuleFull T T.
  Proof.
    constructor.
    - typeclasses eauto.
    - apply TraversableRightModule_TraversableMonad.
      apply ktmf_ktm.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
  Qed.

End instances.

(** * Interaction of [traverse] with functor composition *)
(******************************************************************************)
Section properties.

  Context
    `{TraversableRightModule T U}.

  Lemma bindt_app_l :
    forall {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T U _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f = bindt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma bindt_app_r :
    forall {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T U _ (G ∘ (fun A => A)) (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f = bindt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity1 G).
  Qed.

End properties.

(** * Derived instances *)
(******************************************************************************)
Section DerivedInstances.

  Context
    `{ret_inst : Return T}
    `{Map_T_inst : Map T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Bindt_T_inst : Bindt T T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{Map_U_inst : Map U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Bindt_U_inst : Bindt T U}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{Module_inst : ! TraversableRightModule T U}.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Section kc3_special_cases.

    Context
      `{Applicative G3}
      `{Applicative G2}
      `{Applicative G1}.

    (** *** Homogeneous cases *)
    (******************************************************************************)
    Lemma kc3_22 : forall `(g : B -> G2 C) `(f : A -> G1 B),
        (map ret ∘ g) ⋆3 (map ret ∘ f) =
          map (F := G1 ∘ G2) ret ∘ map (F := G1) g ∘ f.
    Proof.
      intros. unfold kc3.
      reassociate <-.
      rewrite fun_map_map.
      unfold_ops @Map_compose.
      unfold_compose_in_compose.
      rewrite fun_map_map.
      rewrite ktm_bindt0.
      reflexivity.
    Qed.

    Lemma kc3_11 : forall `(g : B -> T C) `(f : A -> T B),
        kc3 (G1 := fun A => A) (G2 := fun A => A) g f = (g ⋆1 f).
    Proof.
      intros. unfold kc3, kc1.
      rewrite (bind_to_bindt (T := T)).
      reflexivity.
    Qed.

    Lemma kc3_00 : forall `(g : B -> C) `(f : A -> B),
        kc3 (T := T) (G1 := fun A => A) (G2 := fun A => A) (ret ∘ g) (ret ∘ f) = ret ∘ g ∘ f.
    Proof.
      intros. unfold kc3.
      reassociate <-.
      change (map (F := fun A => A) ?f) with f.
      rewrite (ktm_bindt0 (G := fun A => A)).
      reflexivity.
    Qed.

    (** *** Heterogeneous cases *)
    (******************************************************************************)
    Lemma kc3_32 : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
        g ⋆3 map ret ∘ f = map g ∘ f.
    Proof.
      intros. unfold kc3.
      reassociate <-.
      rewrite fun_map_map.
      rewrite ktm_bindt0.
      reflexivity.
    Qed.

    Lemma kc3_31 : forall `(g : B -> G2 (T C)) `(f : A -> T B),
        kc3 (G1 := fun A => A) (G2 := G2) g f = bindt (G := G2) g ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_30 : forall `(g : B -> G2 (T C)) `(f : A -> B),
        kc3 (T := T) (G1 := fun A => A) (G2 := G2) g (ret ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      change (map (F := fun A => A) ?f) with f.
      rewrite ktm_bindt0.
      reflexivity.
    Qed.

    Lemma kc3_23 : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
        map ret ∘ g ⋆3 f = map (traverse g) ∘ f.
    Proof.
      intros.
      rewrite traverse_to_bindt.
      reflexivity.
    Qed.

    Lemma kc3_13 : forall `(g : B -> T C) `(f : A -> G1 (T B)),
        kc3 (G2 := fun A => A) g f = map (F := G1) (bind (T := T) g) ∘ f.
    Proof.
      intros.
      rewrite (bind_to_bindt (T := T)).
      reflexivity.
    Qed.

    Lemma kc3_03 : forall `(g : B -> C) `(f : A -> G1 (T B)),
        kc3 (T := T) (G2 := fun A => A) (ret ∘ g) f = map (map g) ∘ f.
    Proof.
      intros.
      rewrite (map_to_bindt (T := T) (U := T)).
      reflexivity.
    Qed.

    Lemma kc3_21 : forall `(g : B -> G2 C) `(f : A -> T B),
        kc3 (map ret ∘ g) f = traverse (G := G2) g ∘ f.
    Proof.
      intros.
      unfold kc3.
      rewrite traverse_to_bindt.
      reflexivity.
    Qed.

    Lemma kc3_20 : forall `(g : B -> G2 C) `(f : A -> B),
        kc3 (T := T) (G1 := fun A => A) (map ret ∘ g) (ret ∘ f) = map ret ∘ g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reassociate <-.
      change (map (F := fun A => A) ?f) with f.
      rewrite ktm_bindt0.
      reflexivity.
    Qed.

    Lemma kc3_12 : forall `(g : B -> T C) `(f : A -> G1 B),
        kc3 (T := T) (G2 := fun A => A) g (map ret ∘ f) = map g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reassociate <-.
      rewrite fun_map_map.
      rewrite (ktm_bindt0 (G := fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_02 : forall `(g : B -> C) `(f : A -> G1 B),
        kc3 (T := T) (G2 := fun A => A) (ret ∘ g) (map ret ∘ f) =
          map ret ∘ map g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reassociate <-.
      rewrite fun_map_map.
      rewrite fun_map_map.
      rewrite (ktm_bindt0 (G := fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_01 : forall `(g : B -> C) `(f : A -> T B),
        kc3 (T := T) (G1 := fun A => A) (G2 := fun A => A) (ret ∘ g) f =
          map g ∘ f.
    Proof.
      intros.
      unfold kc3.
      rewrite (map_to_bindt (U := T) (T := T)).
      reflexivity.
    Qed.

    Lemma kc3_10 : forall `(g : B -> T C) `(f : A -> B),
        kc3 (T := T) (G1 := fun A => A) (G2 := fun A => A) g (ret ∘ f) = g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reassociate <-.
      change (map (F := fun A => A) ?f) with f.
      rewrite (ktm_bindt0 (G := fun A => A)).
      reflexivity.
    Qed.

  End kc3_special_cases.

  (** ** Kleisli composition laws *)
  (******************************************************************************)
  Section Kleisli_composition.

    Context
      `{Applicative G1}
      `{Applicative G2}
      `{Applicative G3}.

    Lemma kc3_id_l : forall `(g : A -> G2 (T B)),
        kc3 (T := T) (G1 := fun A => A) g (ret (T := T)) = g.
    Proof.
      intros. change ret with (ret ∘ @id A).
      now rewrite kc3_30.
    Qed.

    Lemma kc3_id_l' : forall `(g : A -> G2 (T B)),
        kc3 (T := T) g (map (F := G1) ret) = map g.
    Proof.
      intros.
      unfold kc3.
      rewrite (fun_map_map (F := G1)).
      now rewrite ktm_bindt0.
    Qed.

    Lemma kc3_id_r : forall `(f : A -> G1 (T B)),
        kc3 (T := T) (G2 := fun A => A) (ret (T := T)) f = f.
    Proof.
      intros.
      change ret with (ret ∘ @id B).
      rewrite kc3_03.
      rewrite (map_to_bindt (U := T) (T := T)).
      change (ret ∘ @id B) with (ret (A := B)).
      rewrite ktm_bindt1.
      rewrite fun_map_id.
      reflexivity.
    Qed.

    Lemma kc3_assoc : forall `(h : C -> G3 (T D)) `(g : B -> G2 (T C)) `(f : A -> G1 (T B)),
        kc3 (G1 := G1 ∘ G2) h (g ⋆3 f) =
          kc3 (G2 := G2 ∘ G3) (h ⋆3 g) f.
    Proof.
      intros.
      unfold kc3.
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

  (** ** Composition with lesser Kleisli operations *)
  (******************************************************************************)
  Section composition_special_cases.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    (** *** Composition with <<traverse>> *)
    (******************************************************************************)
    Lemma traverse_bindt : forall (A B C : Type) (g : B -> G2 C) (f : A -> G1 (T B)),
        map (traverse g) ∘ bindt f =
          bindt (U := U) (G := G1 ∘ G2) (map (traverse g) ∘ f).
    Proof.
      intros.
      rewrite traverse_to_bindt.
      rewrite traverse_to_bindt.
      rewrite ktm_bindt2.
      reflexivity.
    Qed.

    Lemma bindt_traverse : forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> G1 B),
        map (bindt g) ∘ traverse f = bindt (U := U) (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      intros.
      rewrite traverse_to_bindt.
      rewrite ktm_bindt2.
      rewrite kc3_32.
      reflexivity.
    Qed.

    (** *** Composition with <<bind>> *)
    (******************************************************************************)
    Lemma bind_bindt : forall (A B C : Type) (g : B -> T C) (f : A -> G1 (T B)),
        map (bind g) ∘ bindt f = bindt (U := U) (map (bind g) ∘ f).
    Proof.
      intros.
      rewrite (bind_to_bindt (U := T)).
      rewrite (bind_to_bindt (U := U)).
      rewrite (ktm_bindt2 (G2 := fun A => A)).
      rewrite bindt_app_r.
      reflexivity.
    Qed.

    Lemma bindt_bind : forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> T B),
          bindt g ∘ bind f = bindt (U := U) (bindt g ∘ f).
    Proof.
      intros.
      rewrite bind_to_bindt.
      change (bindt (U := U) g) with
        (map (F := fun A => A) (bindt (U := U) g)).
      rewrite (ktm_bindt2 (G1 := fun A => A)).
      rewrite bindt_app_l.
      reflexivity.
    Qed.

    (** *** Composition with <<map>> *)
    (******************************************************************************)
    Lemma map_bindt : forall (A B C : Type) (g : B -> C) (f : A -> G1 (T B)),
        map (map g) ∘ bindt f = bindt (map (map g) ∘ f).
    Proof.
      intros.
      rewrite (map_to_bindt (U := T)).
      rewrite (map_to_bindt (U := U)).
      rewrite (ktm_bindt2 (G2 := fun A => A)).
      rewrite bindt_app_r.
      reflexivity.
    Qed.

    Lemma bindt_map : forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> B),
        bindt g ∘ map f = bindt (U := U) (g ∘ f).
    Proof.
      intros.
      rewrite (map_to_bindt (T := T) (U := U)).
      change (bindt g) with (map (F := fun A => A) (bindt g)).
      rewrite (ktm_bindt2 (G1 := fun A => A)).
      rewrite bindt_app_l.
      rewrite kc3_30.
      reflexivity.
    Qed.

    (** ** Composition between <<traverse>> and <<bind>> *)
    (******************************************************************************)
    Lemma traverse_bind : forall (A B C : Type) (g : B -> G2 C) (f : A -> T B),
        traverse g ∘ bind f = bindt (traverse g ∘ f).
    Proof.
      intros.
      rewrite traverse_to_bindt.
      rewrite (bind_to_bindt (U := U)).
      change (bindt ?g) with (map (F := fun A => A) (bindt g)) at 1.
      rewrite (ktm_bindt2 (G1 := fun A => A)).
      rewrite bindt_app_l.
      rewrite kc3_21.
      rewrite traverse_to_bindt.
      reflexivity.
    Qed.

    Lemma bind_traverse : forall (A B C : Type) (g : B -> T C) (f : A -> G1 B),
        map (bind g) ∘ traverse f = bindt (map g ∘ f).
    Proof.
      intros.
      rewrite traverse_to_bindt.
      rewrite (bind_to_bindt (U := U)).
      rewrite (ktm_bindt2 (G2 := fun A => A)).
      rewrite bindt_app_r.
      rewrite kc3_12.
      reflexivity.
    Qed.

  End composition_special_cases.

  Section derived_classes.

    (** ** Monad instance *)
    (******************************************************************************)
    Lemma bind_ret : forall (A B : Type) (f : A -> T B),
        bind f ∘ ret = f.
    Proof.
      intros.
      rewrite bind_to_bindt.
      rewrite (ktm_bindt0 (G := fun A => A)).
      reflexivity.
    Qed.

    Lemma bind_id : forall (A : Type),
        bind ret = @id (T A).
    Proof.
      intros.
      rewrite bind_to_bindt.
      rewrite ktm_bindt1.
      reflexivity.
    Qed.

    Lemma bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind g ∘ bind f = bind (g ⋆1 f).
    Proof.
      intros.
      do 2 rewrite bind_to_bindt.
      change (bindt g) with (map (F := fun A => A) (bindt g)).
      change ((fun A => A) ?x) with x.
      rewrite (ktm_bindt2 (G1 := fun A => A) (G2 := fun A => A)).
      rewrite bindt_app_r.
      rewrite kc3_11.
      rewrite bind_to_bindt.
      reflexivity.
    Qed.

    (** ** Traversable instance *)
    (******************************************************************************)
    Lemma traverse_id : forall (A : Type),
        traverse (G := fun A => A) (@id A) = @id (U A).
    Proof.
      intros.
      rewrite (traverse_to_bindt (G := fun A => A)).
      change (?g ∘ id) with g.
      change (map (F := fun A => A) ?f) with f.
      rewrite ktm_bindt1.
      reflexivity.
    Qed.

    Lemma traverse_traverse G1 `{Applicative G1} G2 `{Applicative G2} :
      forall {A B C : Type} (g : B -> G2 C) (f : A -> G1 B),
        map (traverse g) ∘ traverse f =
          traverse (T := U) (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      intros.
      rewrite traverse_to_bindt.
      rewrite traverse_to_bindt.
      rewrite ktm_bindt2.
      rewrite kc3_22.
      rewrite traverse_to_bindt.
      reflexivity.
    Qed.

    Lemma traverse_morphism : forall G1 G2 `{ApplicativeMorphism G1 G2 ϕ} (A B : Type) (f : A -> G1 B),
        ϕ (U B) ∘ traverse f = traverse (ϕ B ∘ f).
    Proof.
      intros.
      infer_applicative_instances.
      rewrite traverse_to_bindt.
      rewrite traverse_to_bindt.
      rewrite ktm_morph.
      reassociate <-.
      (* TODO cleanup below *)
      { fequal. ext a. unfold compose. rewrite appmor_natural.
        reflexivity. }
    Qed.

  End derived_classes.
End DerivedInstances.

Section instances.

  Context
    `{ret_inst : Return T}
    `{Map_T_inst : Map T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Bindt_T_inst : Bindt T T}
    `{! Compat_Map_Bindt T T}
    `{! Compat_Traverse_Bindt T T}
    `{! Compat_Bind_Bindt T T}
    `{Monad_inst : ! TraversableMonad T}.

  #[local] Existing Instance TraversableRightModule_TraversableMonad.

  #[export] Instance TraversableFunctor_TraversableMonad : TraversableFunctor T :=
    {| trf_traverse_id := traverse_id;
      trf_traverse_traverse := traverse_traverse;
      trf_traverse_morphism := traverse_morphism;
    |}.

  #[export] Instance RightPreModule_TraversableMonad : RightPreModule T T :=
    {| kmod_bind1 := bind_id;
       kmod_bind2 := bind_bind;
    |}.

  #[export] Instance Monad_TraversableMonad : Monad T :=
    {| kmon_bind0 := bind_ret;
    |}.

  #[export] Instance RightModule_TraversableRightModule : RightModule T T :=
    {| kmod_monad := _
    |}.

  #[export] Instance Functor_TraversableMonad : Functor T.
  Proof.
    typeclasses eauto.
  Qed.

  Context
    `{Map_U_inst : Map U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Bindt_U_inst : Bindt T U}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{Module_inst : ! TraversableRightModule T U}.

  #[export] Instance TraversableFunctor_TraversableRightModule :
    TraversableFunctor U :=
    {| trf_traverse_id := traverse_id;
      trf_traverse_traverse := traverse_traverse;
      trf_traverse_morphism := traverse_morphism;
    |}.

  #[export] Instance Functor_TraversableRightModule: Functor U :=
    {| fun_map_id := map_id;
       fun_map_map := map_map;
    |}.

End instances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆3" := (kc3) (at level 60) : tealeaves_scope.
End Notations.
