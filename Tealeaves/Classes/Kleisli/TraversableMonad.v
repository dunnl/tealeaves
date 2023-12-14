From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.Applicative
  Classes.Kleisli.Monad
  Classes.Kleisli.TraversableFunctor.

Import Monad.Notations.
Import TraversableFunctor.Notations.

#[local] Generalizable Variables T G A B C D ϕ M f.

(** * Traversable monad *)
(******************************************************************************)

(** ** [bindt] operation *)
(******************************************************************************)
Class Bindt
  (U : Type -> Type)
  (T : Type -> Type)
  := bindt :
    forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B : Type), (A -> G (U B)) -> T A -> G (T B).

#[global] Arguments bindt {U T}%function_scope {Bindt} {G}%function_scope
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
Class TraversableMonad (T : Type -> Type) `{Return T} `{Bindt T T} :=
  { ktm_bindt0 : forall `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt f ∘ ret = f;
    ktm_bindt1 : forall (A : Type),
      bindt (G := fun A => A) (ret (T := T)) = @id (T A);
    ktm_bindt2 : forall `{Applicative G1} `{Applicative G2} {A B C : Type}
                   (g : B -> G2 (T C)) (f : A -> G1 (T B)),
      map (F := G1) (A := T B) (B := G2 (T C)) (bindt g) ∘ bindt f =
        bindt (kc3 (G1 := G1) (G2 := G2) g f);
    ktm_morph : forall `{morph : ApplicativeMorphism G1 G2 ϕ} {A B : Type} `(f : A -> G1 (T B)),
      ϕ (T B) ∘ bindt f = bindt (ϕ (T B) ∘ f);
  }.

Class TraversableMonadFull
  (T : Type -> Type) `{Return T} `{Bindt T T} `{Bind T T} `{Traverse T} `{Map T} :=
  { ktmf_ktm :> TraversableMonad T;
    ktmf_bind_to_bindt : `(@bind T T _ A B = @bindt T T _ (fun A => A) _ _ _ A B);
    ktmf_traverse_to_bindt :
    forall {G : Type -> Type} `{Mult G} `{Map G} `{Pure G} `{! Applicative G},
      `(@traverse T _ G _ _ _ A B f = @bindt T T _ G _ _ _ A B (map ret ∘ f));
    ktmf_map_to_bindt :
    `(@map T _ A B f = @bindt T T _ (fun A => A) _ _ _ A B (ret ∘ f));
  }.


(** * Interaction of [traverse] with functor composition *)
(******************************************************************************)
Section properties.

  Context
    `{TraversableMonad T}.

  Lemma bindt_app_l :
    forall {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f = bindt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma bindt_app_r :
    forall {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f = bindt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity1 G).
  Qed.

End properties.

(** * Derived instances *)
(******************************************************************************)
Section DerivedInstances.

  Context
    `{TraversableMonadFull T}.

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
      rewrite (ktmf_bind_to_bindt (T := T)).
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

    (** **** [3x] *)
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

    (** **** [x3] *)
    (******************************************************************************)
    Lemma kc3_23 : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
        map ret ∘ g ⋆3 f = map (traverse g) ∘ f.
    Proof.
      intros.
      rewrite ktmf_traverse_to_bindt.
      reflexivity.
    Qed.

    Lemma kc3_13 : forall `(g : B -> T C) `(f : A -> G1 (T B)),
        kc3 (G2 := fun A => A) g f = map (bind (T := T) g) ∘ f.
    Proof.
      intros.
      rewrite ktmf_bind_to_bindt.
      reflexivity.
    Qed.

    Lemma kc3_03 : forall `(g : B -> C) `(f : A -> G1 (T B)),
        kc3 (T := T) (G2 := fun A => A) (ret ∘ g) f = map (map g) ∘ f.
    Proof.
      intros.
      rewrite (ktmf_map_to_bindt (T := T)).
      reflexivity.
    Qed.

    (** **** [xy] *)
    (******************************************************************************)
    Lemma kc3_21 : forall `(g : B -> G2 C) `(f : A -> T B),
        kc3 (map ret ∘ g) f = traverse (G := G2) g ∘ f.
    Proof.
      intros.
      unfold kc3.
      rewrite ktmf_traverse_to_bindt.
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
      rewrite (ktmf_map_to_bindt (T := T)).
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
          bindt (G := G1 ∘ G2) (map (traverse g) ∘ f).
    Proof.
      intros.
      rewrite ktmf_traverse_to_bindt.
      rewrite ktm_bindt2.
      reflexivity.
    Qed.

    Lemma bindt_traverse : forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> G1 B),
        map (bindt g) ∘ traverse f = bindt (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      intros.
      rewrite ktmf_traverse_to_bindt.
      rewrite ktm_bindt2.
      rewrite kc3_32.
      reflexivity.
    Qed.

    (** *** Composition with <<bind>> *)
    (******************************************************************************)
    Lemma bind_bindt : forall (A B C : Type) (g : B -> T C) (f : A -> G1 (T B)),
        map (bind g) ∘ bindt f = bindt (map (bind g) ∘ f).
    Proof.
      intros.
      rewrite ktmf_bind_to_bindt.
      rewrite (ktm_bindt2 (G2 := fun A => A)).
      rewrite bindt_app_r.
      reflexivity.
    Qed.

    Lemma bindt_bind : forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> T B),
          bindt g ∘ bind f = bindt (bindt g ∘ f).
    Proof.
      intros.
      rewrite ktmf_bind_to_bindt.
      change (bindt g) with (map (F := fun A => A) (bindt g)).
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
      rewrite (ktmf_map_to_bindt (T := T)).
      rewrite (ktm_bindt2 (G2 := fun A => A)).
      rewrite bindt_app_r.
      reflexivity.
    Qed.

    Lemma bindt_map : forall (A B C : Type) (g : B -> G2 (T C)) (f : A -> B),
        bindt g ∘ map f = bindt (g ∘ f).
    Proof.
      intros.
      rewrite (ktmf_map_to_bindt (T := T)).
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
      rewrite ktmf_traverse_to_bindt.
      rewrite ktmf_bind_to_bindt.
      change (bindt ?g) with (map (F := fun A => A) (bindt g)) at 1.
      rewrite (ktm_bindt2 (G1 := fun A => A)).
      rewrite bindt_app_l.
      rewrite kc3_21.
      rewrite ktmf_traverse_to_bindt.
      reflexivity.
    Qed.

    Lemma bind_traverse : forall (A B C : Type) (g : B -> T C) (f : A -> G1 B),
        map (bind g) ∘ traverse f = bindt (map g ∘ f).
    Proof.
      intros.
      rewrite ktmf_traverse_to_bindt.
      rewrite ktmf_bind_to_bindt.
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
      rewrite ktmf_bind_to_bindt.
      rewrite (ktm_bindt0 (G := fun A => A)).
      reflexivity.
    Qed.

    Lemma bind_id : forall (A : Type),
        bind ret = @id (T A).
    Proof.
      intros.
      rewrite ktmf_bind_to_bindt.
      rewrite ktm_bindt1.
      reflexivity.
    Qed.

    Lemma bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind g ∘ bind f = bind (g ⋆1 f).
    Proof.
      intros.
      do 2 rewrite ktmf_bind_to_bindt.
      change (bindt g) with (map (F := fun A => A) (bindt g)).
      change ((fun A => A) ?x) with x.
      rewrite (ktm_bindt2 (G1 := fun A => A) (G2 := fun A => A)).
      rewrite bindt_app_r.
      rewrite kc3_11.
      rewrite ktmf_bind_to_bindt.
      reflexivity.
    Qed.

    (** ** Traversable instance *)
    (******************************************************************************)
    Lemma traverse_id : forall (A : Type),
        traverse (G := fun A => A) (@id A) = @id (T A).
    Proof.
      intros.
      rewrite (ktmf_traverse_to_bindt (G := fun A => A)).
      change (?g ∘ id) with g.
      change (map (F := fun A => A) ?f) with f.
      rewrite ktm_bindt1.
      reflexivity.
    Qed.

    Lemma traverse_traverse `{Applicative G1} `{Applicative G2} :
      forall {A B C : Type} (g : B -> G2 C) (f : A -> G1 B),
        map (traverse g) ∘ traverse f = traverse (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      intros.
      rewrite ktmf_traverse_to_bindt.
      rewrite ktmf_traverse_to_bindt.
      rewrite ktm_bindt2.
      rewrite kc3_22.
      rewrite ktmf_traverse_to_bindt.
      reflexivity.
    Qed.

    Lemma traverse_morphism : forall `{ApplicativeMorphism G1 G2 ϕ} (A B : Type) (f : A -> G1 B),
        ϕ (T B) ∘ traverse f = traverse (ϕ B ∘ f).
    Proof.
      intros.
      rewrite ktmf_traverse_to_bindt.
      rewrite ktmf_traverse_to_bindt.
      rewrite ktm_morph.
      reassociate <-. (* TODO cleanup below *)
      { fequal. inversion H13.
        ext a. unfold compose. rewrite appmor_natural.
        reflexivity. }
    Qed.

  End derived_classes.

  (** ** Instances *)
  (******************************************************************************)
  Lemma map_to_bind (A B : Type) (f : A -> B):
    map f = bind (ret ∘ f).
  Proof.
    rewrite ktmf_map_to_bindt.
    rewrite ktmf_bind_to_bindt.
    reflexivity.
  Qed.

  #[export] Instance Monad_TM : Monad T :=
    {| kmon_bind0 := bind_ret;
       kmon_bind1 := bind_id;
       kmon_bind2 := bind_bind;
    |}.

  #[export] Instance MonadFull_TM : MonadFull T :=
    {| kmonf_kmon := Monad_TM;
       kmonf_map_to_bind := map_to_bind;
    |}.

  Lemma map_to_traverse :
    @map T _ = @traverse T _ (fun X : Type => X) _ _ _.
  Proof.
    ext A B f.
    rewrite ktmf_map_to_bindt.
    rewrite ktmf_traverse_to_bindt.
    reflexivity.
  Qed.

  #[export] Instance TraversableFunctor_TM : TraversableFunctor T :=
    {| trf_traverse_id := traverse_id;
       trf_traverse_traverse := @traverse_traverse;
       trf_traverse_morphism := @traverse_morphism;
    |}.

  #[export] Instance TraversableFunctorFull_TM : TraversableFunctorFull T :=
    {| trff_trf := TraversableFunctor_TM;
       trff_map_to_traverse := @map_to_traverse;
    |}.

  #[export] Instance Functor_TM : Functor T := ltac:(typeclasses eauto).

  #[export] Instance Natural_ret_TM : Natural (@ret T _) := ltac:(typeclasses eauto).

End DerivedInstances.

(** ** Kleisli composition laws *)
(******************************************************************************)
Section Kleisli_composition.

  Context
    (T : Type -> Type)
    `{TraversableMonadFull T}
    (G1 : Type -> Type)
    (G2 : Type -> Type)
    (G3 : Type -> Type)
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}.

  Lemma kc3_id_l : forall `(g : A -> G2 (T B)),
      kc3 (T := T) (G1 := fun A => A) g (ret (T := T)) = g.
  Proof.
    intros. change (ret) with (ret ∘ @id A).
    now rewrite (kc3_30).
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
    change (ret) with (ret ∘ @id B).
    rewrite kc3_03.
    rewrite (ktmf_map_to_bindt (T := T)).
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
    rewrite (fun_map_map).
    rewrite ktm_bindt2.
    unfold compose at 2 3.
    reflexivity.
  Qed.

End Kleisli_composition.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆3" := (kc3) (at level 60) : tealeaves_scope.
End Notations.

(** ** Derived operations *)
(******************************************************************************)

Module DerivedOperations.
  Section ops.
    Context
      `{Bindt T T}
      `{Return T}.

    #[export] Instance Map_Bindt : Map T | 13 :=
      fun (A B : Type) (f : A -> B) => bindt (U := T) (T := T) (G := fun A => A) (ret ∘ f).

    #[export] Instance Bind_Bindt: Bind T T | 13 :=
      fun A B f => bindt (G := fun A => A) f.

    #[export] Instance Traverse_Bindt: Traverse T | 13 :=
      fun G _ _ _ A B f => bindt (map ret ∘ f).

    #[local, program] Instance TraversableMonadFull_Default
      `{! TraversableMonad T} : TraversableMonadFull T.
  End ops.
End DerivedOperations.
