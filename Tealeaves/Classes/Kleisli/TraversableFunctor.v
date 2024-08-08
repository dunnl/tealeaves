From Tealeaves Require Export
  Classes.Categorical.Applicative.

#[local] Generalizable Variable T G A B C ϕ M.

(** * Traversable functor *)
(******************************************************************************)

(** ** The [traverse] operation *)
(******************************************************************************)
Class Traverse (T : Type -> Type) := traverse :
    forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B : Type), (A -> G B) -> T A -> G (T B).

#[global] Arguments traverse {T}%function_scope {Traverse} {G}%function_scope
  {H H0 H1} {A B}%type_scope _%function_scope _.

(** ** "Kleisli" composition *)
(******************************************************************************)
Definition kc2
  {G1 G2 : Type -> Type} `{Map G1} {A B C : Type} :
  (B -> G2 C) ->
  (A -> G1 B) ->
  (A -> (G1 ∘ G2) C) :=
  fun g f => map (F := G1) (A := B) (B := G2 C) g ∘ f.

#[local] Infix "⋆2" := (kc2) (at level 60) : tealeaves_scope.

(** ** Typeclasses *)
(******************************************************************************)
Class TraversableFunctor (T : Type -> Type) `{Traverse T} :=
  { trf_traverse_id : forall (A : Type),
      traverse (G := fun A => A) id = @id (T A);
    trf_traverse_traverse :
    forall `{Applicative G1} `{Applicative G2}
      (A B C : Type) (g : B -> G2 C) (f : A -> G1 B),
      map (traverse g) ∘ traverse f = traverse (T := T) (G := G1 ∘ G2) (g ⋆2 f);
    trf_traverse_morphism :
    forall `{morphism : ApplicativeMorphism G1 G2 ϕ} (A B : Type) (f : A -> G1 B),
      ϕ (T B) ∘ traverse f = traverse (ϕ B ∘ f);
  }.

(** ** Homomorphisms *)
(******************************************************************************)
Class TraversableMorphism
  (T U : Type -> Type)
  `{Traverse T}
  `{Traverse U}
  (ϕ : forall (A : Type), T A -> U A) :=
  { trvmon_hom : forall `{Applicative G}
      `(f : A -> G B),
      map (F := G) (ϕ B) ∘ @traverse T _ G _ _ _ A B f =
        @traverse U _ G _ _ _ A B f ∘ ϕ A;
  }.

(** * Derived instances *)
(******************************************************************************)
Section derived.

  Definition Map_Traverse T `{Traverse_inst : Traverse T} : Map T :=
    fun (A B : Type) (f : A -> B) => traverse (G := fun A => A) f.

  Class Compat_Map_Traverse T
    `{Map_inst : Map T}
    `{Traverse_inst : Traverse T} : Prop :=
    compat_map_traverse :
      @map T Map_inst = @map T (@Map_Traverse T Traverse_inst).

  #[export] Instance Compat_Map_Traverse_Self
    `{Traverse T} :
    Compat_Map_Traverse T (Map_inst := Map_Traverse T).
  Proof.
    reflexivity.
  Qed.

  Corollary map_to_traverse
    `{Compat_Map_Traverse T} : forall `(f : A -> B),
      map (F := T) f = traverse (G := fun A => A) f.
  Proof.
    rewrite compat_map_traverse.
    reflexivity.
  Qed.

End derived.

Class TraversableFunctorFull (T : Type -> Type)
  `{Traverse_inst : Traverse T}
  `{Map_inst : Map T} :=
  { trff_trf :> TraversableFunctor T;
    trff_map_compat :> Compat_Map_Traverse T;
  }.

(*
#[local] Instance TraversableFunctorFull_Intro
  (T : Type -> Type)
  `{Traverse_inst : Traverse T}
  `{Map_inst : Map T}
  `{Traverse_compat : Compat_Map_Traverse T}
  `{! TraversableFunctor T}:
  TraversableFunctorFull T :=
  ltac:(constructor; typeclasses eauto).
*)

(** * Interaction of [traverse] with functor composition *)
(******************************************************************************)
Section properties.

  Context
    `{TraversableFunctor T}.

  (** ** Left identity law *)
  (******************************************************************************)
  Lemma traverse_app_l {A B : Type} `{Applicative G} :
    forall (f : A -> G B),
      @traverse T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f
      = traverse f.
  Proof.
    intros. fequal.
    now rewrite (Mult_compose_identity2 G).
  Qed.

  (** ** Right identity law *)
  (******************************************************************************)
  Lemma traverse_app_r {A B : Type} `{Applicative G} :
    forall (f : A -> G B),
      @traverse T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f
      = traverse f.
  Proof.
    intros. fequal.
    now rewrite (Mult_compose_identity1 G).
  Qed.

End properties.

(** * Derived instances *)
(******************************************************************************)
Section derived_instances.

    Context
      `{TraversableFunctor T}
      `{Map T}
      `{! Compat_Map_Traverse T }.

    Context
      {G1 G2 : Type -> Type}
      `{Applicative G2}
      `{Applicative G1}.

    (** ** Composition between <<traverse>> and <<map>> *)
    (******************************************************************************)
    Lemma map_traverse {A B C : Type} : forall (g : B -> C) (f : A -> G1 B),
        map (F := G1) (A := T B) (B := T C) (map g) ∘ traverse f =
          traverse (map g ∘ f).
    Proof.
      intros.
      rewrite (map_to_traverse (T := T)).
      rewrite (trf_traverse_traverse (G2 := fun A => A)).
      rewrite traverse_app_r.
      reflexivity.
    Qed.

    Lemma traverse_map {A B C : Type} : forall (g : B -> G2 C) (f : A -> B),
        traverse g ∘ map f = traverse (g ∘ f).
    Proof.
      intros.
      rewrite (map_to_traverse (T := T)).
      change (traverse g)
        with (map (F := fun A => A) (traverse g)).
      rewrite (trf_traverse_traverse (G1 := fun A => A)).
      rewrite traverse_app_l.
      reflexivity.
    Qed.

    (** ** [Functor] laws *)
    (******************************************************************************)
    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map g ∘ map f = map (F := T) (g ∘ f).
    Proof.
      intros.
      rewrite (map_to_traverse (T := T)).
      rewrite (map_to_traverse (T := T)).
      rewrite (map_to_traverse (T := T)).
      change (traverse (G := fun A => A) g)
        with (map (F := fun A => A) (traverse (G := fun A => A) g)).
      rewrite (trf_traverse_traverse (G1 := fun A => A) (G2 := fun A => A)).
      rewrite traverse_app_l.
      reflexivity.
    Qed.

    Lemma map_id : forall (A : Type),
        map id = @id (T A).
    Proof.
      intros.
      rewrite map_to_traverse.
      rewrite trf_traverse_id.
      reflexivity.
    Qed.

    (** ** Typeclass instances *)
    (******************************************************************************)
    #[export] Instance Functor_TraversableFunctor : Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

End derived_instances.

Section traversable_purity.

  Context
    `{TraversableFunctor T}.

  (** ** Interaction between <<traverse>> and <<pure>> *)
  (******************************************************************************)
  Theorem traverse_purity1 :
    forall `{Applicative G},
      `(traverse (G := G) pure = @pure G _ (T A)).
  Proof.
    intros.
    change (@pure G _ A) with (@pure G _ A ∘ id).
    rewrite <- (trf_traverse_morphism (G1 := fun A => A) (G2 := G)).
    rewrite trf_traverse_id.
    reflexivity.
  Qed.

  Lemma traverse_purity2 :
    forall `{Applicative G2}
      `{Applicative G1}
      `(f : A -> G1 B),
      traverse (G := G2 ∘ G1) (pure (F := G2) ∘ f) = pure (F := G2) ∘ traverse f.
  Proof.
    intros.
    rewrite <- (trf_traverse_morphism (G1 := G1) (G2 := G2 ∘ G1)
                 (ϕ := fun A => @pure G2 _ (G1 A))).
    reflexivity.
  Qed.

End traversable_purity.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆2" := (kc2) (at level 60) : tealeaves_scope.
End Notations.
