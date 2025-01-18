From Tealeaves Require Export
  Classes.Categorical.Applicative.

#[local] Generalizable Variables T G A B C ϕ M.

(** * Traversable Functors *)
(******************************************************************************)

(** ** The <<traverse>> Operation *)
(******************************************************************************)
Class Traverse (T: Type -> Type) :=
  traverse:
    forall (G: Type -> Type)
      `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G}
      (A B: Type), (A -> G B) -> T A -> G (T B).

#[global] Arguments traverse {T}%function_scope {Traverse} {G}%function_scope
  {Map_G Pure_G Mult_G} {A B}%type_scope _%function_scope _.

(** ** Kleisli Composition *)
(******************************************************************************)
Definition kc2
  {G1 G2: Type -> Type}
  `{Map_G1: Map G1}
  {A B C: Type}:
  (B -> G2 C) ->
  (A -> G1 B) ->
  (A -> (G1 ∘ G2) C) :=
  fun g f => map (F := G1) (A := B) (B := G2 C) g ∘ f.

#[local] Infix "⋆2" := (kc2) (at level 60): tealeaves_scope.

(** ** Typeclasses *)
(******************************************************************************)
Class TraversableFunctor (T: Type -> Type)
  `{Traverse_T: Traverse T} :=
  { trf_traverse_id: forall (A: Type),
      traverse (G := fun A => A) id = @id (T A);
    trf_traverse_traverse :
    forall `{Applicative G1} `{Applicative G2}
      (A B C: Type) (g: B -> G2 C) (f: A -> G1 B),
      map (traverse g) ∘ traverse f =
        traverse (T := T) (G := G1 ∘ G2) (g ⋆2 f);
    trf_traverse_morphism :
    forall `{morphism: ApplicativeMorphism G1 G2 ϕ} (A B: Type) (f: A -> G1 B),
      ϕ (T B) ∘ traverse f = traverse (ϕ B ∘ f);
  }.

(** ** Kleisli Composition Laws *)
(** TODO *)
(******************************************************************************)

(** ** Traversable Functor Homomorphisms *)
(******************************************************************************)
Class TraversableMorphism
  (T U: Type -> Type)
  `{Traverse_T: Traverse T}
  `{Traverse_U: Traverse U}
  (ϕ: forall (A: Type), T A -> U A) :=
  { trvmon_hom: forall `{Applicative G}
      `(f: A -> G B),
      map (F := G) (ϕ B) ∘ traverse (T := T) (G := G) f =
        traverse (T := U) (G := G) f ∘ ϕ A;
  }.

(** * Derived Structures *)
(******************************************************************************)

(** ** Derived <<map>> Operation *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Map_Traverse (T: Type -> Type)
    `{Traverse_T: Traverse T}: Map T :=
  fun (A B: Type) (f: A -> B) => traverse (G := fun A => A) f.

End DerivedOperations.

Class Compat_Map_Traverse T
  `{Map_T: Map T}
  `{Traverse_T: Traverse T}: Prop :=
  compat_map_traverse:
    Map_T = @DerivedOperations.Map_Traverse T Traverse_T.

#[export] Instance Compat_Map_Traverse_TraversableFunctor
  `{Traverse_T: Traverse T}:
  Compat_Map_Traverse T (Map_T := DerivedOperations.Map_Traverse T).
Proof.
  reflexivity.
Qed.

Corollary map_to_traverse
  `{Compat_Map_Traverse T}: forall `(f: A -> B),
    map (F := T) f = traverse (G := fun A => A) f.
Proof.
  rewrite compat_map_traverse.
  reflexivity.
Qed.

(** ** Composition with the Identity Applicative *)
(******************************************************************************)
Section properties.

  Context
    `{TraversableFunctor T}.

  (** ***Left identity law *)
  (******************************************************************************)
  Lemma traverse_app_id_l {A B : Type} `{Applicative G} :
    forall (f : A -> G B),
      @traverse T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f
      = traverse f.
  Proof.
    intros. fequal.
    now rewrite (Mult_compose_identity2 G).
  Qed.

  (** *** Right identity law *)
  (******************************************************************************)
  Lemma traverse_app_id_r {A B : Type} `{Applicative G} :
    forall (f : A -> G B),
      @traverse T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f
      = traverse f.
  Proof.
    intros. fequal.
    now rewrite (Mult_compose_identity1 G).
  Qed.

End properties.

(** ** Derived Composition Laws *)
(******************************************************************************)
Section traversable_functor_derived_composition_laws.

    Context
      `{TraversableFunctor T}
      `{Map T}
      `{! Compat_Map_Traverse T }.

    Context
      {G1 G2 : Type -> Type}
      `{Applicative G2}
      `{Applicative G1}.

    (** *** Composition between <<traverse>> and <<map>> *)
    (******************************************************************************)
    Lemma map_traverse {A B C : Type} : forall (g : B -> C) (f : A -> G1 B),
        map (F := G1) (A := T B) (B := T C) (map g) ∘ traverse f =
          traverse (map g ∘ f).
    Proof.
      intros.
      rewrite (map_to_traverse (T := T)).
      rewrite (trf_traverse_traverse (G2 := fun A => A)).
      rewrite traverse_app_id_r.
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
      rewrite traverse_app_id_l.
      reflexivity.
    Qed.

    (** *** Functor laws *)
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
      rewrite traverse_app_id_l.
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

End traversable_functor_derived_composition_laws.

(** ** Derived Typeclass Instances *)
(******************************************************************************)
Module DerivedInstances.

  #[export] Instance Functor_TraversableFunctor
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}: Functor T :=
  {| fun_map_id := map_id;
     fun_map_map := map_map;
  |}.

End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆2" := (kc2) (at level 60): tealeaves_scope.
End Notations.
