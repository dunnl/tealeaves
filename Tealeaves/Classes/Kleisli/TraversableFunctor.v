From Tealeaves Require Export
  Classes.Categorical.Applicative.

#[local] Generalizable Variable G A B C ϕ M.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

(** * Traversable functor *)
(******************************************************************************)

(** ** The [traverse] operation *)
(******************************************************************************)
Class Traverse (T : Type -> Type) := traverse :
    forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B : Type), (A -> G B) -> T A -> G (T B).

#[global] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(** ** "Kleisli" composition *)
(******************************************************************************)
Definition kc2
  (G1 G2 : Type -> Type)
  `{Map G1} {A B C : Type} :
  (B -> G2 C) ->
  (A -> G1 B) ->
  (A -> (G1 ∘ G2) C) :=
  fun g f => map G1 B (G2 C) g ∘ f.

#[local] Infix "⋆2" := (kc2 _ _) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class TraversableFunctor (T : Type -> Type) `{Traverse T} :=
  { trf_traverse_id : forall (A : Type),
      traverse T (fun A => A) A A id = @id (T A);
    trf_traverse_traverse :
    forall (G1 G2 : Type -> Type) `{Applicative G1} `{Applicative G2}
      {A B C : Type} (g : B -> G2 C) (f : A -> G1 B),
      map G1 (T B) (G2 (T C)) (traverse T G2 B C g) ∘ traverse T G1 A B f =
        traverse T (G1 ∘ G2) A C (g ⋆2 f);
    trf_traverse_morphism : forall `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : A -> G1 B),
      ϕ (T B) ∘ traverse T G1 A B f = traverse T G2 A B (ϕ B ∘ f);
  }.

Class TraversableFunctorFull (T : Type -> Type) `{Traverse T} `{Map T} :=
  { trff_trf :> TraversableFunctor T;
    trff_map_to_traverse : map T = traverse T (fun A => A);
  }.

(** ** Interaction of [traverse] with functor composition *)
(******************************************************************************)
Section properties.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  (** ** Left identity law *)
  (******************************************************************************)
  Lemma traverse_app_l {A B : Type} (G : Type -> Type) `{Applicative G} :
    forall (f : A -> G B),
      @traverse T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f
      = traverse T G A B f.
  Proof.
    intros. fequal.
    now rewrite (Mult_compose_identity2 G).
  Qed.

  (** ** Right identity law *)
  (******************************************************************************)
  Lemma traverse_app_r {A B : Type} (G : Type -> Type) `{Applicative G} :
    forall (f : A -> G B),
      @traverse T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f
      = traverse T G A B f.
  Proof.
    intros. fequal.
    now rewrite (Mult_compose_identity1 G).
  Qed.

End properties.

(** * Derived instances *)
(******************************************************************************)
Section DerivedLaws.

    Context
    (T : Type -> Type)
    `{TraversableFunctorFull T}
    (G1 G2 : Type -> Type)
    `{Applicative G2}
    `{Applicative G1}.

    (** ** Composition between <<traverse>> and <<map>> *)
    (******************************************************************************)
    Lemma map_traverse {A B C : Type} : forall (g : B -> C) (f : A -> G1 B),
        map G1 (T B) (T C) (@map T _ B C g) ∘ traverse T G1 A B f =
          traverse T G1 A C (map G1 B C g ∘ f).
    Proof.
      intros.
      rewrite (trff_map_to_traverse (T := T)).
      rewrite (trf_traverse_traverse G1 (fun A => A)).
      rewrite (traverse_app_r T G1).
      reflexivity.
    Qed.

    Lemma traverse_map {A B C : Type} : forall (g : B -> G2 C) (f : A -> B),
        traverse T G2 B C g ∘ map T A B f =
          traverse T G2 A C (g ∘ f).
    Proof.
      intros.
      rewrite (trff_map_to_traverse (T := T)).
      change (traverse T G2 B C g)
        with (map (fun A => A) _ _ (traverse T G2 B C g)).
      rewrite (trf_traverse_traverse (fun A => A) G2).
      rewrite (traverse_app_l T G2).
      reflexivity.
    Qed.

    (** ** [Functor] laws *)
    (******************************************************************************)
    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map T B C g ∘ map T A B f = map T A C (g ∘ f).
    Proof.
      intros.
      rewrite (trff_map_to_traverse (T := T)).
      change (traverse T (fun A : Type => A) B C g)
        with (map (fun A => A) _ _ (traverse T (fun A => A) B C g)).
      rewrite (trf_traverse_traverse (fun A => A) (fun A => A)).
      rewrite (traverse_app_l T (fun A => A)).
      reflexivity.
    Qed.

    Lemma map_id : forall (A : Type),
        map T A A (@id A) = @id (T A).
    Proof.
      intros.
      rewrite (trff_map_to_traverse (T := T)).
      now rewrite (trf_traverse_id).
    Qed.

    #[export] Instance Functor_TraversableFunctor : Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

End DerivedLaws.

(** * Notation *)
(******************************************************************************)
Module Notations.
  Infix "⋆2" := (kc2 _ _) (at level 60) : tealeaves_scope.
End Notations.

(** * <<MakeFull>> *)
(******************************************************************************)
#[local] Instance Map_Traverse (T : Type -> Type) `{Traverse T} : Map T :=
  fun (A B : Type) (f : A -> B) => traverse T (fun A => A) A B f.

Corollary map_to_traverse (T : Type -> Type) `{Traverse T} {A B : Type} : forall (f : A -> B),
    @map T _ A B f = traverse T (fun A => A) A B f.
Proof.
  reflexivity.
Qed.

Definition MakeFull
  (T : Type -> Type) (traverse : Traverse T) (traverse_laws : @TraversableFunctor T traverse)
  : @TraversableFunctorFull T traverse (@Map_Traverse T traverse) :=
  {| trff_trf := traverse_laws;
     trff_map_to_traverse := ltac:(reflexivity);
  |}.

(* temporary shim hack ugh *)

#[local] Instance TraversableFunctorMakeFull T `{TraversableFunctor T} : TraversableFunctorFull T.
Proof.
  apply MakeFull. typeclasses eauto.
Qed.
