From Tealeaves Require Export
  Classes.Kleisli.Comonad
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Kleisli.TraversableFunctor.

#[local] Generalizable Variable T G A B C ϕ M.

Import TraversableFunctor.Notations.

(** * CI-Decorated Traversable functor *)
(**********************************************************************)

(** ** The <<mapdt_ci>> Operation *)
(**********************************************************************)
Class Mapdt_CommIdem (W: Type -> Type) (T: Type -> Type) :=
  mapdt_ci:
    forall (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B: Type), (W A -> G B) -> T A -> G (T B).

#[global] Arguments mapdt_ci {W T}%function_scope {Mapdt_CommIdem}
  {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope.

(** ** Kleisli Composition *)
(**********************************************************************)
Section kleisli_composition.

  Context
    {W: Type -> Type}
    `{Mapdt_CommIdem W W}.

  Definition kc3_ci
    {G1 G2: Type -> Type}
    `{Map G1} `{Pure G1} `{Mult G1} {A B C: Type}:
    (W B -> G2 C) ->
    (W A -> G1 B) ->
    (W A -> (G1 ∘ G2) C) :=
    fun g f => map (F := G1) (A := W B) (B := G2 C) g ∘
              mapdt_ci (T := W) (G := G1) f.

End kleisli_composition.

#[local] Infix "⋆3_ci" := (kc3_ci) (at level 60): tealeaves_scope.

(** ** Typeclasses *)
(**********************************************************************)
(** Note that W should itself be DecoratedTraversableCommIdem, but it's not a field in the typeclass because that may
 make the class difficult to instantiate for W itself due to the circularity. In fact W should be a Comonad *)
Class DecoratedTraversableCommIdemFunctor
  (W: Type -> Type)
  (T: Type -> Type)
  `{Extract_W: Extract W}
  `{Mapdt_WW: Mapdt_CommIdem W W}
  `{Mapdt_WT: Mapdt_CommIdem W T} :=
  { kdtfci_mapdt1: forall (A: Type),
      mapdt_ci (G := fun A => A) extract = @id (T A);
    kdtfci_mapdt2:
    forall `{ApplicativeCommutativeIdempotent G1}
      `{ApplicativeCommutativeIdempotent G2}
      (A B C: Type) (g: W B -> G2 C) (f: W A -> G1 B),
      map (mapdt_ci g) ∘ mapdt_ci (T := T) f =
        mapdt_ci (G := G1 ∘ G2) (g ⋆3_ci f);
    kdtfci_morph:
    forall `{ApplicativeMorphism G1 G2 ϕ}
      (A B: Type) (f: W A -> G1 B),
      mapdt_ci (ϕ B ∘ f) = ϕ (T B) ∘ mapdt_ci f;
  }.


Class Compat_Map_Mapdtci W T
  `{Extract W}
  `{Map_T: Map T}
  `{Mapdt_WT: Mapdt_CommIdem W T} :=
  compat_map_mapdt_ci:
    forall (A B: Type) (f: A -> B),
      map (F := T) f = mapdt_ci (G := fun A => A) (f ∘ extract (W := W)).

(** ** Basic Laws *)
(**********************************************************************)
Section basic_laws.


  Context
    {W F: Type -> Type}
    `{DecoratedTraversableCommIdemFunctor W F}
    `{! DecoratedTraversableCommIdemFunctor W W}
    `{Map_W: Map W}
    `{! Functor W}
    `{! Compat_Map_Mapdtci W W}.



  Context
    `{Applicative G1}
    `{Applicative G2}.

  Lemma kc3_ci_pure_extract1:
    forall  (B C: Type) (g: W B -> G2 C),
      kc3_ci (W := W) (G1 := G1) g (pure (F := G1) ∘ extract (W := W)) = pure (F := G1) ∘ g.
  Proof.
    intros.
    unfold kc3_ci.
    rewrite (kdtfci_morph (ϕ := @pure G1 _)).
    rewrite kdtfci_mapdt1.
    reassociate <- on left.
    rewrite (natural (ϕ := @pure G1 _)).
    reflexivity.
  Qed.

  Lemma kc3_ci_pure_extract2:
    forall  (A B: Type) (f: W A -> G1 B),
      kc3_ci (G2 := fun A => A) (pure (F := G2) ∘ extract (W := W)) f = pure (F := G2) ∘ f.
  Proof.
    intros.
    unfold kc3_ci.
    unfold_ops @Map_I.
  Abort.

End basic_laws.

(** * Notations *)
(**********************************************************************)
Module Notations.
  #[global] Infix "⋆3_ci" := (kc3_ci) (at level 60): tealeaves_scope.
End Notations.
