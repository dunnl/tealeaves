From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Classes.Kleisli.TraversableFunctorPoly
  Classes.Kleisli.Theory.TraversableFunctor
  Functors.List
  Functors.List_Telescoping_General
  Functors.Z2.

Import Applicative.Notations.
Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedTraversableCommIdemFunctor.Notations.

#[local] Generalizable Variables ϕ G T.

(** * Polymorphically Decorated Traversable Functors *)
(******************************************************************************)

(** ** Operation <<mapdtp>> *)
(******************************************************************************)
Class MapdtPoly (T: Type -> Type -> Type) :=
    mapdtp:
      forall (B1 B2 A1 A2: Type)
        (G : Type -> Type)
        `{Gmap: Map G} `{Gpure: Pure G} `{Gmult: Mult G},
        (list B1 * B1 -> G B2) ->
        (list B1 * A1 -> G A2) ->
        T B1 A1 ->
        G (T B2 A2).

Arguments mapdtp {T}%function_scope {MapdtPoly} {B1 B2 A1 A2}%type_scope
  {G}%function_scope {Gmap Gpure Gmult} (_ _)%function_scope _.

(** ** Kleisli Composition *)
(******************************************************************************)
Definition kc_dtfp {T}
  `{MapdtPoly T}
  {G1 : Type -> Type}
  `{map_G1: Map G1} `{pure_G1: Pure G1} `{mult_G1: Mult G1}
  {G2 : Type -> Type}
  `{map_G2: Map G2} `{pure_G2: Pure G2} `{mult_G2: Mult G2}
  {B1 A1 B2 A2 A3: Type}
  (σ2: list B2 * A2 -> G2 A3) (* second op to rename variables *)
  (ρ1: list B1 * B1 -> G1 B2) (* first op to rename binders *)
  (σ1: list B1 * A1 -> G1 A2) (* first op to rename variables *)
  : list B1 * A1 -> (G1 ∘ G2) A3 :=
  fun '(ctx, a) =>
    map (F := G1) σ2 (pure pair
                        <⋆> mapdt_ci (W := Z) ρ1 ctx
                        <⋆> σ1 (ctx, a)).

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctorPoly
    (T: Type -> Type -> Type)
    `{MapdtPoly T} :=
  { kdtfp_mapdtp1:
    forall (B A: Type),
      mapdtp (G := fun A => A)
        (extract (W := (list B ×)))
        (extract (W := (list B ×)))
      = @id (T B A);
    kdtfp_mapdtp2:
    forall {B1 B2 B3: Type}
      {A1 A2 A3: Type}
      `{Applicative G1}
      `{Applicative G2}
      (ρ1: list B1 * B1 -> G1 B2)
      (ρ2: list B2 * B2 -> G2 B3)
      (σ1: list B1 * A1 -> G1 A2)
      (σ2: list B2 * A2 -> G2 A3),
      (forall p: list B1 * B1, IdempotentCenter G1 B2 (ρ1 p)) ->
      map (F := G1) (mapdtp (G := G2) ρ2 σ2) ∘
        mapdtp (G := G1) (T := T) ρ1 σ1 =
        mapdtp (T := T) (G := G1 ∘ G2)
          (ρ2 ⋆3_ci ρ1) (kc_dtfp σ2 ρ1 σ1);
    kdtfp_morphism:
    forall {B1 A1 B2 A2: Type} {G1 G2: Type -> Type}
      `{morph: ApplicativeMorphism G1 G2 ϕ}
      (ρ: list B1 * B1 -> G1 B2)
      (σ: list B1 * A1 -> G1 A2),
      ϕ (T B2 A2) ∘ mapdtp ρ σ =
        mapdtp (ϕ B2 ∘ ρ) (ϕ A2 ∘ σ);
  }.

(** * Derived Monomorphic Instances *)
(******************************************************************************)

(** ** Derived Monomorphic Operations *)
(******************************************************************************)
Module DerivedOperations.
  Section decorated_traversable_functor_derived_operations.

    Context
      `{DecoratedTraversableFunctorPoly T}.

    Context {B: Type}.

    #[export] Instance Mapdt_Mapdtp: Mapdt (list B) (T B) :=
      fun G MapG PureG MultG A1 A2 f =>
        mapdtp (T := T) (G := G)
          (pure (F := G) ∘ extract) f.

    #[export] Instance Traversep_Mapdtp: TraversePoly T :=
      fun A1 A2 B1 B2 G MapG PureG MultG g f =>
        mapdtp (T := T) (G := G)
          (g ∘ extract) (f ∘ extract).

  End decorated_traversable_functor_derived_operations.
End DerivedOperations.

(** ** Derived Typeclass Instances *)
(******************************************************************************)
Module DerivedInstances.
  Section decorated_traversable_functor_derived_instances.

    Import DerivedOperations.

    Context
      `{DecoratedTraversableFunctorPoly T}.

    Context {B: Type}.

    #[export] Instance DecoratedTraversableFunctor_DTFP:
      DecoratedTraversableFunctor (list B) (T B).
    Proof.
      constructor.
      - intro A.
        unfold_ops @Mapdt_Mapdtp.
        unfold_ops @Pure_I.
        change (id ∘ ?x) with x.
        rewrite kdtfp_mapdtp1.
        reflexivity.
      - intros.
        unfold_ops @Mapdt_Mapdtp.
        rewrite kdtfp_mapdtp2.
        2:{
          typeclasses eauto.
        }
        fequal.
        { unfold kc3_ci.
          ext [w b].
          unfold compose.
          unfold mapdt_ci.
          unfold Mapdt_CommIdem_Z.
          cbn.
          rewrite map_ap.
          rewrite map_ap.
          rewrite app_pure_natural.
          change (pure (F := G1) ○ extract)
            with (pure (F := G1) ∘ extract (W := prod (list B)) (A := B)).
          rewrite <- traverse_map.
          rewrite (traverse_purity1 (T := list)).
          unfold compose.
          rewrite ap2.
          rewrite ap2.
          reflexivity.
        }
        { unfold kc_dtfp, kc3.
          ext [ctx a].
          unfold mapdt_ci.
          unfold Mapdt_CommIdem_list_prefix.
          rewrite map_ap.
          rewrite map_ap.
          rewrite app_pure_natural.
          unfold mapdt_list_prefix.
          unfold compose at 4.
          rewrite <- traverse_map.
          rewrite (traverse_purity1 (T := list)).
          unfold compose at 4.
          rewrite ap2.
          rewrite <- map_to_ap.
          unfold compose.
          cbn.
          compose near (f (ctx, a)) on right.
          rewrite (fun_map_map (F := G1)).
          fequal.
          ext b.
          unfold compose.
          compose near ctx.
          rewrite decorate_prefix_list_extract.
          reflexivity.
        }
      - intros.
        unfold_ops @Mapdt_Mapdtp.
        rewrite kdtfp_morphism.
        reassociate <- on left.
        rewrite appmor_pure_pf.
        reflexivity.
    Qed.

  End decorated_traversable_functor_derived_instances.

  Export Kleisli.DecoratedTraversableFunctor.DerivedOperations.
  Export Kleisli.DecoratedTraversableFunctor.DerivedInstances.

End DerivedInstances.

(** ** Relating Polymorphic and Monomorphic Operations *)
(******************************************************************************)
Section decorated_traversable_functor_polymorphic_monomorphic.

  Import DerivedOperations.
  Import DerivedInstances.

  Context
    `{DecoratedTraversableFunctorPoly T}.

  Section monomorphic_binders.

    Definition rename_variables {B A1 A2}:
      (list B * A1 -> A2) -> T B A1 -> T B A2 :=
      fun f => mapd (T := T B) f.

    Definition rename_binders {A B1 B2}:
      (list B1 * B1 -> B2) -> T B1 A -> T B2 A :=
      fun f => mapdtp (G := fun A => A) f (extract).

    Context {A1 A2 B1 B2}
      (g: list B1 * B1 -> B2)
      (f: list B2 * A1 -> A2).

    Lemma rename_binders_variables_commute:
      rename_variables f ∘ rename_binders g =
        rename_binders g ∘ rename_variables
          (fun '(ctx, a) =>
             f (mapdt_ci (W := Z) (G := fun A => A) g ctx, a)).
    Proof.
      unfold rename_variables, rename_binders.
      unfold_ops @Mapd_Mapdt.
      unfold_ops @Mapdt_Mapdtp.

      change (mapdtp (T := T) (G := fun A => A) ?g f) with
        (map (F := fun A => A) (mapdtp (T := T) g f)).
      rewrite (kdtfp_mapdtp2 (G1 := fun A => A) (G2 := fun A => A)).
      2:{ intros [ctx b].
          constructor; constructor; reflexivity. }
      change (mapdtp (T := T) (G := fun A => A)
                g ?ext)
        with
        (map (F := fun A => A)
           (mapdtp (T := T) (G := fun A => A)
              g ext)).
      rewrite (kdtfp_mapdtp2 (G1 := fun A => A) (G2 := fun A => A)).
      2:{ intros [ctx b].
          constructor; constructor; reflexivity. }
      fequal.
      {
        unfold kc3_ci.
        ext [w b].
        unfold_ops @Map_I.
        unfold_ops @Mapdt_CommIdem_Z.
        repeat reassociate <-.
        rewrite <- (traverse_map (G2 := fun A => A) (T := Z)).
        rewrite traverse_purity1.
        rewrite <- map_to_traverse.
        unfold_ops @Pure_I.
        unfold compose, id; cbn.
        unfold id.
        compose near w.
        rewrite decorate_prefix_list_extract.
        reflexivity.
      }
    Qed.

  End monomorphic_binders.
End decorated_traversable_functor_polymorphic_monomorphic.
