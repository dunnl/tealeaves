From Tealeaves Require Export
  Classes.Categorical.DecoratedTraversableFunctorPoly
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedTraversableFunctorPoly
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  CategoricalToKleisli.DecoratedTraversableFunctorPoly
  Classes.Monoid
  Functors.List
  Functors.Writer
  Functors.List_Telescoping_General.

Import Applicative.Notations.
Import Monoid.Notations.
Import Product.Notations.
Import DecoratedTraversableCommIdemFunctor.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

(** * Parameterized Decorated Traversable Functor to single DTF *)
(**********************************************************************)
Section dtfp_to_dtf.

  Context
    {T: Type -> Type -> Type}
    `{DecoratedTraversableFunctorPoly T}.

  #[export] Instance Mapdt_of_Mapdtp {B}: Mapdt (list B) (T B) :=
    fun G Gmap Gpure Gmult V1 V2 ρ =>
      mapdtp (G := G) (T := T) (pure ∘ extract (W := prod (list B)) (A := B)) ρ.

  #[export] Instance DTF_of_DTFP {B}: DecoratedTraversableFunctor (list B) (T B).
  Proof.
    constructor.
    - intros.
      unfold_ops @Mapdt_of_Mapdtp.
      rewrite kdtfp_mapdtp1.
      reflexivity.
    - intros.
      unfold_ops @Mapdt_of_Mapdtp.
      rewrite kdtfp_mapdtp2.
      fequal.
      { (* kc lemma *)
        unfold kc3_ci.
        unfold mapdt_ci.
        admit. }
      { (* kc lemma *)
        admit.
      }
      { (* idempotent center of pure extract *)
        admit.
      }
    - intros.
      unfold_ops @Mapdt_of_Mapdtp.
      rewrite kdtfp_morphism.
      reassociate <- on left.
      rewrite appmor_pure_pf.
      reflexivity.
  Abort.

End dtfp_to_dtf.

(** * Parameterized Decorated Traversable Functor to single DTF *)
(**********************************************************************)
Section dtfp_to_dtf_bin.

  Context
    {T: Type -> Type -> Type}
    `{DecoratedTraversableFunctorPoly T}.

  #[export] Instance MapdtB_of_Mapdtp {V}: Mapdt_CommIdem Z (fun B => T B V) :=
    fun G Gmap Gpure Gmult B1 B2 ρ =>
      mapdtp (G := G) (T := T) ρ (pure (F := G) ∘ extract).

  #[export] Instance DTFCI_of_DTFP {V}: DecoratedTraversableCommIdemFunctor Z (fun B => T B V).
  Proof.
    constructor.
    - unfold_ops @MapdtB_of_Mapdtp.
      intros.
      apply kdtfp_mapdtp1.
    - intros.
      unfold_ops @MapdtB_of_Mapdtp.
      rewrite kdtfp_mapdtp2.
      fequal.
      { (* kc_dtfp lemma *)
        admit. }
      { (* idempotentcenter lemma *)
        admit. }
    - intros.
      unfold_ops @MapdtB_of_Mapdtp.
      rewrite kdtfp_morphism.
      reassociate <- on right.
      rewrite appmor_pure_pf.
      reflexivity.
  Abort.

End dtfp_to_dtf_bin.

(* Relating Mono to Poly *)
Section relating.

  Context
    `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.

  Definition rename_binders
    {B1 V1 B2: Type}
      (ρ: list B1 * B1 -> B2)
    := mapdt_ci (W := Z) (G := fun A => A) (T := fun B => T B V1) ρ.

  Section commute.

    Context
      {B1 V1 B2 V2: Type}
      {ρ: list B1 * B1 -> B2}
      `{Applicative G}
      {σ: list B2 * V1 -> G V2}
      (t: T B1 V1).

    Lemma commute:
      map (F := G) (rename_binders (ρ: list B1 * B1 -> B2))
        (mapdt (G := G) (T := T B1)
           (fun '(b1, v1) => σ (mapdt_ci (G := fun A => A) (W := Z) (T := list) ρ b1, v1: V1)) t) =
        mapdt (G := G) (T := T B2) σ (rename_binders (ρ: list B1 * B1 -> B2) t).
    Proof.
      intros.
      unfold rename_binders.
      unfold_ops @MapdtB_of_Mapdtp.
      unfold_ops @Mapdt_of_Mapdtp.
      compose near t.
      change_right ((map (F := fun A =>A) (mapdtp (pure ∘ extract) σ) ∘ mapdtp (G := fun A => A) ρ (pure ∘ extract)) t).
      rewrite (kdtfp_mapdtp2 (G1 := fun A => A)).
      2:{ (* idempotentcenter of ID *)
        admit.
      }
      rewrite (kdtfp_mapdtp2 (G2 := fun A => A)).
      2:{ (* idempotentcenter of pure extract *)
        admit.
      }
      fequal.
      admit.
      admit.
      admit.
    Abort.

  End commute.

End relating.


(** * Derived Monomorphic Instances *)
(**********************************************************************)

(** ** Derived Monomorphic Operations *)
(**********************************************************************)
Module DerivedOperations.
  Section decorated_traversable_functor_derived_operations.

    Context
      `{DecoratedTraversableFunctorPoly T}.

    Context {B: Type}.

    #[export] Instance Mapdt_Mapdtp: Mapdt (list B) (T B) :=
      fun G MapG PureG MultG A1 A2 f =>
        mapdtp (T := T) (G := G)
          (pure (F := G) ∘ extract) f.

    (*
    #[export] Instance Traversep_Mapdtp: Traverse2 T :=
      fun A1 A2 B1 B2 G MapG PureG MultG g f =>
        mapdtp (T := T) (G := G)
          (g ∘ extract) (f ∘ extract).
     *)

  End decorated_traversable_functor_derived_operations.
End DerivedOperations.

(*
(** ** Derived Typeclass Instances *)
(**********************************************************************)
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

(*
(** ** Relating Polymorphic and Monomorphic Operations *)
(**********************************************************************)
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
*)
*)
