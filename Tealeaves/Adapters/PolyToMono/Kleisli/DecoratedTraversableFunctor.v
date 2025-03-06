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
  Admitted.

End dtfp_to_dtf.


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
  Admitted.

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
    Admitted.

  End commute.

End relating.

