From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Classes.Monoid
  Functors.List
  Functors.Writer
  Functors.List_Telescoping_General.

Import Applicative.Notations.
Import Monoid.Notations.
Import Product.Notations.
Import DecoratedTraversableCommIdemFunctor.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

Section dtmp_to_dtm.
  Context
    {T: Type -> Type -> Type}
      `{DecoratedTraversableMonadPoly T}.

  #[export] Instance Binddt_of_Binddtp {B}: Binddt (list B) (T B) (T B) :=
    fun G Gmap Gpure Gmult V1 V2 σ =>
      substitute (G := G) (T := T) (pure ∘ extract (W := prod (list B)) (A := B)) (σ).

  #[export] Instance DTM_of_DTMP {B}: DecoratedTraversableMonad (list B) (T B).
  Proof.
    constructor.
    - typeclasses eauto.
    - intros.
      unfold_ops @Binddt_of_Binddtp.
      rewrite kdtmp_substitute0.
      reflexivity.
    - constructor.
      + intros.
        unfold_ops @Binddt_of_Binddtp.
        unfold_ops @Pure_I.
        apply kdtmp_substitute1.
      + intros.
        unfold_ops @Binddt_of_Binddtp.
        unfold_ops @Pure_I.
        rewrite kdtmp_substitute2.
        { fequal.
          - ext [ctx b].
            unfold kc3_ci.
            admit.
          - ext [ctx v].
            unfold kc_dtmp.
            unfold kc7.
            admit.
        }
        { intros [ctx b].
          cbv.
          typeclasses eauto.
        }
      + intros.
        unfold_ops @Binddt_of_Binddtp.
        rewrite kdtmp_morphism.
        reassociate <- on left.
        rewrite appmor_pure_pf.
        reflexivity.
  Admitted.

End dtmp_to_dtm.


Section dtmp_to_dtf_bin.
  Context
    {T: Type -> Type -> Type}
      `{DecoratedTraversableMonadPoly T}.

  #[export] Instance MapdtB_of_Binddtp {V}: Mapdt_CommIdem Z (fun B => T B V) :=
    fun G Gmap Gpure Gmult B1 B2 ρ =>
      substitute (G := G) (U := T) (T := T) ρ (pure (F := G) ∘ ret (T := T B2) ∘ extract).

  #[export] Instance DTFCI_of_DTMP {V}: DecoratedTraversableCommIdemFunctor Z (fun B => T B V).
  Proof.
    constructor.
    - unfold_ops @MapdtB_of_Binddtp.
      intros.
      apply kdtmp_substitute1.
    - intros.
      unfold_ops @MapdtB_of_Binddtp.
      rewrite kdtmp_substitute2.
      fequal.
      { (* kc_dtmp lemma *)
        admit. }
      { (* idempotentcenter lemma *)
        admit. }
    - intros.
      unfold_ops @MapdtB_of_Binddtp.
      rewrite kdtmp_morphism.
      reassociate <- on right.
      reassociate <- on right.
      rewrite appmor_pure_pf.
      reflexivity.
  Admitted.

End dtmp_to_dtf_bin.
