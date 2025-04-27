From Tealeaves Require Import
  Categorical.DecoratedTraversableMonadPoly.

From Tealeaves Require Import
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.RightComodule.

From Tealeaves Require Import
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedFunctorZ
  Classes.Kleisli.DecoratedTraversableFunctor.

From Tealeaves Require Import
  Classes.Kleisli.DecoratedFunctorPoly.

From Tealeaves Require Import
  CategoricalToKleisli.DecoratedFunctor
  CategoricalToKleisli.TraversableFunctor
  CategoricalToKleisli.Monad
  CategoricalToKleisli.DecoratedTraversableFunctor
  CategoricalToKleisli.DecoratedTraversableMonad.

From Tealeaves Require Import
  CategoricalToKleisli.DecoratedFunctorZ
  CategoricalToKleisli.DecoratedFunctorPoly
  CategoricalToKleisli.DecoratedMonadPoly
  CategoricalToKleisli.DecoratedTraversableFunctorPoly
  CategoricalToKleisli.DecoratedTraversableMonadPoly.

From Tealeaves Require Import
  Adapters.PolyToMono.Categorical.DecoratedFunctor
  Adapters.PolyToMono.Categorical.TraversableFunctor
  Adapters.PolyToMono.Categorical.TraversableMonad
  Adapters.PolyToMono.Categorical.DecoratedMonad
  Adapters.PolyToMono.Categorical.DecoratedTraversableMonad.

From Tealeaves Require
  Adapters.MonoidHom.Categorical.

Module ListUnitToNat.

  Import Adapters.MonoidHom.Categorical.

  #[export] Instance Monoid_Morphism_length:
    Monoid_Morphism (list unit) nat (length (A:=unit)).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - reflexivity.
    - intros.
      apply List.app_length.
  Qed.

  Section with_DTM.

    Context
      {T: Type -> Type}
    `{Dec_orig: Decorate (list unit) T}.

  Context
    `{Map_T: Map T}
    `{Dist_T: ApplicativeDist T}
    `{Join_T: Join T}
    `{Return_T: Return T}.

  #[export] Instance Decorate_list_unit_nat: Decorate nat T.
  Proof.
    apply (Decorate_Monoid_Morphism (@length unit)).
  Defined.

  #[export] Instance Natural_Decorate_list_unit
    `{! DecoratedFunctor (list unit) T}:
    Natural (@dec nat T Decorate_list_unit_nat).
  Proof.
    typeclasses eauto.
  Qed.

  #[export] Instance DecoratedFunctor_list_unit
    `{! DecoratedFunctor (list unit) T}:
    DecoratedFunctor nat T.
  Proof.
    apply DecoratedFunctor_Monoid_Morphism; typeclasses eauto.
  Qed.


  #[export] Instance DecoratedMonad_list_unit
    `{! DecoratedMonad (list unit) T}:
    DecoratedMonad nat T.
  Proof.
    apply DecoratedMonad_Monoid_Morphism; typeclasses eauto.
  Qed.


  #[export] Instance DecoratedTraversableFunctor_list_unit
    `{! DecoratedTraversableFunctor (list unit) T}:
    DecoratedTraversableFunctor nat T.
  Proof.
    apply DecoratedTraversableFunctor_Monoid_Morphism; typeclasses eauto.
  Qed.

  #[export] Instance DecoratedTraversableMonad_list_unit
    `{! DecoratedTraversableMonad (list unit) T}:
    DecoratedTraversableMonad nat T.
  Proof.
    apply DecoratedTraversableMonad_Monoid_Morphism; typeclasses eauto.
  Qed.

  End with_DTM.
End ListUnitToNat.

Module CategoricalToKleisliAll.
  Export Adapters.PolyToMono.Categorical.DecoratedFunctor.
  Export Adapters.PolyToMono.Categorical.DecoratedFunctor.ToMono1.
  Export Adapters.PolyToMono.Categorical.DecoratedFunctor.ToMono2.

  Export Adapters.PolyToMono.Categorical.TraversableFunctor.
  Export Adapters.PolyToMono.Categorical.TraversableFunctor.ToMono.

  Export Adapters.PolyToMono.Categorical.TraversableMonad.
  Export Adapters.PolyToMono.Categorical.TraversableMonad.ToMono.

  Export Adapters.PolyToMono.Categorical.DecoratedMonad.
  Export Adapters.PolyToMono.Categorical.DecoratedMonad.ToMono1.

  Export Adapters.PolyToMono.Categorical.DecoratedTraversableMonad.
  Export Adapters.PolyToMono.Categorical.DecoratedTraversableMonad.ToMono.

  Export CategoricalToKleisli.DecoratedFunctor.
  Export CategoricalToKleisli.DecoratedFunctor.DerivedOperations.
  Export CategoricalToKleisli.DecoratedFunctor.DerivedInstances.

  Export CategoricalToKleisli.DecoratedFunctor.
  Export CategoricalToKleisli.DecoratedFunctor.DerivedOperations.
  Export CategoricalToKleisli.DecoratedFunctor.DerivedInstances.

  Export CategoricalToKleisli.TraversableFunctor.
  Export CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Export CategoricalToKleisli.TraversableFunctor.DerivedInstances.

  Export CategoricalToKleisli.DecoratedTraversableFunctor.
  Export CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Export CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.

  Export CategoricalToKleisli.DecoratedTraversableMonad.
  Export CategoricalToKleisli.DecoratedTraversableMonad.DerivedOperations.
  Export CategoricalToKleisli.DecoratedTraversableMonad.DerivedInstances.

  Export CategoricalToKleisli.Monad.
  Export CategoricalToKleisli.Monad.DerivedOperations.
  Export CategoricalToKleisli.Monad.DerivedInstances.

  Export CategoricalToKleisli.DecoratedFunctorPoly.
  Export CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.
  Export CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.

  Export CategoricalToKleisli.DecoratedFunctorZ.
  Export CategoricalToKleisli.DecoratedFunctorZ.DerivedOperations.
  Export CategoricalToKleisli.DecoratedFunctorZ.DerivedInstances.

  Export CategoricalToKleisli.DecoratedMonadPoly.
  Export CategoricalToKleisli.DecoratedMonadPoly.DerivedOperations.
  Export CategoricalToKleisli.DecoratedMonadPoly.DerivedInstances.

  Export CategoricalToKleisli.DecoratedTraversableFunctorPoly.
  Export CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.
  Export CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.

  Export CategoricalToKleisli.DecoratedTraversableMonadPoly.
  Export CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedOperations.
  Export CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedInstances.
End CategoricalToKleisliAll.


Module KleisliClassesAll.

  Export Classes.Kleisli.DecoratedFunctorPoly.
  Export Classes.Kleisli.DecoratedMonadPoly.
  Export Classes.Kleisli.TraversableFunctor2.
  Export Classes.Kleisli.DecoratedTraversableFunctorPoly.
  Export Classes.Kleisli.DecoratedTraversableMonadPoly.

End KleisliClassesAll.

Section mapdp_decomposed.

  Context
    (T: Type -> Type -> Type)
    `{DecoratedFunctorPoly T}.

  Import CategoricalToKleisliAll.

  Lemma mapdp_decompose {B1 V1 B2 V2: Type}:
    forall (g: list B1 * B1 -> B2)
      (f: list B1 * V1 -> V2),
      mapdp (T := T) g f =
        mapdz (T := fun B => T B V2) g ∘ mapd (T := T B1) f.
  Proof.
    intros.
    unfold_ops @Mapdp_Categorical.
    unfold mapdz.
    unfold mapd.
    unfold_ops @Mapd_Categorical.
    unfold_ops @Mapdz_Categorical.
    unfold_ops @Map2_1.
    unfold_ops @Map2_2.
    unfold right_coaction.
    unfold_ops @BDec.
    reassociate <- on right.
    reassociate <- on right.
    reassociate -> near (map2 id f).
    rewrite polydecnat.
    reassociate <- on right.
    rewrite fun2_map_map.
    rewrite fun2_map_map.
    unfold dec.
    unfold VDec.
    reassociate <- on right.
    reassociate -> near (map2 (@extract Z Extract_Z B1) (@id (L B1 V1))).
    rewrite polydecnat.
    reassociate -> on right.
    reassociate -> on right.
    reassociate -> on right.
    reassociate -> on right.
    rewrite dfunp_dec_dec.
    reassociate <- on right.
    reassociate <- on right.
    reassociate <- on right.
    reassociate <- on right.
    rewrite fun2_map_map.
    rewrite fun2_map_map.
    repeat rewrite fun_map_id.
    repeat change (id ∘ ?f) with f.
    repeat change (?f ∘ id) with f.
    reassociate -> on right.
    setoid_rewrite com_map_extr_cojoin.
    repeat change (?f ∘ id) with f.
    fequal.
    fequal.
    ext [l v1].
    reflexivity.
  Qed.

End mapdp_decomposed.

(** * Convenient Interface to categorically-defined PDTMs *)
(********************************************************************)
Module PDTM_specialized_ops.

Section pdtm.

  Context
    {T: Type -> Type -> Type}.

  Context
    {Map2_T: Map2 T}
    {Decorate2_T: DecoratePoly T}
    {Dist2_T: ApplicativeDist2 T}
    {Join_T: forall B, Join (T B)}
    {Ret_T: forall B, Return (T B)}.

  Context `{! Categorical.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly T}.

  Import CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations.

  (** ** Single-argument Categorical Operations *)
  (********************************************************************)
  #[export] Instance vdec {B: Type}: Decorate (list B) (T B) :=
    PolyToMono.Categorical.DecoratedFunctor.ToMono1.VDec.

  #[export] Instance bdec {V: Type}: RightCoaction (fun B => T B V) Z :=
    PolyToMono.Categorical.DecoratedFunctor.ToMono2.BDec.

  #[global] Arguments vdec {B}%type_scope {V} _ :rename.
  #[global] Arguments bdec {V}%type_scope {B} _ :rename.

  #[export] Instance vdist {B: Type}: ApplicativeDist (T B) :=
    PolyToMono.Categorical.TraversableFunctor.ToMono.Dist2_1.

  #[export] Instance bdist {V: Type}: ApplicativeDist (fun B => T B V) :=
        PolyToMono.Categorical.TraversableFunctor.ToMono.Dist2_2.

  (** ** Single-argument Categorical Instances *)
  (********************************************************************)
  #[export] Instance DecoratedFunctor_PDTM_V: forall B,
      @Categorical.DecoratedFunctor.DecoratedFunctor (list B) (T B) (@vmap T Map2_T B) (@vdec B) :=
    @PolyToMono.Categorical.DecoratedFunctor.ToMono1.DecoratedFunctor_V T Map2_T Decorate2_T _.

  #[export] Instance TraversableFunctor_PDTM_V: forall B,
      @Categorical.TraversableFunctor.TraversableFunctor (T B) (@vmap T Map2_T B) (@vdist B) :=
    @PolyToMono.Categorical.TraversableFunctor.ToMono.TraversableFunctor_Dist2_1 T Map2_T Dist2_T _.

  #[export] Instance DecoratedFunctor_PDTM_B: forall V,
      @RightComodule (fun B => T B V) Z (Map_Z) (Cojoin_Z) (Extract_Z)
        (@bmap T Map2_T V) (@bdec V) :=
    @PolyToMono.Categorical.DecoratedFunctor.ToMono2.DecoratedFunctor_B T Map2_T Decorate2_T _.

  #[export] Instance TraversableFunctor_PDTM_B: forall V,
      @Categorical.TraversableFunctor.TraversableFunctor (fun B => T B V) (@bmap T Map2_T V) (@bdist V) :=
    @PolyToMono.Categorical.TraversableFunctor.ToMono.TraversableFunctor_Dist2_2 T Map2_T Dist2_T _.

  (** ** Single-argument Kleisli operations *)
  (********************************************************************)
  #[export] Instance vtraverse {B}: Traverse (T B) :=
    CategoricalToKleisli.TraversableFunctor.DerivedOperations.Traverse_Categorical (T B).

  #[export] Instance btraverse {V}: Traverse (fun B => T B V) :=
    CategoricalToKleisli.TraversableFunctor.DerivedOperations.Traverse_Categorical (fun B => T B V).

  #[export] Instance Kleisli_TraversableFunctor_PDTM_V {B: Type}:
      @Kleisli.TraversableFunctor.TraversableFunctor (T B) (@vtraverse B) :=
    CategoricalToKleisli.TraversableFunctor.DerivedInstances.TraversableFunctor_Kleisli_Categorical.

  #[export] Instance Kleisli_TraversableFunctor_PDTM_B {V: Type}:
      @Kleisli.TraversableFunctor.TraversableFunctor (fun B => T B V) (@btraverse V) :=
    CategoricalToKleisli.TraversableFunctor.DerivedInstances.TraversableFunctor_Kleisli_Categorical.

  #[global] Arguments vtraverse {B}%type_scope {G Map_G Pure_G Mult_G A B} _ _.
  #[global] Arguments btraverse {V}%type_scope {G Map_G Pure_G Mult_G A B} _ _.

  #[export] Instance vmapd {B: Type}:
    Mapd (list B) (T B) :=
    DerivedOperations.Mapd_Categorical (Decorate_EF := @vdec B) (list B) (T B).

  Definition bmapd {V B1 B2: Type}:
    (list B1 * B1 -> B2) ->
    T B1 V -> T B2 V :=
    (fun f => bmap f ∘ bdec).

  #[global] Arguments vmapd {B}%type_scope {V1 V2}%type_scope _ _ :rename.

  #[export] Instance Compat_VMapd_Categorical_PDTM {B}:
    Compat_Mapd_Categorical (list B) (T B).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Kleisli_DecoratedFunctor_PDTM_V {B: Type}:
      @Kleisli.DecoratedFunctor.DecoratedFunctor (list B) (T B) (@vmapd B) :=
    CategoricalToKleisli.DecoratedFunctor.DerivedInstances.DecoratedFunctor (T B).

  Lemma mapdp_decompose {B1 V1 B2 V2: Type}:
    forall (g: list B1 * B1 -> B2)
      (f: list B1 * V1 -> V2),
      mapdp (T := T) g f = bmapd g ∘ vmapd f.
  Proof.
    intros.
    unfold_ops @Mapdp_Categorical.
    unfold bmapd.
    unfold vmapd.
    unfold_ops @DerivedOperations.Mapd_Categorical.
    unfold bmap.
    unfold_ops @Map2_1.
    unfold_ops @Map2_2.
    unfold bdec.
    unfold_ops @DecoratedFunctor.ToMono2.BDec.
    reassociate <- on right.
    reassociate <- on right.
    reassociate -> near (map2 id f).
    rewrite polydecnat.
    reassociate <- on right.
    rewrite fun2_map_map.
    rewrite fun2_map_map.
    unfold dec.
    unfold vdec.
    unfold DecoratedFunctor.ToMono1.VDec.
    reassociate <- on right.
    reassociate -> near (map2 (@extract Z Extract_Z B1) (@id (L B1 V1))).
    rewrite polydecnat.
    reassociate -> on right.
    reassociate -> on right.
    reassociate -> on right.
    reassociate -> on right.
    rewrite dfunp_dec_dec.
    reassociate <- on right.
    reassociate <- on right.
    reassociate <- on right.
    reassociate <- on right.
    rewrite fun2_map_map.
    rewrite fun2_map_map.
    repeat rewrite fun_map_id.
    repeat change (id ∘ ?f) with f.
    repeat change (?f ∘ id) with f.
    reassociate -> on right.
    setoid_rewrite com_map_extr_cojoin.
    repeat change (?f ∘ id) with f.
    fequal.
    fequal.
    ext [l v1].
    reflexivity.
  Qed.

  #[export] Instance vmapdt {B: Type}:
    Mapdt (list B) (T B) :=
    DerivedOperations.Mapdt_Categorical (Decorate_T := @vdec B) (list B) (T B).

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.

  #[export] Instance: forall B, DecoratedTraversableFunctor (list B) (T B).
  Proof.
    typeclasses eauto.
  Qed.

End pdtm.

End PDTM_specialized_ops.
