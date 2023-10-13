From Tealeaves Require Import
  Classes.Categorical.DecTravFunctor
  Classes.Kleisli.DecTravFunctor.

Import Kleisli.DecTravFunctor.Notations.
Import Product.Notations.

#[local] Generalizable Variables G ϕ.

(** * Kleisli presentation of decorated-traversable functors *)
(******************************************************************************)
Module ToKleisli.

  #[export] Instance Mapdt_distdec
    (E : Type)
    (T : Type -> Type)
    `{Map T} `{Decorate E T} `{ApplicativeDist T} : Mapdt E T :=
  fun (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    (A B : Type) (f : E * A -> G B) => (dist T G ∘ map T f ∘ dec T : T A -> G (T B)).

  Section with_functor.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Categorical.DecTravFunctor.DecoratedTraversableFunctor E T}.

    Theorem mapdt_id : forall (A : Type), mapdt T (fun A => A) (extract (E ×) A) = @id (T A).
    Proof.
      introv. unfold_ops @Mapdt_distdec.
      reassociate -> on left.
      rewrite (dfun_dec_extract (E := E) (F := T)).
      now rewrite (dist_unit (F := T)).
    Qed.

    Theorem mapdt_mapdt :
      forall (G1 G2 : Type -> Type) `{Applicative G1} `{Applicative G2}
        (A B C : Type) (g : E * B -> G2 C) (f : E * A -> G1 B),
        map G1 (mapdt T G2 g) ∘ mapdt T G1 f = mapdt T (G1 ∘ G2) (g ⋆6 f).
    Proof.
      intros. unfold transparent tcs. unfold kc6.
      rewrite <- (fun_map_map (F := G1)).
      repeat reassociate <- on left.
      change (?f ∘ map G1 (dec T) ∘ dist T G1 ∘ ?g) with
        (f ∘ (map G1 (dec T) ∘ dist T G1) ∘ g).
      rewrite <- (dtfun_compat (E := E) (F := T) B).
      rewrite <- (fun_map_map (F := G1)).
      repeat reassociate <- on left.
      change (?f ∘ map G1 (map T g) ∘ dist T G1 ∘ ?h) with
        (f ∘ (map G1 (map T g) ∘ dist T G1) ∘ h).
      change (map G1 (map T g)) with (map (G1 ∘ T) g).
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      rewrite (dist_linear (F := T)).
      repeat reassociate <- on left.
      rewrite <- (fun_map_map (F := T)).
      unfold_ops @Map_compose.
      change (?f ∘ map T (map G1 g) ∘ ?x ∘ ?h) with
        (f ∘ (map T (map G1 g) ∘ x) ∘ h).
      rewrite (fun_map_map (F := T)). reassociate -> near (map T f).
      rewrite <- (natural (ϕ := @dec E T _)).
      repeat reassociate ->.
      repeat fequal.
      rewrite (dfun_dec_dec (E := E) (F := T)).
      reassociate <-. unfold_ops @Map_compose.
      rewrite (fun_map_map (F := T)).
      do 2 fequal. now ext [e a].
    Qed.

    Theorem mapdt_mapdt_morphism : forall `{ApplicativeMorphism G1 G2 ϕ} (A B : Type) (f : E * A -> G1 B),
        mapdt T G2 (ϕ B ∘ f) = ϕ (T B) ∘ mapdt T G1 f.
    Proof.
      intros. unfold transparent tcs.
      do 2 reassociate <-.
      rewrite <- (fun_map_map (F := T)).
      rewrite <- (dist_morph (F := T)).
      reflexivity.
    Qed.

    #[local] Instance: Kleisli.DecTravFunctor.DecoratedTraversableFunctor E T :=
      {| kdtfun_mapdt1 := @mapdt_id;
        kdtfun_mapdt2 := @mapdt_mapdt;
        kdtfun_morph := @mapdt_mapdt_morphism;
      |}.

  End with_functor.

End ToKleisli.
