From Tealeaves Require Import
  Classes.Kleisli.DecoratedContainerMonad.

#[local] Generalizable Variables F T U W.

Import Monoid.Notations.
Import Product.Notations.
Import DecoratedTraversableFunctor.Notations.

Section compose_functors.

  Context
    `{Monoid W}.

  #[export] Instance Mapdt_compose
    `{Mapdt W F1} `{Mapdt W F2}: Mapdt W (F1 ○ F2) :=
    fun G map pure mult A B f =>
      mapdt (T := F1) (G := G) (fun '(w1, t) => mapdt (T := F2) (f ⦿ w1) t).

  Context
    `{Mapdt W F1} `{Mapdt W F2}
    `{! DecoratedTraversableFunctor W F1}
    `{! DecoratedTraversableFunctor W F2}.

  Lemma kdtfun_comp_mapdt1 : forall A : Type,
      mapdt (T := F1 ○ F2) (@extract (W ×) _ A) = id.
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite <- kdtfun_mapdt1.
    fequal.
    ext [w t].
    rewrite extract_preincr.
    rewrite kdtfun_mapdt1.
    reflexivity.
  Qed.

  Lemma kdtfun_comp_mapdt2 :
    forall (G1 : Type -> Type) (H1 : Map G1)
      (H2 : Pure G1) (H3 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H5 : Map G2)
        (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : W * B -> G2 C) (f : W * A -> G1 B),
          map (F := G1) (mapdt (G := G2) (T := F1 ○ F2) g)
              ∘ mapdt (G := G1) (T := F1 ○ F2) f =
            mapdt (G := G1 ∘ G2) (T := F1 ○ F2) (kc6 g f).
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite (kdtfun_mapdt2
               (A := F2 A) (B := F2 B) (C := F2 C)
               (E := W) (G1 := G1) (G2 := G2) (T := F1)).
    fequal.
    ext [w1 t].
    rewrite (kc6_preincr _ _ _ f g w1).
    rewrite <- (kdtfun_mapdt2
               (A := A) (B := B) (C := C)
               (E := W) (G1 := G1) (G2 := G2) (T := F2)).
    unfold kc6, compose; cbn.
    compose near (mapdt (f ⦿ w1) t) on left.
    assert (Functor G1). { now inversion H5. }.
    rewrite (fun_map_map (F := G1)).
    reflexivity.
  Qed.

  Lemma kdtfun_comp_morph :
    forall (G1 G2 : Type -> Type) (H1 : Map G1)
      (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2)
      (H5 : Mult G2) (H6 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : W * A -> G1 B),
        mapdt (ϕ B ∘ f) = ϕ (F1 (F2 B)) ∘ (mapdt (T := F1 ○ F2) (G := G1) f).
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite <- kdtfun_morph.
    fequal.
    ext [w t].
    unfold compose; cbn.
    compose near t on right.
    rewrite <- kdtfun_morph.
    reflexivity.
  Qed.

  #[export] Instance DecoratedTraversableFunctor_compose:
    DecoratedTraversableFunctor W (F1 ○ F2) :=
    {| kdtfun_mapdt1 := kdtfun_comp_mapdt1;
      kdtfun_mapdt2 := kdtfun_comp_mapdt2;
      kdtfun_morph := kdtfun_comp_morph;
    |}.

End compose_functors.

(*
Section compose_functor_module.

  Context
    `{Monoid W}.

  #[export] Instance Mapdt_compose
    `{Mapdt W F1} `{Mapdt W F2}: Mapdt W (F1 ○ F2) :=
    fun G map pure mult A B f =>
      mapdt (T := F1) (G := G) (fun '(w1, t) => mapdt (T := F2) (f ⦿ w1) t).

  Context
    `{Mapdt W F1} `{Mapdt W F2}
    `{! DecoratedTraversableFunctor W F1}
    `{! DecoratedTraversableFunctor W F2}.

  Lemma kdtfun_comp_mapdt1 : forall A : Type,
      mapdt (T := F1 ○ F2) (@extract (W ×) _ A) = id.
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite <- kdtfun_mapdt1.
    fequal.
    ext [w t].
    rewrite extract_preincr.
    rewrite kdtfun_mapdt1.
    reflexivity.
  Qed.

  Lemma kdtfun_comp_mapdt2 :
    forall (G1 : Type -> Type) (H1 : Map G1)
      (H2 : Pure G1) (H3 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H5 : Map G2)
        (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : W * B -> G2 C) (f : W * A -> G1 B),
          map (F := G1) (mapdt (G := G2) (T := F1 ○ F2) g)
              ∘ mapdt (G := G1) (T := F1 ○ F2) f =
            mapdt (G := G1 ∘ G2) (T := F1 ○ F2) (kc6 g f).
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite (kdtfun_mapdt2
               (A := F2 A) (B := F2 B) (C := F2 C)
               (E := W) (G1 := G1) (G2 := G2) (T := F1)).
    fequal.
    ext [w1 t].
    rewrite (kc6_preincr _ _ _ f g w1).
    rewrite <- (kdtfun_mapdt2
               (A := A) (B := B) (C := C)
               (E := W) (G1 := G1) (G2 := G2) (T := F2)).
    unfold kc6, compose; cbn.
    compose near (mapdt (f ⦿ w1) t) on left.
    assert (Functor G1). { now inversion H5. }.
    rewrite (fun_map_map (F := G1)).
    reflexivity.
  Qed.

  Lemma kdtfun_comp_morph :
    forall (G1 G2 : Type -> Type) (H1 : Map G1)
      (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2)
      (H5 : Mult G2) (H6 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : W * A -> G1 B),
        mapdt (ϕ B ∘ f) = ϕ (F1 (F2 B)) ∘ (mapdt (T := F1 ○ F2) (G := G1) f).
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite <- kdtfun_morph.
    fequal.
    ext [w t].
    unfold compose; cbn.
    compose near t on right.
    rewrite <- kdtfun_morph.
    reflexivity.
  Qed.

  #[export] Instance DecoratedTraversableFunctor_compose:
    DecoratedTraversableFunctor W (F1 ○ F2) :=
    {| kdtfun_mapdt1 := kdtfun_comp_mapdt1;
      kdtfun_mapdt2 := kdtfun_comp_mapdt2;
      kdtfun_morph := kdtfun_comp_morph;
    |}.

End compose_functor_module.
*)
