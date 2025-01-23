From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedTraversableMonad.

#[local] Generalizable Variables F T U W.

Import Monoid.Notations.
Import Product.Notations.
Import DecoratedTraversableFunctor.Notations.

(** * Composition of Two <<DTF>> Instances *)
(******************************************************************************)

(** ** Composition of <<mapdt>> Operations *)
(******************************************************************************)
#[export] Instance Mapdt_compose `{op: Monoid_op W}
  `{Mapdt W F1} `{Mapdt W F2}: Mapdt W (F1 ○ F2) :=
  fun G map pure mult A B f =>
    mapdt (T := F1) (G := G) (fun '(w1, t) => mapdt (T := F2) (f ⦿ w1) t).

(** ** <<DecoratedTraversableFunctor>> Laws *)
(******************************************************************************)
Section compose_functors.

  Context
    `{Monoid W}.

  Context
    `{Mapdt W F1} `{Mapdt W F2}
    `{! DecoratedTraversableFunctor W F1}
    `{! DecoratedTraversableFunctor W F2}.

  Lemma kdtf_comp_mapdt1 : forall A : Type,
      mapdt (T := F1 ○ F2) (@extract (W ×) _ A) = id.
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite <- kdtf_mapdt1.
    fequal.
    ext [w t].
    rewrite extract_preincr.
    rewrite kdtf_mapdt1.
    reflexivity.
  Qed.

  Lemma kdtf_comp_mapdt2 :
    forall (G1 : Type -> Type) (H1 : Map G1)
      (H2 : Pure G1) (H3 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H5 : Map G2)
        (H6 : Pure G2) (H7 : Mult G2),
        Applicative G2 ->
        forall (A B C : Type) (g : W * B -> G2 C) (f : W * A -> G1 B),
          map (F := G1) (mapdt (G := G2) (T := F1 ○ F2) g)
              ∘ mapdt (G := G1) (T := F1 ○ F2) f =
            mapdt (G := G1 ∘ G2) (T := F1 ○ F2) (kc3 g f).
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite (kdtf_mapdt2
               (A := F2 A) (B := F2 B) (C := F2 C)
               (E := W) (G1 := G1) (G2 := G2) (T := F1)).
    fequal.
    ext [w1 t].
    rewrite (kc3_preincr _ _ _ f g w1).
    rewrite <- (kdtf_mapdt2
               (A := A) (B := B) (C := C)
               (E := W) (G1 := G1) (G2 := G2) (T := F2)).
    unfold kc3, compose; cbn.
    compose near (mapdt (f ⦿ w1) t) on left.
    assert (Functor G1). { now inversion H5. }
    rewrite (fun_map_map (F := G1)).
    reflexivity.
  Qed.

  Lemma kdtf_comp_morph :
    forall (G1 G2 : Type -> Type) (H1 : Map G1)
      (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2)
      (H5 : Mult G2) (H6 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : W * A -> G1 B),
        ϕ (F1 (F2 B)) ∘ (mapdt (T := F1 ○ F2) (G := G1) f)
          = mapdt (ϕ B ∘ f).
  Proof.
    intros.
    unfold_ops @Mapdt_compose.
    rewrite kdtf_morph.
    fequal.
    ext [w t].
    unfold compose; cbn.
    compose near t on left.
    rewrite kdtf_morph.
    reflexivity.
  Qed.

  (** ** <<DecoratedTraversableFunctor>> Instance *)
  (******************************************************************************)
  #[export] Instance DecoratedTraversableFunctor_compose:
    DecoratedTraversableFunctor W (F1 ○ F2) :=
    {| kdtf_mapdt1 := kdtf_comp_mapdt1;
      kdtf_mapdt2 := kdtf_comp_mapdt2;
      kdtf_morph := kdtf_comp_morph;
    |}.

End compose_functors.

(** * Composition of a <<DTF>> with a <<DTM>> Right Module *)
(******************************************************************************)

(** ** Composition of <<mapdt>> with <<binddt>> *)
(******************************************************************************)
#[export] Instance Mapdt_Binddt_compose
 `{op: Monoid_op W}
 `{Mapdt_F: Mapdt W F}
 `{Binddt_U: Binddt W T U}:
  Binddt W T (F ∘ U) :=
  fun G map pure mult A B f =>
    mapdt (T := F) (G := G)
      (fun '(w1, t) => binddt (U := U) (f ⦿ w1) t).

(** ** <<DecoratedTraversableRightModule>> Laws *)
(******************************************************************************)
Section compose_functor_module.

  Context
    `{Monoid W}.

  Context
    `{Mapdt_WF: Mapdt W F}
    `{Return_T: Return T}
    `{Binddt_WTU: Binddt W T U}
    `{Binddt_WTT: Binddt W T T}
    `{! DecoratedTraversableFunctor W F}
    `{! DecoratedTraversableRightPreModule W T U}.

  Lemma kdtm_binddt1_compose :
    forall A : Type,
      binddt (T := T) (U := F ∘ U) (ret (T := T) ∘ extract) = @id (F (U A)).
  Proof.
    intros.
    unfold_ops @Mapdt_Binddt_compose.
    assert (cut:
        (fun '(w1, t) =>
           binddt (G := fun A => A) (A := A) (B := A)
             (U := U) ((ret (T := T) ∘ extract) ⦿ w1) t)
        = @extract (prod W) _  (U A)).
    { ext [w t].
      rewrite extract_preincr2.
      rewrite (kdtm_binddt1 (U := U) (T := T)).
      reflexivity. }
    replace
      (fun '((w1, t) : W * U A) =>
         binddt (G := fun A => A) (A := A) (B := A)
           (U := U) ((ret (T := T) ∘ extract) ⦿ w1) t)
      with (@extract (prod W) _  (U A)).
    rewrite kdtf_mapdt1.
    reflexivity.
  Qed.

  Lemma kdtm_binddt2_compose :
    forall (G1 : Type -> Type) (H : Map G1)
      (H0 : Pure G1) (H1 : Mult G1),
      Applicative G1 ->
      forall (G2 : Type -> Type) (H3 : Map G2)
        (H4 : Pure G2) (H5 : Mult G2),
        Applicative G2 ->
        forall (B C : Type) (g : W * B -> G2 (T C))
          (A : Type) (f : W * A -> G1 (T B)),
          map (binddt (T := T) (U := F ∘ U) g) ∘
            binddt (T := T) (U := F ∘ U) f =
            binddt (G := G1 ∘ G2) (T := T) (U := F ∘ U) (kc7 G1 G2 g f).
  Proof.
    intros.
    unfold_ops @Mapdt_Binddt_compose.
    change ((F ∘ U) ?X) with (F (U X)).
    rewrite (kdtf_mapdt2 (T := F)).
    fequal. ext [w t].
    change ((G1 ∘ G2) ?X) with (G1 (G2 X)).
    rewrite <- (kc7_preincr).
    rewrite <- kdtm_binddt2.
    rewrite kc3_spec.
    reflexivity.
  Qed.

  Lemma kdtm_morph_compose:
    forall (G1 G2 : Type -> Type) (H : Map G1)
      (H0 : Mult G1) (H1 : Pure G1) (H2 : Map G2)
      (H3 : Mult G2) (H4 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : W * A -> G1 (T B)),
        ϕ (F (U B)) ∘ binddt (U := F ∘ U) f =
          binddt (U := F ∘ U) (ϕ (T B) ∘ f).
  Proof.
    introv Happl. intros.
    assert (Applicative G1) by now inversion Happl.
    assert (Applicative G2) by now inversion Happl.
    unfold_ops @Mapdt_Binddt_compose.
    rewrite (kdtf_morph (A := U A) (B := U B) (ϕ := ϕ) (T := F)).
    fequal.
    ext [w' t'].
    unfold compose; compose near t' on left.
    rewrite (kdtm_morph G1 G2 (U := U)).
    reflexivity.
  Qed.

  (** ** <<DecoratedTraversableRightModule>> Instances *)
  (******************************************************************************)
  #[export] Instance DecoratedTraversableRightPreModule_compose:
    DecoratedTraversableRightPreModule W T (F ○ U) :=
    {| kdtm_binddt1 := kdtm_binddt1_compose;
      kdtm_binddt2 := kdtm_binddt2_compose;
      kdtm_morph := kdtm_morph_compose;
    |}.

End compose_functor_module.
