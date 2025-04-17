From Tealeaves Require Import
  Classes.Categorical.TraversableFunctor2
  Classes.Categorical.TraversableFunctor.

#[local] Generalizable Variables T G A.

Import Functor2.Notations.

(** ** Single-Argument Traversable Functor Instances *)
(**********************************************************************)
Module ToMono.

  Section mono.

    Context
      `{TraversableFunctor2 T}.

    #[export] Instance Dist2_1 {B}: ApplicativeDist (T B) :=
      fun G _ _ _ A => dist2 (G := G) ∘ map2 pure id.

    #[export] Instance Dist2_2 {A}: ApplicativeDist (fun B => T B A) :=
      fun G _ _ _ A => dist2 (G := G) ∘ map2 id pure.

    #[local] Arguments map2 (F)%function_scope {Map2} {B1 A1 B2 A2}%type_scope
      (g f)%function_scope _.

    #[local] Arguments pure F%function_scope {Pure} {A}%type_scope _.

    #[export] Instance TraversableFunctor_Dist2_1 {B}:
      TraversableFunctor (T B)
        (H := Map2_1) (H0 := Dist2_1).
    Proof.
      constructor; intros; unfold_ops @Dist2_1.
      - typeclasses eauto.
      - constructor.
        + apply Functor_compose; typeclasses eauto.
        + apply Functor_compose; typeclasses eauto.
        + (* dist_natural *)
          intros.
          unfold_ops @Map_compose.
          reassociate -> on right.
          unfold_compose_in_compose.
          rewrite (fun2_map2_map21 (F := T)).
          change (id ∘ ?f) with f.
          change (pure G (A := ?A)) with (id ∘ pure G (A := A)) at 2.
          rewrite <- (fun2_map2_map22 (F := T)).
          reassociate <- on right.
          replace (map2 T (@id (G B)) (map f))
            with (map2 (T ○21 G) (@id B) f).
          2:{ unfold_ops @Map21_compose.
              rewrite fun_map_id.
              reflexivity. }
          rewrite <- (natural2 (F := T ○21 G) (@id B) f
                       (Natural2 := dist2_natural)
                       (ϕ := fun B A => dist2 (T := T) (G := G))).
          reflexivity.
      - (* dist_morph *)
        reassociate -> on left.
        rewrite (fun2_map2_map21 (F := T)).
        change (id ∘ ?f) with f.
        change (pure G2 (A := ?A)) with (id ∘ pure G2 (A := A)) at 1.
        rewrite <- (fun2_map2_map22 (F := T)).
        reassociate <- on left.

        reassociate <- on right.
        rewrite <- dist2_morph.
        reassociate -> on left.
        reassociate -> on right.
        fequal.
        rewrite fun2_map2_map22.
        rewrite fun2_map_map.
        change (?f ∘ id) with f.
        change (id ∘ ?f) with f.
        fequal.
        rewrite appmor_pure_pf.
        reflexivity.
      - (* dist unit *)
        rewrite dist2_unit.
        unfold_ops @Pure_I.
        rewrite fun2_map_id.
        reflexivity.
      - (* dist linear *)
        rewrite dist2_linear.
        reassociate <- on right.
        unfold_ops @Pure_compose.
        change (?f ○ ?g) with (f ∘ g).
        rewrite <- (fun_map_map (F := G1)).
        reassociate -> near (dist2 (G := G1)).
        change (map (map2 T ?f ?g)) with (map2 (G1 ○12 T) f g).
        setoid_rewrite (natural2 (Natural2 := dist2_natural) (G := G1 ○12 T)).
        reassociate -> on left.
        unfold_ops @Map21_compose.
        reassociate -> on right.
        reassociate -> on right.
        rewrite (fun2_map_map (F := T)).
        rewrite fun_map_id.
        rewrite (natural (ϕ := @pure G1 _)).
        reflexivity.
    Qed.


    Section commute.

      Context
        `{Applicative G}
        {B1 B2: Type}
        {ρ: B1 -> B2}
        {A: Type}.

      Context
        `{! TraversableFunctor2 T}.

      Lemma dist2_natural_rw `{f: A1 -> A2} (t: T (G B1) (G A1)):
        dist2 (G := G) (map2 T (map (F := G) ρ) (map f) t) =
          map (F := G) (map2 T ρ f) (dist2 (G := G) t).
      Proof.
        compose near t.
        rewrite <- map2_comp12_rw.
        rewrite (natural2 (ϕ := @dist2 T _ G _ _ _) ρ f).
        reflexivity.
      Qed.

      Lemma Dist2_1_natural2: forall (t: T B1 (G A)),
          dist (T B2) G (map (F := fun B => T B (G A)) ρ t) =
            map (F := G) (map (F := fun B => T B A) ρ) (dist (T B1) G t).
      Proof.
        intros.
        unfold_ops @Map2_2.
        unfold_ops @Dist2_1.
        unfold compose.
        rewrite <- (dist2_natural_rw (f := (@id A))).
        compose near t.
        rewrite fun2_map_map.
        rewrite fun2_map_map.
        rewrite (natural (ϕ := @pure G _)).
        unfold_ops @Map_I.
        rewrite fun_map_id.
        reflexivity.
      Qed.

    End commute.

  End mono.

End ToMono.
