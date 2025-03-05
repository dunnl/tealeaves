From Tealeaves Require Export
  Functors.Compose
  Classes.Functor2
  Classes.Categorical.Applicative
  Classes.Categorical.TraversableFunctor.

Import Functor2.Notations.

#[local] Generalizable Variable T G ϕ A B.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.

(** * Traversable Functors of Two Arguments *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Class ApplicativeDist2 (T: Type -> Type -> Type) :=
  dist2: forall (G: Type -> Type)
          `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G},
      T ○21 G ⇒2 G ○12 T.

#[global] Arguments dist2 {T}%function_scope {ApplicativeDist2}
  {G}%function_scope {Map_G Pure_G Mult_G} {B A}%type_scope.


#[local] Arguments dist2 T%function_scope {ApplicativeDist2}
  G%function_scope {Map_G Pure_G Mult_G} {B A}%type_scope.


(** ** Typeclass *)
(******************************************************************************)
Class TraversableFunctor2
  (T: Type -> Type -> Type)
  `{Map2_F: Map2 T}
  `{dist2_F: ApplicativeDist2 T} :=
  { trav2_functor :> Functor2 T;
    dist2_natural :> forall `{Applicative G},
        @Natural2 (T ○21 G) _ (G ○12 T) _ (@dist2 T dist2_F G _ _ _);
    dist2_morph: forall `{ApplicativeMorphism G1 G2 ϕ},
      `(dist2 T G2 ∘ map2 (ϕ B) (ϕ A) = ϕ (T B A) ∘ dist2 T G1);
    dist2_unit:
    `(dist2 T (fun A => A) = id (A := T B A));
    dist2_linear: forall `{Applicative G1} `{Applicative G2},
      `(dist2 T (G1 ∘ G2) = map G1 (dist2 T G2) ∘
                              dist2 T G1 (B := G2 B) (A := G2 A));
  }.

(** ** Single-Argument Traversable Functor Instances *)
(******************************************************************************)
Section composition_with_functor.

  Context
    `{TraversableFunctor2 T}.

  #[export] Instance Dist2_1 {B}: ApplicativeDist (T B) :=
    fun G _ _ _ A => dist2 T G ∘ map2 pure id.

  #[export] Instance Dist2_2 {A}: ApplicativeDist (fun B => T B A) :=
    fun G _ _ _ A => dist2 T G ∘ map2 id pure.

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
        replace (map2 T (@id (G B)) (map G f))
          with (map2 (T ○21 G) (@id B) f).
        2:{ unfold_ops @Map21_compose.
            rewrite fun_map_id.
            reflexivity. }
        rewrite <- (natural2 (F := T ○21 G) (@id B) f
                     (Natural2 := dist2_natural)
                     (ϕ := fun B A => dist2 T G)).
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
      reassociate -> near (dist2 T G1).
      change (map G1 (map2 T ?f ?g)) with (map2 (G1 ○12 T) f g).
      setoid_rewrite (natural2 (Natural2 := dist2_natural) (G := G1 ○12 T)).
      reassociate -> on left.
      unfold_ops @Map21_compose.
      reassociate -> on right.
      reassociate -> on right.
      rewrite (fun2_map_map (F := T)).
      rewrite fun_map_id.
      Search pure "Nat".
      rewrite (natural (ϕ := @pure G1 _)).
      reflexivity.
  Qed.

End composition_with_functor.

(** ** Other rules for <<pure>> *)
(******************************************************************************)
Section purity_law.

  Context
    `{TraversableFunctor2 T}.

  (*
  Corollary map_purity_1: forall `{Applicative G},
      `(dist2 T G ∘ map2 T ((pure G) = pure G (A := T A)).
  Proof.
    intros. rewrite (dist_morph (ϕ := @pure G _)).
    now rewrite (dist_unit).
  Qed.

  Corollary map_purity_2 :
    forall `{Applicative G1} `{Applicative G2} `(f: A -> G1 B),
      dist T (G2 ∘ G1) ∘ map T (pure G2 ∘ f) = pure G2 ∘ dist T G1 ∘ map T f.
  Proof.
    intros. rewrite <- (fun_map_map).
    reassociate <-. rewrite dist_linear.
    reassociate -> near (map T (pure G2)).
    rewrite map_purity_1.
    fequal. ext t. unfold compose.
    now rewrite app_pure_natural.
  Qed.
   *)

End purity_law.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'δ2'" := dist2: tealeaves_scope.
End Notations.
