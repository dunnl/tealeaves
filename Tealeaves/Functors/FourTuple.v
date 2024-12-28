From Tealeaves Require Import
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Kleisli.TraversableFunctor.

Definition FourTuple (A: Type) : Type := A * (A * (A * A)).

Definition mkFour {A: Type} : A -> A -> A -> A -> FourTuple A :=
  (fun x1 x2 x3 x4 => (x1, (x2, (x3, x4)))).

#[export] Instance Traverse_FourTuple: Traverse FourTuple.
Proof.
  intros G GMap GPure GMult A B f [a1 [a2 [a3 a4]]].
  exact (pure mkFour <⋆> f a1 <⋆> f a2 <⋆> f a3 <⋆> f a4).
Defined.

#[export] Instance TraversableFunctor_FourTuple: TraversableFunctor FourTuple.
Proof.
  constructor.
  - intros.
    ext [a1 [a2 [a3 a4]]].
    reflexivity.
  - intros.
    ext [a1 [a2 [a3 a4]]].
    unfold compose, kc2.
    cbn.
    (* left *)
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    (* right *)
    unfold compose at 5 6 7 8.
    change (fun a => G1 (G2 a)) with (G1 ∘ G2).
    unfold_ops @Pure_compose.
    rewrite (ap_compose2 G2 G1 _ (map g (f a1))).
    rewrite app_pure_natural.
    rewrite (ap_compose2 G2 G1 _ (map g (f a2))).
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite (ap_compose2 G2 G1 _ (map g (f a3))).
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite (ap_compose2 G2 G1 _ (map g (f a4))).
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.

    rewrite <- (ap_map).
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- (ap_map).
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- (ap_map).
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- (ap_map).
    rewrite app_pure_natural.
    reflexivity.
  - intros.
    ext [a1 [a2 [a3 a4]]].
    unfold compose.
    cbn.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    reflexivity.
Qed.

Fixpoint square {A:Type} (p: A * A): FourTuple A :=
  match p with
  | pair a1 a2 => (a1, (a1, (a1, a2)))
  end.

Lemma square_commute {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! ApplicativeCommutativeIdempotent G}
  (f: A  -> G B) (p: A * A):
  map (F := G) square (traverse (T := fun A => A * A) f p) =
    traverse (T := FourTuple) f (square p).
Proof.
  induction p.
  cbn.
  rewrite map_ap.
  rewrite map_ap.
  rewrite app_pure_natural.

  rewrite ap_cidup.
  rewrite map_ap.
  rewrite app_pure_natural.
  rewrite ap_cidup.
  rewrite app_pure_natural.
  reflexivity.

(*
  unfold ap.
  rewrite (app_mult_natural_l G).
  compose near (pure (compose square (A := B) ∘ pair) ⊗ f a ⊗ f b).
  rewrite fun_map_map.

  rewrite (app_mult_natural_l G).
  compose near
    ((map apply (map apply (pure mkFour ⊗ f a) ⊗ f a) ⊗ f a ⊗ f b)).
  rewrite fun_map_map.

  rewrite (app_mult_natural_l G).
  rewrite (app_mult_natural_l G).
  compose near ((map apply (pure mkFour ⊗ f a) ⊗ f a ⊗ f a ⊗ f b)).
  rewrite fun_map_map.

  rewrite (app_mult_natural_l G).
  rewrite (app_mult_natural_l G).
  rewrite (app_mult_natural_l G).
  compose near (pure (mkFour (A := B)) ⊗ f a ⊗ f a ⊗ f a ⊗ f b).
  rewrite (fun_map_map).
  *)
Qed.
