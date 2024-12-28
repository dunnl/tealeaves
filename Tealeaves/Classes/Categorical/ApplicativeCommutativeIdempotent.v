From Tealeaves Require Export
  Classes.Categorical.Applicative.

Import Applicative.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ F G A B C.

Class ApplicativeCommutativeIdempotent (G : Type -> Type)
    `{Map G} `{Pure G} `{Mult G} :=
  { appci_applicative :> Applicative G;
    appci_idempotent : forall (A : Type) (x : G A),
      x ⊗ x = map (fun a => (a, a)) x;
    appci_commutative : forall (A B : Type) (x : G A) (y: G B),
      x ⊗ y = map (fun '(x, y) => (y, x)) (y ⊗ x);
  }.


Lemma ap_ci: forall `{ApplicativeCommutativeIdempotent G} {A B: Type} (f: G (A -> B)) (a: G A),
    f <⋆> a = (map evalAt a) <⋆> f.
Proof.
  intros.
  unfold ap.
  inversion H2.
  rewrite appci_commutative.
  compose near (a ⊗ f).
  rewrite (fun_map_map).
  rewrite (app_mult_natural_l G).
  compose near (a ⊗ f) on right.
  rewrite (fun_map_map).
  fequal.
  ext [x y].
  cbn. reflexivity.
Qed.

Lemma ap_ci2: forall `{ApplicativeCommutativeIdempotent G} {A B C: Type} (f: G (A -> B -> C)) (a: G A) (b: G B),
    f <⋆> a <⋆> b = (map flip f) <⋆> b <⋆> a.
Proof.
  intros.
  unfold ap.
  (* left *)
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a ⊗ b).
  rewrite (fun_map_map).
  (* right *)
  rewrite (app_mult_natural_l G).
  compose near (map flip f ⊗ b ⊗ a).
  rewrite (fun_map_map).
  rewrite (app_mult_natural_l G).
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ b ⊗ a).
  rewrite (fun_map_map).
  rewrite <- (app_assoc_inv G _ _ _ f b a).
  compose near (f ⊗ (b ⊗ a)) on right.
  rewrite (fun_map_map).

  inversion H2.
  rewrite (appci_commutative _ _ b a).

  rewrite (app_mult_natural_r G).
  compose near (f ⊗ (a ⊗ b)) on right.
  rewrite fun_map_map.
  rewrite <- (app_assoc _ _ _ f a b).
  compose near (f ⊗ a ⊗ b) on right.
  rewrite (fun_map_map).
  fequal.
  ext [[xf xa] xb].
  reflexivity.
Qed.

Definition dup {A:Type} := fun (a: A) => (a, a).

Definition double_input {A B: Type} (f: A -> A -> B): A -> B :=
  uncurry f ∘ dup.

Lemma ap_cidup: forall `{ApplicativeCommutativeIdempotent G} {A B: Type} (f: G (A -> A -> B)) (a: G A),
    f <⋆> a <⋆> a = (map double_input f) <⋆> a.
Proof.
  intros.
  unfold ap.
  inversion H2.
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a ⊗ a).
  rewrite (fun_map_map).
  rewrite <- (app_assoc_inv G).
  rewrite appci_idempotent.
  rewrite (app_mult_natural_r G).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  (* rhs *)
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  fequal.
  ext [x y].
  cbn. reflexivity.
Qed.

Definition penguin {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G}:
  forall (a: G A) (b: G B), G B :=
  fun a b => (map (F := G) (const (@id B)) a) <⋆> b.

Infix "|⋆>" := penguin (at level 50).
