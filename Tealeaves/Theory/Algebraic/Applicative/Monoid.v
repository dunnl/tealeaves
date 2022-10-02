From Tealeaves Require Import
  Classes.Algebraic.Applicative
  Classes.Monoid.

Import Applicative.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables ϕ G.

Section with_monoid.

  Context
    (G : Type -> Type)
    (M : Type)
    `{Applicative G}
    `{Monoid M}.

  #[export] Instance Monoid_op_applicative : Monoid_op (G M) :=
    fun m1 m2 => fmap G (uncurry monoid_op) (m1 ⊗ m2).

  #[export] Instance Monoid_unit_applicative : Monoid_unit (G M) :=
    pure G Ƶ.

  #[export] Instance Monoid_applicative : Monoid (G M).
  Proof.
    constructor.
    - intros. cbn. unfold_ops @Monoid_op_applicative.
      rewrite (app_mult_natural_l G).
      compose near (x ⊗ y ⊗ z) on left.
      rewrite (fun_fmap_fmap G).
      rewrite (app_mult_natural_r G).
      rewrite <- (app_assoc G).
      compose near (x ⊗ y ⊗ z) on right.
      rewrite (fun_fmap_fmap G).
      compose near (x ⊗ y ⊗ z) on right.
      rewrite (fun_fmap_fmap G).
      fequal. ext [[m1 m2] m3].
      cbn. simpl_monoid.
      reflexivity.
    - intros. unfold_ops @Monoid_op_applicative.
      unfold_ops @Monoid_unit_applicative.
      rewrite ap9.
      rewrite <- fmap_to_ap.
      rewrite ap3.
      rewrite ap5.
      change x with (id x) at 2. rewrite <- (fun_fmap_id G).
      fequal. ext m.
      cbv. now simpl_monoid.
    - intros. unfold_ops @Monoid_op_applicative.
      unfold_ops @Monoid_unit_applicative.
      rewrite ap9.
      rewrite ap2.
      rewrite <- fmap_to_ap.
      change x with (id x) at 2. rewrite <- (fun_fmap_id G).
      fequal. ext m.
      cbv. now simpl_monoid.
  Qed.

End with_monoid.

Section with_hom.

  Context
    `{Applicative G}
    (M1 M2 : Type)
    `{Monoid_Morphism M1 M2 ϕ}.

  #[export] Instance Monoid_hom_applicative :
    Monoid_Morphism (fmap G ϕ).
  Proof.
    inversion H7.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - unfold_ops @Monoid_unit_applicative.
      rewrite (app_pure_natural G).
      now rewrite monmor_unit.
    - intros. unfold_ops @Monoid_op_applicative.
      compose near (a1 ⊗ a2).
      rewrite (fun_fmap_fmap G).
      rewrite (app_mult_natural G).
      compose near (a1 ⊗ a2) on right.
      rewrite (fun_fmap_fmap G).
      fequal. ext [m1 m2].
      unfold compose. cbn. rewrite monmor_op.
      reflexivity.
  Qed.

End with_hom.
