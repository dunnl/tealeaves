From Tealeaves Require Export
  Classes.Kleisli.DT.Functor.

Import Data.Strength.Notations.
Import DT.Functor.Notations.
Import Product.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables W T A B C.

(** * Kleisli decorated traversable functor to functor *)
(******************************************************************************)

(** ** Operation *)
(******************************************************************************)
Module Operation.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Fmapdt W T}.

    #[export] Instance Fmap_Fmapdt: Fmap T := fun A B f => fmapdt T (fun A => A) (f ∘ extract (W ×)).

  End with_kleisli.
End Operation.

(** ** Instance *)
(******************************************************************************)
Module Instance.
  Section with_kleisli.

    Import Operation.

    Context
      (T : Type -> Type)
        `{DecoratedTraversableFunctor W T}.

    Lemma fmap_id_T :
      forall A : Type, fmap T (@id A) = @id (T A).
    Proof.
      unfold_ops @Fmap_Fmapdt.
      intros. now rewrite (kdtfun_fmapdt1 W T).
    Qed.

    Lemma kcompose_dt_00 :
      forall (A B C : Type) (f : A -> B) (g : B -> C),
        kcompose_dt (G1 := fun A => A) (G2 := fun A => A)
          (g ∘ extract (prod W)) (f ∘ extract (prod W)) = g ∘ f ∘ extract (prod W).
    Proof.
      intros. unfold kcompose_dt. unfold strength.
      unfold_ops @Fmap_I. rewrite <- (fmap_to_cobind (W ×)).
      now ext [w a].
    Qed.

    Lemma fmap_fmap_T :
       forall (A B C : Type) (f : A -> B) (g : B -> C), fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      unfold_ops @Fmap_Fmapdt.
      intros.
      change_left (fmap (fun A => A) (fmapdt T (fun A0 : Type => A0) (g ∘ extract (prod W))) ∘
                     fmapdt T (fun A0 : Type => A0) (f ∘ extract (prod W))).
      rewrite (kdtfun_fmapdt2 W T (G1 := fun A => A) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
      now rewrite kcompose_dt_00.
    Qed.

    #[export] Instance: Functor T :=
      {| fun_fmap_id := fmap_id_T;
         fun_fmap_fmap := fmap_fmap_T;
      |}.

  End with_kleisli.
End Instance.
