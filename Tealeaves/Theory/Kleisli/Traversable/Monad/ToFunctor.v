From Tealeaves Require Export
  Classes.Kleisli.Traversable.Monad
  Theory.Kleisli.Traversable.Monad.Properties.

Import Monad.Notations.
Import Functor.Notations.
#[local] Generalizable Variables T.

(** * Kleisli traversable monad to functor *)
(******************************************************************************)

(** ** <<fmap>> operation *)
(******************************************************************************)
Module Operation.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Bindt T T}
      `{Return T}.

  #[export] Instance Fmap_Bindt : Fmap T :=
      fun (A B : Type) (f : A -> B) => bindt T (fun A => A) (ret T ∘ f).

  End with_kleisli.
End Operation.

Import Operation.

(** ** <<Functor>> instance *)
(******************************************************************************)
Module Instance.

  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Kleisli.Traversable.Monad.Monad T}.

    Lemma fmap_id : forall (A : Type),
        fmap T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Fmap_Bindt.
      change (?g ∘ id) with g.
      now rewrite (ktm_bindt1 T).
    Qed.

    Lemma fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Bindt.
      change (bindt T (fun A : Type => A) (ret T ∘ g))
        with (fmap (fun A => A) (bindt T (fun A => A) (ret T ∘ g))).
      rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A) (G2 := fun A => A));
        try typeclasses eauto.
      fequal. now rewrite Mult_compose_identity1.
      rewrite kcompose_tm_ret_I; auto.
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_fmap_id := fmap_id;
        fun_fmap_fmap := fmap_fmap;
      |}.

  End with_kleisli.

End Instance.
(** ** Other properties *)
(******************************************************************************)
Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Kleisli.Traversable.Monad.Monad T}.

  (** *** Composition between <<fmap>> and <<bindt>> *)
  (******************************************************************************)
  Lemma fmap_bindt : forall (G1 : Type -> Type) (A B C : Type) `{Applicative G1}
      (g : B -> C)
      (f : A -> G1 (T B)),
      fmap G1 (fmap T g) ∘ bindt T G1 f =
      bindt T G1 (fmap G1 (fmap T g) ∘ f).
  Proof.
    intros. unfold_ops @Fmap_Bindt.
    rewrite (ktm_bindt2 T _ _ _ (G1 := G1) (G2 := fun A => A)).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma bindt_fmap: forall (G2 : Type -> Type) (A B C : Type) `{Applicative G2}
      (g : B -> G2 (T C))
      (f : A -> B),
      bindt T G2 g ∘ fmap T f =
        bindt T G2 (g ∘ f).
  Proof.
    intros. unfold_ops @Fmap_Bindt.
      change (bindt T G2 g)
        with (fmap (fun A => A) (bindt T G2 g)).
      rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A) (G2 := G2)).
      fequal. now rewrite Mult_compose_identity2.
      now rewrite kcompose_tm_ret2.
  Qed.

End with_kleisli.
