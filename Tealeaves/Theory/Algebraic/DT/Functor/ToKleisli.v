From Tealeaves Require Export
  Classes.Kleisli.DT.Functor
  Classes.Algebraic.DT.Functor
  Theory.Algebraic.Traversable.Functor.ToKleisli
  Theory.Algebraic.Decorated.Functor.ToKleisli
  Theory.Algebraic.Decorated.Functor.Setlike
  Theory.Algebraic.Decorated.Monad.Setlike.
  (*
  Theory.Algebraic.Traversable.Functor.Listable
*)

Import Product.Notations.
Import Kleisli.DT.Functor.Notations.
Import Decorated.Functor.Setlike.Notations.

#[local] Generalizable Variables F G ϕ E A B C.

(** * Kleisli presentation of decorated-traversable functors *)
(******************************************************************************)

(** ** Derived operation <<fmapdt>> *)
(******************************************************************************)
Module Operation.
  Section with_functor.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Fmap T} `{Decorate E T} `{Dist T}.

  #[export] Instance Fmapdt_alg : Fmapdt E T :=
      fun (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
        `(f : E * A -> G B) => (dist T G ∘ fmap T f ∘ dec T : T A -> G (T B)).

  End with_functor.
End Operation.

(** ** Proofs of the axioms for <<fmapdt>> *)
(******************************************************************************)
Module Instance.

  Section with_functor.

    Import Operation.

    Context
      (T : Type -> Type)
      `{Algebraic.DT.Functor.DecoratedTraversableFunctor E T}.

    Theorem fmapdt_id : forall (A : Type), fmapdt T (fun A => A) (extract _) = @id (T A).
    Proof.
      introv. unfold_ops @Fmapdt_alg.
      reassociate -> on left.
      rewrite (dfun_dec_extract E T). now rewrite (dist_unit T).
    Qed.

    Theorem fmapdt_fmapdt : forall `{Applicative G1} `{Applicative G2}
                              `(g : E * B -> G2 C) `(f : E * A -> G1 B),
        fmap G1 (fmapdt T G2 g) ∘ fmapdt T G1 f = fmapdt T (G1 ∘ G2) (g ⋆dt f).
    Proof.
      intros. unfold transparent tcs. unfold kcompose_dt.
      rewrite <- (fun_fmap_fmap G1).
      repeat reassociate <- on left.
      change (?f ∘ fmap G1 (dec T) ∘ dist T G1 ∘ ?g) with
        (f ∘ (fmap G1 (dec T) ∘ dist T G1) ∘ g).
      rewrite <- (dtfun_compat E T B).
      rewrite <- (fun_fmap_fmap G1).
      repeat reassociate <- on left.
      change (?f ∘ fmap G1 (fmap T g) ∘ dist T G1 ∘ ?h) with
        (f ∘ (fmap G1 (fmap T g) ∘ dist T G1) ∘ h).
      change (fmap G1 (fmap T g)) with (fmap (G1 ∘ T) g).
      rewrite (natural (ϕ := @dist T _ G1 _ _ _)).
      rewrite (dist_linear T).
      repeat reassociate <- on left.
      rewrite <- (fun_fmap_fmap T).
      unfold_ops @Fmap_compose.
      change (?f ∘ fmap T (fmap G1 g) ∘ ?x ∘ ?h) with
        (f ∘ (fmap T (fmap G1 g) ∘ x) ∘ h).
      rewrite (fun_fmap_fmap T). reassociate -> near (fmap T f).
      rewrite <- (natural (ϕ := @dec E T _)).
      repeat reassociate ->.
      repeat fequal. rewrite (dfun_dec_dec E T).
      reassociate <-. unfold_ops @Fmap_compose.
      now rewrite (fun_fmap_fmap T).
    Qed.

    Theorem fmapdt_fmapdt_morphism : forall `{ApplicativeMorphism G1 G2 ϕ} `(f : E * A -> G1 B),
        fmapdt T G2 (ϕ B ∘ f) = ϕ (T B) ∘ fmapdt T G1 f.
    Proof.
      intros. unfold transparent tcs.
      do 2 reassociate <-.
      rewrite <- (fun_fmap_fmap T).
      rewrite <- (dist_morph T).
      reflexivity.
    Qed.

    #[local] Instance: Kleisli.DT.Functor.DecoratedTraversableFunctor E T :=
      {| kdtfun_fmapdt1 := @fmapdt_id;
        kdtfun_fmapdt2 := @fmapdt_fmapdt;
        kdtfun_morph := @fmapdt_fmapdt_morphism;
      |}.

  End with_functor.

End Instance.
