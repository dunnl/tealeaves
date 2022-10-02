From Tealeaves Require Export
  Classes.Monoid
  Classes.Algebraic.Applicative
  Classes.Algebraic.Comonad
  Functors.Writer.
From Tealeaves Require
  Classes.Algebraic.Monad
  Classes.Kleisli.Decorated.Monad.

Export Algebraic.Monad (Return, ret).
Export Decorated.Monad (prepromote).

Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F.

Section operations.

  Context
    (W : Type)
    (T : Type -> Type)
    (F : Type -> Type).

  Class Binddt :=
    binddt :
      forall (G : Type -> Type) (A B : Type)
        `{Fmap G} `{Pure G} `{Mult G},
        (W * A -> G (T B)) -> F A -> G (F B).

End operations.

Definition kcompose_dtm
  {A B C}
  `{Fmap G1} `{Pure G1} `{Mult G1}
  `{Fmap G2} `{Pure G2} `{Mult G2}
  `{Binddt W T T} `{Monoid_op W} :
  (W * B -> G2 (T C)) ->
  (W * A -> G1 (T B)) ->
  (W * A -> G1 (G2 (T C))) :=
  fun g f '(w, a) => fmap G1 (binddt W T T G2 B C (prepromote w g)) (f (w, a)).

#[local] Infix "⋆dtm" := kcompose_dtm (at level 60) : tealeaves_scope.

Section class.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Return T}
    `{Binddt W T T}
    `{op: Monoid_op W} `{unit: Monoid_unit W}.

  Class Monad :=
    { kdtm_monoid :> Monoid W;
      kdtm_binddt0 : forall (A B : Type) `{Applicative G} (f : W * A -> G (T B)),
        binddt W T T G A B f ∘ ret T = f ∘ ret (W ×);
      kdtm_binddt1 : forall (A : Type),
        binddt W T T (fun A => A) A A (ret T ∘ extract (prod W)) = @id (T A);
      kdtm_binddt2 :
      forall (A B C : Type) `{Applicative G1} `{Applicative G2}
        (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
        fmap G1 (binddt W T T G2 B C g) ∘ binddt W T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (g ⋆dtm f);
      kdtm_morph : forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : W * A -> G1 (T B)),
          ϕ (T B) ∘ binddt W T T G1 A B f = binddt W T T G2 A B (ϕ (T B) ∘ f);
    }.

End class.

#[global] Arguments binddt {W}%type_scope {T}%function_scope (F)%function_scope
  {Binddt} G%function_scope {A B}%type_scope {H H0 H1} _%function_scope _.

Module Notations.

  Infix "⋆dtm" := kcompose_dtm (at level 60) : tealeaves_scope.

End Notations.

Section class.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Lemma kcompose_dtm_incr : forall
      `{Applicative G1} `{Applicative G2}
      `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)) (w : W),
      (g ∘ incr w) ⋆dtm (f ∘ incr w) = (g ⋆dtm f) ∘ incr w.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w' a]. unfold prepromote.
    reassociate ->. rewrite incr_incr.
    reflexivity.
  Qed.

  Lemma kcompose_dtm_prepromote : forall
      `{Applicative G1} `{Applicative G2}
      `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)) (w : W),
      (prepromote w g) ⋆dtm (prepromote w f) = prepromote w (g ⋆dtm f).
  Proof.
    intros. unfold prepromote. rewrite kcompose_dtm_incr.
    reflexivity.
  Qed.

  Lemma dtm_kleisli_identity1 : forall `{Applicative G} `(f : W * A -> G (T B)),
      kcompose_dtm (G2 := fun A => A) (ret T ∘ extract (W ×)) f = f.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. unfold prepromote.
    reassociate ->. rewrite (extract_incr).
    rewrite (kdtm_binddt1 W T).
    rewrite (fun_fmap_id G).
    reflexivity.
  Qed.

  Lemma dtm_kleisli_identity2 : forall `{Applicative G} `(g : W * A -> G (T B)),
      kcompose_dtm (G1 := fun A => A) g (ret T ∘ extract (W ×)) = g.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. unfold compose. cbn.
    compose near a.
    change (fmap (fun A => A) ?f) with f.
    rewrite (kdtm_binddt0 W T); auto.
    cbv. simpl_monoid.
    reflexivity.
  Qed.

  Lemma dtm_kleisli_assoc :
    forall `{Applicative G1} `{Applicative G2} `{Applicative G3}
      `(h : W * C -> G3 (T D)) `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)),
      kcompose_dtm (G1 := G1 ∘ G2) h (g ⋆dtm f) =
        kcompose_dtm (G2 := G2 ∘ G3) (h ⋆dtm g) f.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. cbn.
    unfold_ops @Fmap_compose.
    compose near (f (w, a)) on left.
    rewrite (fun_fmap_fmap G1).
    fequal.
    rewrite (kdtm_binddt2 W T); auto.
    fequal.
    rewrite kcompose_dtm_prepromote.
    reflexivity.
  Qed.

End class.
