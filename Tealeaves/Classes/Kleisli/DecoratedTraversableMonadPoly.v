From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.Applicative
  (* Classes.Categorical.Comonad *)
  Functors.ListHistory.

Import Monoid.Notations.
Import Product.Notations.
Import List.ListNotations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.

Class Substitute
  (T : Type -> Type -> Type)
  (F : Type -> Type -> Type) :=
  substitute :
    forall (WA WB : Type) (G : Type -> Type)
      `{Map G} `{Pure G} `{Mult G}
      (A B : Type),
      (list WA * WA -> WB) ->
      (list WA * A -> G (T WB B))
      -> F WA A -> G (F WB B).

#[local] Arguments substitute {T F}%function_scope {Substitute}
  {WA WB}%type_scope {G}%function_scope {H H0 H1} {A B}%type_scope
  (_ _)%function_scope _.


Definition kcompose_rename
  {WA WB WC} :
  (list WB * WB -> WC) ->
  (list WA * WA -> WB) ->
  (list WA * WA -> WC) :=
  fun ρg ρf '(ctx, wa) => ρg (hmap ρf ctx, ρf (ctx, wa)).

Definition kcompose_dtmp
  {A B C WA WB WC}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2}
  `{Substitute T T} :
  (list WB * WB -> WC) ->
  (list WB * B -> G2 (T WC C)) ->
  (list WA * WA -> WB) ->
  (list WA * A -> G1 (T WB B)) ->
  (list WA * A -> G1 (G2 (T WC C))) :=
  fun ρg g ρf f '(wa, a) =>
    map (F := G1) (substitute (ρg ⦿ hmap ρf wa) (g ⦿ hmap ρf wa)) (f (wa, a)).


#[local] Infix "⋆ren" := kcompose_rename (at level 60) : tealeaves_scope.
#[local] Notation "| r1 || s1 | '⋆sub' | r2 || s2 |" := (kcompose_dtmp r1 s1 r2 s2) (r1 at level 0, s1 at level 0, r2 at level 0, s2 at level 0, at level 60) : tealeaves_scope.

Class DecoratedTraversableMonadPoly
    (T : Type -> Type -> Type)
    `{forall W, Return (T W)}
    `{Substitute T T} :=
  { kdtm_binddt0 :
    forall (WA WB A B : Type) `{Applicative G}
      (ρ : list WA * WA -> WB) (f : list WA * A -> G (T WB B)),
      substitute ρ f ∘ ret (T WA) A = f ∘ ret (list WA ×) A;
    kdtm_substitute1 :
    forall (W A : Type),
      substitute (G := fun A => A) (extract (W := (list W ×))) (ret (T W) A ∘ extract (W := (list W ×))) = @id (T W A);
    kdtm_substitute2 :
    forall (A B C : Type)
      `{Applicative G1} `{Applicative G2}
      (WA WB WC : Type)
      (ρg : list WB * WB -> WC)
      (g : list WB * B -> G2 (T WC C))
      (ρf : list WA * WA -> WB)
      (f : list WA * A -> G1 (T WB B)),
      map (F := G1) (substitute ρg g) ∘ substitute ρf f =
        substitute (G := G1 ∘ G2) (ρg ⋆ren ρf) (| ρg || g | ⋆sub | ρf || f |);
    kdtm_morph :
    forall (WA WB : Type) (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ} (ρ : list WA * WA -> WB) `(f : list WA * A -> G1 (T WB B)),
      ϕ (T WB B) ∘ substitute ρ f = substitute ρ (ϕ (T WB B) ∘ f);
  }.

Section compose_laws.

  #[local] Generalizable All Variables.

  Lemma kcompose_rename_preincr :
    forall {WA WB WC}
      (ρg : list WB * WB -> WC)
      (ρf : list WA * WA -> WB)
      (wa : list WA),
      preincr (kcompose_rename ρg ρf) wa =
        kcompose_rename (preincr ρg (hmap ρf wa)) (preincr ρf wa).
  Proof.
    intros. ext [ctx a].
    unfold kcompose_rename. cbn.
    rewrite hmap_app.
    reflexivity.
  Qed.

  Lemma kcompose_dtm_preincr :
    forall {A B C WA WB WC : Type}
      `{Map G1} `{Pure G1} `{Mult G1}
      `{Map G2} `{Pure G2} `{Mult G2}
      `{Substitute T T}
      (ρg : list WB * WB -> WC)
      (g : list WB * B -> G2 (T WC C))
      (ρf : list WA * WA -> WB)
      (f : list WA * A -> G1 (T WB B))
      (wa : list WA),
      (kcompose_dtmp ρg g ρf f) ⦿ wa =
        kcompose_dtmp (ρg ⦿ hmap ρf wa) (g  ⦿ hmap ρf wa) (ρf ⦿ wa) (f ⦿ wa).
  Proof.

    intros.
    ext [wa' a]. cbn.
    fequal.
    rewrite hmap_app.
    rewrite <- (preincr_preincr _).
    rewrite <- (preincr_preincr _).
    reflexivity.
  Qed.

End compose_laws.
