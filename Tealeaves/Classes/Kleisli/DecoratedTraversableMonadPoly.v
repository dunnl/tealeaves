From Tealeaves Require Export
  Classes.Categorical.Monad (Return, ret)
  Classes.Categorical.Applicative
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Classes.Kleisli.DecoratedTraversableFunctorPoly
  Classes.Monoid
  Functors.List
  Functors.Writer
  Functors.List_Telescoping_General.

Import Applicative.Notations.
Import Monoid.Notations.
Import Product.Notations.
Import DecoratedTraversableCommIdemFunctor.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.


(** * Polymorphically Decorated Traversable Monads *)
(******************************************************************************)
(** T = type of newly inserted syntax
    U = type of syntax substituted into
    B1 = type of binders before substitution
    B2 = new type of binders after substitution
    A1 = type of variables before substitution
    A2 = new type of variables after substitution *)

(** ** Operation <<substitute>> *)
(******************************************************************************)
Class Substitute
  (T : Type -> Type -> Type)
  (U : Type -> Type -> Type) :=
  substitute:
    forall (B1 A1 B2 A2: Type)
      (G : Type -> Type)
      `{Map_G: Map G} `{Pure_G: Pure G} `{Mult_G: Mult G},
      (list B1 * B1 -> G B2) -> (* rename binders *)
      (list B1 * A1 -> G (T B2 A2)) -> (* insert subtrees *)
      U B1 A1 -> (* press button *)
      G (U B2 A2). (* receive bacon *)

#[global] Arguments substitute {T U}%function_scope {Substitute}
  {B1 A1 B2 A2}%type_scope
  {G}%function_scope {Map_G Pure_G Mult_G}
  (_ _)%function_scope _.

(*
Definition kcompose_rename
  {WA WB WC} :
  (list WB * WB -> WC) ->
  (list WA * WA -> WB) ->
  (list WA * WA -> WC) :=
  fun ρg ρf '(ctx, wa) => ρg (hmap ρf ctx, ρf (ctx, wa)).
 *)


(** ** Kleisli Composition *)
(******************************************************************************)
Definition kc_dtmp {T}
  `{Substitute T T}
  {G1 : Type -> Type}
  `{map_G1: Map G1} `{pure_G1: Pure G1} `{mult_G1: Mult G1}
  {G2 : Type -> Type}
  `{map_G2: Map G2} `{pure_G2: Pure G2} `{mult_G2: Mult G2}
  {B1 A1 B2 A2 B3 A3: Type}
  (ρ2: list B2 * B2 -> G2 B3) (* second op to rename binders *)
  (σ2: list B2 * A2 -> G2 (T B3 A3)) (* second op to insert terms *)
  (ρ1: list B1 * B1 -> G1 B2) (* first op to rename binders *)
  (σ1: list B1 * A1 -> G1 (T B2 A2)) (* first op to insert terms *)
  : list B1 * A1 -> (G1 ∘ G2) (T B3 A3) :=
  fun '(ctx, a) =>
    map (fun '(ctx2, u) => substitute (ρ2 ⦿ ctx2) (σ2 ⦿ ctx2) u)
        (pure pair
           <⋆> mapdt_ci (W := Z) ρ1 ctx
           <⋆> σ1 (ctx, a)).

(*
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
*)

(*
#[local] Infix "⋆ren" := kcompose_rename (at level 60) : tealeaves_scope.
#[local] Notation "| r1 || s1 | '⋆sub' | r2 || s2 |" := (kcompose_dtmp r1 s1 r2 s2) (r1 at level 0, s1 at level 0, r2 at level 0, s2 at level 0, at level 60) : tealeaves_scope.
 *)

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedTraversableMonadPoly
    (T: Type -> Type -> Type)
    `{forall W, Return (T W)}
    `{Substitute T T} :=
  { kdtmp_substitute0:
    forall {B1 B2 A1 A2: Type}
      `{Applicative G}
      (ρ: list B1 * B1 -> G B2)
      (σ: list B1 * A1 -> G (T B2 A2)),
      substitute ρ σ ∘ ret (T B1) A1 = σ ∘ ret (list B1 ×) A1;
    kdtmp_substitute1:
    forall {B A: Type},
      substitute (G := fun A => A)
        (extract (W := (list B ×)))
        (ret (T B) A ∘ extract (W := (list B ×)))
      = @id (T B A);
    kdtmp_substitute2:
    forall {B1 B2 B3: Type}
      {A1 A2 A3: Type}
      `{Applicative G1}
      `{Applicative G2}
      (ρ1: list B1 * B1 -> G1 B2)
      (ρ2: list B2 * B2 -> G2 B3)
      (σ1: list B1 * A1 -> G1 (T B2 A2))
      (σ2: list B2 * A2 -> G2 (T B3 A3)),
      (forall p: list B1 * B1, IdempotentCenter G1 B2 (ρ1 p)) ->
      map (F := G1) (substitute (G := G2) ρ2 σ2) ∘
        substitute (G := G1) (T := T) (U := T) ρ1 σ1 =
        substitute (T := T) (U := T) (G := G1 ∘ G2)
          (ρ2 ⋆3_ci ρ1) (kc_dtmp ρ2 σ2 ρ1 σ1);
    kdtmp_morphism:
    forall {B1 A1 B2 A2: Type} {G1 G2: Type -> Type}
      `{morph: ApplicativeMorphism G1 G2 ϕ}
      (ρ: list B1 * B1 -> G1 B2)
      (σ: list B1 * A1 -> G1 (T B2 A2)),
      ϕ (T B2 A2) ∘ substitute ρ σ =
        substitute (ϕ B2 ∘ ρ) (ϕ (T B2 A2) ∘ σ);
  }.


From  Tealeaves Require
  Classes.Kleisli.TraversableFunctor2
  Classes.Kleisli.DecoratedTraversableFunctorPoly.

(** * Derived Instances *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Import TraversableFunctor2.
Import DecoratedTraversableFunctorPoly.

Module DerivedOperations.
  Section decorated_traversable_monad_poly_derived_operations.

  Context
    `{T: Type -> Type -> Type}
    `{DecoratedTraversableMonadPoly T}.

  #[export] Instance MapdtPoly_Substitute: MapdtPoly T :=
    fun B1 B2 A1 A2 G Gmap Gpure Gmult ρ σ =>
      substitute ρ (map (ret (T B2) A2) ∘ σ).

  #[export] Instance TraversePoly_Substitute: TraversePoly T :=
    fun A1 A2 B1 B2 G Gmap Gpure Gmult ρ σ =>
      substitute
        (ρ ∘ extract (W := prod (list B1)))
        (map (ret (T B2) A2) ∘ σ ∘ extract (W := prod (list B1))).

  End decorated_traversable_monad_poly_derived_operations.
End DerivedOperations.


Module DerivedInstances.
  Section decorated_traversable_monad_poly_derived_instances.

    Import DerivedOperations.

  Context
    `{T: Type -> Type -> Type}
    `{DecoratedTraversableMonadPoly T}.

  #[export] Instance DTFP: DecoratedTraversableFunctorPoly T.
  Proof.
    constructor; intros.
    - unfold_ops @MapdtPoly_Substitute.
      unfold_ops @Map_I.
      apply kdtmp_substitute1.
    - unfold_ops @MapdtPoly_Substitute.
      rewrite kdtmp_substitute2.
      2: { now inversion H2. }
      fequal.
      unfold kc_dtmp, kc_dtfp.
      ext [ctx a]. unfold compose.
      cbn.
      (* LHS *)
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite map_ap.
      (* RHS *)
      rewrite map_ap.
      rewrite app_pure_natural.
      unfold_ops @Map_compose.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      fequal.
      fequal.
      fequal.
      ext ctx2 a2.
      unfold compose, precompose, preincr.
      compose near a2.
      rewrite kdtmp_substitute0.
      unfold compose, incr.
      unfold_ops @Return_Writer.
      rewrite monoid_id_l.
      reflexivity.
    - unfold_ops @MapdtPoly_Substitute.
      rewrite kdtmp_morphism.
      reassociate <- on left.
      rewrite <- natural.
      reflexivity.
  Qed.

  End decorated_traversable_monad_poly_derived_instances.
End DerivedInstances.


(*
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
kdtmp_substitute1  Proof.

    intros.
    ext [wa' a]. cbn.
    fequal.
    rewrite hmap_app.
    rewrite <- (preincr_preincr _).
    rewrite <- (preincr_preincr _).
    reflexivity.
  Qed.

End compose_laws.
*)
