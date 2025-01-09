From Tealeaves Require Export
  Functors.Batch
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.DecoratedShapelyFunctor
  Adapters.KleisliToCoalgebraic.DecoratedTraversableFunctor
  Functors.Environment
  Theory.TraversableFunctor.

Import Product.Notations.
Import Monoid.Notations.
Import Batch.Notations.
Import List.ListNotations.
Import Subset.Notations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables F M E T G A B C ϕ.

(** * Mapdt Poly *)
(******************************************************************************)
Class MapdtPoly (T: Type -> Type -> Type) :=
    mapdtp:
      forall (A1 A2 B1 B2: Type)
        (G : Type -> Type)
        `{Gmap: Map G} `{Gpure: Pure G} `{Gmult: Mult G},
        (list B1 * B1 -> G B2) ->
        (list B1 * A1 -> G A2) ->
        T B1 A1 ->
        G (T B2 A2).

Arguments mapdtp {T}%function_scope {MapdtPoly} {A1 A2 B1 B2}%type_scope
  {G}%function_scope {Gmap Gpure Gmult} (_ _)%function_scope _.

Section decorated_traversable_monad_poly_mapdt.

  Context
    `{T: Type -> Type -> Type}
    `{DecoratedTraversableMonadPoly T}.

  #[export] Instance Mapdtp_Substitute: MapdtPoly T :=
    fun A1 A2 B1 B2 G Gmap Gpure Gmult ρ σ =>
        substitute ρ (map (F := G) (ret (T := T B2)) ∘ σ).
End decorated_traversable_monad_poly_mapdt.

(** * The [Batch] idiom *)
(******************************************************************************)
Inductive Batch2 (A1 A2 B1 B2 C : Type) : Type :=
| Done : C -> Batch2 A1 A2 B1 B2 C
| StepA : Batch2 A1 A2 B1 B2 (A2 -> C) -> A1 -> Batch2 A1 A2 B1 B2 C
| StepB : Batch2 A1 A2 B1 B2 (B2 -> C) -> B1 -> Batch2 A1 A2 B1 B2 C.

#[global] Arguments Done  {A1 A2 B1 B2 C}%type_scope _.
#[global] Arguments StepA {A1 A2 B1 B2 C}%type_scope _ _.
#[global] Arguments StepB {A1 A2 B1 B2 C}%type_scope _ _.

(** ** Functor instance *)
(******************************************************************************)

(** *** Map operations *)
(******************************************************************************)
Fixpoint map_Batch2 {A1 A2 B1 B2: Type} {C1 C2: Type} (f : C1 -> C2)
  (b : Batch2 A1 A2 B1 B2 C1): Batch2 A1 A2 B1 B2 C2 :=
  match b with
  | Done c => Done (f c)
  | StepA mk a => StepA (map_Batch2 (compose f) mk) a
  | StepB mk b => StepB (map_Batch2 (compose f) mk) b
  end.

#[export] Instance Map_Batch2 {A1 A2 B1 B2: Type}: Map (Batch2 A1 A2 B1 B2) :=
  @map_Batch2 A1 A2 B1 B2.

(** ** Applicative instance *)
(******************************************************************************)

(** *** Operations *)
(******************************************************************************)
#[export] Instance Pure_Batch2 {A1 A2 B1 B2}: Pure (@Batch2 A1 A2 B1 B2) :=
  @Done A1 A2 B1 B2.

#[program] Fixpoint mult_Batch {A1 A2 B1 B2} {C1 C2: Type}
  (b1 : Batch2 A1 A2 B1 B2 C1)
  (b2 : Batch2 A1 A2 B1 B2 C2):
  Batch2 A1 A2 B1 B2 (C1 * C2) :=
    match b2 with
    | Done c2 => map (F := Batch2 A1 A2 B1 B2) (fun (c1 : C1) => (c1, c2)) b1
    | StepA mk a =>
        StepA
          (map (F := Batch2 A1 A2 B1 B2) strength_arrow (mult_Batch b1 mk))
          a
    | StepB mk b =>
        StepB
          (map (F := Batch2 A1 A2 B1 B2) strength_arrow (mult_Batch b1 mk))
          b
    end.

#[export] Instance Mult_Batch2 {A1 A2 B1 B2: Type}:
  Mult (Batch2 A1 A2 B1 B2) :=
  fun C1 C2 => uncurry (@mult_Batch A1 A2 B1 B2 C1 C2).

About runBatch.

(** ** The <<runBatch>> operation *)
(******************************************************************************)
Fixpoint runBatch2 {A1 A2 B1 B2: Type}
  (F : Type -> Type) `{Map F} `{Mult F} `{Pure F}
  (ϕB : B1 -> F B2)
  (ϕA : A1 -> F A2)
  {C : Type} (b : Batch2 A1 A2 B1 B2 C) : F C :=
  match b with
  | Done c => pure c
  | StepA mk a => runBatch2 F ϕB ϕA (C := A2 -> C) mk <⋆> ϕA a
  | StepB mk b => runBatch2 F ϕB ϕA (C := B2 -> C) mk <⋆> ϕB b
  end.

(** * "Element of" relations *)
(******************************************************************************)
Section element_of.

  Context
    `{T: Type -> Type -> Type}
      `{DecoratedTraversableMonadPoly T}.

  Definition binder_of {A B: Type}:
    T B A -> list B * B -> Prop :=
    mapdtp (B2 := False) (A2 := False)
      (G := const (subset (list B * B)))
      (Gpure := Pure_const) (Gmult := Mult_const)
      (@eq (list B * B))
      (const (const False)).

  Definition leaf_of {A B: Type}:
    T B A -> list B * A -> Prop :=
    mapdtp (B2 := False) (A2 := False)
      (G := const (subset (list B * A)))
      (Gpure := Pure_const) (Gmult := Mult_const)
      (const (const False))
      (@eq (list B * A)).

End element_of.

(** * Factoring through runBatch *)
(******************************************************************************)
Section decorated_traversable_monad_poly_toBatch.

  Context
    `{T: Type -> Type -> Type}
      `{DecoratedTraversableMonadPoly T}.

  Definition toBatchA {A1 A2 B1 B2: Type}:
      A1 -> Batch2 A1 A2 B1 B2 A2 :=
    fun a1 => StepA (Done (C := A2 -> A2) id) a1.

  Definition toBatchB {A1 A2 B1 B2: Type}:
      B1 -> Batch2 A1 A2 B1 B2 B2 :=
    fun b1 => StepB (Done (C := B2 -> B2) id) b1.

  Definition toBatchp {A1 A2 B1 B2: Type}:
      T B1 A1 ->
      Batch2
        (list B1 * A1) A2
        (list B1 * B1) B2
        (T B2 A2) :=
    mapdtp (G := Batch2 (list B1 * A1) A2 (list B1 * B1) B2) toBatchB toBatchA.

  Instance ApplicativeMorphism_runBatch2
    `{Applicative G}
    {A1 A2 B1 B2: Type}
    {ϕB : B1 -> G B2}
    {ϕA : A1 -> G A2}:
    ApplicativeMorphism (Batch2 A1 A2 B1 B2) G
      (fun C => runBatch2 G ϕB ϕA (C := C)).
  Proof.
    constructor.
    - admit.
    - assumption.
    - intros C1 C2 f b.
      generalize dependent C2.
      induction b; intros.
      + cbn.
        rewrite app_pure_natural.
        reflexivity.
      + cbn.
        rewrite map_ap.
        rewrite IHb.
        reflexivity.
      + cbn.
        rewrite map_ap.
        rewrite IHb.
        reflexivity.
    - intros C c.
      reflexivity.
    - intros C1 C2 b1 b2.
      cbn.
      admit.
  Admitted.

  Lemma mapdtp_through_toBatchp:
      forall (B1 A1 B2 A2: Type)
        (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
        `{! Applicative G}
        (ϕB: list B1 * B1 -> G B2)
        (ϕA: list B1 * A1 -> G A2),
        mapdtp ϕB ϕA =
          runBatch2 (C := T B2 A2) G ϕB ϕA ∘
            toBatchp (A1 := A1) (A2 := A2) (B1 := B1) (B2 := B2).
  Proof.
    intros.
    unfold toBatchp.
    unfold mapdtp.
    unfold Mapdtp_Substitute.
    rewrite (kdtmp_morph _ _ _ _ _ _
                 (ϕ := fun C => runBatch2 G ϕB ϕA (C := C))
                 (morph := ApplicativeMorphism_runBatch2)).
    fequal.
    - ext [w b]. cbn.
      rewrite ap1.
      reflexivity.
    - ext [w a]. cbn.
      unfold compose.
      rewrite map_to_ap.
      reflexivity.
  Qed.

  (** ** Pointwise reasoning corollaries of factoring through runBatch *)
  (******************************************************************************)
  Section pointwise_corollaries.

    Context
      (A1 A2 B1 B2: Type)
        (ρ1: list B1 * B1 -> B2)
        (σ1: list B1 * A1 -> A2)
        (ρ2: list B1 * B1 -> B2)
        (σ2: list B1 * A1 -> A2)
        (t: T B1 A1).

    Lemma mapdtp_pw:
      (forall (b_occ: list B1 * B1),
          binder_of t b_occ -> ρ1 b_occ = ρ2 b_occ) ->
      (forall (v_occ: list B1 * A1),
          leaf_of t v_occ -> σ1 v_occ = σ2 v_occ) ->
      mapdtp (G := fun A => A) ρ1 σ1 t =
        mapdtp (G := fun A => A) ρ2 σ2 t.
    Proof.
      introv Hpwb Hpwv.
      unfold binder_of in *.
      unfold leaf_of in *.
      rewrite mapdtp_through_toBatchp in *.
      rewrite mapdtp_through_toBatchp in *.
      all: try typeclasses eauto.
      unfold compose in *.
      assert (Hpwb': forall b_occ : list B1 * B1,
         @runBatch2 (list B1 * A1) A2 (list B1 * B1) B2 (@const Type Type (list B1 * B1 -> Prop))
           (@Map_const (list B1 * B1 -> Prop)) (@Mult_const (list B1 * B1 -> Prop) (@Monoid_op_subset (list B1 * B1)))
           (@Pure_const (list B1 * B1 -> Prop) (@Monoid_unit_subset (list B1 * B1))) (@eq (list B1 * B1))
           (@const (list B1 * A1) (list B1 * B1 -> Prop) (@const (list B1 * B1) Prop False)) (T B2 A2)
           (@toBatchp A1 A2 B1 B2 t) b_occ -> ρ1 b_occ = ρ2 b_occ).
      admit. clear Hpwb.
      assert (Hpwv': forall v_occ : list B1 * A1,
         @runBatch2 (list B1 * A1) A2 (list B1 * B1) B2 (@const Type Type (list B1 * A1 -> Prop))
           (@Map_const (list B1 * A1 -> Prop)) (@Mult_const (list B1 * A1 -> Prop) (@Monoid_op_subset (list B1 * A1)))
           (@Pure_const (list B1 * A1 -> Prop) (@Monoid_unit_subset (list B1 * A1)))
           (@const (list B1 * B1) (list B1 * A1 -> Prop) (@const (list B1 * A1) Prop False)) (@eq (list B1 * A1))
           (T B2 A2) (@toBatchp A1 A2 B1 B2 t) v_occ -> σ1 v_occ = σ2 v_occ).
      admit. clear Hpwv.
      induction (@toBatchp A1 A2 B1 B2 t).
      - cbn. reflexivity.
      - cbn in *.
        rewrite IHb.
        2:{ intros. apply Hpwb'.
            unfold monoid_op in *.
            unfold Monoid_op_subset in *.
            rewrite subset_in_add.
            tauto. }
        2:{ intros. apply Hpwv'.
            unfold monoid_op in *.
            unfold Monoid_op_subset in *.
            rewrite subset_in_add.
            tauto. }
        fequal. apply Hpwv'.
        now right.
      - cbn in *.
        rewrite IHb.
        2:{ intros. apply Hpwb'.
            unfold monoid_op in *.
            unfold Monoid_op_subset in *.
            rewrite subset_in_add.
            tauto. }
        2:{ intros. apply Hpwv'.
            unfold monoid_op in *.
            unfold Monoid_op_subset in *.
            rewrite subset_in_add.
            tauto. }
        fequal. apply Hpwb'.
        now right.
    Admitted.

  End pointwise_corollaries.

End decorated_traversable_monad_poly_toBatch.
