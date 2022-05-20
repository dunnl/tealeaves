From Tealeaves Require Export
     Classes.Functor
     Classes.Applicative
     Classes.ListableFunctor
     Functors.Constant
     Functors.Batch.

Import List.ListNotations.
#[local] Open Scope list_scope.

Import Functor.Notations.
Import Batch.Notations.
Import SetlikeFunctor.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

(** * Traversable functors *)
(******************************************************************************)
Section TraversableFunctor_operation.

  Context
    (F : Type -> Type).

  Class Dist :=
    dist : forall (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}, F ○ G ⇒ G ○ F.

End TraversableFunctor_operation.

Section TraversableFunctor.

  Context
    (F : Type -> Type)
    `{Functor F}
    `{Dist F}.

  Class TraversableFunctor :=
    { trav_functor :> Functor F;
      dist_natural : forall `{Applicative G} `(f : A -> B),
          fmap (G ∘ F) f ∘ dist F G A = dist F G B ∘ fmap (F ∘ G) f;
      dist_morph : forall `{ApplicativeMorphism G1 G2 ϕ} A,
          dist F G2 A ∘ fmap F (ϕ A) = ϕ (F A) ∘ dist F G1 A;
      dist_unit :
        `(dist F (fun A => A) A = id);
      dist_linear : forall `{Applicative G1} `{Applicative G2},
          `(dist F (G1 ∘ G2) A = fmap G1 (dist F G2 A) ∘ dist F G1 (G2 A));
    }.

End TraversableFunctor.

#[local] Notation "'δ'" := (dist).

(* Mark the type argument implicit *)
Arguments dist F%function_scope {Dist} G%function_scope {H H0 H1} {A}%type_scope.

(** ** Distribution-respecting natural transformations *)
(******************************************************************************)
Section TraversableMorphism.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  Class TraversableMorphism (ϕ : T ⇒ U) :=
    { trvmor_trv_F : TraversableFunctor T;
      trvmor_trv_G : TraversableFunctor U;
      trvmor_nat :> Natural ϕ;
      trvmor_hom : forall `{Applicative G},
          `(fmap G (ϕ A) ∘ dist T G = dist U G ∘ ϕ (G A));
    }.

End TraversableMorphism.

(** * Monoid structure of traversable functors *)
(******************************************************************************)

(** ** The identity functor is traversable *)
(******************************************************************************)
Instance Dist_I : Dist (fun A => A) := fun F fmap mult pure A a => a.

#[program] Instance Traversable_I : TraversableFunctor (fun A => A).

Next Obligation.
  unfold transparent tcs. ext a.
  symmetry. now rewrite (fun_fmap_id G1).
Qed.

(** ** Traversable functors are closed under composition *)
(******************************************************************************)
Section TraversableFunctor_compose.

  Context
    `{TraversableFunctor T}
    `{TraversableFunctor U}.

  #[global] Instance Dist_compose : Dist (T ∘ U) :=
    fun G map mult pure A =>
      dist T G ∘ fmap T (dist U G (A := A)).

  Lemma dist_unit_compose : forall A,
      dist (T ∘ U) (fun A => A) = @id (T (U A)).
  Proof.
    intros. unfold transparent tcs.
    rewrite (dist_unit T).
    rewrite (dist_unit U).
    now rewrite (fun_fmap_id T).
  Qed.

  Lemma dist_natural_compose : forall `{Applicative G} `(f : X -> Y),
      fmap (G ∘ (T ∘ U)) f ∘ dist (T ∘ U) G = dist (T ∘ U) G ∘ fmap ((T ∘ U) ∘ G) f.
  Proof.
    intros. unfold transparent tcs.
    change_left (fmap (G ∘ T) (fmap U f) ∘ dist T G ∘ fmap T (dist U G)).
    rewrite (dist_natural T (fmap U f)).
    unfold_ops @Fmap_compose.
    reassociate -> on left.
    reassociate -> on right.
    rewrite (fun_fmap_fmap T).
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f).
    now rewrite <- (dist_natural U (G := G) f).
  Qed.

  Lemma dist_morph_compose : forall `{ApplicativeMorphism G1 G2 ϕ} (A : Type),
      dist (T ∘ U) G2 ∘ fmap (T ∘ U) (ϕ A) = ϕ (T (U A)) ∘ dist (T ∘ U) G1.
  Proof.
    intros. unfold transparent tcs.
    reassociate -> on left.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    rewrite (dist_morph U).
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on left.
    now rewrite (dist_morph T).
  Qed.

  Lemma dist_linear_compose : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (T ∘ U) (G1 ∘ G2) = fmap G1 (dist (T ∘ U) G2) ∘ dist (T ∘ U) G1 (A := G2 A).
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap G1).
    reassociate -> on right;
      change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f);
      reassociate <- near (fmap (G1 ∘ T) (dist U G2)).
    rewrite (dist_natural T (dist U G2) (G := G1)).
    reassociate -> on right;
      unfold_ops @Fmap_compose;
      rewrite (fun_fmap_fmap T).
    #[local] Set Keyed Unification.
    rewrite (dist_linear U).
    rewrite (dist_linear T).
    #[local] Unset Keyed Unification.
    reflexivity.
  Qed.

  #[global] Instance Traversable_compose : TraversableFunctor (T ∘ U) :=
    {| dist_natural := @dist_natural_compose;
       dist_morph := @dist_morph_compose;
       dist_unit := @dist_unit_compose;
       dist_linear := @dist_linear_compose;
    |}.

End TraversableFunctor_compose.

(** * Basic properties of traversable functors *)
(******************************************************************************)

(** ** Purity laws *)
(******************************************************************************)
Section pure_as_applicative_transformation.

  Context
    `{Applicative G}.

  Lemma pure_appmor_1 : forall A B (f : A -> B) (t : A),
      pure G (fmap (fun A : Type => A) f t) = fmap G f (pure G t).
  Proof.
    intros. now rewrite (app_pure_natural G).
  Qed.

  Lemma pure_appmor_2 : forall (A : Type) (a : A),
      pure G (pure (fun A => A) a) = pure G a.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma pure_appmor_3 : forall (A B : Type) (a : A) (b : B),
      pure G (mult (fun A => A) (a, b)) = mult G (pure G a, pure G b).
  Proof.
    unfold transparent tcs. intros. now rewrite (app_mult_pure G).
  Qed.

  #[global] Instance ApplicativeMorphism_pure :
    ApplicativeMorphism (fun A => A) G (@pure G _) :=
    {| appmor_natural := pure_appmor_1;
       appmor_pure := pure_appmor_2;
       appmor_mult := pure_appmor_3;
    |}.

End pure_as_applicative_transformation.

Section purity_law.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Corollary fmap_purity_1 `{Applicative G} : forall A,
    dist T G ∘ fmap T (pure G) (A := A) = pure G.
  Proof.
    intros. rewrite (dist_morph T (ϕ := @pure G _)).
    now rewrite (dist_unit T).
  Qed.

  Corollary fmap_purity_2 `{Applicative G1} `{Applicative G2} : forall `(f : A -> G1 B),
      dist T (G2 ∘ G1) ∘ fmap T (pure G2 ∘ f) = pure G2 ∘ dist T G1 ∘ fmap T f.
  Proof.
    intros. rewrite <- (fun_fmap_fmap T).
    reassociate <-. rewrite (dist_linear T).
    reassociate -> near (fmap T (pure G2)).
    rewrite fmap_purity_1.
    fequal. ext t. unfold compose.
    now rewrite (app_pure_natural G2).
  Qed.

End purity_law.

(** * Kleisi presentation of traversable functors *)
(******************************************************************************)
Definition traverse (T : Type -> Type) (G : Type -> Type)
           `{Fmap T} `{Dist T}
           `{Fmap G} `{Pure G} `{Mult G}
           `(f : A -> G B) : T A -> G (T B)
  := dist T G ∘ fmap T f.

(* We don't give a dedicated name or notation to the composition
   operation <<g ⋆ f = fmap F g ∘ f>> because it is trivial and one
   wants to avoid making up too many notations. *)

(** ** Specification for <<fmap>>  *)
(******************************************************************************)
Section TraversableFunctor_fmap.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Corollary fmap_to_traverse : forall `(f : A -> B),
      fmap T f = traverse T (fun A => A) f.
  Proof.
    intros. unfold traverse. ext t.
    now rewrite (dist_unit T).
  Qed.

End TraversableFunctor_fmap.

(** ** Kleisi presentation of traversable functors *)
(******************************************************************************)
Section TraversableFunctor_kleisli.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Theorem traverse_id : forall (A : Type),
      traverse T (fun A => A) id = @id (T A).
  Proof.
    intros. unfold traverse. ext t. rewrite (dist_unit T).
    now rewrite (fun_fmap_id T).
  Qed.

  Theorem traverse_id_purity : forall `{Applicative G} (A : Type),
      traverse T G (pure G) = @pure G _ (T A).
  Proof.
    intros. unfold traverse. ext t. now rewrite fmap_purity_1.
  Qed.

  Lemma traverse_traverse `{Applicative G2} `{Applicative G1} :
    forall `(g : B -> G2 C) `(f : A -> G1 B),
      fmap G1 (traverse T G2 g) ∘ traverse T G1 f = traverse T (G1 ∘ G2) (fmap G1 g ∘ f).
  Proof.
    introv. unfold traverse.
    rewrite (dist_linear T).
    repeat reassociate <-.
    rewrite <- (fun_fmap_fmap T).
    repeat reassociate <-.
    reassociate -> near (fmap T (fmap G1 g)).
    change (fmap T (fmap G1 g)) with (fmap (T ∘ G1) g).
    rewrite <- (dist_natural T g (G := G1)).
    unfold_ops @Fmap_compose.
    reassociate <-.
    unfold_compose_in_compose.
    now rewrite (fun_fmap_fmap G1).
  Qed.

  Lemma traverse_morphism `{morph : ApplicativeMorphism G1 G2 ϕ} : forall `(f : A -> G1 B),
      ϕ (T B) ∘ traverse T G1 f = traverse T G2 (ϕ B ∘ f).
  Proof.
    intros. unfold traverse. reassociate <-.
    inversion morph.
    rewrite <- (dist_morph T).
    reassociate ->.
    now rewrite (fun_fmap_fmap T).
  Qed.

End TraversableFunctor_kleisli.

(** ** Purity laws *)
(******************************************************************************)
Section traverse_purity_law.

  Context
    `{TraversableFunctor T}
    `{Applicative G1}
    `{Applicative G2}.

  Corollary traverse_purity : forall A B (f : A -> G1 B),
      traverse T (G2 ∘ G1) (pure G2 ∘ f) = pure G2 ∘ traverse T G1 f.
  Proof.
    intros. unfold traverse.
    now rewrite (fmap_purity_2 T (G2 := G2) f).
  Qed.

End traverse_purity_law.

(** ** Composition with sub-operations  *)
(******************************************************************************)
Section TraversableFunctor_composition.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G}.

  Corollary fmap_traverse : forall `(g : B -> C) `(f : A -> G B),
      fmap G (fmap T g) ∘ traverse T G f = traverse T G (fmap G g ∘ f).
  Proof.
    intros. unfold traverse. ext t.
    repeat reassociate <-.
    change (fmap G (fmap T g)) with (fmap (G ∘ T) g).
    rewrite (dist_natural T g (G := G)).
    reassociate ->.
    unfold_ops @Fmap_compose.
    now rewrite (fun_fmap_fmap T).
  Qed.

  Corollary traverse_fmap : forall `(g : B -> G C) `(f : A -> B),
      traverse T G g ∘ fmap T f = traverse T G (g ∘ f).
  Proof.
    intros. unfold traverse. ext t.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

End TraversableFunctor_composition.

(** * Characterization of distribution w.r.t. (F ◻ G) *)
(******************************************************************************)
Section traversable_product.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G1}
    `{Applicative G2}.

  Variables
    (A B : Type)
    (f : A -> G1 B) (g : A -> G2 B).

  Lemma dist_combine1 : forall (t : T A),
    pi1 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G1 f t.
  Proof.
    intros. pose (ApplicativeMorphism_pi1 G1 G2).
    compose near t on left.
    now rewrite (traverse_morphism T).
  Qed.

  Lemma dist_combine2 : forall (t : T A),
    pi2 (traverse T (G1 ◻ G2) (f <◻> g) t) = traverse T G2 g t.
  Proof.
    intros. pose (ApplicativeMorphism_pi2 G1 G2).
    compose near t on left.
    now rewrite (traverse_morphism T).
  Qed.

  Theorem dist_combine : forall (t : T A),
    dist T (G1 ◻ G2) (fmap T (f <◻> g) t) =
    product (traverse T G1 f t) (traverse T G2 g t).
  Proof.
    intros. compose near t on left.
    erewrite <- (dist_combine1).
    erewrite <- (dist_combine2).
    now rewrite <- product_eta.
  Qed.

  Theorem traverse_combine :
    traverse T (G1 ◻ G2) (f <◻> g) = (traverse T G1 f) <◻> (traverse T G2 g).
  Proof.
    intros. unfold traverse.
    ext t. unfold compose.
    now rewrite dist_combine.
  Qed.

End traversable_product.

(** * Operations involving constant applicative functors *)
(******************************************************************************)
(** To distributive over constant applicative functors, i.e. to fold
    over monoidal values, we can use the <<Const>> applicative
    functor. Unfortunately this tends to clutter operations with
    <<unconst>> operations which get in the way of convenient
    rewriting. We provide a lighter-weight alternative in this section
    and some specifications proving equivalence with the <<Const>>
    versions. *)
Section TraversableFunctor_const.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  (* TODO Move me *)
  Definition exfalso {X : Type} : False -> X.
    intuition.
  Defined.

  (* TODO Move me *)
  Existing Instance Fmap_const.
  Existing Instance Pure_const.
  Existing Instance Mult_const.
  Existing Instance Applicative_const.
  Existing Instance ApplicativeMorphism_unconst.
  Existing Instance ApplicativeMorphism_monoid_hom.

  (** *** Distribution over <<const>> is agnostic about the tag. *)
  (** Distribution over a constant applicative functor is agnostic
      about the type argument ("tag") to the constant functor. On
      paper it is easy to ignore this, but in Coq this must be
      proved. Observe this equality is ill-typed if [Const] is used instead. *)
  (******************************************************************************)
  Lemma dist_const1 : forall (X : Type) `{Monoid M},
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) X)
      =
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) False).
  Proof.
    intros. symmetry. change (?f = ?g) with (f = g ∘ (@id (T M))).
    rewrite <- (fun_fmap_id T).
    change (@id M) with
        (fmap (A := False) (B:=X) (const M) exfalso).
    change (fmap T (fmap (const M) ?f))
      with (fmap (T ∘ const M) f).
    rewrite <- (dist_natural T (B := X) (A := False) (G := const M)).
    reflexivity.
  Qed.

  Lemma dist_const2 : forall (X Y : Type) `{Monoid M},
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) X)
      =
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) Y).
  Proof.
    intros. now rewrite (dist_const1 X), (dist_const1 Y).
  Qed.

  (** *** Distribution over [Const] vs <<const>> *)
  (******************************************************************************)
  Theorem traversable_const_spec (tag : Type) `{Monoid M} :
    unconst ∘ @dist T _ (Const M)
            (Fmap_Const)
            (Pure_Const)
            (Mult_Const) tag ∘ fmap T (mkConst)
    = @dist T _ (const M)
            (Fmap_const)
            (Pure_const)
            (Mult_const) tag.
  Proof.
    intros. rewrite <- (dist_morph T (ϕ := @unconst _)).
    reassociate -> on left. rewrite (fun_fmap_fmap T).
    change (unconst ∘ mkConst) with (@id M).
    now rewrite (fun_fmap_id T).
  Qed.

End TraversableFunctor_const.

(** ** The [tolist] operation *)
(** We only define this operation and prove it forms a natural
transformation. This does not immediately give a [ListableFunctor]
instance until we prove the shapeliness property in another section
below. *)
(******************************************************************************)
(* set <<tag := False>> to emphasize this type is arbitrary *)
#[global] Instance Tolist_Traversable `{Fmap T} `{Dist T} : Tolist T :=
  fun A => unconst ∘ dist T (Const (list A)) ∘
                fmap T (mkConst (tag := False) ∘ ret list (A := A)).

Instance Natural_tolist_Traversable
         `{TraversableFunctor T} : Natural (@tolist T Tolist_Traversable).
Proof.
  constructor; try typeclasses eauto.
  intros. unfold_ops @Tolist_Traversable.
  repeat reassociate <-.
  rewrite (mapConst_2 (fmap list f)).
  repeat reassociate -> on left;
    reassociate <- near (mapConst (fmap list f)).
  rewrite <- (dist_morph T).
  repeat reassociate ->.
  repeat rewrite (fun_fmap_fmap T).
  reflexivity.
Qed.

(** ** Specifications for <<tolist>> and <<foldMap>> *)
(******************************************************************************)
Section TraversableFunctor_fold_spec.

  Context
    (T : Type -> Type)
    `{Monoid M}
    `{TraversableFunctor T}.

  Existing Instance Fmap_const.
  Existing Instance Pure_const.
  Existing Instance Mult_const.
  Existing Instance Applicative_const.
  Existing Instance ApplicativeMorphism_unconst.
  Existing Instance ApplicativeMorphism_monoid_hom.

  (** *** Specification for <<Tolist_Traversable>> *)
  (******************************************************************************)
  Theorem traversable_tolist_spec {A : Type} (tag : Type) :
    @tolist T Tolist_Traversable A
    = @traverse T (const (list A)) _ _
            (Fmap_const)
            (Pure_const)
            (Mult_const) A tag (ret list).
  Proof.
    intros. unfold tolist, Tolist_Traversable, traverse.
    rewrite <- (fun_fmap_fmap T). reassociate <- on left.
    rewrite (traversable_const_spec T (M := list A) False).
    now rewrite (dist_const1 T tag).
  Qed.

  (** *** Specification for folding over traversables *)
  (******************************************************************************)
  Theorem traversable_fold_spec (tag : Type) `{Monoid M} :
    @fold T Tolist_Traversable M _ _
    = @dist T _ (const M)
            (Fmap_const)
            (Pure_const)
            (Mult_const) tag.
  Proof.
    unfold fold. rewrite (traversable_tolist_spec tag). unfold traverse.
    reassociate <- on left.
    change (@List.fold M _ _) with (const (@List.fold M _ _) (T tag)).
    rewrite <- (dist_morph T (ϕ := const (@List.fold M _ _))).
    reassociate -> on left.
    rewrite (fun_fmap_fmap T).
    replace (const List.fold tag ∘ ret list) with (@id M).
    - now rewrite (fun_fmap_id T).
    - ext m. cbn. now simpl_monoid.
  Qed.

  Theorem traversable_foldMap_spec (tag : Type) `{Monoid M} `{f : A -> M} :
    @foldMap T _ Tolist_Traversable A M _ _  f =
    @traverse T (const M) _ _ (Fmap_const) (Pure_const) (Mult_const) A tag f.
  Proof.
    unfold foldMap. now rewrite (traversable_fold_spec tag).
  Qed.

  (* TODO polish me *)
  Theorem traversable_tolist_spec2 {A : Type} :
    @tolist T Tolist_Traversable A
    = foldMap (ret list).
  Proof.
    intros. unfold foldMap. unfold fold.
    reassociate -> on right. rewrite <- (natural (ϕ := @tolist T _)).
    reassociate <- on right.
    ext t. unfold compose.
    induction (tolist T t).
    - easy.
    - cbn. now rewrite <- IHl.
  Qed.

End TraversableFunctor_fold_spec.

(** * Traversals as <<Batch>> coalgebras *)
(******************************************************************************)
Section traversals_coalgebras.

  Context
    `{TraversableFunctor T}.

  Definition batch {A : Type} (B : Type) : A -> @Batch A B B :=
    fun a => (Go (@id B)) ⧆ a.
  Definition iterate {A : Type} (B : Type) : T A -> @Batch A B (T B) :=
    traverse T Batch (batch B).

End traversals_coalgebras.

Lemma extract_to_runBatch : forall (A X : Type) (j : @Batch A A X),
    extract_Batch j = runBatch (@id A) j.
Proof.
  intros. induction j.
  - reflexivity.
  - cbn. now rewrite <- IHj.
Qed.

(** ** Decomposing <<traverse>> in terms of <<iterate>> *)
(******************************************************************************)
Section traversal_iterate.

  Context
    `{TraversableFunctor T}.

  (** ** Identities for <<traverse>> *)
  (******************************************************************************)
  Lemma traverse_to_runBatch `{Applicative F} `(f : A -> F B) (t : T A) :
    traverse T F f t = runBatch f (iterate B t).
  Proof.
    unfold iterate. compose near t on right.
    rewrite (traverse_morphism T (ϕ := @runBatch A F B f _ _ _)).
    fequal. ext a. cbn. now rewrite ap1.
  Qed.

  Lemma dist_to_runBatch `{Applicative F} {A : Type} (t : T (F A)) :
    dist T F t = runBatch (@id (F A)) (iterate A t).
  Proof.
    replace (dist T F t) with (traverse T F id t).
    2:{ unfold traverse. unfold compose. now rewrite (fun_fmap_id T). }
    now rewrite traverse_to_runBatch.
  Qed.

  Lemma traverse_to_runBatch'  `{Applicative F} `(f : A -> F B) :
    traverse T F f = runBatch f ∘ iterate B.
  Proof.
    ext t. now rewrite traverse_to_runBatch.
  Qed.

  Lemma dist_to_runBatch' `{Applicative F} {A : Type} :
    dist T F (A := A) = runBatch (@id (F A)) ∘ iterate A.
  Proof.
    ext t. now rewrite dist_to_runBatch.
  Qed.

  (** ** Identities for <<fmap>> *)
  (******************************************************************************)
  Lemma fmap_to_runBatch `(f : A -> B) (t : T A) :
    fmap T f t = runBatch f (iterate B t).
  Proof.
    rewrite (fmap_to_traverse T).
    now rewrite traverse_to_runBatch.
  Qed.

  (** ** Identity for all <<t>> *)
  (******************************************************************************)
  Lemma id_to_runBatch `(t : T A) :
    t = runBatch (@id A) (iterate A t).
  Proof.
    change t with (id t) at 1.
    rewrite <- (traverse_id T).
    now rewrite traverse_to_runBatch.
  Qed.

  (** ** Mapping over <<Batch>> and <<iterate>> *)
  (******************************************************************************)
  Lemma iterate_mapfst `(f : A -> B) {C : Type} (t : T A) :
    iterate C (fmap T f t) = mapfst_Batch f (iterate C t).
  Proof.
    unfold iterate. compose near t on left.
    rewrite (traverse_fmap T).
    do 2 rewrite traverse_to_runBatch. induction (iterate C t).
    - cbv. reflexivity.
    - do 2 rewrite runBatch_rw2. rewrite IHb.
      now rewrite mapfst_Batch3.
  Qed.

  (** ** Identities for <<tolist>> and <<foldMap>> *)
  (******************************************************************************)
  Existing Instance Fmap_const.
  Existing Instance Pure_const.
  Existing Instance Mult_const.
  Existing Instance Applicative_const.
  Existing Instance ApplicativeMorphism_unconst.

  Lemma tolist_to_runBatch `{Applicative F} `(t : T A) :
    tolist T t = runBatch (ret list : A -> const (list A) A) (iterate A t).
  Proof.
    unfold iterate. compose near t on right.
    rewrite (traverse_morphism T (ϕ := @runBatch A (const (list A)) _ (ret list) _ _ _)).
    rewrite (traversable_tolist_spec T A).
    fequal.
  Qed.

  Lemma foldMap_to_runBatch
        `{Monoid M} `(f : A -> M) (t : T A) (B : Type) :
    foldMap f t = runBatch_monoid f (iterate B t).
  Proof.
    rewrite runBatch_monoid1.
    rewrite (traversable_foldMap_spec T B).
    unfold traverse. rewrite dist_to_runBatch'.
    unfold compose. rewrite iterate_mapfst.
    induction (iterate B t).
    - reflexivity.
    - cbn. fequal. now rewrite IHb.
  Qed.

  Lemma tolist_to_runBatch2 `(t : T A) (B : Type) :
    tolist T t = runBatch_monoid (ret list) (iterate B t).
  Proof.
    rewrite (traversable_tolist_spec2 T).
    now rewrite <- (foldMap_to_runBatch (ret list)).
  Qed.

End traversal_iterate.

(** ** Reassembly operation *)
(******************************************************************************)
Section traversal_reassemble.

  Existing Instance Fmap_const.
  Existing Instance Pure_const.
  Existing Instance Mult_const.
  Existing Instance Applicative_const.
  Existing Instance ApplicativeMorphism_unconst.

  Context
    `{TraversableFunctor T}.
  Fixpoint add_elements `(s : @Batch i1 o X) `(l : list i2) : @Batch (Maybe i2) o X :=
    match s with
    | Go t' => Go t'
    | Ap rest a =>
      match l with
      | nil => Ap (add_elements rest nil) None
      | cons a l' => Ap (add_elements rest l') (Just a)
      end
    end.

  Definition reassemble `(t : T X) `(l : list A) : Maybe (T A) :=
    runBatch id (add_elements (iterate _ t) l).

End traversal_reassemble.

(** * Shapeliness *)
(******************************************************************************)
Section traversal_shapeliness.

  Context
    `{TraversableFunctor T}.

  Lemma shapeliness_tactical : forall A (b1 b2 : @Batch A A (T A)),
      runBatch_monoid (ret list) b1 = runBatch_monoid (ret list) b2 ->
      mapfst_Batch (const tt) b1 = mapfst_Batch (const tt) b2 ->
      runBatch id b1 = runBatch id b2.
  Proof.
    intros. induction b1, b2; cbn in *.
    - now inversion H3.
    - now inversion H2.
    - now inversion H2.
    - specialize (list_app_inv_l2 _ _ _ _ _ H2).
      specialize (list_app_inv_r2 _ _ _ _ _ H2).
      introv hyp1 hyp2. subst.
      erewrite IHb1. eauto. eauto.
      now inversion H3.
  Qed.

  Theorem shapeliness : forall A (t1 t2 : T A),
      shape T t1 = shape T t2 /\
      tolist T t1 = tolist T t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    assert (hyp1' : iterate A (shape T t1) = iterate A (shape T t2)).
    { unfold shape in *. now rewrite hyp1. }
    clear hyp1; rename hyp1' into hyp1.
    unfold shape in hyp1.
    do 2 rewrite iterate_mapfst in hyp1.
    rewrite (tolist_to_runBatch2 t1 A) in hyp2.
    rewrite (tolist_to_runBatch2 t2 A) in hyp2.
    rewrite (id_to_runBatch t1).
    rewrite (id_to_runBatch t2).
    auto using shapeliness_tactical.
  Qed.

End traversal_shapeliness.

Instance ListableFunctor_Traversable `{TraversableFunctor T} : ListableFunctor T :=
  {| lfun_shapeliness := shapeliness (T := T) |}.

(** * Traversable instance for [list] *)
(******************************************************************************)
Instance Dist_list : Dist list :=
  fun G map mlt pur A =>
    (fix dist (l : list (G A)) :=
       match l with
       | nil => pure G nil
       | cons x xs =>
         (pure G (@cons A) <⋆> x) <⋆> (dist xs)
       end).

(** ** Rewriting lemmas for <<dist>> *)
(******************************************************************************)
Section list_dist_rewrite.

  Context
    `{Applicative G}.

  Variable (A : Type).

  Lemma dist_list_nil :
    dist list G (@nil (G A)) = pure G nil.
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_1 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      (pure G cons <⋆> x) <⋆> (dist list G xs).
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_2 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      (fmap G (@cons A) x) <⋆> (dist list G xs).
  Proof.
    intros. rewrite dist_list_cons_1.
    now rewrite fmap_to_ap.
  Qed.

  Lemma dist_list_one (a : G A) : dist list G [ a ] = fmap G (ret list) a.
  Proof.
    cbn. rewrite fmap_to_ap. rewrite ap3.
    rewrite <- ap4. now do 2 rewrite ap2.
  Qed.

  Lemma dist_list_app : forall (l1 l2 : list (G A)),
      dist list G (l1 ++ l2) = pure G (@app _) <⋆> dist list G l1 <⋆> dist list G l2.
  Proof.
    intros. induction l1.
    - cbn. rewrite ap2. change (app []) with (@id (list A)).
      now rewrite ap1.
    - cbn [app]. rewrite dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl1; clear IHl1.
      rewrite <- fmap_to_ap.
      rewrite <- fmap_to_ap.
      rewrite <- ap4. rewrite <- fmap_to_ap.
      fequal. rewrite <- ap7.
      rewrite ap6. fequal.
      compose near a.
      rewrite (fun_fmap_fmap G).
      rewrite (fun_fmap_fmap G).
      compose near a on left.
      now rewrite (fun_fmap_fmap G).
  Qed.

End list_dist_rewrite.

Hint Rewrite @dist_list_nil @dist_list_cons_1
     @dist_list_one @dist_list_app : tea_list.

Section dist_list_properties.

  #[local] Arguments dist _%function_scope {Dist} _%function_scope {H H0 H1}
   A%type_scope _.

  Lemma dist_list_1 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      fmap G (fmap list f) ((fmap G (@cons A) a) <⋆> dist list G A l) =
      (fmap G (@cons B ○ f) a) <⋆> fmap G (fmap list f) (dist list G A l).
  Proof.
    intros. rewrite ap6. rewrite <- ap7.
    fequal. compose near a. now rewrite 2(fun_fmap_fmap G).
  Qed.

  Lemma dist_list_2 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      fmap G (fmap list f) ((pure G (@cons A) <⋆> a) <⋆> dist list G A l) =
      (pure G cons <⋆> fmap G f a) <⋆> fmap G (fmap list f) (dist list G A l).
  Proof.
    intros. rewrite <- fmap_to_ap.
    rewrite ap6.
    compose near a on left.
    rewrite (fun_fmap_fmap G).
    rewrite ap5.
    unfold ap. rewrite (app_mult_natural G).
    rewrite (app_mult_natural_1 G).
    compose near ((a ⊗ dist list G A l)) on right.
    rewrite (fun_fmap_fmap G). fequal. ext [? ?].
    reflexivity.
  Qed.

  Lemma dist_natural_list : forall `{Applicative G} `(f : A -> B),
      fmap (G ∘ list) f ∘ dist list G A =
      dist list G B ∘ fmap (list ∘ G) f.
  Proof.
    intros; cbn. unfold_ops @Fmap_compose. unfold compose.
    ext l. induction l.
    + cbn. now rewrite (app_pure_natural G).
    + rewrite dist_list_cons_2.
      rewrite fmap_list_cons, dist_list_cons_2.
      rewrite <- IHl. rewrite dist_list_1.
      compose near a on right. now rewrite (fun_fmap_fmap G).
  Qed.

  Lemma dist_morph_list : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist list G2 A ∘ fmap list (ϕ A) = ϕ (list A) ∘ dist list G1 A.
  Proof.
    intros. ext l. unfold compose. induction l.
    - cbn. now rewrite (appmor_pure G1 G2).
    - specialize (appmor_app_F G1 G2);
        specialize (appmor_app_G G1 G2);
        intros.
      rewrite fmap_list_cons, dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl. rewrite ap_morphism_1.
      fequal. now rewrite (appmor_natural G1 G2 A).
  Qed.

  Lemma dist_unit_list : forall (A : Type),
      dist list (fun A => A) A = @id (list A).
  Proof.
    intros. ext l. induction l.
    - reflexivity.
    - cbn. now rewrite IHl.
  Qed.

  #[local] Set Keyed Unification.
  Lemma dist_linear_list
    : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist list (G1 ∘ G2) A =
      fmap G1 (dist list G2 A) ∘ dist list G1 (G2 A).
  Proof.
    intros. unfold compose. ext l. induction l.
    - cbn. unfold_ops @Pure_compose.
      rewrite fmap_to_ap. now rewrite ap2.
    - rewrite (dist_list_cons_2 (G := G1 ○ G2)).
      rewrite (dist_list_cons_2 (G := G1)).
      rewrite IHl; clear IHl.
      unfold_ops @Mult_compose @Pure_compose @Fmap_compose.
      rewrite (ap_compose_1 G2 G1).
      rewrite (app_mult_natural G1).
      unfold ap at 2. rewrite (app_mult_natural_1 G1).
      fequal. compose near (a ⊗ dist list G1 (G2 A) l).
      repeat rewrite (fun_fmap_fmap G1). fequal.
      ext [? ?]. cbn. now rewrite fmap_to_ap.
  Qed.
  #[local] Unset Keyed Unification.

End dist_list_properties.

Instance Traversable_list : TraversableFunctor list :=
  {| dist_natural := @dist_natural_list;
     dist_morph := @dist_morph_list;
     dist_unit := @dist_unit_list;
     dist_linear := @dist_linear_list;
  |}.

(** * Traversable instance for <<prod>> *)
(******************************************************************************)
Section TraversableFunctor_prod.

  Context
    (X : Type).

  #[global] Instance Dist_prod : Dist (prod X) :=
    fun F map mlt pur A '(x, a) => fmap F (pair x) a.

  Lemma dist_natural_prod : forall `{Applicative G} `(f : A -> B),
      fmap (G ∘ prod X) f ∘ dist (prod X) G = dist (prod X) G ∘ fmap (prod X ∘ G) f.
  Proof.
    intros; unfold compose; cbn. ext [x a]; cbn.
    unfold_ops @Fmap_compose. compose near a.
    now do 2 rewrite (fun_fmap_fmap G).
  Qed.

  Lemma dist_morph_prod : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist (prod X) G2 ∘ fmap (prod X) (ϕ A) = ϕ (X * A) ∘ dist (prod X) G1.
  Proof.
    intros; unfold compose; cbn. ext [x a]; cbn.
    specialize (appmor_app_F G1 G2);
        specialize (appmor_app_G G1 G2);
        intros.
    now rewrite (appmor_natural G1 G2).
  Qed.

  Lemma dist_unit_prod : forall (A : Type),
      dist (prod X) (fun A => A) = @id (prod X A).
  Proof.
    intros; unfold compose; cbn. ext [x a]; now cbn.
  Qed.

  Lemma dist_linear_prod : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist (prod X) (G1 ∘ G2) (A := A) =
      fmap G1 (dist (prod X) G2) ∘ dist (prod X) G1.
  Proof.
    intros; unfold compose; cbn. ext [x a].
    unfold_ops @Dist_prod @Fmap_compose.
    compose near a on right. now rewrite (fun_fmap_fmap G1).
  Qed.

  #[global] Instance Traversable_prod : TraversableFunctor (prod X) :=
    {| dist_natural := @dist_natural_prod;
       dist_morph := @dist_morph_prod;
       dist_unit := @dist_unit_prod;
       dist_linear := @dist_linear_prod;
    |}.

End TraversableFunctor_prod.

(** * Respectfulness properties *)
(******************************************************************************)
Section TraversableFunctor_respectfulness.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}
    `{Applicative G}.

  Lemma traverse_respectful {A B} : forall t (f g : A -> G B),
      (forall a, a ∈ t -> f a = g a) -> traverse T G f t = traverse T G g t.
  Proof.
    intros. unfold traverse, compose. fequal.
    now apply (fmap_respectful T).
  Qed.

  Lemma traverse_respectful_fmap {A B} : forall t (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure G (g a)) -> traverse T G f t = pure G (fmap T g t).
  Proof.
    intros. rewrite <- (traverse_id_purity T). compose near t on right.
    rewrite (traverse_fmap T). apply (traverse_respectful).
    auto.
  Qed.

  Corollary traverse_respectful_id {A} : forall t (f : A -> G A),
      (forall a, a ∈ t -> f a = pure G a) -> traverse T G f t = pure G t.
  Proof.
    intros. rewrite <- (traverse_id_purity T).
    now apply traverse_respectful.
  Qed.

End TraversableFunctor_respectfulness.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'δ'" := (dist) : tealeaves_scope.
End Notations.
