From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.Comonad
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.TraversableFunctor
  Functors.Early.Reader.

Import Monoid.Notations.
Import Strength.Notations.
Import TraversableFunctor.Notations.
Import Comonad.Notations.
Import Product.Notations.

#[local] Generalizable Variables E T ϕ G A B C M.

(** * Decorated Traversable Functor *)
(******************************************************************************)

(** ** The <<mapdt>> Operation *)
(******************************************************************************)
Class Mapdt (E: Type) (T: Type -> Type) :=
  mapdt: forall (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
            (A B: Type), (E * A -> G B) -> T A -> G (T B).

#[global] Arguments mapdt {E}%type_scope {T}%function_scope {Mapdt}
  {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

(** ** Kleisli Composition *)
(******************************************************************************)
Definition kc3
  {E A B C: Type}
  {G1 G2: Type -> Type}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2}
  (g: E * B -> G2 C)
  (f: E * A -> G1 B) :
  (E * A -> G1 (G2 C)) :=
  map (F := G1) (A := E * B) (B := G2 C) g ∘ strength ∘ cobind f.

#[local] Infix "⋆3" := kc3 (at level 60): tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctor
  (E: Type) (T: Type -> Type) `{Mapdt E T} :=
  { kdtf_mapdt1: forall (A: Type),
      mapdt (G := fun A => A) extract = @id (T A);
    kdtf_mapdt2 :
    forall `{Applicative G1} `{Applicative G2}
      {A B C: Type} (g: E * B -> G2 C) (f: E * A -> G1 B),
      map (mapdt g) ∘ mapdt f = mapdt (G := G1 ∘ G2) (g ⋆3 f);
    kdtf_morph: forall `{morphism: ApplicativeMorphism G1 G2 ϕ}
                    {A B: Type} (f: E * A -> G1 B),
      ϕ (T B) ∘ mapdt f = mapdt (ϕ B ∘ f);
  }.

(** ** Kleisli Category Laws *)
(** TODO: The left and right unit are simply <<extract>> with <<G>> = <<fun A => A>> *)
(******************************************************************************)


(** * Derived Structures *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.
  Section operations.

    Context
      `{Mapdt_ET: Mapdt E T}.

    #[export] Instance Mapd_Mapdt: Mapd E T := fun A B f => mapdt (G := fun A => A) f.
    #[export] Instance Traverse_Mapdt: Traverse T := fun G _ _ _ A B f => mapdt (f ∘ extract).
    #[export] Instance Map_Mapdt: Map T := fun A B f => mapdt (G := fun A => A) (f ∘ extract).

  End operations.
End DerivedOperations.

Section compat.

  Context
    (E: Type)
    (T: Type -> Type)
    `{Map_T: Map T}
    `{Mapd_ET: Mapd E T}
    `{Traverse_T: Traverse T}
    `{Mapdt_ET: Mapdt E T}.

  Class Compat_Map_Mapdt: Prop :=
    compat_map_mapdt:
      @Map_T = @DerivedOperations.Map_Mapdt E T Mapdt_ET.

  Class Compat_Mapd_Mapdt: Prop :=
    compat_mapd_mapdt:
      @Mapd_ET = @DerivedOperations.Mapd_Mapdt E T Mapdt_ET.

  Class Compat_Traverse_Mapdt: Prop :=
    compat_traverse_mapdt:
      @Traverse_T =
        @DerivedOperations.Traverse_Mapdt E T Mapdt_ET.
      (*
      forall {G: Type -> Type}
        `{Map_G: Map G}
        `{Mult_G: Mult G}
        `{Pure_G: Pure G}
        `{! Applicative G},
        @Traverse_T G Map_G Pure_G Mult_G =
          @DerivedOperations.Traverse_Mapdt E T Mapdt_ET G Map_G Pure_G Mult_G.
       *)

End compat.

Section rewriting.

  Context
    `{Map_T: Map T}
    `{Mapd_ET: Mapd E T}
    `{Traverse_T: Traverse T}
    `{Mapdt_ET: Mapdt E T}
    `{! Compat_Map_Mapdt E T}
    `{! Compat_Mapd_Mapdt E T}
    `{! Compat_Traverse_Mapdt E T}.

  Definition traverse_to_mapdt
    `{Applicative G}: forall `(f: A -> G B),
      traverse (T := T) f = mapdt (f ∘ extract).
  Proof.
    rewrite (compat_traverse_mapdt E T).
    reflexivity.
  Qed.

  Definition mapd_to_mapdt: forall `(f: E * A -> B),
      mapd f = mapdt (T := T) (G := fun A => A) f :=
    ltac:(now rewrite (compat_mapd_mapdt E T)).

  Definition map_to_mapdt: forall `(f: A -> B),
      map f = mapdt (T := T) (G := fun A => A) (f ∘ extract) :=
    ltac:(now rewrite (compat_map_mapdt E T)).

  Corollary map_to_mapd: forall `(f: A -> B),
      map f = mapd (T := T) (f ∘ extract).
  Proof.
    intros.
    rewrite map_to_mapdt.
    rewrite mapd_to_mapdt.
    reflexivity.
  Qed.

  Corollary map_to_traverse: forall `(f: A -> B),
      map f = traverse (T := T) (G := fun A => A) f.
  Proof.
    intros.
    rewrite map_to_mapdt.
    rewrite traverse_to_mapdt.
    reflexivity.
  Qed.

End rewriting.

#[export] Instance Compat_Map_Mapdt_Self `{Mapdt_ET: Mapdt E T}:
  Compat_Map_Mapdt E T (Map_T := DerivedOperations.Map_Mapdt)
  := ltac:(reflexivity).

#[export] Instance Compat_Mapd_Mapdt_Self `{Mapdt_inst: Mapdt E T}:
  Compat_Mapd_Mapdt E T (Mapd_ET := DerivedOperations.Mapd_Mapdt)
  := ltac:(reflexivity).

#[export] Instance Compat_Traverse_Mapdt_Self `{Mapdt_inst: Mapdt E T} :
  Compat_Traverse_Mapdt E T (Traverse_T := DerivedOperations.Traverse_Mapdt) :=
  ltac:(hnf; reflexivity).

#[export] Instance Compat_Map_Mapd_Mapdt
  `{Map_T: Map T}
  `{Mapd_ET: Mapd E T}
  `{Mapdt_ET: Mapdt E T}
  `{! Compat_Map_Mapdt E T}
  `{! Compat_Mapd_Mapdt E T}:
  Compat_Map_Mapd E T.
Proof.
  hnf.
  rewrite (compat_map_mapdt E T).
  rewrite (compat_mapd_mapdt E T).
  reflexivity.
Qed.

#[export] Instance Compat_Map_Traverse_Mapdt
  `{Map_T: Map T}
  `{Traverse_T: Traverse T}
  `{Mapdt_ET: Mapdt E T}
  `{! Compat_Map_Mapdt E T}
  `{! Compat_Traverse_Mapdt E T}:
  Compat_Map_Traverse T.
Proof.
  hnf.
  rewrite (compat_map_mapdt E T).
  rewrite (compat_traverse_mapdt E T).
  reflexivity.
Qed.

(** ** Composition with the Identity Applicative Functor *)
(******************************************************************************)
Section mapdt_identity_applicative.

  #[local] Arguments mapdt E%type_scope T%function_scope {Mapdt}
    G%function_scope (H H0 H1) (A B)%type_scope _%function_scope _.

  Context
    `{DecoratedTraversableFunctor E T}.

  Context
    {G: Type -> Type}
    {A B: Type}
    {mapG : Map G}
    {pureG: Pure G}
    {multG: Mult G}
    `{! Applicative G}.

  Lemma mapdt_app_id_l: forall (f: E * A -> G B),
      mapdt E T ((fun A => A) ∘ G)
        (Map_compose  (fun A => A) G)
        (Pure_compose (fun A => A) G)
        (Mult_compose (fun A => A) G)
        A B f = mapdt E T G mapG pureG multG A B f.
  Proof.
    intros. cbv. fequal. ext A' B' p. now destruct p.
  Qed.

  Lemma mapdt_app_id_r: forall (f: E * A -> G B),
      mapdt E T (G ∘ (fun A => A))
        (Map_compose  G (fun A => A))
        (Pure_compose G (fun A => A))
        (Mult_compose G (fun A => A))
        A B f = mapdt E T G mapG pureG multG A B f.
  Proof.
    intros. cbv. fequal. ext A' B' p.
    destruct p.
    change (mapG (A' * B') (A' * B') (fun p: A' * B' => p))
      with (map (F := G) (@id (A' * B'))).
    rewrite (fun_map_id (F := G)).
    reflexivity.
  Qed.

End mapdt_identity_applicative.

(** ** Derived Kleisli Composition Laws *)
(******************************************************************************)
Section decorated_traversable_functor_derived_kleisli_laws.

  Context
    {E: Type} {T: Type -> Type}
    `{Map_inst: Map T}
    `{Mapd_inst: Mapd E T}
    `{Traverse_inst: Traverse T}
    `{Mapdt_inst: Mapdt E T}
    `{! Compat_Map_Mapdt E T}
    `{! Compat_Mapd_Mapdt E T}
    `{! Compat_Traverse_Mapdt E T}
    `{! DecoratedTraversableFunctor E T}.

  Lemma kc3_spec `{Applicative G2} `{Applicative G1} :
    forall (A B C: Type) (f: E * A -> G1 B) (g: E * B -> G2 C),
      g ⋆3 f =
        (fun '(w, a) => map (g ∘ pair w) (f (w, a))).
  Proof.
    intros. unfold kc3.
    rewrite (map_strength_cobind_spec E).
    reflexivity.
  Qed.

  Import Monoid.

  Lemma kc3_preincr `{Monoid_op E} `{Applicative G2} `{Applicative G1} :
    forall (A B C: Type) (f: E * A -> G1 B) (g: E * B -> G2 C) (e: E),
      (g ⋆3 f) ⦿ e =
        (g  ⦿ e ⋆3 f ⦿ e).
  Proof.
    intros.
    do 2 rewrite kc3_spec.
    ext [e' a].
    unfold compose; cbn.
    reflexivity.
  Qed.

  Import Comonad.Notations.
  Import Product.Notations.

  Context
    `{Applicative G1}
    `{Applicative G2}
    (A B C: Type).

  (** *** Homogeneous cases *)
  (******************************************************************************)
  Lemma kc3_11:
    forall (g: E * B -> C) (f: E * A -> B),
      kc3 (G1 := fun A => A) (G2 := fun A => A) g f = g ⋆1 f.
  Proof.
    intros. unfold kc3.
    rewrite strength_I.
    unfold_ops @Map_I.
    reflexivity.
  Qed.

  Lemma kc3_22:
    forall (g: B -> G2 C) (f: A -> G1 B),
      (g ∘ extract) ⋆3 (f ∘ extract) =
        map g ∘ f ∘ (extract (W := (E ×))).
  Proof.
    intros.
    unfold kc3.
    rewrite <- map_to_cobind.
    ext [e a].
    do 2 (unfold compose; cbn).
    compose near (f a) on left.
    rewrite fun_map_map.
    reflexivity.
  Qed.

  Lemma kc3_00 :
    forall (f: A -> B) (g: B -> C),
      kc3 (G1 := fun A => A) (G2 := fun A => A)
        (g ∘ extract) (f ∘ extract) =
        g ∘ f ∘ extract (W := (E ×)).
  Proof.
    intros. unfold kc3.
    unfold_ops @Map_I.
    rewrite strength_I.
    change (?f ∘ id) with f.
    reassociate ->.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  (** *** Heterogeneous cases *)
  (******************************************************************************)

  (** **** [3x] *)
  (******************************************************************************)
  Lemma kc3_31:
    forall (g: E * B -> G2 C)
      (f: E * A -> B),
      g ⋆3 f = g ⋆1 f.
  Proof.
    intros. unfold kc3.
    unfold strength.
    ext [w a].
    reflexivity.
  Qed.

  Lemma kc3_32:
    forall (g: E * B -> G2 C) (f: A -> G1 B),
      g ⋆3 (f ∘ extract) = map g ∘ σ ∘ map f.
  Proof.
    intros. unfold kc3.
    ext [w a].
    rewrite <- map_to_cobind.
    unfold compose; cbn.
    reflexivity.
  Qed.

  Lemma kc3_30 :
    forall (g: E * B -> G2 C) (f: A -> B),
      g ⋆3 (f ∘ extract) = g ∘ map f.
  Proof.
    intros. unfold kc3.
    rewrite strength_I.
    unfold_ops @Map_I.
    ext [e a].
    reflexivity.
  Qed.

  (** **** [x3] *)
  (******************************************************************************)
  Lemma kc3_13:
    forall (g: E * B -> C) (f: E * A -> G1 B),
      kc3 (G2 := fun A => A) g f = map g ∘ σ ∘ cobind f.
  Proof.
    intros.
    unfold kc3.
    reflexivity.
  Qed.

  Lemma kc3_23:
    forall (g: B -> G2 C) (f: E * A -> G1 B),
      (g ∘ extract) ⋆3 f = map g ∘ f.
  Proof.
    intros. unfold kc3.
    ext [w a].
    unfold compose; cbn.
    compose near (f (w, a)) on left.
    now rewrite fun_map_map.
  Qed.

  Lemma kc3_03:
    forall (g: B -> C) (f: E * A -> G1 B),
      kc3 (G2 := fun A => A) (g ∘ extract) f = map g ∘ f.
  Proof.
    intros. unfold kc3.
    ext [w a].
    unfold compose; cbn.
    compose near (f (w, a)) on left.
    now rewrite fun_map_map.
  Qed.

  (** **** [xy] *)
  (******************************************************************************)
  Lemma kc3_21:
    forall (g: B -> G2 C)
      (f: E * A -> B),
      kc3 (G1 := fun A => A) (g ∘ extract) f = g ∘ f.
  Proof.
    intros. unfold kc3.
    unfold strength.
    ext [e a].
    reflexivity.
  Qed.

  Lemma kc3_12:
    forall (g: E * B -> C) (f: A -> G1 B),
      kc3 (G2 := fun A => A) g (f ∘ extract) =
        fun '(e, a) => map (g ∘ pair e) (f a).
  Proof.
    intros. unfold kc3.
    ext [e a].
    unfold compose; cbn.
    compose near (f a) on left.
    rewrite fun_map_map.
    reflexivity.
  Qed.

  Lemma kc3_01:
    forall (g: B -> C)
      (f: E * A -> B),
      kc3 (G1 := fun A => A) (G2 := fun A => A) (g ∘ extract) f = g ∘ f.
  Proof.
    intros. unfold kc3.
    unfold strength; unfold_ops @Map_I.
    ext [e a].
    reflexivity.
  Qed.

  Lemma kc3_10:
    forall (g: E * B -> C) (f: A -> B),
      kc3 (G1 := fun A => A) (G2 := fun A => A) g (f ∘ extract) = g ∘ map f.
  Proof.
    intros. unfold kc3.
    ext [e a].
    reflexivity.
  Qed.

  Lemma kc3_20:
    forall (g: B -> G2 C) (f: A -> B),
      kc3 (E := E) (G1 := fun A => A) (g ∘ extract) (f ∘ extract) =
        g ∘ f ∘ extract.
  Proof.
    intros. unfold kc3.
    unfold strength; unfold_ops @Map_I.
    ext [e a].
    reflexivity.
  Qed.

  Lemma kc3_02:
    forall (g: B -> C) (f: E * A -> B),
      kc3 (E := E) (G1 := fun A => A) (G2 := fun A => A)
        (g ∘ extract) f = g ∘ f.
  Proof.
    intros. unfold kc3.
    unfold strength; unfold_ops @Map_I.
    ext [e a].
    reflexivity.
  Qed.

End decorated_traversable_functor_derived_kleisli_laws.

(** ** Derived Composition Laws *)
(******************************************************************************)
Section composition.

  Context
    {E: Type} {T: Type -> Type}
    `{Mapdt_ET: Mapdt E T}
    `{Mapd_ET: Mapd E T}
    `{Traverse_T: Traverse T}
    `{Map_T: Map T}
    `{! Compat_Map_Mapdt E T}
    `{! Compat_Mapd_Mapdt E T}
    `{! Compat_Traverse_Mapdt E T}
    `{! DecoratedTraversableFunctor E T}.

  Context
    `{Applicative G1}
    `{Applicative G2}
    {A B C: Type}.

  (** *** <<mapdt>> on the right *)
  (******************************************************************************)
  Corollary traverse_mapdt: forall (g: B -> G2 C) (f: E * A -> G1 B),
      map (traverse g) ∘ mapdt f = mapdt (G := G1 ∘ G2) (map g ∘ f).
  Proof.
    intros.
    rewrite traverse_to_mapdt.
    rewrite kdtf_mapdt2.
    rewrite kc3_23.
    reflexivity.
  Qed.

  Corollary mapd_mapdt: forall (g: E * B -> C) (f: E * A -> G1 B),
      map (mapd g) ∘ mapdt f = mapdt (map g ∘ σ ∘ cobind f).
  Proof.
    intros.
    rewrite mapd_to_mapdt.
    rewrite (kdtf_mapdt2 (G2 := fun A => A)).
    rewrite mapdt_app_id_r.
    reflexivity.
  Qed.

  Corollary map_mapdt: forall (g: B -> C) (f: E * A -> G1 B),
      map (map g) ∘ mapdt f = mapdt (map g ∘ f).
  Proof.
    intros.
    rewrite (map_to_mapdt (T := T)).
    rewrite (kdtf_mapdt2 (G2 := fun A => A)).
    rewrite mapdt_app_id_r.
    rewrite kc3_03.
    reflexivity.
  Qed.

  (** *** <<mapdt>> on the left *)
  (******************************************************************************)
  Corollary mapdt_traverse: forall (g: E * B -> G2 C) (f: A -> G1 B),
      map (mapdt g) ∘ traverse (T := T) f =
        mapdt (E := E) (G := G1 ∘ G2)
          (map g ∘ σ ∘ map (F := prod E) f).
  Proof.
    intros.
    rewrite traverse_to_mapdt.
    rewrite kdtf_mapdt2.
    rewrite kc3_32.
    reflexivity.
  Qed.

  Lemma mapdt_mapd: forall (g: E * B -> G2 C) (f: E * A -> B),
      mapdt g ∘ mapd f = mapdt (g ⋆1 f).
  Proof.
    intros.
    rewrite mapd_to_mapdt.
    change (mapdt g)
      with (map (F := fun A => A) (mapdt g)).
    rewrite (kdtf_mapdt2 (G1 := fun A => A)).
    rewrite mapdt_app_id_l.
    rewrite kc3_31.
    reflexivity.
  Qed.

  Lemma mapdt_map: forall (g: E * B -> G2 C) (f: A -> B),
      mapdt g ∘ map f = mapdt (g ∘ map f).
  Proof.
    intros.
    rewrite map_to_mapdt.
    change (mapdt g)
      with (map (F := fun A => A) (mapdt g)).
    rewrite (kdtf_mapdt2 (G1 := fun A => A)).
    rewrite mapdt_app_id_l.
    rewrite kc3_30.
    reflexivity.
  Qed.

  (** *** Other cases *)
  (******************************************************************************)
  Corollary map_mapd: forall (g: B -> C) (f: E * A -> B),
      map g ∘ mapd f = mapd (g ∘ f).
  Proof.
    intros.
    rewrite map_to_mapdt.
    do 2 rewrite mapd_to_mapdt.
    change (mapdt ?g)
      with (map (F := fun A => A) (mapdt (G := fun A => A) g)) at 1.
    rewrite (kdtf_mapdt2 (G1 := fun A => A) (G2 := fun A => A)).
    rewrite mapdt_app_id_l.
    rewrite kc3_01.
    reflexivity.
  Qed.

  Corollary mapd_map: forall (g: E * B -> C) (f: A -> B),
      mapd g ∘ map f = mapd (g ∘ map f).
  Proof.
    intros.
    do 2 rewrite mapd_to_mapdt.
    rewrite map_to_mapdt.
    change (mapdt ?g)
      with (map (F := fun A => A) (mapdt (G := fun A => A) g)) at 1.
    rewrite (kdtf_mapdt2 (G1 := fun A => A) (G2 := fun A => A)).
    rewrite mapdt_app_id_l.
    rewrite kc3_11.
    reflexivity.
  Qed.

  Corollary mapd_mapd: forall (g: E * B -> C) (f: E * A -> B),
      mapd g ∘ mapd f = mapd (g ⋆1 f).
  Proof.
    intros.
    do 2 rewrite mapd_to_mapdt.
    change (mapdt ?g)
      with (map (F := fun A => A) (mapdt (G := fun A => A) g)) at 1.
    rewrite (kdtf_mapdt2 (G1 := fun A => A) (G2 := fun A => A)).
    rewrite mapdt_app_id_l.
    rewrite kc3_11.
    rewrite mapd_to_mapdt.
    reflexivity.
  Qed.

  Corollary traverse_traverse: forall (g: B -> G2 C) (f: A -> G1 B),
      map (F := G1) (traverse g) ∘ traverse f = traverse (G := G1 ∘ G2) (g ⋆2 f).
  Proof.
    intros.
    do 3 rewrite traverse_to_mapdt.
    rewrite kdtf_mapdt2.
    rewrite kc3_22.
    reflexivity.
  Qed.

  Lemma map_map: forall {A B C: Type} (f: A -> B) (g: B -> C),
      map g ∘ map f = map (F := T) (g ∘ f).
  Proof.
    intros.
    do 3 rewrite map_to_mapdt.
    change_left (map (F := fun A => A)
                   (mapdt (T := T) (g ∘ extract)) ∘ mapdt (T := T) (f ∘ extract)).
    rewrite (kdtf_mapdt2 (G1 := fun A => A) (G2 := fun A => A)).
    rewrite mapdt_app_id_l.
    rewrite kc3_00.
    reflexivity.
  Qed.

  (** *** Identity laws *)
  (******************************************************************************)
  Lemma traverse_id: forall A: Type,
      traverse (G := fun A => A) id = @id (T A).
  Proof.
    intros.
    rewrite traverse_to_mapdt.
    change (id ∘ ?f) with f.
    now rewrite kdtf_mapdt1.
  Qed.

  Lemma mapd_id: forall A: Type,
      mapd extract = @id (T A).
  Proof.
    intros.
    rewrite mapd_to_mapdt.
    rewrite kdtf_mapdt1.
    reflexivity.
  Qed.

  Lemma map_id: forall A: Type,
      map (@id A) = @id (T A).
  Proof.
    intros.
    rewrite map_to_mapdt.
    change (id ∘ ?f) with f.
    rewrite kdtf_mapdt1.
    reflexivity.
  Qed.

  (** *** Naturality in applicative morphisms *)
  (******************************************************************************)
  Lemma traverse_morphism :
    forall `{ApplicativeMorphism G1 G2 ϕ},
    forall (A B: Type) (f: A -> G1 B),
      ϕ (T B) ∘ traverse f = traverse (ϕ B ∘ f).
  Proof.
    intros.
    infer_applicative_instances.
    rewrite traverse_to_mapdt.
    rewrite traverse_to_mapdt.
    rewrite kdtf_morph.
    reflexivity.
  Qed.

End composition.

(** ** Derived Typeclass Instances *)
(******************************************************************************)
Module DerivedInstances.
  Section instances.

    Context
      {E: Type} {T: Type -> Type}
      `{Map_T: Map T}
      `{Mapd_ET: Mapd E T}
      `{Traverse_T: Traverse T}
      `{Mapdt_ET: Mapdt E T}
      `{! Compat_Map_Mapdt E T}
      `{! Compat_Mapd_Mapdt E T}
      `{! Compat_Traverse_Mapdt E T}
      `{! DecoratedTraversableFunctor E T}.

    #[export] Instance DecoratedFunctor_DecoratedTraversableFunctor:
      DecoratedFunctor E T.
    Proof.
      constructor; intros.
      - apply mapd_id.
      - apply mapd_mapd.
    Qed.

    #[export] Instance TraversableFunctor_DecoratedTraversableFunctor:
      TraversableFunctor T.
    Proof.
      constructor; intros.
      - apply traverse_id.
      - apply traverse_traverse.
      - apply traverse_morphism.
    Qed.

    #[export] Instance Functor_DecoratedTraversableFunctor:
      Functor T :=
      TraversableFunctor.DerivedInstances.Functor_TraversableFunctor.

  End instances.
End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆3" := kc3 (at level 60): tealeaves_scope.
End Notations.
