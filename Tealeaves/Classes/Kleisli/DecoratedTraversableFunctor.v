From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.Comonad
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.TraversableFunctor
  Functors.Reader.

Import Strength.Notations.
Import TraversableFunctor.Notations.
Import Comonad.Notations.
Import Product.Notations.

#[local] Generalizable Variables E T ϕ G A B C M.

(** * Decorated traversable functors *)
(******************************************************************************)

(** ** Typeclass *)
(******************************************************************************)

(** *** Operation *)
(******************************************************************************)
Class Mapdt (E : Type) (T : Type -> Type) :=
  mapdt : forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
            (A B : Type), (E * A -> G B) -> T A -> G (T B).

(* Suppress type parameters *)
#[global] Arguments mapdt {E}%type_scope {T}%function_scope {Mapdt}
  {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

(** *** Kleisli composition *)
(******************************************************************************)
Definition kc6
  {E A B C : Type}
  {G1 G2 : Type -> Type}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2}
  (g : E * B -> G2 C)
  (f : E * A -> G1 B) :
  (E * A -> G1 (G2 C)) :=
  map (F := G1) (A := E * B) (B := G2 C) g ∘ strength ∘ cobind f.

#[local] Infix "⋆6" := kc6 (at level 60) : tealeaves_scope.

(** *** Typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctor
  (E : Type) (T : Type -> Type) `{Mapdt E T} :=
  { kdtfun_mapdt1 : forall (A : Type),
      mapdt (G := fun A => A) extract = @id (T A);
    kdtfun_mapdt2 :
    forall `{Applicative G1} `{Applicative G2}
      {A B C : Type} (g : E * B -> G2 C) (f : E * A -> G1 B),
      map (mapdt g) ∘ mapdt f = mapdt (G := G1 ∘ G2) (g ⋆6 f);
    kdtfun_morph : forall `{ApplicativeMorphism G1 G2 ϕ} {A B : Type} (f : E * A -> G1 B),
      mapdt (ϕ B ∘ f) = ϕ (T B) ∘ mapdt f;
  }.

(** *** "Full" typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctorFull (E : Type) (T : Type -> Type)
  `{Mapdt E T} `{Mapd E T} `{Traverse T} `{Map T} :=
  { kdtfunf_dtf :> DecoratedTraversableFunctor E T;
    kdtfunf_map_to_mapdt : forall `(f : A -> B),
      @map T _ A B f = @mapdt E T _ (fun A => A) Map_I Pure_I Mult_I A B (f ∘ extract (W := (E ×)));
    kdtfunf_mapd_to_mapdt : forall `(f : E * A -> B),
      @mapd E T _ A B f = @mapdt E T _ (fun A => A) Map_I Pure_I Mult_I A B f;
    kdtfunf_traverse_to_mapdt : forall `{Applicative G} `(f : A -> G B),
    @traverse T _ G _ _ _ A B f = @mapdt E T _ G _ _ _ A B (f ∘ extract (W := (E ×)));
  }.

(** ** Theory *)
(******************************************************************************)
Section theory.

  Context
    `{DecoratedTraversableFunctorFull E T}.

  Lemma map_strength_cobind_spec
    `{Functor G} : forall (A B C : Type) (f : E * A -> G B) (g : E * B -> C),
      map g ∘ strength ∘ cobind (W := (E ×)) f =
        (fun '(w, a) => map (g ∘ pair w) (f (w, a))).
  Proof.
    intros. ext [w a].
    unfold strength, compose; cbn.
    compose near (f (w, a)) on left.
    rewrite fun_map_map.
    reflexivity.
  Qed.

  Lemma kc6_spec `{Applicative G2} `{Applicative G1} :
    forall (A B C : Type) (f : E * A -> G1 B) (g : E * B -> G2 C),
      g ⋆6 f =
        (fun '(w, a) => map (g ∘ pair w) (f (w, a))).
  Proof.
    intros. unfold kc6. apply map_strength_cobind_spec.
  Qed.

  (** *** Functor composition in the applicative functor *)
  (******************************************************************************)
  Section constant.

    #[local] Arguments mapdt E%type_scope T%function_scope {Mapdt}
      G%function_scope (H H0 H1) (A B)%type_scope _%function_scope _.

    Context
      {G : Type -> Type}
      {A B : Type}
      {mapG  : Map G}
      {pureG : Pure G}
      {multG : Mult G}
      `{! Applicative G}.

    Lemma mapdt_app_l: forall (f : E * A -> G B),
        mapdt E T ((fun A => A) ∘ G)
          (Map_compose  (fun A => A) G)
          (Pure_compose (fun A => A) G)
          (Mult_compose (fun A => A) G)
          A B f = mapdt E T G mapG pureG multG A B f.
    Proof.
      intros. cbv. fequal. ext A' B' p. now destruct p.
    Qed.

    Lemma mapdt_app_r: forall (f : E * A -> G B),
        mapdt E T (G ∘ (fun A => A))
          (Map_compose  G (fun A => A))
          (Pure_compose G (fun A => A))
          (Mult_compose G (fun A => A))
          A B f = mapdt E T G mapG pureG multG A B f.
    Proof.
      intros. cbv. fequal. ext A' B' p.
      destruct p.
      change (mapG (A' * B') (A' * B') (fun p : A' * B' => p))
        with (map (F := G) (@id (A' * B'))).
      rewrite (fun_map_id (F := G)).
      reflexivity.
    Qed.

  End constant.

  (** *** Derived Kleisli composition laws *)
  (******************************************************************************)
  Section kc6_lemmas.

    Context
      `{Applicative G1}
      `{Applicative G2}
      (A B C : Type).

    (** **** Homogeneous cases *)
    (******************************************************************************)
    Lemma kc6_44 :
      forall (g : E * B -> C) (f : E * A -> B),
        kc6 (G1 := fun A => A) (G2 := fun A => A) g f = g ⋆4 f.
    Proof.
      intros. unfold kc6.
      rewrite strength_I.
      unfold_ops @Map_I.
      reflexivity.
    Qed.

    Lemma kc6_22 :
      forall (g : B -> G2 C) (f : A -> G1 B),
        (g ∘ extract (W := (E ×))) ⋆6 f ∘ extract =
          map g ∘ f ∘ extract.
    Proof.
      intros.
      unfold kc6.
      rewrite <- map_to_cobind.
      ext [e a].
      do 2 (unfold compose; cbn).
      compose near (f a) on left.
      rewrite fun_map_map.
      reflexivity.
    Qed.

    (* This holds by `ext [e a]; reflexivity` but I prefer using rewriting
     to understand what's happening *)
    Lemma kc6_00 :
      forall (f : A -> B) (g : B -> C),
        kc6 (G1 := fun A => A) (G2 := fun A => A)
          (g ∘ extract) (f ∘ extract) =
          g ∘ f ∘ extract (W := (E ×)).
    Proof.
      intros. unfold kc6.
      unfold_ops @Map_I.
      rewrite strength_I.
      change (?f ∘ id) with f.
      reassociate ->.
      rewrite kcom_cobind0.
      reflexivity.
    Qed.

    (** **** Heterogeneous cases *)
    (******************************************************************************)

    (** ***** [6x] *)
    (******************************************************************************)
    Lemma kc6_64 :
      forall (g : E * B -> G2 C)
        (f : E * A -> B),
        g ⋆6 f = g ⋆4 f.
    Proof.
      intros. unfold kc6.
      unfold strength.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_62 :
      forall (g : E * B -> G2 C) (f : A -> G1 B),
        g ⋆6 (f ∘ extract) = map g ∘ σ ∘ map f.
    Proof.
      intros. unfold kc6.
      ext [w a].
      rewrite <- map_to_cobind.
      unfold compose; cbn.
      reflexivity.
    Qed.

    Lemma kc6_60 :
      forall (g : E * B -> G2 C) (f : A -> B),
        g ⋆6 (f ∘ extract) = g ∘ map f.
    Proof.
      intros. unfold kc6.
      rewrite strength_I.
      unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

    (** ***** [x6] *)
    (******************************************************************************)
    Lemma kc6_46 :
      forall (g : E * B -> C) (f : E * A -> G1 B),
        kc6 (G2 := fun A => A) g f = map g ∘ σ ∘ cobind f.
    Proof.
      intros.
      unfold kc6.
      reflexivity.
    Qed.

    Lemma kc6_26 :
      forall (g : B -> G2 C) (f : E * A -> G1 B),
        (g ∘ extract) ⋆6 f = map g ∘ f.
    Proof.
      intros. unfold kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      now rewrite fun_map_map.
    Qed.

    Lemma kc6_06 :
      forall (g : B -> C) (f : E * A -> G1 B),
        kc6 (G2 := fun A => A) (g ∘ extract) f = map g ∘ f.
    Proof.
      intros. unfold kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      now rewrite fun_map_map.
    Qed.

    (** ***** [xy] *)
    (******************************************************************************)
    Lemma kc6_24 :
      forall (g : B -> G2 C)
        (f : E * A -> B),
        kc6 (G1 := fun A => A) (g ∘ extract) f = g ∘ f.
    Proof.
      intros. unfold kc6.
      unfold strength.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_42 :
      forall (g : E * B -> C) (f : A -> G1 B),
        kc6 (G2 := fun A => A) g (f ∘ extract) =
          fun '(e, a) => map (g ∘ pair e) (f a).
    Proof.
      intros. unfold kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite fun_map_map.
      reflexivity.
    Qed.

    Lemma kc6_04 :
      forall (g : B -> C)
        (f : E * A -> B),
        kc6 (G1 := fun A => A) (G2 := fun A => A) (g ∘ extract) f = g ∘ f.
    Proof.
      intros. unfold kc6.
      unfold strength; unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_40 :
      forall (g : E * B -> C) (f : A -> B),
        kc6 (G1 := fun A => A) (G2 := fun A => A) g (f ∘ extract) = g ∘ map f.
    Proof.
      intros. unfold kc6.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_20 :
      forall (g : B -> G2 C) (f : A -> B),
        kc6 (E := E) (G1 := fun A => A) (g ∘ extract) (f ∘ extract) =
          g ∘ f ∘ extract.
    Proof.
      intros. unfold kc6.
      unfold strength; unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_02 :
      forall (g : B -> C) (f : E * A -> B),
        kc6 (E := E) (G1 := fun A => A) (G2 := fun A => A)
          (g ∘ extract) f = g ∘ f.
    Proof.
      intros. unfold kc6.
      unfold strength; unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

  End kc6_lemmas.

  (** *** Derived composition laws *)
  (******************************************************************************)
  Section composition.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<mapdt>> on the right *)
    (******************************************************************************)
    Corollary traverse_mapdt : forall (g : B -> G2 C) (f : E * A -> G1 B),
        map (traverse g) ∘ mapdt f = mapdt (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      intros.
      rewrite (kdtfunf_traverse_to_mapdt).
      rewrite kdtfun_mapdt2.
      rewrite kc6_26.
      reflexivity.
    Qed.

    Corollary mapd_mapdt : forall (g : E * B -> C) (f : E * A -> G1 B),
        map (mapd g) ∘ mapdt f = mapdt (map g ∘ σ ∘ cobind f).
    Proof.
      intros.
      rewrite (kdtfunf_mapd_to_mapdt).
      rewrite (kdtfun_mapdt2 (G2 := fun A => A)).
      rewrite mapdt_app_r.
      reflexivity.
    Qed.

    Corollary map_mapdt : forall (g : B -> C) (f : E * A -> G1 B),
        map (map g) ∘ mapdt f = mapdt (map g ∘ f).
    Proof.
      intros.
      rewrite (kdtfunf_map_to_mapdt (T := T)).
      rewrite (kdtfun_mapdt2 (G2 := fun A => A)).
      rewrite mapdt_app_r.
      rewrite kc6_06.
      reflexivity.
    Qed.

    (** *** <<mapdt>> on the left *)
    (******************************************************************************)
    Corollary mapdt_traverse : forall (g : E * B -> G2 C) (f : A -> G1 B),
        map (mapdt g) ∘ traverse (T := T) f =
          mapdt (E := E) (G := G1 ∘ G2)
            (map g ∘ σ ∘ map (F := prod E) f).
    Proof.
      intros.
      rewrite (kdtfunf_traverse_to_mapdt).
      rewrite kdtfun_mapdt2.
      rewrite kc6_62.
      reflexivity.
    Qed.

    Lemma mapdt_mapd : forall (g : E * B -> G2 C) (f : E * A -> B),
        mapdt g ∘ mapd f = mapdt (g ⋆4 f).
    Proof.
      intros.
      rewrite (kdtfunf_mapd_to_mapdt).
      change (mapdt g)
        with (map (F := fun A => A) (mapdt g)).
      rewrite (kdtfun_mapdt2 (G1 := fun A => A)).
      rewrite mapdt_app_l.
      rewrite kc6_64.
      reflexivity.
    Qed.

    Lemma mapdt_map : forall (g : E * B -> G2 C) (f : A -> B),
        mapdt g ∘ map f = mapdt (g ∘ map f).
    Proof.
      intros.
      rewrite (kdtfunf_map_to_mapdt).
      change (mapdt g)
        with (map (F := fun A => A) (mapdt g)).
      rewrite (kdtfun_mapdt2 (G1 := fun A => A)).
      rewrite mapdt_app_l.
      rewrite kc6_60.
      reflexivity.
    Qed.

    (** *** Other cases *)
    (******************************************************************************)
    Corollary map_mapd : forall (g : B -> C) (f : E * A -> B),
        map g ∘ mapd f = mapd (g ∘ f).
    Proof.
      intros.
      rewrite (kdtfunf_map_to_mapdt).
      do 2 rewrite (kdtfunf_mapd_to_mapdt).
      change (mapdt ?g)
        with (map (F := fun A => A) (mapdt (G := fun A => A) g)) at 1.
      rewrite (kdtfun_mapdt2 (G1 := fun A => A) (G2 := fun A => A)).
      rewrite mapdt_app_l.
      rewrite kc6_04.
      reflexivity.
    Qed.

    Corollary mapd_map : forall (g : E * B -> C) (f : A -> B),
        mapd g ∘ map f = mapd (g ∘ map f).
    Proof.
      intros.
      do 2 rewrite (kdtfunf_mapd_to_mapdt).
      rewrite (kdtfunf_map_to_mapdt).
      change (mapdt ?g)
        with (map (F := fun A => A) (mapdt (G := fun A => A) g)) at 1.
      rewrite (kdtfun_mapdt2 (G1 := fun A => A) (G2 := fun A => A)).
      rewrite mapdt_app_l.
      rewrite kc6_44.
      reflexivity.
    Qed.

    Corollary mapd_mapd : forall (g : E * B -> C) (f : E * A -> B),
        mapd g ∘ mapd f = mapd (g ⋆4 f).
    Proof.
      intros.
      do 2 rewrite (kdtfunf_mapd_to_mapdt).
      change (mapdt ?g)
        with (map (F := fun A => A) (mapdt (G := fun A => A) g)) at 1.
      rewrite (kdtfun_mapdt2 (G1 := fun A => A) (G2 := fun A => A)).
      rewrite mapdt_app_l.
      rewrite kc6_44.
      rewrite (kdtfunf_mapd_to_mapdt).
      reflexivity.
    Qed.

    Corollary traverse_traverse : forall (g : B -> G2 C) (f : A -> G1 B),
        map (F := G1) (traverse g) ∘ traverse f = traverse (G := G1 ∘ G2) (g ⋆2 f).
    Proof.
      intros.
      do 3 rewrite (kdtfunf_traverse_to_mapdt).
      rewrite kdtfun_mapdt2.
      rewrite kc6_22.
      reflexivity.
    Qed.

    Lemma map_map : forall {A B C : Type} (f : A -> B) (g : B -> C),
        map g ∘ map f = map (F := T) (g ∘ f).
    Proof.
      intros.
      do 3 rewrite (kdtfunf_map_to_mapdt).
      change_left (map (F := fun A => A)
                     (mapdt (T := T) (g ∘ extract)) ∘ mapdt (T := T) (f ∘ extract)).
      rewrite (kdtfun_mapdt2 (G1 := fun A => A) (G2 := fun A => A)).
      rewrite mapdt_app_l.
      rewrite kc6_00.
      reflexivity.
    Qed.

    (** ** Identity laws *)
    (******************************************************************************)
    Lemma traverse_id : forall A : Type,
        traverse (G := fun A => A) id = @id (T A).
    Proof.
      intros.
      rewrite (kdtfunf_traverse_to_mapdt).
      change (id ∘ ?f) with f.
      now rewrite kdtfun_mapdt1.
    Qed.

    Lemma mapd_id : forall A : Type,
      mapd extract = @id (T A).
    Proof.
      intros.
      rewrite (kdtfunf_mapd_to_mapdt).
      rewrite kdtfun_mapdt1.
      reflexivity.
    Qed.

    Lemma map_id : forall A : Type,
      map (@id A) = @id (T A).
    Proof.
      intros.
      rewrite (kdtfunf_map_to_mapdt).
      change (id ∘ ?f) with f.
      rewrite kdtfun_mapdt1.
      reflexivity.
    Qed.

    (** ** Naturality in applicative morphisms *)
    (******************************************************************************)
    Lemma traverse_morphism :
      forall `{ApplicativeMorphism G1 G2 ϕ},
      forall (A B : Type) (f : A -> G1 B),
        ϕ (T B) ∘ traverse f = traverse (ϕ B ∘ f).
    Proof.
      intros.
      infer_applicative_instances.
      do 2 rewrite (kdtfunf_traverse_to_mapdt).
      rewrite <- kdtfun_morph.
      reflexivity.
    Qed.

  End composition.

  (** *** Derived typeclass instances *)
  (******************************************************************************)
  #[export] Instance Functor_DT : Functor T :=
    {| fun_map_id := map_id;
      fun_map_map := @map_map;
    |}.

  #[export] Instance DF_DT : DecoratedFunctor E T :=
    {| dfun_mapd1 := mapd_id;
      dfun_mapd2 := @mapd_mapd;
    |}.

  #[export] Instance DF_DT_Full : DecoratedFunctorFull E T.
  Proof.
    constructor.
    - apply DF_DT.
    - intros. now rewrite kdtfunf_map_to_mapdt,
        kdtfunf_mapd_to_mapdt.
  Qed.

  #[export] Instance Traversable_DT : TraversableFunctor T :=
    {| trf_traverse_id := traverse_id;
      trf_traverse_traverse := @traverse_traverse;
      trf_traverse_morphism := @traverse_morphism;
    |}.

  #[export] Instance Traversable_DT_Full : TraversableFunctorFull T.
  Proof.
    constructor.
    - apply Traversable_DT.
    - ext A B f. now rewrite kdtfunf_map_to_mapdt,
        kdtfunf_traverse_to_mapdt.
  Qed.

End theory.

(** ** Derived operations *)
(******************************************************************************)
Module DerivedOperations.

  Section operations.

    Context
      `{Mapdt E T}.

    #[export] Instance Mapd_Mapdt: Mapd E T := fun A B f => mapdt (G := fun A => A) f.
    #[export] Instance Traverse_Mapdt: Traverse T := fun G _ _ _ A B f => mapdt (f ∘ extract).
    #[export] Instance Map_Mapdt: Map T := fun A B f => mapdt (G := fun A => A) (f ∘ extract).

    Context
      `{Applicative G}.

    Corollary traverse_to_mapdt : forall `(f : A -> G B),
        traverse f = mapdt (f ∘ extract).
    Proof.
      reflexivity.
    Qed.

    Corollary mapd_to_mapdt : forall `(f : E * A -> B),
        mapd f = mapdt (T := T) (G := fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Corollary map_to_mapdt : forall `(f : A -> B),
        map f = mapdt (T := T) (G := fun A => A) (f ∘ extract).
    Proof.
      reflexivity.
    Qed.

    Corollary map_to_mapd : forall `(f : A -> B),
        map f = mapd (T := T) (f ∘ extract).
    Proof.
      reflexivity.
    Qed.

    Corollary map_to_traverse : forall `(f : A -> B),
        map f = traverse (T := T) (G := fun A => A) f.
    Proof.
      reflexivity.
    Qed.

  End operations.

  #[local] Instance MakeFull_DecoratedTraversableFunctor
    `{DecoratedTraversableFunctor E T} :
    DecoratedTraversableFunctorFull E T.
  Proof.
    now constructor.
  Qed.

End DerivedOperations.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆6" := kc6 (at level 60) : tealeaves_scope.
End Notations.
