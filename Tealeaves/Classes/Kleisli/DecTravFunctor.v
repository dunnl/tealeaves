From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.Comonad
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.TraversableFunctor
  Functors.Environment.

Import Strength.Notations.
Import TraversableFunctor.Notations.
Import Comonad.Notations.
Import Product.Notations.

#[local] Generalizable Variables E ϕ G A B C M.

(* Locally enable explicit arguments *)
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments cobind W%function_scope {Cobind} (A B)%type_scope _%function_scope _.

(** * Decorated traversable functors *)
(******************************************************************************)

(** ** Operation *)
(******************************************************************************)
Class Mapdt
  (E : Type)
  (T : Type -> Type)
  := mapdt :
    forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B : Type),
      (E * A -> G B) -> T A -> G (T B).

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc6
  {E A B C : Type}
  (G1 G2 : Type -> Type)
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2} :
  (E * B -> G2 C) ->
  (E * A -> G1 B) ->
  (E * A -> G1 (G2 C)) :=
  fun g f => map G1 (E * B) (G2 C) g ∘ strength G1 ∘ cobind (prod E) A (G1 B) f.

#[local] Infix "⋆6" := (kc6 _ _) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedTraversableFunctor
  (E : Type)
  (T : Type -> Type)
  `{Mapdt E T} :=
  { kdtfun_mapdt1 : forall (A : Type),
      mapdt (fun A => A) A A (extract (E ×) A) = @id (T A);
    kdtfun_mapdt2 :
    forall (G1 G2 : Type -> Type)
      `{Applicative G1} `{Applicative G2}
      (A B C : Type)
      `(g : E * B -> G2 C) `(f : E * A -> G1 B),
      map G1 (T B) (G2 (T C)) (mapdt G2 B C g) ∘ mapdt G1 A B f = mapdt (G1 ∘ G2) A C (g ⋆6 f);
    kdtfun_morph : forall `{ApplicativeMorphism G1 G2 ϕ} `(f : E * A -> G1 B),
      mapdt G2 A B (ϕ B ∘ f) = ϕ (T B) ∘ mapdt G1 A B f;
  }.

(* Globally suppress type parameters, but locally make them explicit. *)
#[global] Arguments mapdt {E}%type_scope T%function_scope {Mapdt} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local]  Arguments mapdt {E}%type_scope T%function_scope {Mapdt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(** * Functor composition in the applicative functor *)
(******************************************************************************)
Section operations.

  Context
    (E : Type)
    (T : Type -> Type)
    `{DecoratedTraversableFunctor E T}.

  #[local]  Arguments mapdt E%type_scope T%function_scope {Mapdt} G%function_scope (H H0 H1) (A B)%type_scope _%function_scope _.

  Context
    (G : Type -> Type)
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
    intros. fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma mapdt_app_r: forall (f : E * A -> G B),
      mapdt E T (G ∘ (fun A => A))
        (Map_compose  G (fun A => A))
        (Pure_compose G (fun A => A))
        (Mult_compose G (fun A => A))
        A B f = mapdt E T G mapG pureG multG A B f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity1.
  Qed.

End operations.

(** * Derived instances *)
(******************************************************************************)
Module DerivedInstances.

  (** ** Operations *)
  (******************************************************************************)
  Section operations.

    Context
      (E : Type)
      (T : Type -> Type)
      `{Mapdt E T}.

    #[export] Instance Map_Mapdt: Map T := fun A B f => mapdt T (fun A => A) A B (f ∘ extract (E ×) A).
    #[export] Instance Mapd_Mapdt: Mapd E T := fun A B f => mapdt T (fun A => A) A B f.
    #[export] Instance Traverse_Mapdt: Traverse T := fun G _ _ _ A B f => mapdt T G A B (f ∘ extract (E ×) A).

    Context
      (G : Type -> Type)
        `{Applicative G}.

    Corollary traverse_to_mapdt {A B : Type} : forall (f : A -> G B),
        traverse T G A B f = mapdt T G A B (f ∘ extract (E ×) A).
    Proof.
      reflexivity.
    Qed.

    Corollary mapd_to_mapdt {A B : Type} : forall (f : E * A -> B),
        mapd T f = mapdt T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    Corollary map_to_mapdt {A B : Type} : forall (f : A -> B),
        map T A B f = mapdt T (fun A => A) A B (f ∘ extract (E ×) A).
    Proof.
      reflexivity.
    Qed.

    Corollary map_to_mapd {A B : Type} : forall (f : A -> B),
        map T A B f = mapd T (f ∘ extract (E ×) A).
    Proof.
      reflexivity.
    Qed.

    Corollary map_to_traverse {A B : Type} : forall (f : A -> B),
        map T A B f = traverse T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

  End operations.

  (** ** Derived Kleisli composition laws *)
  (******************************************************************************)
  Section kc6_lemmas.

    Context
      (T : Type -> Type)
      `{DecoratedTraversableFunctor E T}
      (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      (A B C : Type).

    (** *** Homogeneous cases *)
    (******************************************************************************)
    Lemma kc6_44 :
      forall (g : E * B -> C) (f : E * A -> B),
        kc6 (fun A => A) (fun A => A) g f = kc4 (E ×) g f.
    Proof.
      intros. unfold kc6.
      rewrite strength_I.
      unfold_ops @Map_I.
      reflexivity.
    Qed.

    Lemma kc6_22 :
      forall (g : B -> G2 C) (f : A -> G1 B),
        (g ∘ extract (E ×) B) ⋆6 (f ∘ extract (E ×) A) =
          map G1 B (G2 C) g ∘ f ∘ extract (E ×) A.
    Proof.
      intros. unfold kc6.
      rewrite <- (map_to_cobind A (G1 B)).
      ext [e a].
      do 2 (unfold compose; cbn).
      compose near (f a) on left.
      rewrite (fun_map_map).
      reflexivity.
    Qed.

    (* This holds by `ext [e a]; reflexivity` but I prefer using rewriting
     to understand what's happening *)
    Lemma kc6_00 :
      forall (f : A -> B) (g : B -> C),
        kc6 (fun A => A) (fun A => A)
          (g ∘ extract (E ×) B)
          (f ∘ extract (E ×) A)
        = g ∘ f ∘ extract (E ×) A.
    Proof.
      intros. unfold kc6.
      unfold_ops @Map_I.
      rewrite strength_I.
      change (?f ∘ id) with f.
      reassociate ->.
      rewrite (kcom_cobind0).
      reflexivity.
    Qed.

    (** *** Heterogeneous cases *)
    (******************************************************************************)

    (** **** [6x] *)
    (******************************************************************************)
    Lemma kc6_64 :
      forall (g : E * B -> G2 C)
        (f : E * A -> B),
        g ⋆6 f = g ⋆4 f.
    Proof.
      intros. unfold kc6.
      unfold strength; unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_62 :
      forall (g : E * B -> G2 C) (f : A -> G1 B),
        g ⋆6 (f ∘ extract (E ×) A) =
          map G1 (E * B) (G2 C) g ∘ σ G1 ∘ map (E ×) A (G1 B) f.
    Proof.
      intros. unfold kc6.
      ext [w a].
      rewrite <- (map_to_cobind).
      unfold compose; cbn.
      reflexivity.
    Qed.

    Lemma kc6_60 :
      forall (g : E * B -> G2 C) (f : A -> B),
        g ⋆6 (f ∘ extract (E ×) A) = g ∘ map (E ×) A B f.
    Proof.
      intros. unfold kc6.
      rewrite strength_I.
      unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

    (** **** [x6] *)
    (******************************************************************************)
    Lemma kc6_46 :
      forall (g : E * B -> C) (f : E * A -> G1 B),
        kc6 G1 (fun A => A) g f =
          map G1 (E * B) C g ∘ σ G1 ∘ cobind (E ×) A (G1 B) f.
    Proof.
      intros.
      unfold kc6.
      reflexivity.
    Qed.

    Lemma kc6_26 :
      forall (g : B -> G2 C) (f : E * A -> G1 B),
        (g ∘ extract (E ×) B) ⋆6 f = map G1 B (G2 C) g ∘ f.
    Proof.
      intros. unfold kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      now rewrite (fun_map_map).
    Qed.

    Lemma kc6_06 :
      forall (g : B -> C) (f : E * A -> G1 B),
        kc6 G1 (fun A => A) (g ∘ extract (E ×) B) f = map G1 B C g ∘ f.
    Proof.
      intros. unfold kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      now rewrite (fun_map_map).
    Qed.

    (** **** [xy] *)
    (******************************************************************************)
    Lemma kc6_24 :
      forall (g : B -> G2 C)
        (f : E * A -> B),
        kc6 (fun A => A) G2 (g ∘ extract (E ×) B) f = g ∘ f.
    Proof.
      intros. unfold kc6.
      unfold strength; unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_42 :
      forall (g : E * B -> C) (f : A -> G1 B),
        kc6 G1 (fun A => A) g (f ∘ extract (E ×) A) =
          fun '(e, a) => map G1 _ _ (g ∘ pair e) (f a).
    Proof.
      intros. unfold kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite (fun_map_map).
      reflexivity.
    Qed.

    Lemma kc6_04 :
      forall (g : B -> C)
        (f : E * A -> B),
        kc6 (fun A => A) (fun A => A) (g ∘ extract (E ×) B) f = g ∘ f.
    Proof.
      intros. unfold kc6.
      unfold strength; unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_40 :
      forall (g : E * B -> C) (f : A -> B),
        kc6 (fun A => A) (fun A => A) g (f ∘ extract (E ×) A) = g ∘ map (E ×) A B f.
    Proof.
      intros. unfold kc6.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_20 :
      forall (g : B -> G2 C) (f : A -> B),
        kc6 (fun A => A) G2 (g ∘ extract (E ×) B) (f ∘ extract (E ×) A) =
          g ∘ f ∘ extract (E ×) A.
    Proof.
      intros. unfold kc6.
      unfold strength; unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

    Lemma kc6_02 :
      forall (g : B -> C) (f : E * A -> B),
        kc6 (fun A => A) (fun A => A) (g ∘ extract (E ×) B) f = g ∘ f.
    Proof.
      intros. unfold kc6.
      unfold strength; unfold_ops @Map_I.
      ext [w a].
      reflexivity.
    Qed.

  End kc6_lemmas.

  (** ** Derived Kleisli composition operations *)
  (******************************************************************************)
  Section composition.

    Context
      (T : Type -> Type)
      `{DecoratedTraversableFunctor E T}
      (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<mapdt>> on the right *)
    (******************************************************************************)
    Corollary traverse_mapdt : forall (g : B -> G2 C) (f : E * A -> G1 B),
        map G1 (T B) (G2 (T C)) (traverse T G2 B C g) ∘ mapdt T G1 A B f =
          mapdt T (G1 ∘ G2) A C (map G1 B (G2 C) g ∘ f).
    Proof.
      intros.
      rewrite (traverse_to_mapdt).
      rewrite (kdtfun_mapdt2 G1 G2).
      rewrite (kc6_26 G1 G2).
      reflexivity.
    Qed.

    Corollary mapd_mapdt : forall (g : E * B -> C) (f : E * A -> G1 B),
        map G1 (T B) (T C) (mapd T g) ∘ mapdt T G1 A B f =
            mapdt T G1 A C (map G1 (E * B) C g ∘ σ G1 ∘ cobind (E ×) A (G1 B) f).
    Proof.
      intros.
      rewrite (mapd_to_mapdt).
      rewrite (kdtfun_mapdt2 G1 (fun A => A)).
      rewrite (mapdt_app_r E T G1).
      reflexivity.
    Qed.

    Corollary map_mapdt : forall (g : B -> C) (f : E * A -> G1 B),
        map G1 (T B) (T C) (map T B C g) ∘ mapdt T G1 A B f = mapdt T G1 A C (map G1 B C g ∘ f).
    Proof.
      intros.
      rewrite (map_to_mapdt).
      rewrite (kdtfun_mapdt2 G1 (fun A => A)).
      rewrite (mapdt_app_r E T G1).
      rewrite (kc6_06 G1).
      reflexivity.
    Qed.

    (** *** <<mapdt>> on the left *)
    (******************************************************************************)
    Corollary mapdt_traverse : forall (g : E * B -> G2 C) (f : A -> G1 B),
        map G1 (T B) (G2 (T C)) (mapdt T G2 B C g) ∘ traverse T G1 A B f =
          mapdt T (G1 ∘ G2) A C (map G1 (E * B) (G2 C) g ∘ σ G1 ∘ map (E ×) A (G1 B) f).
    Proof.
      intros.
      rewrite (traverse_to_mapdt).
      rewrite (kdtfun_mapdt2 G1 G2).
      rewrite kc6_62.
      reflexivity.
    Qed.

    Lemma mapdt_mapd : forall (g : E * B -> G2 C) (f : E * A -> B),
        mapdt T G2 B C g ∘ mapd T f = mapdt T G2 A C (g ⋆4 f).
    Proof.
      intros.
      rewrite (mapd_to_mapdt).
      change (mapdt T G2 B C g)
        with (map (fun A => A) _ _ (mapdt T G2 B C g)).
      rewrite (kdtfun_mapdt2 (fun A => A) G2).
      rewrite (mapdt_app_l E T G2).
      rewrite kc6_64.
      reflexivity.
    Qed.

    Lemma mapdt_map : forall (g : E * B -> G2 C) (f : A -> B),
        mapdt T G2 B C g ∘ map T A B f = mapdt T G2 A C (g ∘ map (E ×) A B f).
    Proof.
      intros.
      rewrite (map_to_mapdt).
      change (mapdt T G2 B C g)
        with (map (fun A => A) _ _ (mapdt T G2 B C g)).
      rewrite (kdtfun_mapdt2 (fun A => A) G2).
      rewrite (mapdt_app_l E T G2).
      rewrite kc6_60.
      reflexivity.
    Qed.

    (** *** Other cases *)
    (******************************************************************************)
    Corollary map_mapd : forall (g : B -> C) (f : E * A -> B),
        map T B C g ∘ mapd T f = mapd T (g ∘ f).
    Proof.
      intros.
      rewrite (map_to_mapdt).
      rewrite (mapd_to_mapdt).
      change (mapdt T ?G B C ?g)
        with (map (fun A => A) _ _ (mapdt T G B C g)).
      rewrite (kdtfun_mapdt2 (fun A => A) (fun A => A)).
      rewrite (mapdt_app_l E T (fun A => A)).
      rewrite kc6_04.
      reflexivity.
    Qed.

    Corollary mapd_map : forall (g : E * B -> C) (f : A -> B),
        mapd T g ∘ map T A B f = mapd T (g ∘ map (E ×) A B f).
    Proof.
      intros.
      do 2 rewrite (mapd_to_mapdt).
      rewrite (map_to_mapdt).
      change (mapdt T ?G B C ?g)
        with (map (fun A => A) _ _ (mapdt T G B C g)).
      rewrite (kdtfun_mapdt2 (fun A => A) (fun A => A)).
      rewrite (mapdt_app_l E T (fun A => A)).
      rewrite kc6_44.
      reflexivity.
    Qed.

    Corollary mapd_mapd : forall (g : E * B -> C) (f : E * A -> B),
        mapd T g ∘ mapd T f = mapd T (g ⋆4 f).
    Proof.
      intros.
      do 2 rewrite (mapd_to_mapdt).
      change (mapdt T ?G B C ?g)
        with (map (fun A => A) _ _ (mapdt T G B C g)).
      rewrite (kdtfun_mapdt2 (fun A => A) (fun A => A)).
      rewrite (mapdt_app_l E T (fun A => A)).
      rewrite kc6_44.
      reflexivity.
    Qed.

    Corollary traverse_traverse : forall (g : B -> G2 C) (f : A -> G1 B),
        map G1 (T B) (G2 (T C)) (traverse T G2 B C g) ∘ traverse T G1 A B f = traverse T (G1 ∘ G2) A C (g ⋆2 f).
    Proof.
      intros.
      do 2 rewrite (traverse_to_mapdt).
      rewrite (kdtfun_mapdt2 G1 G2).
      rewrite (kc6_22 G1 G2).
      reflexivity.
    Qed.

    Lemma map_map : forall (f : A -> B) (g : B -> C),
        map T B C g ∘ map T A B f = map T A C (g ∘ f).
    Proof.
      intros.
      do 2 rewrite (map_to_mapdt).
      change_left (map (fun A => A) _ _ (mapdt T (fun A => A) B C (g ∘ extract (prod E) B)) ∘ mapdt T (fun A => A) A B (f ∘ extract (prod E) A)).
      rewrite (kdtfun_mapdt2 (fun A => A) (fun A => A)).
      rewrite (mapdt_app_l _ _ (fun A => A)).
      rewrite kc6_00.
      reflexivity.
    Qed.

    (** ** Identity laws *)
    (******************************************************************************)
    Lemma traverse_id :
      forall A : Type, traverse T (fun A => A) A A (id) = @id (T A).
    Proof.
      intros.
      rewrite (traverse_to_mapdt).
      change (id ∘ ?f) with f.
      now rewrite (kdtfun_mapdt1).
    Qed.

    Lemma mapd_id :
      forall A : Type, mapd T (extract (E ×) A) = @id (T A).
    Proof.
      intros.
      rewrite (mapd_to_mapdt).
      now rewrite (kdtfun_mapdt1).
    Qed.

    Lemma map_id :
      forall A : Type, map T A A (@id A) = @id (T A).
    Proof.
      intros.
      rewrite (map_to_mapdt).
      change (id ∘ ?f) with f.
      now rewrite (kdtfun_mapdt1).
    Qed.

    (** ** Naturality in applicative morphisms *)
    (******************************************************************************)
    Lemma traverse_morphism :
      forall (ϕ : forall (A : Type), G1 A -> G2 A)
        `{! ApplicativeMorphism G1 G2 ϕ},
      forall (A B : Type) (f : A -> G1 B), ϕ (T B) ∘ traverse T G1 A B f = traverse T G2 A B (ϕ B ∘ f).
    Proof.
      intros.
      rewrite (traverse_to_mapdt).
      rewrite <- (kdtfun_morph).
      reflexivity.
    Qed.

  End composition.

  (** ** Derived typeclass instances *)
  (******************************************************************************)
  Section instances.

    Context
      (T : Type -> Type)
      `{DecoratedTraversableFunctor E T}.

    #[export] Instance Functor_DT : Functor T :=
      {| fun_map_id := map_id T;
        fun_map_map := @map_map T E _ _;
      |}.

    #[export] Instance DF_DT : DecoratedFunctor E T :=
      {| dfun_mapd1 := mapd_id T;
        dfun_mapd2 := @mapd_mapd T E _ _;
      |}.

    #[export] Instance Traversable_DT : TraversableFunctor T :=
      {| trf_traverse_id := traverse_id T;
        trf_traverse_traverse := @traverse_traverse T _ _ _;
        trf_traverse_morphism := @traverse_morphism T _ _ _;
      |}.

  End instances.

End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆6" := (kc6 _ _) (at level 60) : tealeaves_scope.
End Notations.
