From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.Applicative
  Classes.Kleisli.Monad
  Classes.Kleisli.TraversableFunctor.

Import Monad.Notations.
Import TraversableFunctor.Notations.

#[local] Generalizable Variables T G A B C D ϕ M.

#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(** * Traversable monad *)
(******************************************************************************)

(** ** [bindt] operation *)
(******************************************************************************)
Class Bindt
  (U : Type -> Type)
  (T : Type -> Type)
  := bindt :
    forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
      (A B : Type), (A -> G (U B)) -> T A -> G (T B).

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc3
  (T : Type -> Type)
  `{Bindt T T}
  {A B C : Type}
  (G1 G2 : Type -> Type)
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2} :
  (B -> G2 (T C)) ->
  (A -> G1 (T B)) ->
  (A -> G1 (G2 (T C))) :=
  fun g f => map G1 (T B) (G2 (T C)) (@bindt T T _ G2 _ _ _ B C g) ∘ f.

#[local] Infix "⋆3" := (kc3 _ _ _) (at level 60) : tealeaves_scope.

#[local] Arguments bindt (U T)%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(** ** Typeclass *)
(******************************************************************************)
Class TraversableMonad
  (T : Type -> Type)
  `{Return T}
  `{Bindt T T} :=
  { ktm_bindt0 : forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt T T G A B f ∘ ret T A = f;
    ktm_bindt1 : forall (A : Type),
      bindt T T (fun A => A) A A (ret T A) = @id (T A);
    ktm_bindt2 : forall (G1 G2 : Type -> Type) `{Applicative G1} `{Applicative G2} (A B C : Type)
                   (g : B -> G2 (T C)) (f : A -> G1 (T B)),
      map G1 (T B) (G2 (T C)) (bindt T T G2 B C g) ∘ bindt T T G1 A B f =
        bindt T T (G1 ∘ G2) A C (g ⋆3 f);
    ktm_morph : forall `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : A -> G1 (T B)),
      ϕ (T B) ∘ bindt T T G1 A B f = bindt T T G2 A B (ϕ (T B) ∘ f);
  }.


(** * Interaction of [traverse] with functor composition *)
(******************************************************************************)
Section properties.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma bindt_app_l :
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f = bindt T T G A B f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma bindt_app_r :
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f = bindt T T G A B f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity1 G).
  Qed.

End properties.

(** * Derived instances *)
(******************************************************************************)
Module DerivedInstances.

  (** ** Derived operations *)
  (******************************************************************************)
  Section operations.

    Context
      (T : Type -> Type)
      `{Bindt T T}
      `{Return T}.

    #[export] Instance Map_Bindt : Map T :=
      fun (A B : Type) (f : A -> B) => bindt T T (fun A => A) A B (ret T B ∘ f).
    #[export] Instance Bind_Bindt: Bind T T :=
      fun A B f => bindt T T (fun A => A) A B f.
    #[export] Instance Traverse_Bindt: Traverse T :=
      fun G _ _ _ A B f => bindt T T G A B (map G _ _ (ret T B) ∘ f).

    Lemma bind_to_bindt `(f : A -> T B):
      @bind T T _ A B f = bindt T T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_bindt `{Map G} `{Mult G} `{Pure G} `(f : A -> G B):
      @traverse T _ G _ _ _ A B f = bindt T T G A B (map G B (T B) (ret T B) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindt `(f : A -> B):
      @map T _ A B f = bindt T T (fun A => A) A B (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_traverse `(f : A -> B):
      map T A B f = traverse T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bind `(f : A -> B):
      map T A B f = @bind T T _ A B (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

  End operations.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Section kc3_special_cases.

    Context
      (T : Type -> Type)
      `{TraversableMonad T}
      `{Applicative G3}
      `{Applicative G2}
      `{Applicative G1}.

  (** *** Homogeneous cases *)
  (******************************************************************************)
  Lemma kc3_22 : forall `(g : B -> G2 C) `(f : A -> G1 B),
      (map G2 C (T C) (ret T C) ∘ g) ⋆3 (map G1 B (T B) (ret T B) ∘ f) =
        map (G1 ∘ G2) C (T C) (ret T C) ∘ (map G1 B (G2 C) g ∘ f).
  Proof.
    intros. unfold kc3.
    reassociate <-.
    rewrite (fun_map_map).
    reassociate <-.
    unfold_ops @Map_compose.
    unfold_compose_in_compose.
    rewrite (fun_map_map).
    rewrite (ktm_bindt0 G2).
    reflexivity.
  Qed.

  Lemma kc3_11 : forall `(g : B -> T C) `(f : A -> T B),
      kc3 T (fun A => A) (fun A => A) g f = (g ⋆1 f).
  Proof.
    intros. unfold kc3, kc1.
    reflexivity.
  Qed.

  Lemma kc3_00 : forall `(g : B -> C) `(f : A -> B),
      kc3 T (fun A => A) (fun A => A) (ret T C ∘ g) (ret T B ∘ f) = ret T C ∘ g ∘ f.
  Proof.
    intros. unfold kc3.
    reassociate <-.
    change (map (fun A => A) _ _ ?f) with f.
    rewrite (ktm_bindt0 (fun A => A)).
    reflexivity.
  Qed.

  (** *** Heterogeneous cases *)
  (******************************************************************************)

  (** **** [3x] *)
  (******************************************************************************)

  Lemma kc3_32 : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
        g ⋆3 map G1 B (T B) (ret T B) ∘ f = map G1 B (G2 (T C)) g ∘ f.
    Proof.
      intros. unfold kc3.
      reassociate <-.
      rewrite (fun_map_map).
      rewrite (ktm_bindt0 G2).
      reflexivity.
    Qed.

    Lemma kc3_31 : forall `(g : B -> G2 (T C)) `(f : A -> T B),
        kc3 T (fun A => A) G2 g f = bindt T T G2 B C g ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_30 : forall `(g : B -> G2 (T C)) `(f : A -> B),
        kc3 T (fun A => A) G2 g (ret T B ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (ktm_bindt0 G2).
      reflexivity.
    Qed.

    (** **** [x3] *)
    (******************************************************************************)
    Lemma kc3_23 : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
        (map G2 C (T C) (ret T C) ∘ g) ⋆3 f = map G1 (T B) (G2 (T C)) (traverse T G2 B C g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_13 : forall `(g : B -> T C) `(f : A -> G1 (T B)),
        kc3 T G1 (fun A => A) g f = map G1 (T B) (T C) (@bind T T _ B C g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_03 : forall `(g : B -> C) `(f : A -> G1 (T B)),
        kc3 T G1 (fun A => A) (ret T C ∘ g) f = map G1 (T B) (T C) (map T B C g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    (** **** [xy] *)
    (******************************************************************************)
    Lemma kc3_21 : forall `(g : B -> G2 C) `(f : A -> T B),
        (map G2 C (T C) (ret T C) ∘ g) ⋆3 (f : A -> (fun A => A)(T B)) =
          traverse T G2 B C g ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_20 : forall `(g : B -> G2 C) `(f : A -> B),
        kc3 T (fun A => A) G2 (map G2 C (T C) (ret T C) ∘ g) (ret T B ∘ f) = map G2 C (T C) (ret T C) ∘ g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (ktm_bindt0 G2).
      reflexivity.
    Qed.

    Lemma kc3_12 : forall `(g : B -> T C) `(f : A -> G1 B),
        kc3 T G1 (fun A => A) g (map G1 B (T B) (ret T B) ∘ f) = (map G1 B (T C) g ∘ f).
    Proof.
      intros. unfold kc3. reassociate <-.
      rewrite (fun_map_map).
      rewrite (ktm_bindt0 (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_02 : forall `(g : B -> C) `(f : A -> G1 B),
        kc3 T G1 (fun A => A) (ret T C ∘ g) (map G1 B (T B) (ret T B) ∘ f) =
          map G1 C (T C) (ret T C) ∘ map G1 B C g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reassociate <-; rewrite (fun_map_map).
      rewrite (fun_map_map).
      rewrite (ktm_bindt0 (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_01 : forall `(g : B -> C) `(f : A -> T B),
        kc3 T (fun A => A) (fun A => A) (ret T C ∘ g) f =
          map T B C g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reflexivity.
    Qed.

    Lemma kc3_10 : forall `(g : B -> T C) `(f : A -> B),
        kc3 T (fun A => A) (fun A => A) g (ret T B ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (ktm_bindt0 (fun A => A)).
      reflexivity.
    Qed.

  End kc3_special_cases.

  (** ** Composition with lesser Kleisli operations *)
  (******************************************************************************)
  Section composition_special_cases.

    Context
      (T : Type -> Type)
     `{TraversableMonad T}
      (G1 : Type -> Type)
      (G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      (A B C : Type).

    #[local] Arguments bindt                 {U} (T)%function_scope {Bindt}    G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
    #[local] Arguments traverse              T%function_scope     {Traverse} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
    #[local] Arguments bind                  {U} (T)%function_scope {Bind}                                {A B}%type_scope _%function_scope _.
    #[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma traverse_bindt : forall (g : B -> G2 C) (f : A -> G1 (T B)),
      map G1 (traverse T G2 g) ∘ bindt T G1 f =
        bindt T (G1 ∘ G2) (map G1 (traverse T G2 g) ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt).
    rewrite (ktm_bindt2 G1 G2).
    reflexivity.
  Qed.

  Lemma bindt_traverse : forall (g : B -> G2 (T C)) (f : A -> G1 B),
      map G1 (bindt T G2 g) ∘ traverse T G1 f =
        bindt T (G1 ∘ G2) (map G1 g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt).
    rewrite (ktm_bindt2 G1 G2).
    rewrite (kc3_32 T).
    reflexivity.
  Qed.

  (** *** Composition with <<bind>> *)
  (******************************************************************************)
  Lemma bind_bindt : forall (g : B -> T C) (f : A -> G1 (T B)),
      map G1 (bind T g) ∘ bindt T G1 f =
        bindt T G1 (map G1 (bind T g) ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt).
    rewrite (ktm_bindt2 G1 (fun A => A)).
    rewrite (bindt_app_r T G1).
    reflexivity.
  Qed.

  Lemma bindt_bind : forall (g : B -> G2 (T C)) (f : A -> T B),
      bindt T G2 g ∘ bind T f =
        bindt T G2 (bindt T G2 g ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt).
    change (bindt T G2 g) with (map (fun A => A) (bindt T G2 g)).
    rewrite (ktm_bindt2 (fun A => A) G2).
    rewrite (bindt_app_l T G2).
    reflexivity.
  Qed.

  (** *** Composition with <<map>> *)
  (******************************************************************************)
  Lemma map_bindt : forall (g : B -> C) (f : A -> G1 (T B)),
      map G1 (map T g) ∘ bindt T G1 f = bindt T G1 (map G1 (map T g) ∘ f).
  Proof.
    intros.
    rewrite (map_to_bindt T).
    rewrite (ktm_bindt2 G1 (fun A => A)).
    rewrite (bindt_app_r T G1).
    reflexivity.
  Qed.

  Lemma bindt_map : forall (g : B -> G2 (T C)) (f : A -> B),
      bindt T G2 g ∘ map T f = bindt T G2 (g ∘ f).
  Proof.
    intros.
    rewrite (map_to_bindt T).
    change (bindt T G2 g) with (map (fun A => A) (bindt T G2 g)).
    rewrite (ktm_bindt2 (fun A => A) G2).
    rewrite (bindt_app_l T G2).
    rewrite (kc3_30 T).
    reflexivity.
  Qed.

  (** *** Composition between <<traverse>> and <<bind>> *)
  (******************************************************************************)
  Lemma traverse_bind : forall (g : B -> G2 C) (f : A -> T B),
      traverse T G2 g ∘ bind T f =
        bindt T G2 (traverse T G2 g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    rewrite (bind_to_bindt T).
    change (bindt T G2 ?g) with (map (fun A => A) (bindt T G2 g)).
    rewrite (ktm_bindt2 (fun A => A) G2).
    rewrite (bindt_app_l T G2).
    rewrite (kc3_21 T).
    reflexivity.
  Qed.

  Lemma bind_traverse : forall (g : B -> T C) (f : A -> G1 B),
      map G1 (bind T g) ∘ traverse T G1 f =
        bindt T G1 (map G1 g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    rewrite (bind_to_bindt T).
    rewrite (ktm_bindt2 G1 (fun A => A)).
    rewrite (bindt_app_r T G1).
    rewrite (kc3_12 T).
    reflexivity.
  Qed.

  Lemma bind_bind : forall (g : B -> T C) (f : A -> T B),
      bind T g ∘ bind T f =
        bind T (g ⋆1 f).
  Proof.
    intros.
    do 2 rewrite (bind_to_bindt T).
    change (bindt T ?G g) with (map (fun A => A) (bindt T G g)).
    rewrite (ktm_bindt2 (fun A => A) (fun A => A)).
    rewrite (bindt_app_r T (fun A => A)).
    rewrite (kc3_11 T).
    reflexivity.
  Qed.

  Lemma traverse_traverse : forall (g : B -> G2 C) (f : A -> G1 B),
      map G1 (traverse T G2 g) ∘ traverse T G1 f =
        traverse T (G1 ∘ G2) (map G1 g ∘ f).
  Proof.
    intros.
    do 2 rewrite (traverse_to_bindt T).
    rewrite (ktm_bindt2 G1 G2).
    rewrite (kc3_22 T).
    reflexivity.
  Qed.

  (** *** Composition between <<traverse>> and <<map>> *)
  (******************************************************************************)
  Lemma map_traverse : forall (A B C : Type)
                          (g : B -> C)
                          (f : A -> G1 B),
      map G1 (map T g) ∘ traverse T G1 f =
        traverse T G1 (map G1 g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    rewrite (map_to_bindt T).
    rewrite (ktm_bindt2 G1 (fun A => A)).
    rewrite (bindt_app_r T G1).
    rewrite (kc3_02 T).
    reflexivity.
  Qed.

  Lemma traverse_map: forall (A B C : Type)
                         (g : B -> G2 C)
                         (f : A -> B),
      traverse T G2 g ∘ map T f =
        traverse T G2 (g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    rewrite (map_to_bindt T).
    change (bindt T G2 ?g) with (map (fun A => A) (bindt T G2 g)).
    rewrite (ktm_bindt2 (fun A => A) G2).
    rewrite (bindt_app_l T G2).
    rewrite (kc3_20 T).
    reflexivity.
  Qed.

  (** *** Composition between <<bind>> and <<map>> *)
  (******************************************************************************)
  Lemma bind_map : forall (A B C : Type)
                     (g : B -> T C)
                     (f : A -> B),
      bind T g ∘ map T f = bind T (g ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt T).
    rewrite (map_to_bindt T).
    change (bindt T ?G g) with (map (fun A => A) (bindt T G g)).
    rewrite (ktm_bindt2 (fun A => A) (fun A => A)).
    rewrite (bindt_app_r T (fun A => A)).
    rewrite (kc3_10 T).
    reflexivity.
  Qed.

  Lemma map_bind : forall (A B C : Type)
                         (g : B -> C)
                         (f : A -> T B),
      map T g ∘ bind T f = bind T (map T g ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt T).
    rewrite (map_to_bindt T).
    change (bindt T (fun A => A) (?r ∘ g)) with (map (fun A => A) (bindt T (fun A => A) (r ∘ g))).
    rewrite (ktm_bindt2 (fun A => A) (fun A => A)).
    rewrite (bindt_app_r T (fun A => A)).
    rewrite (kc3_01 T).
    reflexivity.
  Qed.

  Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
      map T g ∘ map T f = map T (g ∘ f).
  Proof.
    intros.
    do 3 rewrite (map_to_bindt T).
    change (bindt T (fun A => A) (?r ∘ g)) with (map (fun A => A) (bindt T (fun A => A) (r ∘ g))).
    rewrite (ktm_bindt2 (fun A => A) (fun A => A)).
    rewrite (bindt_app_r T (fun A => A)).
    rewrite (kc3_00 T).
    reflexivity.
  Qed.

  (** *** Identity laws *)
  (******************************************************************************)
  Lemma bind_id : forall (A : Type),
      bind T (ret T A) = @id (T A).
  Proof.
    intros.
    rewrite (bind_to_bindt T).
    now rewrite (ktm_bindt1).
  Qed.

  Lemma traverse_id : forall (A : Type),
      traverse T (fun A => A) (@id A) = @id (T A).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    change (?g ∘ id) with g.
    change (map (fun A => A) ?f) with f.
    now rewrite (ktm_bindt1).
  Qed.

  Lemma map_id : forall (A : Type),
      map T (@id A) = @id (T A).
  Proof.
    intros.
    rewrite (map_to_bindt T).
    change (?g ∘ id) with g.
    now rewrite (ktm_bindt1).
  Qed.

  (** *** Composition with <<ret>> *)
  (******************************************************************************)
  Lemma bind_ret : forall (A B : Type) (f : A -> T B),
      bind T f ∘ ret T A = f.
  Proof.
    intros. rewrite (bind_to_bindt).
    rewrite (ktm_bindt0 (fun A => A)).
    reflexivity.
  Qed.

  (** *** Composition with applicative morphisms *)
  (******************************************************************************)
  Lemma traverse_morphism : forall `{! ApplicativeMorphism G1 G2 ϕ} (A B : Type) (f : A -> G1 B),
      ϕ (T B) ∘ traverse T G1 f = traverse T G2 (ϕ B ∘ f).
  Proof.
    intros. do 2 rewrite (traverse_to_bindt).
    rewrite (ktm_morph).
    reassociate <-.
    fequal. ext a.
    inversion ApplicativeMorphism0.
    unfold compose; cbn. rewrite appmor_natural.
    reflexivity.
  Qed.

  End composition_special_cases.

  Section instances.

    Context
      (T : Type -> Type)
      `{TraversableMonad T}.

    #[export] Instance Functor_TM : Functor T :=
      {| fun_map_id := map_id T;
        fun_map_map := map_map T;
      |}.

    #[export] Instance Monad_TM : Monad T :=
      {| kmon_bind0 := bind_ret T;
        kmon_bind1 := bind_id T;
        kmon_bind2 := bind_bind T;
      |}.

    #[export] Instance Traversable_TM : TraversableFunctor T :=
      {| trf_traverse_id := traverse_id T;
        trf_traverse_traverse := traverse_traverse T;
        trf_traverse_morphism := traverse_morphism T;
      |}.

    #[export] Instance Natural_ret_TM : Natural (ret T).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. rewrite (map_to_bindt T).
        rewrite (ktm_bindt0 (fun A => A)).
        reflexivity.
    Qed.

  End instances.

  End DerivedInstances.

(** ** Kleisli composition laws *)
(******************************************************************************)
Section special_cases.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}
    (G1 : Type -> Type)
    (G2 : Type -> Type)
    (G3 : Type -> Type)
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}.

  Lemma kc3_id_l : forall `(g : A -> G2 (T B)),
      kc3 T (fun A => A) G2 g (ret T A) = g.
  Proof.
    intros. change (ret T A) with (ret T A ∘ id).
    now rewrite (DerivedInstances.kc3_30 T).
  Qed.

  Lemma kc3_id_l' : forall `(g : A -> G2 (T B)),
      kc3 T G1 G2 g (map G1 A (T A) (ret T A)) = map G1 A (G2 (T B)) g.
  Proof.
    intros.
    unfold kc3.
    rewrite (fun_map_map (F := G1)).
    now rewrite (ktm_bindt0 G2).
  Qed.

  Lemma kc3_id_r : forall `(f : A -> G1 (T B)),
      kc3 T G1 (fun A => A) (ret T B) f = f.
  Proof.
    intros.
    change (ret T B) with (ret T B ∘ id).
    rewrite (DerivedInstances.kc3_03).
    rewrite (DerivedInstances.map_to_bindt).
    change (ret T B ∘ id) with (ret T B).
    rewrite (ktm_bindt1).
    rewrite (fun_map_id).
    reflexivity.
  Qed.

  Lemma kc3_assoc : forall `(h : C -> G3 (T D)) `(g : B -> G2 (T C)) `(f : A -> G1 (T B)),
      kc3 T (G1 ∘ G2) G3 h (g ⋆3 f) =
        kc3 T G1 (G2 ∘ G3) (kc3 T G2 G3 h g) f.
  Proof.
    intros.
    unfold kc3.
    unfold_ops @Map_compose.
    unfold_compose_in_compose.
    ext a.
    unfold compose at 1 2.
    compose near (f a) on left.
    rewrite (fun_map_map).
    rewrite (ktm_bindt2 G2 G3).
    unfold compose at 2 3.
    reflexivity.
  Qed.

End special_cases.

Module Notations.

  Infix "⋆3" := (kc3 _ _ _) (at level 60) : tealeaves_scope.

End Notations.
