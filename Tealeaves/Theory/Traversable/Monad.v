From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Classes.Kleisli
  Theory.Traversable.Functor.

#[local] Generalizable Variables T G A B C ϕ M.

Import Kleisli.Notations.

Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments traverse T%function_scope {Traverse} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments bind (T)%function_scope {U}%function_scope {Bind} {A B}%type_scope _%function_scope _.
#[local] Arguments bindt (T)%function_scope {U}%function_scope {Bindt} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

(** * Derived instances *)
(******************************************************************************)
Module DerivedInstances.

  Section operations.

    Context
      (T : Type -> Type)
      `{Bindt T T}
      `{Return T}.

    #[export] Instance Map_Bindt : Map T :=
      fun (A B : Type) (f : A -> B) => bindt T (fun A => A) (ret T B ∘ f).
    #[export] Instance Bind_Bindt: Bind T T :=
      fun A B f => bindt T (fun A => A) f.
    #[export] Instance Traverse_Bindt: Traverse T :=
      fun G _ _ _ A B f => bindt T G (map G (ret T B) ∘ f).

  End operations.

  Section special_cases.

    Context
      (W : Type)
      (T : Type -> Type)
      (G : Type -> Type)
      `{Return T}
      `{Bindt T T}
      `{Applicative G}.

    (** *** Rewriting rules for special cases of <<bindt>> *)
    (******************************************************************************)
    Lemma bind_to_bindt `(f : A -> T B):
      bind T (U := T) f = bindt T (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_bindt `(f : A -> G B):
      traverse T G f = bindt T G (map G (ret T B) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mapt_to_bindt `(f : A -> G B):
      traverse T G f = bindt T G (map G (ret T B) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindt `(f : A -> B):
      map T f = bindt T (fun A => A) (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mapt>> *)
    (******************************************************************************)
    Lemma map_to_traverse `(f : A -> B):
      map T f = traverse T (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bind>> *)
    (******************************************************************************)
    Lemma map_to_bind `(f : A -> B):
      map T f = bind T (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

  End special_cases.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Section kc_special_cases.

    Context
      `{TraversableMonad T}.
    (*
    t/m:
    00 0 no t or m
    01 1 m
    10 2 t
    11 3 everything
     *)

    Lemma kc3_22 (G1 G2 : Type -> Type):
      forall `{Applicative G1} `{Applicative G2}
        `(g : B -> G2 C) `(f : A -> G1 B),
        (map G2 (ret T C) ∘ g) ⋆3 (map G1 (ret T B) ∘ f) =
          map (G1 ∘ G2) (ret T C) ∘ (map G1 g ∘ f).
    Proof.
      intros. unfold_ops @Map_compose.
      reassociate <- on right. unfold_compose_in_compose.
      rewrite (fun_map_map G1).
      unfold kc3.
      reassociate <- on left.
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt0 T G2).
      reflexivity.
    Qed.

    Lemma kc3_11 : forall `(g : B -> T C) `(f : A -> T B),
        kc3 T (fun A => A) (fun A => A) g f = (g ⋆1 f).
    Proof.
      intros. unfold kc3, kc1.
      reflexivity.
    Qed.

    Corollary kc3_00 : forall `(g : B -> C) `(f : A -> B),
        kc3 T (fun A => A) (fun A => A) (ret T C ∘ g) (ret T B ∘ f) = ret T C ∘ (g ∘ f).
    Proof.
      intros.
      change (@ret T _ C) with (map (fun A => A) (@ret T _ C)).
      change (@ret T _ B) with (map (fun A => A) (@ret T _ B)).
      rewrite (kc3_22 (fun A => A) (fun A => A)).
      reflexivity.
    Qed.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Lemma kc3_32 : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
        kc3 T G1 G2 g (map G1 (ret T B) ∘ f) =
          map G1 g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt0 T); auto.
    Qed.

    Lemma kc3_31 : forall `(g : B -> G2 (T C)) `(f : A -> T B),
        kc3 T (fun A => A) G2 g f = bindt T G2 g ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_30 : forall `(g : B -> G2 (T C)) `(f : A -> B),
        kc3 T (fun A => A) G2 g (ret T B ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc3.
      reassociate <- on left.
      change (map (fun A => A) ?g) with g.
      now rewrite (ktm_bindt0 T G2).
    Qed.

    Lemma kc3_23 : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
        (map G2 (ret T C) ∘ g) ⋆3 f = map G1 (traverse T G2 g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_13 : forall `(g : B -> T C) `(f : A -> G1 (T B)),
        kc3 T G1 (fun A => A) g f = map G1 (bind T g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_03 : forall `(g : B -> C) `(f : A -> G1 (T B)),
        kc3 T G1 (fun A => A) (ret T C ∘ g) f = map G1 (map T g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_21 : forall `(g : B -> G2 C) `(f : A -> T B),
        (map G2 (ret T C) ∘ g) ⋆3 (f : A -> (fun A => A)(T B)) =
          traverse T G2 g ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_20 : forall `(g : B -> G2 C) `(f : A -> B),
        (map G2 (ret T C) ∘ g) ⋆3 (ret T B ∘ f : A -> (fun A => A)(T B)) =
          map G2 (ret T C) ∘ g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reassociate <-.
      change (map (fun A => A) ?f) with f.
      rewrite (ktm_bindt0 T G2).
      reflexivity.
    Qed.

    Lemma kc3_12 : forall `(g : B -> T C) `(f : A -> G1 B),
        kc3 T G1 (fun A => A) g (map G1 (ret T B) ∘ f) = (map G1 g ∘ f).
    Proof.
      intros. unfold kc3. reassociate <-.
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt0 T (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_02 : forall `(g : B -> C) `(f : A -> G1 B),
        kc3 T G1 (fun A => A) (ret T C ∘ g) (map G1 (ret T B) ∘ f) =
          map G1 (ret T C ∘ g) ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt0 T (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_10 : forall `(g : B -> T C) `(f : A -> B),
        kc3 T (fun A => A) (fun A => A) g (ret T B ∘ f) =
          g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      change (map (fun A => A) ?f) with f.
      rewrite (ktm_bindt0 T (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_01 : forall `(g : B -> C) `(f : A -> T B),
        kc3 T (fun A => A) (fun A => A) (ret T C ∘ g) f =
          map T g ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_id_l : forall `(g : A -> G2 (T B)),
        kc3 T (fun A => A) G2 g (ret T A) = g.
    Proof.
      intros. change (ret T A) with (ret T A ∘ (@id A)).
      now rewrite (kc3_30).
    Qed.

    Lemma kc3_id_r : forall `(f : A -> G1 (T B)),
        kc3 T G1 (fun A => A) (ret T B) f = f.
    Proof.
      intros. change (ret T B) with (ret T B ∘ (@id B)).
      rewrite (kc3_03).
      unfold_ops @Map_Bindt.
      change (?f ∘ id) with f.
      rewrite (ktm_bindt1 T).
      now rewrite (fun_map_id G1).
    Qed.

  End kc_special_cases.

  (** ** Composition with lesser Kleisli operations *)
  (******************************************************************************)
  Lemma bindt_app_l `{TraversableMonad T} :
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G) (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f = bindt T G f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma bindt_app_r `{TraversableMonad T} :
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A)) (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f = bindt T G f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity1.
  Qed.

  Section composition_special_cases.

    Context
      (T : Type -> Type)
      `{TraversableMonad T}
      (G1 : Type -> Type)
      (G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}.

    (** *** Composition with <<map>> *)
    (******************************************************************************)
    Lemma map_bindt : forall `(g : B -> C) `(f : A -> G1 (T B)),
        map G1 (map T g) ∘ bindt T G1 f = bindt T G1 (map G1 (map T g) ∘ f).
    Proof.
      intros.
      rewrite map_to_bindt.
      rewrite (ktm_bindt2 T G1 (fun A => A)).
      rewrite (bindt_app_r G1).
      reflexivity.
    Qed.

    Lemma bindt_map : forall `(g : B -> G2 (T C)) `(f : A -> B),
        bindt T G2 g ∘ map T f = bindt T G2 (g ∘ f).
    Proof.
      intros.
      rewrite map_to_bindt.
      change_left (map (fun A => A) (bindt T G2 g) ∘ bindt T (U := T) (fun A => A) (ret T B ∘ f)).
      rewrite (ktm_bindt2 T (fun A => A) G2).
      rewrite (bindt_app_l G2).
      rewrite (kc3_30).
      reflexivity.
    Qed.

    (** *** Composition with <<traverse>> *)
    (******************************************************************************)
    Lemma traverse_bindt : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
        map G1 (traverse T G2 g) ∘ bindt T G1 f =
          bindt T (G1 ∘ G2) (map G1 (traverse T G2 g) ∘ f).
    Proof.
      intros.
      rewrite (traverse_to_bindt).
      rewrite (ktm_bindt2 T); auto.
    Qed.

    Lemma bindt_traverse : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
        map G1 (bindt T G2 g) ∘ traverse T G1 f =
          bindt T (G1 ∘ G2) (map G1 g ∘ f).
    Proof.
      intros.
      rewrite traverse_to_bindt.
      rewrite (ktm_bindt2 T G1 G2).
      rewrite (kc3_32).
      reflexivity.
    Qed.

    (** *** Composition with <<bind>> *)
    (******************************************************************************)
    Lemma bind_bindt : forall `(g : B -> T C) `(f : A -> G1 (T B)),
        map G1 (bind T g) ∘ bindt T G1 f =
          bindt T G1 (map G1 (bind T g) ∘ f).
    Proof.
      intros.
      rewrite bind_to_bindt.
      rewrite (ktm_bindt2 T G1 (fun A => A)).
      rewrite (bindt_app_r G1).
      reflexivity.
    Qed.

    Lemma bindt_bind : forall `(g : B -> G2 (T C)) `(f : A -> T B),
        bindt T G2 g ∘ bind T f =
          bindt T G2 (bindt T G2 g ∘ f).
    Proof.
      intros.
      change_left (map (fun A => A) (bindt T G2 g) ∘ bind T f).
      rewrite bind_to_bindt.
      rewrite (ktm_bindt2 T (fun A => A) G2).
      rewrite (bindt_app_l G2).
      reflexivity.
    Qed.

    (** *** Composition between <<traverse>> and <<bind>> *)
    (******************************************************************************)
    Lemma traverse_bind : forall `(g : B -> G2 C) `(f : A -> T B),
        traverse T G2 g ∘ bind T f =
          bindt T G2 (traverse T G2 g ∘ f).
    Proof.
      intros.
      change_left (map (fun A => A) (traverse T G2 g) ∘ bind T f).
      rewrite (traverse_to_bindt).
      rewrite (bind_to_bindt).
      rewrite (ktm_bindt2 T (fun A => A) G2).
      rewrite (bindt_app_l G2).
      rewrite kc3_21.
      reflexivity.
    Qed.

    Lemma bind_traverse : forall `(g : B -> T C) `(f : A -> G1 B),
        map G1 (bind T g) ∘ traverse T G1 f =
          bindt T G1 (map G1 g ∘ f).
    Proof.
      intros.
      rewrite (traverse_to_bindt).
      rewrite (bind_to_bindt).
      rewrite (ktm_bindt2 T G1 (fun A => A)).
      rewrite (bindt_app_r G1).
      rewrite kc3_12.
      reflexivity.
    Qed.

    (** *** Composition between <<traverse>> and <<map>> *)
    (******************************************************************************)
    Lemma map_traverse : forall
        (A B C : Type) (g : B -> C) (f : A -> G1 B),
        map G1 (map T g) ∘ traverse T G1 f =
          traverse T G1 (map G1 g ∘ f).
    Proof.
      intros.
      rewrite (traverse_to_bindt).
      rewrite (map_to_bindt).
      rewrite (ktm_bindt2 T G1 (fun A => A)).
      rewrite (bindt_app_r G1).
      rewrite kc3_02.
      rewrite (traverse_to_bindt).
      reassociate <-.
      rewrite (fun_map_map G1).
      reflexivity.
    Qed.

    Lemma traverse_map: forall
        (A B C : Type) (g : B -> G2 C) (f : A -> B),
        traverse T G2 g ∘ map T f =
          traverse T G2 (g ∘ f).
    Proof.
      intros.
      change_left (map (fun A => A) (traverse T G2 g) ∘ map T f).
      rewrite (traverse_to_bindt).
      rewrite (map_to_bindt).
      rewrite (ktm_bindt2 T (fun A => A) G2).
      rewrite (bindt_app_l G2).
      rewrite kc3_20.
      reflexivity.
    Qed.

    (** *** Composition between <<bind>> and <<bind>> *)
    (******************************************************************************)
    Lemma bind_bind : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind T g ∘ bind T f = bind T (g ⋆1 f).
    Proof.
      intros.
      change_left (map (fun A => A) (bind T g) ∘ bind T f).
      rewrite (bind_to_bindt).
      rewrite (bind_to_bindt).
      rewrite (ktm_bindt2 T (fun A => A) (fun A => A)).
      rewrite (bindt_app_l (fun A => A)).
      rewrite kc3_11.
      reflexivity.
    Qed.

    Lemma traverse_traverse : forall (A B C : Type)
                                (g : B -> G2 C)
                                (f : A -> G1 B),
        map G1 (traverse T G2 g) ∘ traverse T G1 f = traverse T (G1 ∘ G2) (g ⋆2 f).
    Proof.
      intros.
      rewrite (traverse_to_bindt).
      rewrite (traverse_to_bindt).
      rewrite (ktm_bindt2 T G1 G2).
      rewrite (kc3_22 G1 G2).
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
      change_left (map (fun A => A) (bind T g) ∘ map T f).
      rewrite (bind_to_bindt).
      rewrite (map_to_bindt).
      rewrite (ktm_bindt2 T (fun A => A) (fun A => A)).
      rewrite (bindt_app_l (fun A => A)).
      rewrite kc3_10.
      reflexivity.
    Qed.

    Lemma map_bind : forall (A B C : Type)
                       (g : B -> C)
                       (f : A -> T B),
        map T g ∘ bind T f = bind T (map T g ∘ f).
    Proof.
      intros.
      change_left (map (fun A => A) (map T g) ∘ bind T f).
      rewrite (bind_to_bindt).
      rewrite (map_to_bindt).
      rewrite (ktm_bindt2 T (fun A => A) (fun A => A)).
      rewrite (bindt_app_l (fun A => A)).
      rewrite kc3_01.
      reflexivity.
    Qed.

    (** *** Composition between <<map>> and <<map>> *)
    (******************************************************************************)
    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map T g ∘ map T f = map T (g ∘ f).
    Proof.
      intros.
      change_left (map (fun A => A) (map T g) ∘ map T f).
      do 2 rewrite (map_to_bindt).
      rewrite (ktm_bindt2 T (fun A => A) (fun A => A)).
      rewrite (bindt_app_l (fun A => A)).
      rewrite kc3_00.
      reflexivity.
    Qed.

    (** ** Identity laws *)
    (******************************************************************************)
    Lemma map_id : forall (A : Type),
        map T (@id A) = @id (T A).
    Proof.
      intros.
      rewrite (map_to_bindt).
      change (?g ∘ id) with g.
      now rewrite (ktm_bindt1 T).
    Qed.

    Lemma bind_id : forall (A : Type),
        bind T (ret T A) = id.
    Proof.
      intros.
      rewrite (bind_to_bindt).
      rewrite (ktm_bindt1 T).
      reflexivity.
    Qed.

    Lemma traverse_id : forall (A : Type),
        traverse T (fun A : Type => A) (@id A) = id.
    Proof.
      intros.
      rewrite (traverse_to_bindt).
      change (?g ∘ id) with g.
      change (map (fun A => A) ?g) with g.
      now rewrite (ktm_bindt1 T).
    Qed.

    (** ** Composition with <<ret>> *)
    (******************************************************************************)
    Lemma bind_ret :
      forall (A B : Type) (f : A -> T B),
        bind T f ∘ ret T A = f.
    Proof.
      intros.
      rewrite (bind_to_bindt).
      now rewrite (ktm_bindt0 T (fun A => A)).
    Qed.

    (** ** Morphisms *)
    (******************************************************************************)
    Lemma traverse_morph {ϕ : forall A : Type, G1 A -> G2 A} `{! ApplicativeMorphism G1 G2 ϕ} :
      forall (A B : Type) (f : A -> G1 B), ϕ (T B) ∘ traverse T G1 f = traverse T G2 (ϕ B ∘ f).
    Proof.
      intros.
      do 2 rewrite (traverse_to_bindt).
      rewrite (ktm_morph T).
      reassociate <-.
      inversion ApplicativeMorphism0.
      fequal. unfold compose. ext a.
      rewrite appmor_natural.
      reflexivity.
    Qed.

  End composition_special_cases.

  (** ** Instances *)
  (******************************************************************************)
  Section instances.

    Context
      `{TraversableMonad T}.

    #[export] Instance TM_Functor : Functor T :=
      {| fun_map_id := map_id T;
        fun_map_map := map_map T;
      |}.

    #[export] Instance TM_Monad : Monad T :=
      {| kmon_bind0 := bind_ret T;
        kmon_bind1 := bind_id T;
        kmon_bind2 := bind_bind T;
      |}.

    #[export] Instance TM_TF : TraversableFunctor T :=
      {| trf_traverse_id := traverse_id T;
        trf_traverse_traverse := traverse_traverse T;
        trf_traverse_morphism := traverse_morph T;
      |}.

  End instances.

End DerivedInstances.

Import DerivedInstances.

(** * Batch *)
(******************************************************************************)
Section batch.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma runBatch_batch : forall `{Applicative G} (A B : Type) (f : A -> G (T B)),
      runBatch f ∘ (@batch A (T B)) = f.
  Proof.
    intros. apply (runBatch_batch G).
  Qed.

  Definition toBatch_1 {A : Type} (B : Type) : T A -> @Batch A (T B) (T B) :=
    bindt T (Batch A (T B)) (batch (T B)).

End batch.

(** * <<foldMap>> on monads *)
(******************************************************************************)
Section foldMap.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  (** ** Composition with <<bindt>> *)
  (******************************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M} : forall `(g : B -> M) `(f : A -> G (T B)),
      map G (foldMap T g) ∘ bindt T G f =
        foldMap T (map G (foldMap T g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt T G (const M)).
    rewrite (traverse_to_bindt T (const (G M))).
    fequal.
    - ext A' B' f' t. unfold_ops @Map_compose @Map_const.
      now rewrite (fun_map_id G).
    - ext A' B' [a b]. reflexivity.
  Qed.

  (** ** Composition with <<bind>> and <<ret>> *)
  (******************************************************************************)
  Lemma foldMap_bind `{Monoid M} : forall `(g : B -> M) `(f : A -> T B),
      foldMap T g ∘ bind T f =
        foldMap T (foldMap T g ∘ f).
  Proof.
    intros. unfold foldMap. rewrite (traverse_bind T (const M)).
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M} : forall `(f : A -> M),
      foldMap T f ∘ ret T A = f.
  Proof.
    intros. unfold foldMap. unfold_ops @Traverse_Bindt.
    rewrite (ktm_bindt0 T (const M) A _).
    reflexivity.
  Qed.

End foldMap.

Import Theory.Traversable.Functor.DerivedInstances.

(** ** Expressing operations using <<runBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma bindt_to_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt T G f = runBatch f ∘ toBatch_1 T B.
  Proof.
    unfold toBatch_1.
    rewrite (ktm_morph T (ϕ := @runBatch A G (T B) f _ _ _)).
    now rewrite (runBatch_batch T).
  Qed.

  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse T G f = runBatch f ∘ toBatch T B.
  Proof.
    now rewrite (traverse_to_runBatch T).
  Qed.

  Corollary map_to_runBatch `(f : A -> B) :
    map T f = runBatch f ∘ toBatch T B.
  Proof.
    change (@Map_Bindt T H0 H) with (Map_Traverse T).
    rewrite (map_to_traverse T).
    now rewrite traverse_to_runBatch.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
    @id (T A) = runBatch (@id A) ∘ toBatch T A.
  Proof.
    intros. rewrite <- (trf_traverse_id T).
    rewrite traverse_to_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_to_runBatch : forall `{Monoid M} (fake : Type) `(f : A -> M),
      foldMap T f = runBatch f ∘ toBatch_1 T fake.
  Proof.
    intros.
    unfold foldMap.
    rewrite (traverse_const1 T fake).
    rewrite (traverse_to_bindt).
    rewrite (bindt_to_runBatch).
    reflexivity.
  Qed.

End runBatch.

(*
Import Sets.Notations.
Import Setlike.Functor.Notations.

(** * Characterizing <<∈>> *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  #[export] Instance Monad_Hom_Toset : Kleisli.Monad.Monad_Hom T set (@toset T _).
  Proof.
    constructor.
    - intros.
      unfold_ops @Toset_Traverse.
      rewrite (foldMap_bind T (ret set) f).
      unfold_ops @Traverse_Bindt.
      rewrite (foldMap_morphism T).
      rewrite (kmon_bind0 set).
      reflexivity.
    - intros.
      unfold_ops @Toset_Traverse.
      rewrite (foldMap_ret T).
      reflexivity.
  Qed.

  Theorem in_ret_iff :
    forall (A : Type) (a1 a2 : A), a1 ∈ ret T a2 <-> a1 = a2.
  Proof.
    intros. unfold_ops @Toset_Traverse.
    compose near a2 on left. rewrite (foldMap_ret T).
    solve_basic_set.
  Qed.

  Theorem in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros. compose near t on left.
    rewrite (kmon_hom_bind T set); try typeclasses eauto.
    unfold compose. now rewrite bind_set_spec.
  Qed.

End with_monad.

(** * Respectfulness properties *)
(******************************************************************************)
Section respectfulness_properties.

  Context
    (T : Type -> Type)
    `{Traversable.Monad.Monad T}.

  Lemma bindt_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G (T B)) `(f2 : A -> G (T B)) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> bindt T G f1 t = bindt T G f2 t.
  Proof.
    introv ? hyp. do 2 (rewrite (bindt_to_runBatch T); auto).
    unfold toset, Toset_Traverse in hyp.
    rewrite (foldMap_to_runBatch T B) in hyp.
    unfold compose in *.
    induction (toBatch_tm T B t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros. apply hyp. now left.
      + apply hyp. now right.
  Qed.

  Lemma traverse_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse T G f1 t = traverse T G f2 t.
  Proof.
    apply (Traversable.Functor.traverse_respectful T).
  Qed.

  Lemma traverse_respectful_pure : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = pure G a) -> traverse T G f1 t = pure G t.
  Proof.
    apply (Traversable.Functor.traverse_respectful_pure T).
  Qed.

  Lemma traverse_respectful_map {A B} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure G (g a)) -> traverse T G f t = pure G (map T g t).
  Proof.
    change (@Map_Bindt T H0 H) with (@ToFunctor.Map_Traverse T _).
    apply (Traversable.Functor.traverse_respectful_map T).
  Qed.

  Corollary traverse_respectful_id {A} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G A),
      (forall a, a ∈ t -> f a = pure G a) -> traverse T G f t = pure G t.
  Proof.
    apply (Traversable.Functor.traverse_respectful_id T).
  Qed.

  Corollary map_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> map T f1 t = map T f2 t.
  Proof.
    intros. change (@Map_Bindt T H0 H) with (@ToFunctor.Map_Traverse T _).
    now apply (Traversable.Functor.map_respectful T).
  Qed.

  Corollary map_respectful_id : forall `(f1 : A -> A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = a) -> map T f1 t = t.
  Proof.
    intros. change (@Map_Bindt T H0 H) with (@ToFunctor.Map_Traverse T _).
    now apply (Traversable.Functor.map_respectful_id T).
  Qed.

End respectfulness_properties.
*)




