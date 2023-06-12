From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Classes.Monad
  Classes.Traversable.Functor.

#[local] Generalizable Variables T G A B C ϕ M.

#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

(** * Traversable monad *)
(******************************************************************************)
Section operations.

  Context
    (M : Type)
    (T : Type -> Type)
    (U : Type -> Type).

    Class Bindt := bindt :
        forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (A -> G (T B)) -> U A -> G (U B).

End operations.

Section kc.

  Context
    (T : Type -> Type)
    `{Bindt T T}.

  Definition kc3
    {A B C : Type}
    (G1 G2 : Type -> Type)
    `{Map G1} `{Pure G1} `{Mult G1}
    `{Map G2} `{Pure G2} `{Mult G2} :
    (B -> G2 (T C)) ->
    (A -> G1 (T B)) ->
    (A -> G1 (G2 (T C))) :=
    fun g f => map G1 (T B) (G2 (T C)) (bindt T T G2 B C g) ∘ f.

End kc.

#[local] Infix "⋆3" := (kc3 _ _ _) (at level 60) : tealeaves_scope.

Section class.

  Context
    (T : Type -> Type)
    `{Return T}
    `{Bindt T T}.

  Class TraversableMonad :=
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

End class.

Section kc3_special_cases.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma kc3_22 : forall `{Applicative G1} `{Applicative G2} `(g : B -> G2 C) `(f : A -> G1 B),
      (map G2 C (T C) (ret T C) ∘ g) ⋆3 (map G1 B (T B) (ret T B) ∘ f) =
        map (G1 ∘ G2) C (T C) (ret T C) ∘ map G1 B (G2 C) g ∘ f.
  Proof.
    intros.
    unfold kc3.
    reassociate <-.
    rewrite (fun_map_map G1).
    unfold_ops @Map_compose.
    unfold_compose_in_compose.
    rewrite (fun_map_map G1).
    rewrite (ktm_bindt0 T G2).
    reflexivity.
  Qed.

  Corollary kc3_00 : forall `(g : B -> C) `(f : A -> B),
      (ret T C ∘ g) ⋆3 (ret T B ∘ f) = ret T C ∘ (g ∘ f).
  Proof.
    intros.
    unfold kc3.
    change (map (fun A => A) _ _ ?f) with f.
    reassociate <-.
    rewrite (ktm_bindt0 T (fun A => A)).
    reflexivity.
  Qed.

  Lemma kc3_30 : forall `{Applicative G2} `(g : B -> G2 (T C)) `(f : A -> B),
      g ⋆3 (ret T B ∘ f) = g ∘ f.
  Proof.
    intros. unfold kc3.
    reassociate <- on left.
    change (map (fun A => A) _ _ ?g) with g.
    now rewrite (ktm_bindt0 T).
  Qed.

End kc3_special_cases.

(** * Derived instances *)
(******************************************************************************)
Module DerivedInstances.

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

  End operations.

  Section special_cases.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Return T}
      `{Bindt T T}
      `{Applicative G}.

    (** *** Rewriting rules for special cases of <<bindt>> *)
    (******************************************************************************)
    Lemma bind_to_bindt `(f : A -> T B):
      bind T T A B f = bindt T T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_bindt `(f : A -> G B):
      traverse T G f = bindt T G (map G (ret T) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mapt_to_bindt `(f : A -> G B):
      traverse T G f = bindt T G (map G (ret T) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindt `(f : A -> B):
      map T f = bindt T (fun A => A) (ret T ∘ f).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mapt>> *)
    (******************************************************************************)
    Lemma map_to_mapt `(f : A -> B):
      map T f = traverse T (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bind>> *)
    (******************************************************************************)
    Lemma map_to_bind `(f : A -> B):
      map T f = bind T (ret T ∘ f).
    Proof.
      reflexivity.
    Qed.

  End special_cases.

  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Kleisli.Traversable.Monad.Monad T}.

    (** *** Functor instance *)
    (******************************************************************************)
    Lemma map_id : forall (A : Type),
        map T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Map_Bindt.
      change (?g ∘ id) with g.
      now rewrite (ktm_bindt1 T).
    Qed.

    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map T g ∘ map T f = map T (g ∘ f).
    Proof.
      intros. unfold_ops @Map_Bindt.
      change (bindt T (fun A : Type => A) (ret T ∘ g))
        with (map (fun A => A) (bindt T (fun A => A) (ret T ∘ g))).
      rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A) (G2 := fun A => A));
        try typeclasses eauto.
      fequal. now rewrite Mult_compose_identity1.
      rewrite kcompose_tm_ret_I; auto.
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

    (** *** Monad instance *)
    (******************************************************************************)
    #[export] Instance: Kleisli.Monad.Monad T.
    Proof.
      constructor; unfold_ops @Bind_Bindt.
      - intros. now rewrite (ktm_bindt0 T _ _ (G := fun A => A)).
      - intros. now rewrite (ktm_bindt1 T).
      - intros.
        change_left (map (fun A => A) (bindt T (fun A0 : Type => A0) g) ∘ bindt T (fun A0 : Type => A0) f).
        rewrite (ktm_bindt2 T _ _ _ (G2 := fun A => A) (G1 := fun A => A)).
        fequal. now rewrite Mult_compose_identity1.
    Qed.

    (** *** Traversable functor instance *)
    (******************************************************************************)
    #[export] Instance: Kleisli.Traversable.Functor.TraversableFunctor T.
    Proof.
      constructor; unfold_ops @Traverse_Bindt.
      - intros. change (?g ∘ id) with g.
        change (map (fun A => A) ?g) with g.
        now rewrite (ktm_bindt1 T).
      - intros. rewrite (ktm_bindt2 T); auto.
        rewrite kcompose_tm_ret; auto.
      - intros. rewrite (ktm_morph T); auto. reassociate <-.
        fequal. unfold compose. ext a. now rewrite (appmor_natural G1 G2).
    Qed.

  End with_kleisli.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Section Kleisli_composition.

    Context
     `{Traversable.Monad.Monad T}
      `{Applicative G2}
      `{Applicative G1}.
    (*
    t/m:
    00 0 no t or m
    01 1 no m
    10 2 no t
    11 3 everything
     *)

  Lemma kcompose_tm00 : forall `(g : B -> C) `(f : A -> B),
     kcompose_tm (G1 := fun A => A) (G2 := fun A => A) (ret T ∘ g) (ret T ∘ f) = ret T ∘ g ∘ f.
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    change (map (fun A => A) ?f) with f.
    rewrite (ktm_bindt0 T _ _ (G := fun A => A)); auto.
  Qed.

  Lemma kcompose_tm11 : forall `(g : B -> G2 C) `(f : A -> G1 B),
      (map G2 (ret T) ∘ g) ⋆tm (map G1 (ret T) ∘ f) = map (G1 ∘ G2) (ret T) ∘ (map G1 g ∘ f).
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    rewrite (fun_map_map G1). reassociate <-.
    unfold_ops @Map_compose.
    unfold_compose_in_compose.
    rewrite (fun_map_map G1).
    rewrite (ktm_bindt0 T); auto.
  Qed.

  Lemma kcompose_tm22 : forall `(g : B -> T C) `(f : A -> T B),
      kcompose_tm (G1 := fun A => A) (G2 := fun A => A) g f = (g ⋆ f).
  Proof.
    intros. unfold kcompose_tm, kcompose.
    reflexivity.
  Qed.

  Lemma kcompose_tm12 : forall `(g : B -> G2 C) `(f : A -> T B),
      (map G2 (ret T) ∘ g) ⋆tm (f : A -> (fun A => A)(T B)) =
        traverse T G2 g ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm21 : forall `(g : B -> T C) `(f : A -> G1 B),
      kcompose_tm (G1 := G1) (G2 := fun A => A) g (map G1 (ret T) ∘ f) = (map G1 g ∘ f).
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    rewrite (fun_map_map G1). rewrite (ktm_bindt0 T _ _ (G := fun A => A)); auto.
  Qed.

  Lemma kcompose_tm31 : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
      g ⋆tm map G1 (ret T) ∘ f = map G1 g ∘ f.
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    rewrite (fun_map_map G1). rewrite (ktm_bindt0 T); auto.
  Qed.

  Lemma kcompose_tm32 : forall `(g : B -> G2 (T C)) `(f : A -> T B),
      kcompose_tm (G1 := fun A => A) g f = bindt T G2 g ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm30 : forall `(g : B -> G2 (T C)) `(f : A -> B),
      kcompose_tm (G1 := fun A => A) g (ret T ∘ f) = g ∘ f.
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    change (map (fun A => A) ?f) with f.
    rewrite (ktm_bindt0 T); auto.
  Qed.

  Lemma kcompose_tm13 : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
      (map G2 (ret T) ∘ g) ⋆tm f = map G1 (traverse T G2 g) ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm23 : forall `(g : B -> T C) `(f : A -> G1 (T B)),
      kcompose_tm (G2 := fun A => A) g f = map G1 (bind T g) ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm03 : forall `(g : B -> C) `(f : A -> G1 (T B)),
      kcompose_tm (G2 := fun A => A) (ret T ∘ g) f = map G1 (map T g) ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm_lunit : forall `(g : A -> G2 (T B)),
     kcompose_tm (G1 := fun A => A) g (ret T) = g.
  Proof.
    intros. change (ret T) with (ret T ∘ (@id A)).
    now rewrite (kcompose_tm30).
  Qed.

  Lemma kcompose_tm_runit : forall `(f : A -> G1 (T B)),
     kcompose_tm (G2 := fun A => A) (ret T) f = f.
  Proof.
    intros. change (ret T) with (ret T ∘ (@id B)).
    rewrite (kcompose_tm03).
    rewrite (fun_map_id T).
    now rewrite (fun_map_id G1).
  Qed.

  End Kleisli_composition.

  (** ** Composition with lesser Kleisli operations *)
  (******************************************************************************)
  Section Kleisli_composition.

    Context
      (T : Type -> Type)
     `{Traversable.Monad.Monad T}
      (G1 : Type -> Type)
      (G2 : Type -> Type)
      `{Applicative G2}
      `{Applicative G1}.

  (** *** Composition with <<map>> *)
  (******************************************************************************)
  Lemma map_bindt : forall `(g : B -> C) `(f : A -> G1 (T B)),
      map G1 (map T g) ∘ bindt T G1 f = bindt T G1 (map G1 (map T g) ∘ f).
  Proof.
    intros. unfold map at 2. unfold_ops @Map_Bindt.
    rewrite (ktm_bindt2 T _ _ _ (G1 := G1) (G2 := fun A => A)).
    fequal. rewrite Mult_compose_identity1.
    reflexivity.
  Qed.

  Lemma bindt_map : forall `(g : B -> G2 (T C)) `(f : A -> B),
      bindt T G2 g ∘ map T f = bindt T G2 (g ∘ f).
  Proof.
    intros. unfold map. unfold_ops @Map_Bindt.
    change_left (map (fun A => A) (bindt T G2 g) ∘ bindt T (fun A => A) (ret T ∘ f)).
    rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A) (G2 := G2)).
    fequal. now rewrite Mult_compose_identity2.
    rewrite kcompose_tm30; auto.
  Qed.

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma traverse_bindt : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
      map G1 (traverse T G2 g) ∘ bindt T G1 f =
        bindt T (G1 ∘ G2) (map G1 (traverse T G2 g) ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Bindt @Bind_Bindt.
    rewrite (ktm_bindt2 T); auto.
  Qed.

  Lemma bindt_traverse : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
      map G1 (bindt T G2 g) ∘ traverse T G1 f =
        bindt T (G1 ∘ G2) (map G1 g ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Bindt @Bind_Bindt.
    rewrite (ktm_bindt2 T); auto.
    fequal. rewrite kcompose_tm31; auto.
  Qed.

  (** *** Composition with <<bind>> *)
  (******************************************************************************)
  Lemma bind_bindt : forall `(g : B -> T C) `(f : A -> G1 (T B)),
      map G1 (bind T g) ∘ bindt T G1 f =
        bindt T G1 (map G1 (bind T g) ∘ f).
  Proof.
    intros. unfold_ops @Bind_Bindt @Bind_Bindt.
    rewrite (ktm_bindt2 T _ _ _ (G2 := fun A => A) (G1 := G1)); auto.
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma bindt_bind : forall `(g : B -> G2 (T C)) `(f : A -> T B),
      bindt T G2 g ∘ bind T f =
        bindt T G2 (bindt T G2 g ∘ f).
  Proof.
    intros. unfold_ops @Bind_Bindt @Bind_Bindt.
    change_left (map (fun A => A) (bindt T G2 g) ∘ (bindt T (fun A0 : Type => A0) f)).
    rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A) (G2 := G2)); auto.
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  (** *** Composition between <<traverse>> and <<bind>> *)
  (******************************************************************************)
  Lemma traverse_bind : forall `(g : B -> G2 C) `(f : A -> T B),
      traverse T G2 g ∘ bind T f =
        bindt T G2 (traverse T G2 g ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Bindt @Bind_Bindt.
    change_left (map (fun A => A) (bindt T G2 (map G2 (ret T) ∘ g)) ∘ bindt T (fun A0 : Type => A0) f).
    rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A)); auto.
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma bind_traverse : forall `(g : B -> T C) `(f : A -> G1 B),
      map G1 (bind T g) ∘ traverse T G1 f =
        bindt T G1 (map G1 g ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Bindt @Bind_Bindt.
    rewrite (ktm_bindt2 T _ _ _ (G2 := fun A => A)); auto.
    fequal. now rewrite Mult_compose_identity1.
    now rewrite kcompose_tm31.
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
    change (@Map_Bindt T H0 H) with (@ToFunctor.Map_Traverse T _).
    rewrite (ToFunctor.map_traverse T G1); try typeclasses eauto.
    reflexivity.
  Qed.

  Lemma traverse_map: forall (A B C : Type)
                         (g : B -> G2 C)
                         (f : A -> B),
      traverse T G2 g ∘ map T f =
        traverse T G2 (g ∘ f).
  Proof.
    intros.
    change (@Map_Bindt T H0 H) with (@ToFunctor.Map_Traverse T _).
    rewrite (ToFunctor.traverse_map T G2); try typeclasses eauto.
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
    change (@Map_Bindt T H0 H) with (@ToFunctor.Map_Bind T _ _).
    now rewrite (ToFunctor.bind_map T).
  Qed.

  Lemma map_bind : forall (A B C : Type)
                         (g : B -> C)
                         (f : A -> T B),
      map T g ∘ bind T f = bind T (map T g ∘ f).
  Proof.
    intros.
    change (@Map_Bindt T H0 H) with (@ToFunctor.Map_Bind T _ _).
    now rewrite (ToFunctor.map_bind T).
  Qed.

  End Kleisli_composition.

End Derived.
